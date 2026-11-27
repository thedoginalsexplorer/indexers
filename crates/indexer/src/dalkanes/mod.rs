//! Dalkanes: WebAssembly smart contracts on Dogecoin (github.com/jonheaven/dalkanes, spec v0.4).
//!
//! A background task follows the main index block by block from the mainnet activation height
//! (6,466,500). For each block it stores the WASM deploys the inscription index completed
//! (§4), runs every `0xD1` call in the pinned interpreter (`vm.rs`, wasmi 1.1.0, §5–§7), keeps
//! contract storage and the host ledger (§8), and moves output parcels (§16). Everything a block
//! changes is written in one batch together with the block's undo record and the next height, so a
//! crash never leaves half a block, and a reorg puts back exactly what the block changed (§11).

pub mod sig;
pub mod vm;
pub mod wire;

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::rc::Rc;
use std::sync::Mutex;
use std::time::{Duration, Instant};

use anyhow::{Context, Result};
use dogeord_core::Config;
use once_cell::sync::Lazy;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use tokio::time::sleep;
use tracing::{info, warn};

use crate::insc_index::{self as ii, SeqEntry};
use crate::store::{self, Batch, Tree};
use crate::{RpcBlock, RpcTx, decode_inscription_content, indexer_rpc_client, rpc_call};
use vm::{Id, StateView, id_from_key, id_key};
use wire::{Message, TxMessage};

/// Mainnet activation (§2): blocks below it have no Dalkanes effect.
pub const ACTIVATION: u64 = 6_466_500;
const STATE_KEY: &[u8] = b"dalk_state_v1";
/// The rules this index was built with. Raising it clears the Dalkanes trees and replays from
/// activation (about a minute): 2 = spec v0.4 edge-case pass (strict call forms, the pointer as a
/// deposit, print births, 2026-11-26).
const RULES: u64 = 2;
const RULES_KEY: &[u8] = b"dalk_rules";
/// Undo records and block hashes kept for reorgs.
const KEEP: u64 = 200;

/// Canonical builds, labelled only when the code hash matches (§17–§21).
const CANON: &[(&str, &str, &str)] = &[
  ("5b9fa2476e0e669aa3126cbdb4c172c29a0685e5bc0e831411e96d7836a5a916", "howl", "Howl"),
  ("0d48882f4c3a5a564e6a0db55d04daa5ef7c60b765e7cbe5965a4324133999f6", "ash", "Ash"),
  ("9fa39d1c852c1113f25fbae64cb87ca628f1e151586e3c11db88c51d15548148", "vigil", "Vigil"),
  ("6a0d1a554907a38c1505b25829aeaa6dc600bb69cbf76c793ee1019ca5494f78", "quiet", "Quiet"),
  ("9f0b242421ddac33991e66e6fca4242b6a356c602d7e61c40baec65b55664194", "ember", "Ember"),
  ("43a9ebb3a709a6622d15df9328670aea26ffb4c30a9f65fe8e78848fa142183c", "proof", "Proof"),
  ("3cba30282ed8344d15416e980c997cb8197d3d587972ea9c3df93a261ae89bf0", "shibkane", "Shibkane"),
  ("38f37f99d4cd20529ef865daf5bef3fb2c44e977f9b0c8cb623b5aee6b0236ab", "amm", "Ðalkanes AMM template"),
  ("6cabfb3380a98a4b4767b8d83d0d32374fbea3e651540e2fcbf13a6e236b258c", "freemint", "Free-mint template"),
];

pub fn canon_of(code_hash: &str) -> Option<(&'static str, &'static str)> {
  CANON.iter().find(|(h, _, _)| *h == code_hash).map(|(_, k, l)| (*k, *l))
}

pub fn fmt_id(id: Id) -> String {
  format!("{}:{}", id.0, id.1)
}

pub fn parse_id(s: &str) -> Option<Id> {
  let (a, b) = s.split_once(':')?;
  Some((a.parse().ok()?, b.parse().ok()?))
}

// ---------------------------------------------------------------------------
// Stored records

/// A contract (§4.3).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeployMeta {
  pub id: String,
  pub height: u64,
  pub tx_index: u32,
  /// The transaction the deploy completed in.
  pub txid: String,
  pub inscription_id: String,
  pub content_type: String,
  pub code_hash: String,
  pub code_len: usize,
  pub time: u64,
  /// For a print (§20): the inscribed program it was born from.
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub program: Option<String>,
}

/// A call's receipt (§9).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Receipt {
  pub target: String,
  pub ok: bool,
  pub fuel_used: u64,
  pub fuel_granted: u64,
  pub return_hex: String,
  pub error: Option<String>,
  pub logs: Vec<String>,
  /// The print id this call bore (§20); consensus-relevant.
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub born: Option<String>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Amount {
  pub id: String,
  pub amount: String,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct OutParcel {
  pub vout: u32,
  pub address: Option<String>,
  pub id: String,
  pub amount: String,
}

/// Everything Dalkanes saw in one transaction.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct TxRecord {
  pub txid: String,
  pub height: u64,
  pub tx_index: u32,
  pub time: u64,
  /// A contract this transaction deployed.
  pub deploy: Option<String>,
  /// none, call, parcel or ambiguous.
  pub message: String,
  pub carrier_vout: Option<u32>,
  /// Koinu burned on the carrier output (`alkane_value`).
  pub value: u64,
  pub target: Option<String>,
  pub fuel: Option<String>,
  pub inputs: Vec<String>,
  pub opcode: Option<String>,
  pub pointer: Option<u32>,
  pub edicts: Vec<serde_json::Value>,
  pub sender: Option<String>,
  pub receipt: Option<Receipt>,
  /// Parcels the inputs carried in.
  pub parcels_in: Vec<Amount>,
  /// Parcels placed on this transaction's outputs.
  pub parcels_out: Vec<OutParcel>,
  pub burned: Vec<Amount>,
  /// Deposited into the call and kept on the contract's sheet.
  pub deposited: Vec<Amount>,
}

/// Parcels on one output.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct ParcelRec {
  address: Option<String>,
  items: Vec<(String, String)>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct State {
  next_height: u64,
  hashes: VecDeque<(u64, String)>,
}

// ---------------------------------------------------------------------------
// Trees

const T_CODE: u8 = 0;
const T_WASM: u8 = 1;
const T_STORAGE: u8 = 2;
const T_LEDGER: u8 = 3;
const T_PARCEL: u8 = 4;
const T_TX: u8 = 5;
const T_IDX: u8 = 6;
const TREE_NAMES: [&str; 7] = ["dalk_code", "dalk_wasm", "dalk_storage", "dalk_ledger", "dalk_parcel", "dalk_tx", "dalk_idx"];

struct Trees {
  meta: Tree,
  seq: Tree,
  content: Tree,
  t: Vec<Tree>,
  undo: Tree,
}

impl Trees {
  fn open(db: &store::Db) -> Result<Self> {
    Ok(Self {
      meta: db.open_tree("meta")?,
      seq: db.open_tree("inscription_seq")?,
      content: db.open_tree("inscription_content")?,
      t: TREE_NAMES.iter().map(|n| db.open_tree(n)).collect::<Result<_>>()?,
      undo: db.open_tree("dalk_undo")?,
    })
  }
  fn get(&self, tree: u8, key: &[u8]) -> Result<Option<Vec<u8>>> {
    Ok(self.t[tree as usize].get(key)?.map(|v| v.as_ref().to_vec()))
  }
}

fn load_state(meta: &Tree) -> Result<State> {
  Ok(match meta.get(STATE_KEY)? {
    Some(raw) => serde_json::from_slice(raw.as_ref()).context("decode dalkanes state")?,
    None => State { next_height: ACTIVATION, ..Default::default() },
  })
}

fn hk(height: u64, tx: u32) -> [u8; 12] {
  ii::seq_key(height, tx)
}

fn u128_of(v: &[u8]) -> u128 {
  let mut b = [0u8; 16];
  let n = v.len().min(16);
  b[..n].copy_from_slice(&v[..n]);
  u128::from_le_bytes(b)
}

// ---------------------------------------------------------------------------
// Writes with undo

/// Every write of one block. Reads see the block's own writes; the first time a key is touched its
/// value from before the block is kept for the undo record.
struct Writes<'a> {
  t: &'a Trees,
  pending: HashMap<(u8, Vec<u8>), Option<Vec<u8>>>,
  order: Vec<(u8, Vec<u8>)>,
}

impl<'a> Writes<'a> {
  fn new(t: &'a Trees) -> Self {
    Self { t, pending: HashMap::new(), order: Vec::new() }
  }
  fn get(&self, tree: u8, key: &[u8]) -> Result<Option<Vec<u8>>> {
    match self.pending.get(&(tree, key.to_vec())) {
      Some(v) => Ok(v.clone()),
      None => self.t.get(tree, key),
    }
  }
  fn put(&mut self, tree: u8, key: Vec<u8>, val: Option<Vec<u8>>) {
    let k = (tree, key);
    if !self.pending.contains_key(&k) {
      self.order.push(k.clone());
    }
    self.pending.insert(k, val);
  }
  /// The batch for the block, its undo record, and the next state, all in one.
  fn commit(self, height: u64, st: &State) -> Result<()> {
    let mut batch = Batch::default();
    let mut undo: Vec<(u8, Vec<u8>, Option<Vec<u8>>)> = Vec::new();
    for (tree, key) in &self.order {
      let prev = self.t.get(*tree, key)?;
      let new = self.pending.get(&(*tree, key.clone())).cloned().flatten();
      if prev == new {
        continue;
      }
      undo.push((*tree, key.clone(), prev));
      match new {
        Some(v) => batch.insert(&self.t.t[*tree as usize], key.clone(), v),
        None => batch.remove(&self.t.t[*tree as usize], key.clone()),
      }
    }
    batch.insert(&self.t.undo, height.to_be_bytes().to_vec(), bincode::serialize(&undo)?);
    if height >= KEEP {
      batch.remove(&self.t.undo, (height - KEEP).to_be_bytes().to_vec());
    }
    batch.insert(&self.t.meta, STATE_KEY.to_vec(), serde_json::to_vec(st)?);
    batch.commit(&self.t.meta)
  }
}

/// Puts back everything block `height` changed.
fn undo_block(t: &Trees, height: u64, st: &State) -> Result<()> {
  let mut batch = Batch::default();
  if let Some(raw) = t.undo.get(height.to_be_bytes())? {
    let undo: Vec<(u8, Vec<u8>, Option<Vec<u8>>)> = bincode::deserialize(raw.as_ref())?;
    for (tree, key, prev) in undo.into_iter().rev() {
      match prev {
        Some(v) => batch.insert(&t.t[tree as usize], key, v),
        None => batch.remove(&t.t[tree as usize], key),
      }
    }
  }
  batch.remove(&t.undo, height.to_be_bytes().to_vec());
  batch.insert(&t.meta, STATE_KEY.to_vec(), serde_json::to_vec(st)?);
  batch.commit(&t.meta)
}

// ---------------------------------------------------------------------------
// Execution state for one block

/// Committed state with this block's earlier effects in front of it (§6.1).
struct BlockView {
  code: Tree,
  wasm: Tree,
  storage: Tree,
  ledger: Tree,
  height: u64,
  /// Deploys of this block: id -> code (visible to a call at a later or equal tx index).
  deploys: RefCell<HashMap<Id, Rc<Vec<u8>>>>,
  store: RefCell<HashMap<(Id, Vec<u8>), Vec<u8>>>,
  led: RefCell<HashMap<Vec<u8>, u128>>,
}

impl BlockView {
  fn open(db: &store::Db, height: u64) -> Result<Self> {
    Ok(Self {
      code: db.open_tree("dalk_code")?,
      wasm: db.open_tree("dalk_wasm")?,
      storage: db.open_tree("dalk_storage")?,
      ledger: db.open_tree("dalk_ledger")?,
      height,
      deploys: RefCell::new(HashMap::new()),
      store: RefCell::new(HashMap::new()),
      led: RefCell::new(HashMap::new()),
    })
  }
}

fn storage_key(id: Id, key: &[u8]) -> Vec<u8> {
  let mut k = id_key(id).to_vec();
  k.extend_from_slice(key);
  k
}

impl BlockView {
  /// Whether `id` is a print (§20), born earlier in this block or before it.
  fn is_print(&self, id: Id, births: &HashMap<Id, Id>) -> bool {
    births.contains_key(&id)
      || self.code.get(id_key(id)).ok().flatten().and_then(|v| serde_json::from_slice::<DeployMeta>(v.as_ref()).ok()).is_some_and(|m| m.program.is_some())
  }
}

impl StateView for BlockView {
  fn code(&self, id: Id, height: u64, tx: u32) -> Option<Rc<Vec<u8>>> {
    if id.0 == self.height {
      return if id.1 <= tx || height > self.height { self.deploys.borrow().get(&id).cloned() } else { None };
    }
    if id.0 > height {
      return None;
    }
    let _ = &self.code;
    self.wasm.get(id_key(id)).ok().flatten().map(|v| Rc::new(v.as_ref().to_vec()))
  }
  fn storage(&self, id: Id, key: &[u8]) -> Option<Vec<u8>> {
    if let Some(v) = self.store.borrow().get(&(id, key.to_vec())) {
      return Some(v.clone());
    }
    self.storage.get(storage_key(id, key)).ok().flatten().map(|v| v.as_ref().to_vec())
  }
  fn ledger(&self, key: &[u8]) -> u128 {
    if let Some(v) = self.led.borrow().get(key) {
      return *v;
    }
    self.ledger.get(key).ok().flatten().map(|v| u128_of(v.as_ref())).unwrap_or(0)
  }
}

static ENGINE: Lazy<wasmi::Engine> = Lazy::new(vm::engine);

// ---------------------------------------------------------------------------
// Addresses

const B58: &[u8] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";

/// The Dogecoin P2PKH address of a 20-byte key hash.
pub fn p2pkh_address(h: &[u8; 20]) -> String {
  let mut b = vec![0x1e];
  b.extend_from_slice(h);
  let c = Sha256::digest(Sha256::digest(&b));
  b.extend_from_slice(&c[..4]);
  let zeros = b.iter().take_while(|x| **x == 0).count();
  let mut digits: Vec<u8> = Vec::new();
  for &byte in &b {
    let mut carry = byte as u32;
    for d in digits.iter_mut() {
      carry += (*d as u32) << 8;
      *d = (carry % 58) as u8;
      carry /= 58;
    }
    while carry > 0 {
      digits.push((carry % 58) as u8);
      carry /= 58;
    }
  }
  let mut s = "1".repeat(zeros);
  s.extend(digits.iter().rev().map(|d| B58[*d as usize] as char));
  s
}

// ---------------------------------------------------------------------------
// One block

fn is_op_return(tx: &RpcTx, vout: u32) -> Option<bool> {
  tx.vout.iter().find(|o| o.n == vout).map(|o| o.script_pub_key.hex.as_deref().unwrap_or("").starts_with("6a"))
}

fn addr_of(tx: &RpcTx, vout: u32) -> Option<String> {
  tx.vout.iter().find(|o| o.n == vout).and_then(|o| o.script_pub_key.addresses.as_ref()).and_then(|a| a.first().cloned())
}

fn first_real_output(tx: &RpcTx) -> Option<u32> {
  tx.vout.iter().find(|o| !o.script_pub_key.hex.as_deref().unwrap_or("").starts_with("6a")).map(|o| o.n)
}

fn add(m: &mut BTreeMap<Id, u128>, id: Id, a: u128) {
  if a > 0 {
    let e = m.entry(id).or_insert(0);
    *e = e.saturating_add(a);
  }
}

fn amounts(m: &BTreeMap<Id, u128>) -> Vec<Amount> {
  m.iter().filter(|(_, a)| **a > 0).map(|(id, a)| Amount { id: fmt_id(*id), amount: a.to_string() }).collect()
}

fn parcel_key(txid: &str, vout: u32) -> Vec<u8> {
  format!("{txid}:{vout}").into_bytes()
}

/// Holder rows: `h|token12|address|outpoint` -> amount, and `a|address|outpoint` -> (empty).
fn holder_key(token: Id, addr: &str, outpoint: &[u8]) -> Vec<u8> {
  let mut k = b"h|".to_vec();
  k.extend_from_slice(&id_key(token));
  k.extend_from_slice(addr.as_bytes());
  k.push(b'|');
  k.extend_from_slice(outpoint);
  k
}

fn addr_key(addr: &str, outpoint: &[u8]) -> Vec<u8> {
  let mut k = b"a|".to_vec();
  k.extend_from_slice(addr.as_bytes());
  k.push(b'|');
  k.extend_from_slice(outpoint);
  k
}

/// What a transaction's message says to do with the parcels its inputs carry (§16.2).
pub(crate) enum Routing<'a> {
  /// No `0xD1` output, or a version `0x01` call: everything to the first output that can hold it.
  Default,
  /// §5.1 ambiguous: everything burns.
  Ambiguous,
  Message { pointer: u32, edicts: &'a [wire::Edict] },
}

#[derive(Debug, Default)]
pub(crate) struct Routed {
  pub alloc: BTreeMap<u32, BTreeMap<Id, u128>>,
  /// Routed to `u32::MAX - 1`: into the call (§16.3).
  pub deposits: BTreeMap<Id, u128>,
  pub burned: BTreeMap<Id, u128>,
}

/// §16.2: edicts in order (clamped, skipping tokens the inputs lack), then the rest to the pointer.
/// An output that cannot hold a parcel (missing, or any `OP_RETURN`) burns what is sent to it;
/// `u32::MAX - 1` deposits into the call, as an edict output or as the pointer.
pub(crate) fn route(gathered: &BTreeMap<Id, u128>, routing: Routing, can_hold: &dyn Fn(u32) -> bool, first_real: Option<u32>) -> Routed {
  let mut r = Routed::default();
  let send = |r: &mut Routed, out: u32, id: Id, a: u128| {
    if out == wire::DEPOSIT_VOUT {
      add(&mut r.deposits, id, a);
    } else if out != wire::NO_POINTER && can_hold(out) {
      add(r.alloc.entry(out).or_default(), id, a);
    } else {
      add(&mut r.burned, id, a);
    }
  };
  match routing {
    Routing::Default => {
      for (id, a) in gathered {
        match first_real {
          Some(v) => add(r.alloc.entry(v).or_default(), *id, *a),
          None => add(&mut r.burned, *id, *a),
        }
      }
    }
    Routing::Ambiguous => {
      for (id, a) in gathered {
        add(&mut r.burned, *id, *a);
      }
    }
    Routing::Message { pointer, edicts } => {
      let mut avail = gathered.clone();
      for e in edicts {
        let Some(have) = avail.get_mut(&e.token) else { continue };
        let amt = if e.amount == 0 { *have } else { e.amount.min(*have) };
        if amt == 0 {
          continue;
        }
        *have -= amt;
        send(&mut r, e.output, e.token, amt);
      }
      for (id, a) in avail {
        if a > 0 {
          send(&mut r, pointer, id, a);
        }
      }
    }
  }
  r
}

/// §16.3: a deposit the call did not keep goes to the pointer when it names an output that can hold
/// it; otherwise (no pointer, the deposit sentinel, a missing or `OP_RETURN` output) it burns.
pub(crate) fn refund(r: &mut Routed, deposits: &BTreeMap<Id, u128>, pointer: u32, can_hold: &dyn Fn(u32) -> bool) {
  for (id, a) in deposits {
    if pointer != wire::NO_POINTER && pointer != wire::DEPOSIT_VOUT && can_hold(pointer) {
      add(r.alloc.entry(pointer).or_default(), *id, *a);
    } else {
      add(&mut r.burned, *id, *a);
    }
  }
}

/// What a call needs from the transaction: message parts and its raw bytes (for the sender).
struct CallIn<'a> {
  cp: &'a wire::Cellpack,
  carrier: u32,
  incoming: Vec<(Id, u128)>,
}

struct BlockCtx<'a> {
  height: u64,
  time: u64,
  view: Rc<BlockView>,
  budget: u64,
  raw: &'a HashMap<String, Vec<u8>>,
  /// Prints born in this block: print id -> program id (§20).
  births: HashMap<Id, Id>,
}

/// Runs one call (§6), landing check included (§16). Commits it into the block view on success.
fn run_call(ctx: &mut BlockCtx, tx: &RpcTx, i: u32, c: &CallIn, rec: &mut TxRecord) -> Option<vm::CallResult> {
  let target = c.cp.target;
  // no visible code: no effect, no receipt (§5.4)
  let code = ctx.view.code(target, ctx.height, i)?;
  // §20: opcode 77 on an inscribed Proof or Shibkane program births a print, the pull's own block:tx,
  // and the program runs as that id
  let print_program = matches!(canon_of(&hex::encode(Sha256::digest(&code[..]))), Some(("proof" | "shibkane", _)));
  let birth = print_program && c.cp.inputs.first() == Some(&77) && !ctx.view.is_print(target, &ctx.births);
  let born: Id = (ctx.height, i);
  let value = tx.vout.iter().find(|o| o.n == c.carrier).and_then(|o| crate::to_satoshis(o.value).ok()).unwrap_or(0);
  rec.value = value;
  let sender = ctx.raw.get(&tx.txid).and_then(|r| sig::sender(r));
  rec.sender = sender.as_ref().map(p2pkh_address);
  if ctx.budget == 0 {
    rec.receipt = Some(Receipt { target: fmt_id(target), error: Some("block fuel budget exhausted".into()), ..Default::default() });
    return None;
  }
  if birth && ctx.view.code(born, ctx.height, i).is_some() {
    // one transaction has one id: a transaction that deployed a contract cannot also be a print
    rec.receipt = Some(Receipt { target: fmt_id(target), error: Some("print birth refused: this transaction already has an id".into()), ..Default::default() });
    return None;
  }
  if birth {
    ctx.view.deploys.borrow_mut().insert(born, code.clone());
  }
  let granted = c.cp.fuel.min(vm::MAX_FUEL).max(1).min(ctx.budget);
  let env = vm::CallEnv {
    height: ctx.height,
    tx: i,
    time: ctx.time,
    target: if birth { born } else { target },
    fuel: granted,
    calldata: vm::calldata(&c.cp.inputs),
    value,
    sender,
    incoming: c.incoming.clone(),
  };
  let view: Rc<dyn StateView> = ctx.view.clone();
  let mut r = vm::execute(&ENGINE, view, &env);
  ctx.budget = ctx.budget.saturating_sub(r.fuel_used);
  if r.ok && r.outgoing.iter().any(|(_, v, _)| is_op_return(tx, *v) != Some(false)) {
    r.ok = false;
    r.error = Some("parcel sent to a missing or OP_RETURN output".into());
    r.storage.clear();
    r.ledger.clear();
    r.outgoing.clear();
  }
  rec.receipt = Some(Receipt {
    target: fmt_id(target),
    ok: r.ok,
    fuel_used: r.fuel_used,
    fuel_granted: granted,
    return_hex: hex::encode(&r.ret),
    error: r.error.clone(),
    logs: r.logs.clone(),
    born: (birth && r.ok).then(|| fmt_id(born)),
  });
  if !r.ok {
    if birth {
      ctx.view.deploys.borrow_mut().remove(&born);
    }
    return None;
  }
  if birth {
    ctx.births.insert(born, target);
  }
  {
    let mut s = ctx.view.store.borrow_mut();
    for (k, v) in &r.storage {
      s.insert(k.clone(), v.clone());
    }
    let mut l = ctx.view.led.borrow_mut();
    for (k, v) in &r.ledger {
      l.insert(k.clone(), *v);
    }
  }
  Some(r)
}

/// The deploys block `height` completes: tx index -> (inscription id, content type, code).
fn deploys_of(t: &Trees, height: u64) -> Result<BTreeMap<u32, (String, String, Vec<u8>)>> {
  let mut out = BTreeMap::new();
  let mut rows = Vec::new();
  t.seq.for_each_prefix(height.to_be_bytes(), |k, v| {
    let e: SeqEntry = bincode::deserialize(v).context("decode seq entry")?;
    rows.push((u32::from_be_bytes(k[8..12].try_into().unwrap()), e.id));
    Ok(true)
  })?;
  for (i, id) in rows {
    if out.contains_key(&i) {
      continue;
    }
    let Some(raw) = t.content.get(id.as_bytes())? else { continue };
    let c = decode_inscription_content(raw.as_ref())?;
    if let Some(code) = wire::deploy_code(&c.content_type, &c.body) {
      out.insert(i, (id, c.content_type, code));
    }
  }
  Ok(out)
}

/// Transactions that carry a `0xD1` call, whose raw bytes the sender check needs.
fn call_txids(block: &RpcBlock) -> Vec<String> {
  block
    .tx
    .iter()
    .filter(|tx| {
      let scripts: Vec<Vec<u8>> = tx.vout.iter().map(|o| hex::decode(o.script_pub_key.hex.as_deref().unwrap_or("")).unwrap_or_default()).collect();
      let refs: Vec<&[u8]> = scripts.iter().map(|s| s.as_slice()).collect();
      matches!(
        wire::tx_message(&refs),
        TxMessage::One { message: Message::Call(_), .. } | TxMessage::One { message: Message::Parcel { call: Some(_), .. }, .. }
      )
    })
    .map(|tx| tx.txid.clone())
    .collect()
}

fn index_block(db: &store::Db, t: &Trees, height: u64, block: &RpcBlock, raw: &HashMap<String, Vec<u8>>, st: &State) -> Result<(usize, usize)> {
  let time = block.time.unwrap_or(0);
  let mut w = Writes::new(t);
  let mut view = BlockView::open(db, height)?;
  // 1. deploys, in reveal order (§6.1)
  let deploys = deploys_of(t, height)?;
  for (&i, (insc, ct, code)) in &deploys {
    let id = (height, i);
    let hash = hex::encode(Sha256::digest(code));
    let meta = DeployMeta {
      id: fmt_id(id),
      height,
      tx_index: i,
      txid: block.tx.get(i as usize).map(|x| x.txid.clone()).unwrap_or_default(),
      inscription_id: insc.clone(),
      content_type: ct.clone(),
      code_hash: hash,
      code_len: code.len(),
      time,
      program: None,
    };
    w.put(T_CODE, id_key(id).to_vec(), Some(serde_json::to_vec(&meta)?));
    w.put(T_WASM, id_key(id).to_vec(), Some(code.clone()));
    let mut dk = b"d|".to_vec();
    dk.extend_from_slice(&hk(height, i));
    w.put(T_IDX, dk, Some(id_key(id).to_vec()));
    view.deploys.borrow_mut().insert(id, Rc::new(code.clone()));
  }
  let view = Rc::new(view);
  let mut ctx = BlockCtx { height, time, view: view.clone(), budget: vm::BLOCK_FUEL_BUDGET, raw, births: HashMap::new() };
  let (mut n_tx, mut n_calls) = (0, 0);
  // 2. transactions in order: parcels and calls
  for (idx, tx) in block.tx.iter().enumerate() {
    let i = idx as u32;
    // parcels the inputs carry
    let mut gathered: BTreeMap<Id, u128> = BTreeMap::new();
    for vin in &tx.vin {
      let (Some(ptx), Some(pv)) = (vin.txid.as_deref(), vin.vout) else { continue };
      let pk = parcel_key(ptx, pv);
      let Some(prev) = w.get(T_PARCEL, &pk)? else { continue };
      let p: ParcelRec = serde_json::from_slice(&prev)?;
      for (id, a) in &p.items {
        let (Some(id), Ok(a)) = (parse_id(id), a.parse::<u128>()) else { continue };
        add(&mut gathered, id, a);
        if let Some(addr) = &p.address {
          w.put(T_IDX, holder_key(id, addr, &pk), None);
        }
      }
      if let Some(addr) = &p.address {
        w.put(T_IDX, addr_key(addr, &pk), None);
      }
      w.put(T_PARCEL, pk, None);
    }
    let scripts: Vec<Vec<u8>> = tx.vout.iter().map(|o| hex::decode(o.script_pub_key.hex.as_deref().unwrap_or("")).unwrap_or_default()).collect();
    let refs: Vec<&[u8]> = scripts.iter().map(|s| s.as_slice()).collect();
    let msg = wire::tx_message(&refs);
    let deployed = deploys.contains_key(&i);
    if gathered.is_empty() && msg == TxMessage::None && !deployed {
      continue;
    }
    let mut rec = TxRecord {
      txid: tx.txid.clone(),
      height,
      tx_index: i,
      time,
      deploy: deployed.then(|| fmt_id((height, i))),
      message: "none".into(),
      parcels_in: amounts(&gathered),
      ..Default::default()
    };
    let can_hold = |v: u32| is_op_return(tx, v) == Some(false);
    let mut result: Option<vm::CallResult> = None;
    let mut cp_shown: Option<&wire::Cellpack> = None;
    let mut deposited: BTreeMap<Id, u128> = BTreeMap::new();
    let routed = match &msg {
      TxMessage::None => route(&gathered, Routing::Default, &can_hold, first_real_output(tx)),
      TxMessage::Ambiguous => {
        rec.message = "ambiguous".into();
        route(&gathered, Routing::Ambiguous, &can_hold, None)
      }
      TxMessage::One { vout, message: Message::Call(cp) } => {
        rec.message = "call".into();
        rec.carrier_vout = Some(*vout);
        cp_shown = Some(cp);
        let routed = route(&gathered, Routing::Default, &can_hold, first_real_output(tx));
        result = run_call(&mut ctx, tx, i, &CallIn { cp, carrier: *vout, incoming: Vec::new() }, &mut rec);
        routed
      }
      TxMessage::One { vout, message: Message::Parcel { pointer, edicts, call } } => {
        rec.message = "parcel".into();
        rec.carrier_vout = Some(*vout);
        rec.pointer = (*pointer != wire::NO_POINTER).then_some(*pointer);
        rec.edicts = edicts.iter().map(|e| serde_json::json!({ "id": fmt_id(e.token), "amount": e.amount.to_string(), "output": e.output })).collect();
        let mut routed = route(&gathered, Routing::Message { pointer: *pointer, edicts }, &can_hold, None);
        let deposits = std::mem::take(&mut routed.deposits);
        if let Some(cp) = call {
          cp_shown = Some(cp);
          let incoming: Vec<(Id, u128)> = deposits.iter().filter(|(_, a)| **a > 0).map(|(k, v)| (*k, *v)).collect();
          result = run_call(&mut ctx, tx, i, &CallIn { cp, carrier: *vout, incoming }, &mut rec);
        }
        if result.is_some() {
          deposited = deposits;
        } else {
          refund(&mut routed, &deposits, *pointer, &can_hold);
        }
        routed
      }
    };
    let Routed { mut alloc, burned, .. } = routed;
    if let Some(born) = rec.receipt.as_ref().and_then(|r| r.born.clone()) {
      let pid = (height, i);
      let program = ctx.births.get(&pid).copied().context("born print without a program")?;
      let pm: DeployMeta = serde_json::from_slice(&w.get(T_CODE, &id_key(program))?.context("print program metadata")?)?;
      let code = w.get(T_WASM, &id_key(program))?.context("print program code")?;
      let meta = DeployMeta { id: born, height, tx_index: i, txid: tx.txid.clone(), time, program: Some(pm.id.clone()), ..pm };
      w.put(T_CODE, id_key(pid).to_vec(), Some(serde_json::to_vec(&meta)?));
      w.put(T_WASM, id_key(pid).to_vec(), Some(code));
      let mut dk = b"d|".to_vec();
      dk.extend_from_slice(&hk(height, i));
      w.put(T_IDX, dk, Some(id_key(pid).to_vec()));
      let mut ck = b"c|".to_vec();
      ck.extend_from_slice(&id_key(pid));
      ck.extend_from_slice(&hk(height, i));
      w.put(T_IDX, ck, Some(tx.txid.clone().into_bytes()));
    }
    if let Some(cp) = cp_shown {
      rec.target = Some(fmt_id(cp.target));
      rec.fuel = Some(cp.fuel.to_string());
      rec.inputs = cp.inputs.iter().map(|v| v.to_string()).collect();
      rec.opcode = cp.inputs.first().map(|v| v.to_string());
      if rec.receipt.is_some() {
        n_calls += 1;
        let mut ck = b"c|".to_vec();
        ck.extend_from_slice(&id_key(cp.target));
        ck.extend_from_slice(&hk(height, i));
        w.put(T_IDX, ck, Some(tx.txid.clone().into_bytes()));
      }
    }
    if let Some(r) = &result {
      for (tok, vout, a) in &r.outgoing {
        add(alloc.entry(*vout).or_default(), *tok, *a);
      }
    }
    // outputs that now hold parcels
    for (vout, m) in &alloc {
      if m.values().all(|a| *a == 0) {
        continue;
      }
      let pk = parcel_key(&tx.txid, *vout);
      let address = addr_of(tx, *vout);
      for (id, a) in m {
        rec.parcels_out.push(OutParcel { vout: *vout, address: address.clone(), id: fmt_id(*id), amount: a.to_string() });
        if let Some(addr) = &address {
          w.put(T_IDX, holder_key(*id, addr, &pk), Some(a.to_le_bytes().to_vec()));
        }
      }
      if let Some(addr) = &address {
        w.put(T_IDX, addr_key(addr, &pk), Some(Vec::new()));
      }
      let p = ParcelRec { address, items: m.iter().map(|(id, a)| (fmt_id(*id), a.to_string())).collect() };
      w.put(T_PARCEL, pk, Some(serde_json::to_vec(&p)?));
    }
    rec.burned = amounts(&burned);
    rec.deposited = amounts(&deposited);
    // per-token activity
    let mut toks: Vec<Id> = gathered.keys().copied().collect();
    for m in alloc.values() {
      toks.extend(m.keys().copied());
    }
    toks.extend(burned.keys().copied());
    toks.sort();
    toks.dedup();
    for tok in toks {
      let mut kk = b"k|".to_vec();
      kk.extend_from_slice(&id_key(tok));
      kk.extend_from_slice(&hk(height, i));
      w.put(T_IDX, kk, Some(tx.txid.clone().into_bytes()));
    }
    let mut tk = b"t|".to_vec();
    tk.extend_from_slice(&hk(height, i));
    w.put(T_IDX, tk, Some(tx.txid.clone().into_bytes()));
    w.put(T_TX, tx.txid.clone().into_bytes(), Some(serde_json::to_vec(&rec)?));
    n_tx += 1;
  }
  // 3. the block's storage and ledger writes (§8: zero balances are deleted)
  for ((id, key), v) in view.store.borrow().iter() {
    w.put(T_STORAGE, storage_key(*id, key), Some(v.clone()));
  }
  for (k, v) in view.led.borrow().iter() {
    w.put(T_LEDGER, k.clone(), (*v > 0).then(|| v.to_le_bytes().to_vec()));
  }
  w.commit(height, st)?;
  Ok((n_tx, n_calls))
}

/// Follows the main index, block by block, for good.
pub async fn run_dalkanes_index(config: Config) -> Result<()> {
  let db = ii::db_of(&config)?;
  let t = Trees::open(&db)?;
  let client = indexer_rpc_client()?;
  if ii::meta_u64(&t.meta, RULES_KEY)?.unwrap_or(1) < RULES {
    for tree in t.t.iter().chain([&t.undo]) {
      tree.delete_range(Vec::new(), vec![0xffu8; 96])?;
    }
    t.meta.remove(STATE_KEY)?;
    t.meta.insert(RULES_KEY, RULES.to_be_bytes())?;
    info!("dalkanes: rules are now version {RULES}; replaying from activation (block {ACTIVATION})");
  }
  let mut st = load_state(&t.meta)?;
  info!("dalkanes: starting at block {}", st.next_height);
  let (mut last_log, mut caught_up) = (Instant::now(), false);
  loop {
    let indexed = ii::meta_u64(&t.meta, b"indexed_height")?.unwrap_or(0);
    if st.next_height > indexed {
      if !caught_up {
        caught_up = true;
        info!("dalkanes: caught up at block {indexed}");
      }
      sleep(Duration::from_secs(2)).await;
      continue;
    }
    let h = st.next_height;
    let block = match crate::repair::fetch_block(client, &config, h).await {
      Ok(b) => b,
      Err(e) => {
        warn!("dalkanes: block {h}: {e:#}");
        sleep(Duration::from_secs(10)).await;
        continue;
      }
    };
    if let Some((ph, phash)) = st.hashes.back()
      && *ph + 1 == h
      && block.previousblockhash.as_deref() != Some(phash.as_str())
    {
      let back = *ph;
      st.hashes.pop_back();
      st.next_height = back;
      undo_block(&t, back, &st)?;
      warn!("dalkanes: reorg, block {back} taken back");
      continue;
    }
    // raw transactions of the calls, for the sender check (§6.5)
    let mut raw = HashMap::new();
    let mut failed = false;
    for txid in call_txids(&block) {
      match rpc_call::<String>(client, &config, "getrawtransaction", serde_json::json!([txid])).await {
        Ok(hx) => {
          raw.insert(txid, hex::decode(hx).unwrap_or_default());
        }
        Err(e) => {
          warn!("dalkanes: block {h}: transaction {txid}: {e:#}");
          failed = true;
          break;
        }
      }
    }
    if failed {
      sleep(Duration::from_secs(10)).await;
      continue;
    }
    let mut next = st.clone();
    next.hashes.push_back((h, block.hash.clone()));
    while next.hashes.len() > KEEP as usize {
      next.hashes.pop_front();
    }
    next.next_height = h + 1;
    let res = tokio::task::block_in_place(|| index_block(&db, &t, h, &block, &raw, &next));
    match res {
      Ok((n, c)) => {
        st = next;
        if n > 0 {
          info!("dalkanes: block {h}: {n} transactions, {c} calls");
        }
      }
      Err(e) => {
        warn!("dalkanes: block {h} failed, reading it again: {e:#}");
        sleep(Duration::from_secs(10)).await;
        continue;
      }
    }
    caught_up = false;
    if last_log.elapsed() > Duration::from_secs(300) {
      last_log = Instant::now();
      info!("dalkanes: at block {h}");
    }
  }
}

// ---------------------------------------------------------------------------
// Reading

fn read_trees(config: &Config) -> Result<Trees> {
  Trees::open(&ii::db_of(config)?)
}

#[derive(Debug, Clone, Serialize)]
pub struct DalkStatus {
  pub activation: u64,
  pub height: u64,
  pub indexed: u64,
  #[serde(rename = "caughtUp")]
  pub caught_up: bool,
  pub contracts: usize,
  pub transactions: usize,
}

pub fn dalk_status(config: &Config) -> Result<DalkStatus> {
  let t = read_trees(config)?;
  let st = load_state(&t.meta)?;
  let indexed = ii::meta_u64(&t.meta, b"indexed_height")?.unwrap_or(0);
  let mut contracts = 0;
  t.t[T_CODE as usize].for_each_prefix(b"", |_, _| {
    contracts += 1;
    Ok(true)
  })?;
  let mut transactions = 0;
  t.t[T_IDX as usize].for_each_prefix(b"t|", |_, _| {
    transactions += 1;
    Ok(true)
  })?;
  let height = st.next_height.saturating_sub(1);
  Ok(DalkStatus { activation: ACTIVATION, height, indexed, caught_up: height + 1 >= indexed, contracts, transactions })
}

/// Committed state, for views run by the API.
struct DbView {
  wasm: Tree,
  storage: Tree,
  ledger: Tree,
}

impl StateView for DbView {
  fn code(&self, id: Id, _h: u64, _tx: u32) -> Option<Rc<Vec<u8>>> {
    self.wasm.get(id_key(id)).ok().flatten().map(|v| Rc::new(v.as_ref().to_vec()))
  }
  fn storage(&self, id: Id, key: &[u8]) -> Option<Vec<u8>> {
    self.storage.get(storage_key(id, key)).ok().flatten().map(|v| v.as_ref().to_vec())
  }
  fn ledger(&self, key: &[u8]) -> u128 {
    self.ledger.get(key).ok().flatten().map(|v| u128_of(v.as_ref())).unwrap_or(0)
  }
}

/// A token's views (§13), read with a dry run.
#[derive(Debug, Clone, Default, Serialize)]
pub struct TokenInfo {
  pub name: Option<String>,
  pub symbol: Option<String>,
  /// opcode 101: total supply, or minted for the Pack builds
  pub supply: Option<String>,
  pub v102: Option<String>,
  pub v103: Option<String>,
  pub v104: Option<String>,
}

static VIEW_CACHE: Lazy<Mutex<HashMap<(String, u64), TokenInfo>>> = Lazy::new(|| Mutex::new(HashMap::new()));

fn view_text(b: &[u8]) -> Option<String> {
  if b.is_empty() {
    return None;
  }
  let s = String::from_utf8(b.to_vec()).ok()?;
  (s.chars().all(|c| !c.is_control()) && s.len() <= 64).then_some(s)
}

fn view_num(b: &[u8]) -> Option<String> {
  match b.len() {
    16 => Some(u128::from_le_bytes(b.try_into().ok()?).to_string()),
    8 => Some(u64::from_le_bytes(b.try_into().ok()?).to_string()),
    4 => Some(u32::from_le_bytes(b.try_into().ok()?).to_string()),
    _ => None,
  }
}

/// Runs a read-only view of a contract against committed state.
pub fn dalk_view(config: &Config, id: Id, inputs: &[u128], height: u64) -> Result<vm::CallResult> {
  let db = ii::db_of(config)?;
  let view: Rc<dyn StateView> = Rc::new(DbView { wasm: db.open_tree("dalk_wasm")?, storage: db.open_tree("dalk_storage")?, ledger: db.open_tree("dalk_ledger")? });
  let env = vm::CallEnv { height, tx: u32::MAX, time: 0, target: id, fuel: 1_000_000, calldata: vm::calldata(inputs), ..Default::default() };
  Ok(vm::execute(&ENGINE, view, &env))
}

pub fn token_info(config: &Config, id: Id, height: u64) -> TokenInfo {
  let key = (fmt_id(id), height);
  if let Some(v) = VIEW_CACHE.lock().unwrap().get(&key) {
    return v.clone();
  }
  let run = |op: u128| dalk_view(config, id, &[op], height + 1).ok().filter(|r| r.ok).map(|r| r.ret);
  let info = TokenInfo {
    name: run(99).as_deref().and_then(view_text),
    symbol: run(100).as_deref().and_then(view_text),
    supply: run(101).as_deref().and_then(view_num),
    v102: run(102).as_deref().and_then(view_num),
    v103: run(103).as_deref().and_then(view_num),
    v104: run(104).as_deref().and_then(view_num),
  };
  let mut c = VIEW_CACHE.lock().unwrap();
  if c.len() > 2000 {
    c.clear();
  }
  c.insert(key, info.clone());
  info
}

#[derive(Debug, Clone, Serialize)]
pub struct ContractSummary {
  #[serde(flatten)]
  pub meta: DeployMeta,
  pub kind: Option<String>,
  pub label: Option<String>,
  pub token: TokenInfo,
  pub calls: usize,
  pub holders: usize,
  pub circulating: String,
}

fn holders_of(t: &Trees, id: Id) -> Result<(Vec<(String, u128, usize)>, u128)> {
  let mut prefix = b"h|".to_vec();
  prefix.extend_from_slice(&id_key(id));
  let mut by: BTreeMap<String, (u128, usize)> = BTreeMap::new();
  let mut total: u128 = 0;
  t.t[T_IDX as usize].for_each_prefix(&prefix, |k, v| {
    let rest = &k[prefix.len()..];
    let addr = rest.split(|b| *b == b'|').next().unwrap_or(&[]);
    let a = u128_of(v);
    let e = by.entry(String::from_utf8_lossy(addr).into_owned()).or_insert((0, 0));
    e.0 = e.0.saturating_add(a);
    e.1 += 1;
    total = total.saturating_add(a);
    Ok(true)
  })?;
  let mut v: Vec<(String, u128, usize)> = by.into_iter().map(|(a, (n, o))| (a, n, o)).collect();
  v.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
  Ok((v, total))
}

fn count_prefix(t: &Tree, prefix: &[u8]) -> Result<usize> {
  let mut n = 0;
  t.for_each_prefix(prefix, |_, _| {
    n += 1;
    Ok(true)
  })?;
  Ok(n)
}

fn summary(config: &Config, t: &Trees, meta: DeployMeta, height: u64) -> Result<ContractSummary> {
  let id = parse_id(&meta.id).context("bad id")?;
  let canon = canon_of(&meta.code_hash);
  let mut ck = b"c|".to_vec();
  ck.extend_from_slice(&id_key(id));
  let calls = count_prefix(&t.t[T_IDX as usize], &ck)?;
  let (holders, circ) = holders_of(t, id)?;
  Ok(ContractSummary {
    kind: canon.map(|c| c.0.to_string()),
    label: canon.map(|c| c.1.to_string()),
    token: token_info(config, id, height),
    calls,
    holders: holders.len(),
    circulating: circ.to_string(),
    meta,
  })
}

/// Contracts, newest first.
pub fn dalk_contracts(config: &Config, offset: usize, limit: usize) -> Result<(Vec<ContractSummary>, usize)> {
  let t = read_trees(config)?;
  let height = load_state(&t.meta)?.next_height.saturating_sub(1);
  let mut all = Vec::new();
  t.t[T_CODE as usize].for_each_rev_from(b"", |_, v| {
    all.push(serde_json::from_slice::<DeployMeta>(v)?);
    Ok(true)
  })?;
  let total = all.len();
  let out = all.into_iter().skip(offset).take(limit).map(|m| summary(config, &t, m, height)).collect::<Result<_>>()?;
  Ok((out, total))
}

#[derive(Debug, Clone, Serialize)]
pub struct Holder {
  pub address: String,
  pub amount: String,
  pub outputs: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct ContractDetail {
  #[serde(flatten)]
  pub summary: ContractSummary,
  pub top_holders: Vec<Holder>,
  pub sheet: Vec<Amount>,
  pub storage_keys: usize,
}

pub fn dalk_contract(config: &Config, id: Id) -> Result<Option<ContractDetail>> {
  let t = read_trees(config)?;
  let Some(raw) = t.get(T_CODE, &id_key(id))? else { return Ok(None) };
  let meta: DeployMeta = serde_json::from_slice(&raw)?;
  let height = load_state(&t.meta)?.next_height.saturating_sub(1);
  let summary = summary(config, &t, meta, height)?;
  let (holders, _) = holders_of(&t, id)?;
  // what this contract's own 12-byte sheet holds, of any token
  let mut sheet = Vec::new();
  let me = id_key(id);
  t.t[T_LEDGER as usize].for_each_prefix(b"", |k, v| {
    if k.len() == 24 && k[12..] == me[..] {
      sheet.push(Amount { id: id_from_key(&k[..12]).map(fmt_id).unwrap_or_default(), amount: u128_of(v).to_string() });
    }
    Ok(true)
  })?;
  let storage_keys = count_prefix(&t.t[T_STORAGE as usize], &me)?;
  Ok(Some(ContractDetail {
    summary,
    top_holders: holders.into_iter().take(100).map(|(a, n, o)| Holder { address: a, amount: n.to_string(), outputs: o }).collect(),
    sheet,
    storage_keys,
  }))
}

pub fn dalk_holders(config: &Config, id: Id, offset: usize, limit: usize) -> Result<(Vec<Holder>, usize, String)> {
  let t = read_trees(config)?;
  let (h, circ) = holders_of(&t, id)?;
  let total = h.len();
  Ok((h.into_iter().skip(offset).take(limit).map(|(a, n, o)| Holder { address: a, amount: n.to_string(), outputs: o }).collect(), total, circ.to_string()))
}

fn records_from(t: &Trees, prefix: &[u8], offset: usize, limit: usize) -> Result<(Vec<TxRecord>, usize)> {
  let mut txids = Vec::new();
  t.t[T_IDX as usize].for_each_prefix(prefix, |_, v| {
    txids.push(String::from_utf8_lossy(v).into_owned());
    Ok(true)
  })?;
  let total = txids.len();
  let mut out = Vec::new();
  for txid in txids.into_iter().rev().skip(offset).take(limit) {
    if let Some(r) = t.get(T_TX, txid.as_bytes())? {
      out.push(serde_json::from_slice(&r)?);
    }
  }
  Ok((out, total))
}

/// Calls to a contract, newest first.
pub fn dalk_calls(config: &Config, id: Id, offset: usize, limit: usize) -> Result<(Vec<TxRecord>, usize)> {
  let t = read_trees(config)?;
  let mut p = b"c|".to_vec();
  p.extend_from_slice(&id_key(id));
  records_from(&t, &p, offset, limit)
}

/// Transactions that moved a token's parcels, newest first.
pub fn dalk_token_activity(config: &Config, id: Id, offset: usize, limit: usize) -> Result<(Vec<TxRecord>, usize)> {
  let t = read_trees(config)?;
  let mut p = b"k|".to_vec();
  p.extend_from_slice(&id_key(id));
  records_from(&t, &p, offset, limit)
}

/// Every Dalkanes transaction, newest first.
pub fn dalk_activity(config: &Config, offset: usize, limit: usize) -> Result<(Vec<TxRecord>, usize)> {
  let t = read_trees(config)?;
  records_from(&t, b"t|", offset, limit)
}

pub fn dalk_tx(config: &Config, txid: &str) -> Result<Option<TxRecord>> {
  let t = read_trees(config)?;
  Ok(t.get(T_TX, txid.as_bytes())?.map(|r| serde_json::from_slice(&r)).transpose()?)
}

#[derive(Debug, Clone, Serialize)]
pub struct OutputParcels {
  pub outpoint: String,
  pub address: Option<String>,
  pub items: Vec<Amount>,
}

pub fn dalk_output(config: &Config, txid: &str, vout: u32) -> Result<Option<OutputParcels>> {
  let t = read_trees(config)?;
  let Some(raw) = t.get(T_PARCEL, &parcel_key(txid, vout))? else { return Ok(None) };
  let p: ParcelRec = serde_json::from_slice(&raw)?;
  Ok(Some(OutputParcels {
    outpoint: format!("{txid}:{vout}"),
    address: p.address,
    items: p.items.into_iter().map(|(id, amount)| Amount { id, amount }).collect(),
  }))
}

#[derive(Debug, Clone, Serialize)]
pub struct AddressBalance {
  pub id: String,
  pub amount: String,
  pub outputs: usize,
  pub label: Option<String>,
  pub name: Option<String>,
  pub symbol: Option<String>,
}

/// What an address holds on its outputs.
pub fn dalk_address(config: &Config, address: &str) -> Result<(Vec<AddressBalance>, Vec<OutputParcels>)> {
  let t = read_trees(config)?;
  let height = load_state(&t.meta)?.next_height.saturating_sub(1);
  let mut prefix = b"a|".to_vec();
  prefix.extend_from_slice(address.as_bytes());
  prefix.push(b'|');
  let mut outs = Vec::new();
  t.t[T_IDX as usize].for_each_prefix(&prefix, |k, _| {
    outs.push(String::from_utf8_lossy(&k[prefix.len()..]).into_owned());
    Ok(true)
  })?;
  let mut by: BTreeMap<String, (u128, usize)> = BTreeMap::new();
  let mut list = Vec::new();
  for op in outs {
    let Some(raw) = t.get(T_PARCEL, op.as_bytes())? else { continue };
    let p: ParcelRec = serde_json::from_slice(&raw)?;
    for (id, a) in &p.items {
      let e = by.entry(id.clone()).or_insert((0, 0));
      e.0 = e.0.saturating_add(a.parse().unwrap_or(0));
      e.1 += 1;
    }
    list.push(OutputParcels { outpoint: op, address: p.address, items: p.items.into_iter().map(|(id, amount)| Amount { id, amount }).collect() });
  }
  let mut bal = Vec::new();
  for (id, (a, o)) in by {
    let pid = parse_id(&id);
    let meta: Option<DeployMeta> = match pid {
      Some(p) => t.get(T_CODE, &id_key(p))?.map(|r| serde_json::from_slice(&r)).transpose()?,
      None => None,
    };
    let info = pid.map(|p| token_info(config, p, height)).unwrap_or_default();
    bal.push(AddressBalance {
      id,
      amount: a.to_string(),
      outputs: o,
      label: meta.and_then(|m| canon_of(&m.code_hash).map(|c| c.1.to_string())),
      name: info.name,
      symbol: info.symbol,
    });
  }
  Ok((bal, list))
}

#[derive(Debug, Clone, Serialize)]
pub struct StorageRow {
  pub key_hex: String,
  pub key_text: Option<String>,
  pub value_hex: String,
}

pub fn dalk_storage(config: &Config, id: Id, limit: usize) -> Result<Vec<StorageRow>> {
  let t = read_trees(config)?;
  let me = id_key(id);
  let mut out = Vec::new();
  t.t[T_STORAGE as usize].for_each_prefix(me, |k, v| {
    let key = &k[12..];
    out.push(StorageRow {
      key_hex: hex::encode(key),
      key_text: std::str::from_utf8(key).ok().filter(|s| s.chars().all(|c| !c.is_control())).map(str::to_string),
      value_hex: hex::encode(&v[..v.len().min(512)]),
    });
    Ok(out.len() < limit)
  })?;
  Ok(out)
}

pub fn dalk_code(config: &Config, id: Id) -> Result<Option<Vec<u8>>> {
  let t = read_trees(config)?;
  t.get(T_WASM, &id_key(id))
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn address_encoding() {
    let h: [u8; 20] = hex::decode("9dabb48cc18082a37ff23d46f891f5f9256d8d12").unwrap().try_into().unwrap();
    assert!(p2pkh_address(&h).starts_with('D'));
  }

  #[test]
  fn canon_labels() {
    assert_eq!(canon_of("5b9fa2476e0e669aa3126cbdb4c172c29a0685e5bc0e831411e96d7836a5a916").unwrap().1, "Howl");
  }
  fn txj(txid: &str, vin: serde_json::Value, vout: serde_json::Value) -> serde_json::Value {
    serde_json::json!({ "txid": txid, "vin": vin, "vout": vout })
  }

  fn filler(n: usize, h: u64) -> Vec<serde_json::Value> {
    (0..n).map(|i| txj(&format!("{:064x}", h * 1000 + i as u64), serde_json::json!([{}]), serde_json::json!([{ "value": 1.0, "n": 0, "scriptPubKey": { "hex": "51" } }]))).collect()
  }

  fn block(h: u64, txs: Vec<serde_json::Value>) -> RpcBlock {
    serde_json::from_value(serde_json::json!({ "hash": format!("{h:064x}"), "previousblockhash": format!("{:064x}", h - 1), "tx": txs, "time": 1795725000u64 + h })).unwrap()
  }

  /// Deploy Howl, run the live claim, then spend the claimed output: the parcel follows the first
  /// real output (§16), holders follow it, and undo puts everything back.
  #[test]
  fn howl_block_flow() {
    let db = store::Db::temporary().unwrap();
    let t = Trees::open(&db).unwrap();
    let body = hex::decode(include_str!("vectors/howl-deploy.hex").trim()).unwrap();
    let insc = "ca11ac36f54684b7b633d8e7f512896ed2cde837987195158dc61586f8b78d79i0";
    t.seq.insert(ii::seq_key(6474082, 35), bincode::serialize(&SeqEntry { id: insc.into(), kinds: 0, time: 0 }).unwrap()).unwrap();
    let rec = crate::InscriptionContentRecord { content_type: "application/wasm".into(), body, delegate: None };
    t.content.insert(insc.as_bytes(), bincode::serialize(&rec).unwrap()).unwrap();
    let mut st = State { next_height: 6474082, ..Default::default() };
    // block 1: the deploy at index 35
    let mut txs = filler(35, 6474082);
    txs.push(txj("109d44ed4c7c78ae5bc0086f55df65b87773e3327af915fed215139ce54f6959", serde_json::json!([{ "txid": "ca11ac36f54684b7b633d8e7f512896ed2cde837987195158dc61586f8b78d79", "vout": 0 }]), serde_json::json!([{ "value": 0.001, "n": 0, "scriptPubKey": { "hex": "76a9145a21f9448e65dc1657385e2b79fb08590845a6cf88ac" } }])));
    st.next_height = 6474083;
    index_block(&db, &t, 6474082, &block(6474082, txs), &HashMap::new(), &st).unwrap();
    // block 2: the claim at index 15
    let call = "9d361c832deea6288143af01a49fb463235c6ad9ad77f9ac440ef5c40dda7e96";
    let mut txs = filler(15, 6474090);
    txs.push(txj(call, serde_json::json!([{ "txid": "11a4847a75fc211ec297be8f5312144515b376266b09e912d5c0c771a24cb44e", "vout": 3 }]), serde_json::json!([
      { "value": 0.16, "n": 0, "scriptPubKey": { "hex": "6a0dd101e2928b0323c09a0c024d01" } },
      { "value": 0.82184, "n": 1, "scriptPubKey": { "hex": "76a9149dabb48cc18082a37ff23d46f891f5f9256d8d1288ac", "addresses": ["DKbD8jBVQ8Q7hSQBzNrhm3zt5nNTanFAWB"] } }
    ])));
    let mut raw = HashMap::new();
    raw.insert(call.to_string(), hex::decode(include_str!("vectors/howl-call-tx.hex").trim()).unwrap());
    st.next_height = 6474091;
    index_block(&db, &t, 6474090, &block(6474090, txs), &raw, &st).unwrap();
    let r: TxRecord = serde_json::from_slice(&t.get(T_TX, call.as_bytes()).unwrap().unwrap()).unwrap();
    let rc = r.receipt.clone().unwrap();
    assert!(rc.ok, "{:?}", rc.error);
    assert_eq!(r.value, 16_000_000);
    assert_eq!(r.parcels_out.len(), 1);
    assert_eq!((r.parcels_out[0].vout, r.parcels_out[0].amount.as_str()), (1, "16"));
    let (h, circ) = holders_of(&t, (6474082, 35)).unwrap();
    assert_eq!((h.len(), circ), (1, 16));
    // Howl's treasury (its own account 0x01) keeps the rest of the 2,048; the emptied sheet row is deleted
    let treasury = t.get(T_LEDGER, &ledger_key_of((6474082, 35), &[1])).unwrap().map(|v| u128_of(&v));
    assert_eq!(treasury, Some(2032));
    assert!(t.get(T_LEDGER, &ledger_key_of((6474082, 35), &id_key((6474082, 35)))).unwrap().is_none());
    // block 3: spend the claimed output with no 0xD1 message, OP_RETURN first: the parcel goes to output 1
    let spend = "ee".repeat(32);
    let txs = vec![txj(&spend, serde_json::json!([{ "txid": call, "vout": 1 }]), serde_json::json!([
      { "value": 0.0, "n": 0, "scriptPubKey": { "hex": "6a0100" } },
      { "value": 0.5, "n": 1, "scriptPubKey": { "hex": "76a914000000000000000000000000000000000000000088ac", "addresses": ["DAAAA"] } }
    ]))];
    st.next_height = 6474092;
    index_block(&db, &t, 6474091, &block(6474091, txs), &HashMap::new(), &st).unwrap();
    let (h, circ) = holders_of(&t, (6474082, 35)).unwrap();
    assert_eq!((h[0].0.as_str(), h.len(), circ), ("DAAAA", 1, 16));
    assert!(t.get(T_PARCEL, format!("{call}:1").as_bytes()).unwrap().is_none());
    // undo block 3: the parcel is back on the claim output
    undo_block(&t, 6474091, &st).unwrap();
    let (h, _) = holders_of(&t, (6474082, 35)).unwrap();
    assert_eq!(h[0].0, "DKbD8jBVQ8Q7hSQBzNrhm3zt5nNTanFAWB");
    // undo block 2 and 1: nothing left
    undo_block(&t, 6474090, &st).unwrap();
    undo_block(&t, 6474082, &st).unwrap();
    assert!(t.get(T_CODE, &id_key((6474082, 35))).unwrap().is_none());
    assert!(holders_of(&t, (6474082, 35)).unwrap().0.is_empty());
  }

  fn ledger_key_of(tok: Id, acct: &[u8]) -> Vec<u8> {
    vm::ledger_key(tok, acct)
  }

  fn pid(s: &str) -> Id {
    parse_id(s).unwrap()
  }

  fn amounts_of(v: &serde_json::Value) -> Vec<(Id, u128)> {
    let mut out: Vec<(Id, u128)> = v.as_array().unwrap().iter().map(|x| (pid(x[0].as_str().unwrap()), x[1].as_str().unwrap().parse().unwrap())).collect();
    out.sort();
    out
  }

  /// vectors/parcel.json `routing` (spec §16.2), mirrored from dogex `routing_edge_cases`.
  #[test]
  fn parcel_routing_vectors() {
    let v: serde_json::Value = serde_json::from_str(include_str!("vectors/parcel.json")).unwrap();
    for c in v["routing"].as_array().unwrap() {
      let name = c["name"].as_str().unwrap();
      let mut gathered = BTreeMap::new();
      for (id, a) in amounts_of(&c["inputs"]) {
        add(&mut gathered, id, a);
      }
      let hold: Vec<bool> = c["can_hold"].as_array().unwrap().iter().map(|b| b.as_bool().unwrap()).collect();
      let can_hold = |o: u32| hold.get(o as usize).copied().unwrap_or(false);
      let first_real = hold.iter().position(|b| *b).map(|i| i as u32);
      let edicts: Vec<wire::Edict>;
      let routing = match c["routing"]["kind"].as_str().unwrap() {
        "default" => Routing::Default,
        "burn" => Routing::Ambiguous,
        "message" => {
          let m = &c["routing"]["message"];
          edicts = m["edicts"]
            .as_array()
            .unwrap()
            .iter()
            .map(|e| wire::Edict { token: pid(e["id"].as_str().unwrap()), amount: e["amount"].as_str().unwrap().parse().unwrap(), output: e["output"].as_u64().unwrap() as u32 })
            .collect();
          Routing::Message { pointer: m["pointer"].as_u64().map(|p| p as u32).unwrap_or(wire::NO_POINTER), edicts: &edicts }
        }
        k => panic!("{name}: routing kind {k}"),
      };
      let r = route(&gathered, routing, &can_hold, first_real);
      let mut got: Vec<(u32, Id, u128)> = r.alloc.iter().flat_map(|(v, m)| m.iter().map(move |(id, a)| (*v, *id, *a))).collect();
      got.sort();
      let mut want: Vec<(u32, Id, u128)> = c["to_output"]
        .as_array()
        .unwrap()
        .iter()
        .map(|x| (x[0].as_u64().unwrap() as u32, pid(x[1].as_str().unwrap()), x[2].as_str().unwrap().parse().unwrap()))
        .collect();
      want.sort();
      assert_eq!(got, want, "{name}: outputs");
      assert_eq!(r.deposits.into_iter().collect::<Vec<_>>(), amounts_of(&c["deposits"]), "{name}: deposits");
      assert_eq!(r.burned.into_iter().collect::<Vec<_>>(), amounts_of(&c["burned"]), "{name}: burned");
    }
  }

  /// vectors/sender.json (spec §6.5): the mainnet Howl claim whose pubkey hash contains 0xab.
  #[test]
  fn sender_vectors() {
    let v: serde_json::Value = serde_json::from_str(include_str!("vectors/sender.json")).unwrap();
    for c in v["cases"].as_array().unwrap() {
      let raw = hex::decode(c["raw_tx_hex"].as_str().unwrap()).unwrap();
      assert_eq!(sig::sender(&raw).map(hex::encode), c["sender_hash160"].as_str().map(str::to_string), "{}", c["name"]);
    }
  }

  fn leb(mut v: u128, out: &mut Vec<u8>) {
    loop {
      let b = (v & 0x7f) as u8;
      v >>= 7;
      if v == 0 {
        out.push(b);
        return;
      }
      out.push(b | 0x80);
    }
  }

  /// A one-input P2PKH transaction signed SIGHASH_ALL with `key`, carrying a call (form A).
  fn signed_call(key: &secp256k1::SecretKey, target: Id, inputs: &[u128], vout_script: &[u8]) -> Vec<u8> {
    let secp = secp256k1::Secp256k1::new();
    let pk = secp256k1::PublicKey::from_secret_key(&secp, key).serialize();
    let mut cp = Vec::new();
    for v in [target.0 as u128, target.1 as u128, 1_000_000, inputs.len() as u128] {
      leb(v, &mut cp);
    }
    for v in inputs {
      leb(*v, &mut cp);
    }
    let mut payload = vec![0xd1, 0x01];
    payload.extend_from_slice(&cp);
    let mut call = vec![0x6a, payload.len() as u8];
    call.extend_from_slice(&payload);
    let ser = |script_sig: &[u8]| {
      let mut t = 1i32.to_le_bytes().to_vec();
      t.push(1);
      t.extend_from_slice(&[0x11; 32]);
      t.extend_from_slice(&0u32.to_le_bytes());
      sig::put_varint(&mut t, script_sig.len() as u64);
      t.extend_from_slice(script_sig);
      t.extend_from_slice(&u32::MAX.to_le_bytes());
      t.push(2);
      for (value, script) in [(0u64, &call[..]), (100_000u64, vout_script)] {
        t.extend_from_slice(&value.to_le_bytes());
        sig::put_varint(&mut t, script.len() as u64);
        t.extend_from_slice(script);
      }
      t.extend_from_slice(&0u32.to_le_bytes());
      t
    };
    let unsigned = sig::parse_tx(&ser(&[])).unwrap();
    let mut code = vec![0x76, 0xa9, 0x14];
    code.extend_from_slice(&sig::hash160(&pk));
    code.extend_from_slice(&[0x88, 0xac]);
    let digest = sig::sighash_all_input0(&unsigned, &code, 1);
    let s = secp.sign_ecdsa(&secp256k1::Message::from_digest_slice(&digest).unwrap(), key);
    let mut der = s.serialize_der().to_vec();
    der.push(0x01);
    let mut script_sig = vec![der.len() as u8];
    script_sig.extend_from_slice(&der);
    script_sig.push(pk.len() as u8);
    script_sig.extend_from_slice(&pk);
    ser(&script_sig)
  }

  fn call_tx(txid: &str, raw: &[u8]) -> serde_json::Value {
    let t = sig::parse_tx(raw).unwrap();
    let mut i = 0usize;
    let mut outs = Vec::new();
    for n in 0..t.n_outputs {
      let value = u64::from_le_bytes(t.outputs_raw[i..i + 8].try_into().unwrap());
      let l = t.outputs_raw[i + 8] as usize;
      let script = hex::encode(&t.outputs_raw[i + 9..i + 9 + l]);
      i += 9 + l;
      outs.push(serde_json::json!({ "value": value as f64 / 1e8, "n": n, "scriptPubKey": { "hex": script, "addresses": if n == 1 { serde_json::json!(["DPuller"]) } else { serde_json::Value::Null } } }));
    }
    txj(txid, serde_json::json!([{ "txid": "11".repeat(32), "vout": 0 }]), serde_json::Value::Array(outs))
  }

  /// §20: opcode 77 on the inscribed Proof program births a print with the pull's own id; the
  /// program runs as the print; a later 77 on the program births another; 77 on a print births none.
  #[test]
  fn proof_print_births() {
    let db = store::Db::temporary().unwrap();
    let t = Trees::open(&db).unwrap();
    let body = hex::decode(include_str!("vectors/proof-deploy.hex").trim()).unwrap();
    let h0 = 6_480_000u64;
    let insc = format!("{}i0", "ab".repeat(32));
    t.seq.insert(ii::seq_key(h0, 1), bincode::serialize(&SeqEntry { id: insc.clone(), kinds: 0, time: 0 }).unwrap()).unwrap();
    t.content.insert(insc.as_bytes(), bincode::serialize(&crate::InscriptionContentRecord { content_type: "application/wasm".into(), body, delegate: None }).unwrap()).unwrap();
    let mut st = State { next_height: h0 + 1, ..Default::default() };
    let mut txs = filler(1, h0);
    txs.push(txj(&"ab".repeat(32), serde_json::json!([{}]), serde_json::json!([{ "value": 0.001, "n": 0, "scriptPubKey": { "hex": "51" } }])));
    index_block(&db, &t, h0, &block(h0, txs), &HashMap::new(), &st).unwrap();
    let meta: DeployMeta = serde_json::from_slice(&t.get(T_CODE, &id_key((h0, 1))).unwrap().unwrap()).unwrap();
    assert_eq!(canon_of(&meta.code_hash).map(|c| c.0), Some("proof"));

    let key = secp256k1::SecretKey::from_slice(&[7u8; 32]).unwrap();
    let p2pkh = hex::decode("76a914000000000000000000000000000000000000000088ac").unwrap();
    let pull = |h: u64, target: Id, st: &mut State| -> TxRecord {
      let raw = signed_call(&key, target, &[77, 1], &p2pkh);
      let txid = format!("{:064x}", h);
      let mut txs = filler(1, h);
      txs.push(call_tx(&txid, &raw));
      let mut rawmap = HashMap::new();
      rawmap.insert(txid.clone(), raw);
      st.next_height = h + 1;
      index_block(&db, &t, h, &block(h, txs), &rawmap, st).unwrap();
      serde_json::from_slice(&t.get(T_TX, txid.as_bytes()).unwrap().unwrap()).unwrap()
    };
    // first pull: a print is born at (h0+1, 1)
    let r = pull(h0 + 1, (h0, 1), &mut st);
    let rc = r.receipt.unwrap();
    assert!(rc.ok, "{:?}", rc.error);
    assert!(r.sender.is_some());
    let born = fmt_id((h0 + 1, 1));
    assert_eq!(rc.born.as_deref(), Some(born.as_str()));
    assert_eq!(r.parcels_out.len(), 1);
    assert_eq!((r.parcels_out[0].id.as_str(), r.parcels_out[0].amount.as_str(), r.parcels_out[0].vout), (born.as_str(), "1", 1));
    let pm: DeployMeta = serde_json::from_slice(&t.get(T_CODE, &id_key((h0 + 1, 1))).unwrap().unwrap()).unwrap();
    assert_eq!(pm.program.as_deref(), Some(fmt_id((h0, 1)).as_str()));
    // the pull's storage belongs to the print, not the program
    assert_eq!(count_prefix(&t.t[T_STORAGE as usize], &id_key((h0, 1))).unwrap(), 0);
    assert!(count_prefix(&t.t[T_STORAGE as usize], &id_key((h0 + 1, 1))).unwrap() > 0);
    // a later 77 on the program births another print
    let r = pull(h0 + 2, (h0, 1), &mut st);
    assert_eq!(r.receipt.unwrap().born.as_deref(), Some(fmt_id((h0 + 2, 1)).as_str()));
    // 77 on a print births nothing, and the print was already pulled
    let r = pull(h0 + 3, (h0 + 1, 1), &mut st);
    let rc = r.receipt.unwrap();
    assert!(!rc.ok && rc.born.is_none(), "{rc:?}");
    assert!(t.get(T_CODE, &id_key((h0 + 3, 1))).unwrap().is_none());
    // a reorg takes the print back
    undo_block(&t, h0 + 2, &st).unwrap();
    assert!(t.get(T_CODE, &id_key((h0 + 2, 1))).unwrap().is_none());
  }
}

