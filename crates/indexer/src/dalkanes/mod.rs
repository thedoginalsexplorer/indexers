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
/// deposit, print births, 2026-11-26); 3 = deployers, project cards (§22), the Proof gate and
/// collection keys (§20), 2026-11-27; 4 = per-address history (`w|address|…`), 2026-11-27.
const RULES: u64 = 5;
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
  // §24 (spec 0.4.2, vectors/canonical-builds.json): the three print programs (§20.1). Nothing else is
  // one: the superseded bodies 43a9ebb3 (Proof), 3cba3028 and 9e9bfc04 (Shibkane) get no label and no gate.
  ("7c9b14ca1babaf1ee229f26a49b89e8d54e7ad86af6adc228492e273ec9e1694", "proof", "Proof"),
  ("b69f0aa9b8cd66335d1c08fa6c86d3af7d6b0def30c8d8688eff6ebefe9c71a4", "shibkane", "Shibkane"),
  ("aeafccfee33779532d930b86bfbd2fbb0e5519db072dc26e29888e3c4040a4c4", "doge", "Doge Orbital"),
  ("ee4c6e7ba6096c1ed5908485135a107f793f8295c2baa0c6e4734a8c9e16a3dd", "kibble", "Kibble"),
  // §17 fair-launch: official dogex launch/build for DogePay / DPAY, cap 21,000,000, 10,000 per mint.
  // Hash is SHA-256 of the wasm after the \0ALK\x01 header (same method as the §24 table).
  ("9a4e2f5e047393f4896436896fefc72531f50f8aa38f0bd32c59b7bf01eb70d8", "launch", "DogePay"),
  // builds with baked ids, as deployed on mainnet (Collar: Howl, Ash, Vigil; Bone: Howl)
  ("66c3610d07e8f2fee6db975f52fe41c74bae826847cbc446146ae42334b315c0", "collar", "Collar"),
  ("cbb467a319b130e53724de61aba4eb32f2d33ebe2d28b4fcf3a182f79f8d808e", "bone", "Bone"),
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
  /// The P2PKH address of the reveal key (§22.2); none for a print.
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub deployer: Option<String>,
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
  /// Addresses whose outputs held those parcels (who sent them).
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub parcels_from: Vec<String>,
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

/// `w|address|height‖tx` -> txid: what an address did with Ðalkanes, in chain order.
fn addr_history_key(addr: &str, height: u64, tx: u32) -> Vec<u8> {
  let mut k = b"w|".to_vec();
  k.extend_from_slice(addr.as_bytes());
  k.push(b'|');
  k.extend_from_slice(&hk(height, tx));
  k
}

fn addr_key(addr: &str, outpoint: &[u8]) -> Vec<u8> {
  let mut k = b"a|".to_vec();
  k.extend_from_slice(addr.as_bytes());
  k.push(b'|');
  k.extend_from_slice(outpoint);
  k
}

/// Prints a Proof, Shibkane or Doge Orbital collection may bear (§20.1).
const PROOF_CAP: u64 = 420;

/// The first block where a print program no longer refuses a second pull in the same block (key `0x14`).
/// This follows jonheaven's 2026-11-27 note: the block lock came from Howl and Kibble and is wrong for a
/// drop (Bitcoin's Orbital draft lets several children be born in one block). The 420 cap and one pull
/// per address stay. Blocks below this keep the old rule, so the prints already born (#0–#3) and the
/// pulls refused in old blocks (e.g. 6475541 tx 31) stay as they are, and nothing replays. Spec 0.4.3
/// names this height: "from height 6,475,700 on, this check is not made."
pub const PRINT_BLOCK_LOCK_END: u64 = 6_475_700;

/// §20.1: why a pull at `height` from `sender` is refused before execution, if it is: the collection
/// is full, this block already pulled (only below PRINT_BLOCK_LOCK_END), or this address already pulled.
/// Shared by the block and the dry run.
fn proof_refusal(view: &dyn StateView, program: Id, height: u64, sender: Option<[u8; 20]>) -> Option<&'static str> {
  let count = view.storage(program, &[0x10]).map(|v| u64_le(&v)).unwrap_or(0);
  let last = view.storage(program, &[0x14]).map(|v| u64_le(&v));
  let pulled = sender.is_some_and(|s| view.storage(program, &[&[0x15u8][..], &s[..]].concat()).is_some());
  if count >= PROOF_CAP {
    Some("the collection is full")
  } else if height < PRINT_BLOCK_LOCK_END && last == Some(height) {
    Some("this block already pulled")
  } else if pulled {
    Some("this address already pulled")
  } else {
    None
  }
}

fn u64_le(v: &[u8]) -> u64 {
  let mut b = [0u8; 8];
  let n = v.len().min(8);
  b[..n].copy_from_slice(&v[..n]);
  u64::from_le_bytes(b)
}

/// The key that signed a reveal (§22.2): the redeem script, the last push of input 0's scriptSig,
/// starts with `<pubkey> OP_CHECKSIGVERIFY`.
fn reveal_signer(tx: &RpcTx) -> Option<[u8; 20]> {
  let ss = hex::decode(&tx.vin.first()?.script_sig.as_ref()?.hex).ok()?;
  let redeem = script_pushes(&ss)?.pop()?;
  let first = script_pushes_prefix(&redeem)?;
  ((first.0.len() == 33 || first.0.len() == 65) && redeem.get(first.1) == Some(&0xad)).then(|| sig::hash160(&first.0))
}

/// Every push of a script made only of pushes.
fn script_pushes(s: &[u8]) -> Option<Vec<Vec<u8>>> {
  let mut out = Vec::new();
  let mut i = 0;
  while i < s.len() {
    let (p, next) = push_at(s, i)?;
    out.push(p);
    i = next;
  }
  Some(out)
}

/// The first push of a script and where the next opcode starts.
fn script_pushes_prefix(s: &[u8]) -> Option<(Vec<u8>, usize)> {
  push_at(s, 0)
}

fn push_at(s: &[u8], i: usize) -> Option<(Vec<u8>, usize)> {
  let op = *s.get(i)?;
  let (len, hdr) = match op {
    0x00..=0x4b => (op as usize, 1),
    0x4c => (*s.get(i + 1)? as usize, 2),
    0x4d => (u16::from_le_bytes([*s.get(i + 1)?, *s.get(i + 2)?]) as usize, 3),
    0x51..=0x60 => return Some((vec![op - 0x50], i + 1)),
    _ => return None,
  };
  Some((s.get(i + hdr..i + hdr + len)?.to_vec(), i + hdr + len))
}

/// A project card (§22.1), as stored.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ProjectCard {
  pub dalkane: String,
  pub image: String,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub name: Option<String>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub description: Option<String>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub links: Vec<CardLink>,
  /// The card's own inscription, and where it was revealed.
  #[serde(default)]
  pub inscription_id: String,
  #[serde(default)]
  pub height: u64,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CardLink {
  pub label: String,
  pub url: String,
}

/// Parses a card body under §22.1 and schemas/project-card.schema.json (no other fields).
pub fn parse_card(body: &[u8]) -> Option<ProjectCard> {
  if body.len() > 2048 {
    return None;
  }
  let v: serde_json::Value = serde_json::from_slice(body).ok()?;
  let o = v.as_object()?;
  if o.keys().any(|k| !matches!(k.as_str(), "dalkane" | "image" | "name" | "description" | "links")) {
    return None;
  }
  let dalkane = o.get("dalkane")?.as_str()?;
  parse_id(dalkane)?;
  if !dalkane.bytes().all(|b| b.is_ascii_digit() || b == b':') {
    return None;
  }
  let image = o.get("image")?.as_str()?;
  let (txid, idx) = image.split_once('i')?;
  if txid.len() != 64 || !txid.bytes().all(|b| b.is_ascii_hexdigit()) || idx.is_empty() || !idx.bytes().all(|b| b.is_ascii_digit()) {
    return None;
  }
  let text = |k: &str, max: usize| -> Option<Option<String>> {
    match o.get(k) {
      None => Some(None),
      Some(v) => {
        let s = v.as_str()?;
        (!s.is_empty() && s.chars().count() <= max).then(|| Some(s.to_string()))
      }
    }
  };
  let name = text("name", 64)?;
  let description = text("description", 280)?;
  let mut links = Vec::new();
  if let Some(l) = o.get("links") {
    let arr = l.as_array()?;
    if arr.len() > 4 {
      return None;
    }
    for x in arr {
      let xo = x.as_object()?;
      if xo.keys().any(|k| k != "label" && k != "url") {
        return None;
      }
      let label = xo.get("label")?.as_str()?;
      let url = xo.get("url")?.as_str()?;
      let ok_url = (url.starts_with("http://") || url.starts_with("https://")) && url.len() >= 8 && url.len() <= 200 && !url.chars().any(char::is_whitespace);
      if label.is_empty() || label.chars().count() > 32 || !ok_url {
        return None;
      }
      links.push(CardLink { label: label.into(), url: url.into() });
    }
  }
  Some(ProjectCard { dalkane: dalkane.into(), image: format!("{}i{idx}", txid.to_ascii_lowercase()), name, description, links, ..Default::default() })
}

fn card_key(id: Id) -> Vec<u8> {
  let mut k = b"card|".to_vec();
  k.extend_from_slice(&id_key(id));
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
  let print_program = matches!(canon_of(&hex::encode(Sha256::digest(&code[..]))), Some(("proof" | "shibkane" | "doge", _)));
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
  // §20.1: Proof, Shibkane and Doge Orbital share the gate: 420 prints and one per verified sender, and
  // one pull per block only below PRINT_BLOCK_LOCK_END
  let proof = birth && matches!(canon_of(&hex::encode(Sha256::digest(&code[..]))), Some(("proof" | "shibkane" | "doge", _)));
  if proof {
    // §20: a Proof collection stops at 420, one pull per block and one per verified sender. Refused
    // before execution: no fuel, no new id, and the block and the address are not used up.
    if let Some(why) = proof_refusal(&*ctx.view, target, ctx.height, sender) {
      rec.receipt = Some(Receipt { target: fmt_id(target), error: Some(why.into()), ..Default::default() });
      return None;
    }
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
    caller: if birth { target } else { (0, 0) },
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
    // §20: the birth records the print on the program (the program, running as the print, cannot):
    // the count, the slot, and the print's index; a Proof also its block and its sender
    let count = ctx.view.storage(target, &[0x10]).map(|v| u64_le(&v)).unwrap_or(0);
    let mut s = ctx.view.store.borrow_mut();
    let mut slot = vec![0x11];
    slot.extend_from_slice(&(count as u32).to_le_bytes());
    let mut child = born.0.to_le_bytes().to_vec();
    child.extend_from_slice(&(born.1 as u64).to_le_bytes());
    s.insert((target, vec![0x10]), (count + 1).to_le_bytes().to_vec());
    s.insert((target, slot), child);
    s.insert((born, vec![0x13]), count.to_le_bytes().to_vec());
    if proof {
      s.insert((target, vec![0x14]), ctx.height.to_le_bytes().to_vec());
      if let Some(snd) = sender {
        // §20 (spec 071cff3): the value is the single byte 0x01, as dogex stores it
        s.insert((target, [&[0x15u8][..], &snd[..]].concat()), vec![0x01]);
      }
    }
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
/// Card candidates of block `height`, in reveal order: tx index, inscription id, the card.
type Cards = Vec<(u32, String, ProjectCard)>;

fn deploys_of(t: &Trees, height: u64) -> Result<(BTreeMap<u32, (String, String, Vec<u8>)>, Cards, std::collections::HashSet<String>)> {
  let mut out = BTreeMap::new();
  let mut cards = Vec::new();
  let mut ids = std::collections::HashSet::new();
  let mut rows = Vec::new();
  t.seq.for_each_prefix(height.to_be_bytes(), |k, v| {
    let e: SeqEntry = bincode::deserialize(v).context("decode seq entry")?;
    rows.push((u32::from_be_bytes(k[8..12].try_into().unwrap()), e.id));
    Ok(true)
  })?;
  for (i, id) in rows {
    ids.insert(id.clone());
    let Some(raw) = t.content.get(id.as_bytes())? else { continue };
    let c = decode_inscription_content(raw.as_ref())?;
    if c.content_type.to_ascii_lowercase().starts_with("application/json") {
      if let Some(card) = parse_card(&c.body) {
        cards.push((i, id.clone(), card));
      }
    }
    if out.contains_key(&i) {
      continue;
    }
    if let Some(code) = wire::deploy_code(&c.content_type, &c.body) {
      out.insert(i, (id, c.content_type, code));
    }
  }
  Ok((out, cards, ids))
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
  let (deploys, cards, block_ids) = deploys_of(t, height)?;
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
      deployer: block.tx.get(i as usize).and_then(reveal_signer).as_ref().map(p2pkh_address),
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
    let mut from_addrs: Vec<String> = Vec::new();
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
        if !from_addrs.contains(addr) {
          from_addrs.push(addr.clone());
        }
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
      parcels_from: from_addrs.clone(),
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
      let meta = DeployMeta { id: born, height, tx_index: i, txid: tx.txid.clone(), time, program: Some(pm.id.clone()), deployer: None, ..pm };
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
    // per-address history: the verified sender, every address whose parcels were spent, every address
    // that received some
    let mut who: Vec<String> = from_addrs;
    who.extend(rec.sender.iter().cloned());
    who.extend(rec.parcels_out.iter().filter_map(|o| o.address.clone()));
    who.sort();
    who.dedup();
    for a in who {
      w.put(T_IDX, addr_history_key(&a, height, i), Some(tx.txid.clone().into_bytes()));
    }
    w.put(T_TX, tx.txid.clone().into_bytes(), Some(serde_json::to_vec(&rec)?));
    n_tx += 1;
  }
  // 3. project cards (§22): from the contract's reveal key, naming an image of an earlier block;
  // a later card from that key replaces the stored one
  for (i, insc, mut card) in cards {
    let Some(tx) = block.tx.get(i as usize) else { continue };
    let (Some(id), Some(signer)) = (parse_id(&card.dalkane), reveal_signer(tx)) else { continue };
    let Some(raw) = w.get(T_CODE, &id_key(id))? else { continue };
    let meta: DeployMeta = serde_json::from_slice(&raw)?;
    if meta.program.is_some() || meta.deployer.as_deref() != Some(p2pkh_address(&signer).as_str()) {
      continue;
    }
    if block_ids.contains(&card.image) {
      continue;
    }
    let Some(img) = t.content.get(card.image.as_bytes())? else { continue };
    if !decode_inscription_content(img.as_ref())?.content_type.to_ascii_lowercase().starts_with("image/") {
      continue;
    }
    card.inscription_id = insc;
    card.height = height;
    w.put(T_IDX, card_key(id), Some(serde_json::to_vec(&card)?));
  }
  // 4. the block's storage and ledger writes (§8: zero balances are deleted)
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
  // caught up = every block the main index has is read here too (wallets rely on it: until then a
  // parcel on an output of a newer block is unknown)
  Ok(DalkStatus { activation: ACTIVATION, height, indexed, caught_up: height >= indexed, contracts, transactions })
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
  /// The project card (§22), if its deployer inscribed one.
  pub card: Option<ProjectCard>,
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
    card: t.get(T_IDX, &card_key(id))?.map(|v| serde_json::from_slice(&v)).transpose()?,
    meta,
  })
}

/// Contracts, newest first.
/// One page of inscribed contracts, newest first. Walks the code tree once, counts matches, and only
/// materialises `limit` metas (and their summaries). `prints: false` leaves out ids born by a pull (§20),
/// so the factories and tokens can't be pushed off a page by a collection's prints.
fn page_contract_metas(t: &Trees, offset: usize, limit: usize, prints: bool) -> Result<(Vec<DeployMeta>, usize)> {
  let mut total = 0usize;
  let mut out = Vec::new();
  t.t[T_CODE as usize].for_each_rev_from(b"", |_, v| {
    let m = serde_json::from_slice::<DeployMeta>(v)?;
    if prints || m.program.is_none() {
      if total >= offset && out.len() < limit {
        out.push(m);
      }
      total += 1;
    }
    Ok(true)
  })?;
  Ok((out, total))
}

pub fn dalk_contracts(config: &Config, offset: usize, limit: usize, prints: bool) -> Result<(Vec<ContractSummary>, usize)> {
  let t = read_trees(config)?;
  let height = load_state(&t.meta)?.next_height.saturating_sub(1);
  let (page, total) = page_contract_metas(&t, offset, limit, prints)?;
  let out = page.into_iter().map(|m| summary(config, &t, m, height)).collect::<Result<_>>()?;
  Ok((out, total))
}

/// Whether `sender` has already taken this contract's once-per-address claim. Print programs use key
/// `0x15 ‖ sender` (§20.1). Other builds try opcode 106 (Howl, §18) and, if that is not a yes/no
/// view, any successful receipt from this sender. `None` if the id is not a contract.
pub fn dalk_sender_claimed(config: &Config, id: Id, sender: [u8; 20]) -> Result<Option<bool>> {
  let db = ii::db_of(config)?;
  let t = Trees::open(&db)?;
  sender_claimed_in(&t, Some(&db), id, sender)
}

fn sender_claimed_in(t: &Trees, db: Option<&store::Db>, id: Id, sender: [u8; 20]) -> Result<Option<bool>> {
  let Some(raw) = t.get(T_CODE, &id_key(id))? else { return Ok(None) };
  let meta: DeployMeta = serde_json::from_slice(&raw)?;
  let print_program = meta.program.is_none()
    && canon_of(&meta.code_hash).is_some_and(|c| matches!(c.0, "proof" | "shibkane" | "doge"));
  if print_program {
    let v = t.get(T_STORAGE, &storage_key(id, &[&[0x15u8][..], &sender[..]].concat()))?;
    return Ok(Some(v.as_deref() == Some(&[0x01])));
  }
  if let Some(db) = db {
    let height = load_state(&t.meta)?.next_height;
    let view: Rc<dyn StateView> = Rc::new(DbView {
      wasm: db.open_tree("dalk_wasm")?,
      storage: db.open_tree("dalk_storage")?,
      ledger: db.open_tree("dalk_ledger")?,
    });
    let env = vm::CallEnv {
      height,
      tx: u32::MAX,
      time: 0,
      target: id,
      fuel: 1_000_000,
      calldata: vm::calldata(&[106]),
      sender: Some(sender),
      ..Default::default()
    };
    let r = vm::execute(&ENGINE, view, &env);
    if r.ok {
      return Ok(Some(r.ret.first() == Some(&1)));
    }
  }
  let addr = p2pkh_address(&sender);
  let mut p = b"c|".to_vec();
  p.extend_from_slice(&id_key(id));
  let mut found = false;
  t.t[T_IDX as usize].for_each_prefix(&p, |_, v| {
    if found {
      return Ok(true);
    }
    let txid = String::from_utf8_lossy(v);
    if let Some(raw) = t.get(T_TX, txid.as_bytes())? {
      let rec: TxRecord = serde_json::from_slice(&raw)?;
      if rec.sender.as_deref() == Some(addr.as_str()) && rec.receipt.as_ref().is_some_and(|x| x.ok) {
        found = true;
      }
    }
    Ok(true)
  })?;
  Ok(Some(found))
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
  /// A Proof or Shibkane collection (§20): the tag, the count and the first 48 prints on a program;
  /// the parent and the index on a print.
  pub orbital: Option<serde_json::Value>,
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
  let st = |key: &[u8]| -> Result<Option<Vec<u8>>> { t.get(T_STORAGE, &storage_key(id, key)) };
  let orbital = if matches!(summary.kind.as_deref(), Some("proof" | "shibkane" | "doge")) {
    if let Some(parent) = summary.meta.program.clone() {
      Some(serde_json::json!({ "standard": "dalkane-orbital/1", "parent": parent, "index": st(&[0x13])?.map(|v| u64_le(&v)) }))
    } else {
      let count = st(&[0x10])?.map(|v| u64_le(&v)).unwrap_or(0);
      let mut prints = Vec::new();
      for n in 0..count.min(48) {
        let mut k = vec![0x11];
        k.extend_from_slice(&(n as u32).to_le_bytes());
        if let Some(v) = st(&k)? {
          if v.len() >= 16 {
            prints.push(fmt_id((u64_le(&v[..8]), u64_le(&v[8..16]) as u32)));
          }
        }
      }
      Some(serde_json::json!({ "standard": "dalkane-orbital/1", "count": count, "prints": prints }))
    }
  } else {
    None
  };
  Ok(Some(ContractDetail {
    summary,
    top_holders: holders.into_iter().take(100).map(|(a, n, o)| Holder { address: a, amount: n.to_string(), outputs: o }).collect(),
    sheet,
    storage_keys,
    orbital,
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

/// An address's Ðalkanes history (claims it made, units it received or sent), newest first.
pub fn dalk_address_activity(config: &Config, address: &str, offset: usize, limit: usize) -> Result<(Vec<TxRecord>, usize)> {
  let t = read_trees(config)?;
  let mut p = b"w|".to_vec();
  p.extend_from_slice(address.as_bytes());
  p.push(b'|');
  records_from(&t, &p, offset, limit)
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

/// The parcels on each of `outpoints` ("txid:vout"), in order: (alkane id, amount), empty for none.
pub(crate) fn parcels_on(db: &store::Db, outpoints: &[&str]) -> Result<Vec<Vec<(String, String)>>> {
  let tree = db.open_tree("dalk_parcel")?;
  let got = tree.multi_get(outpoints)?;
  got
    .into_iter()
    .map(|hit| match hit {
      Some(raw) => Ok(serde_json::from_slice::<ParcelRec>(raw.as_ref())?.items.into_iter().filter(|(_, a)| a != "0").collect()),
      None => Ok(Vec::new()),
    })
    .collect()
}

/// What a dry run reports: the call's result and, for a print birth (§20), the id it ran as.
pub struct SimOutcome {
  pub result: vm::CallResult,
  /// The id a successful pull would give its print. The real id is the pull's own block:tx, known
  /// only once it is mined; the dry run uses the next block and index 1.
  pub born: Option<Id>,
}

/// Committed state, plus the program's code under the id a birth would take (§20).
struct SimView {
  db: DbView,
  born: Option<(Id, Rc<Vec<u8>>)>,
}

impl StateView for SimView {
  fn code(&self, id: Id, h: u64, tx: u32) -> Option<Rc<Vec<u8>>> {
    match &self.born {
      Some((b, code)) if *b == id => Some(code.clone()),
      _ => self.db.code(id, h, tx),
    }
  }
  fn storage(&self, id: Id, key: &[u8]) -> Option<Vec<u8>> {
    // Appendix A (spec 0.4.2): the birth runs with the print's storage empty, even if the placeholder
    // id is already taken in committed state
    match &self.born {
      Some((b, _)) if *b == id => None,
      _ => self.db.storage(id, key),
    }
  }
  fn ledger(&self, key: &[u8]) -> u128 {
    self.db.ledger(key)
  }
}

/// A dry run of a top-level call against committed state at the next block: what a wallet asks
/// before it signs. `sender` is the verified sender's 20-byte hash, `value` the koinu the carrier
/// would burn. Nothing is written. Opcode 77 on an inscribed Proof or Shibkane program runs as the
/// block does (§20): a Proof's gate first, then the program as the new id with the program as caller.
pub fn dalk_simulate(config: &Config, target: Id, inputs: &[u128], value: u64, sender: Option<[u8; 20]>, fuel: Option<u64>) -> Result<SimOutcome> {
  let db = ii::db_of(config)?;
  let meta = load_state(&db.open_tree("meta")?)?;
  let now = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0);
  simulate_at(&db, meta.next_height, now, target, inputs, value, sender, fuel)
}

fn simulate_at(db: &store::Db, height: u64, time: u64, target: Id, inputs: &[u128], value: u64, sender: Option<[u8; 20]>, fuel: Option<u64>) -> Result<SimOutcome> {
  let base = DbView { wasm: db.open_tree("dalk_wasm")?, storage: db.open_tree("dalk_storage")?, ledger: db.open_tree("dalk_ledger")? };
  let tx = 1u32;
  let mut birth: Option<(Id, Rc<Vec<u8>>)> = None;
  if inputs.first() == Some(&77) {
    if let Some(code) = base.code(target, height, tx) {
      let kind = canon_of(&hex::encode(Sha256::digest(&code[..]))).map(|c| c.0);
      let is_print = db.open_tree("dalk_code")?.get(id_key(target))?.and_then(|v| serde_json::from_slice::<DeployMeta>(v.as_ref()).ok()).is_some_and(|m| m.program.is_some());
      if matches!(kind, Some("proof" | "shibkane" | "doge")) && !is_print {
        if matches!(kind, Some("proof" | "shibkane" | "doge")) {
          if let Some(why) = proof_refusal(&base, target, height, sender) {
            return Ok(SimOutcome { result: vm::CallResult { ok: false, error: Some(why.into()), ..Default::default() }, born: None });
          }
        }
        birth = Some(((height, tx), code));
      }
    }
  }
  let born = birth.as_ref().map(|(b, _)| *b);
  let env = vm::CallEnv {
    height,
    tx,
    time,
    target: born.unwrap_or(target),
    fuel: fuel.unwrap_or(vm::MAX_FUEL).min(vm::MAX_FUEL).max(1),
    calldata: vm::calldata(inputs),
    value,
    sender,
    caller: if born.is_some() { target } else { (0, 0) },
    ..Default::default()
  };
  let view: Rc<dyn StateView> = Rc::new(SimView { db: base, born: birth });
  let result = vm::execute(&ENGINE, view, &env);
  let born = born.filter(|_| result.ok);
  Ok(SimOutcome { result, born })
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
    // §24: the print programs, and the superseded bodies that are not
    assert_eq!(canon_of("7c9b14ca1babaf1ee229f26a49b89e8d54e7ad86af6adc228492e273ec9e1694").unwrap().0, "proof");
    assert_eq!(canon_of("b69f0aa9b8cd66335d1c08fa6c86d3af7d6b0def30c8d8688eff6ebefe9c71a4").unwrap().0, "shibkane");
    assert_eq!(canon_of("aeafccfee33779532d930b86bfbd2fbb0e5519db072dc26e29888e3c4040a4c4").unwrap().0, "doge");
    for old in [
      "43a9ebb3a709a6622d15df9328670aea26ffb4c30a9f65fe8e78848fa142183c",
      "3cba30282ed8344d15416e980c997cb8197d3d587972ea9c3df93a261ae89bf0",
      "9e9bfc0422676b8d7c76597fb08a8645c90ab15ecd378e32f927cf54084cf345",
    ] {
      assert!(canon_of(old).is_none(), "{old}");
    }
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
    // per-address history: the claimer has the claim and the spend, the receiver the spend
    assert_eq!(count_prefix(&t.t[T_IDX as usize], b"w|DKbD8jBVQ8Q7hSQBzNrhm3zt5nNTanFAWB|").unwrap(), 2);
    assert_eq!(count_prefix(&t.t[T_IDX as usize], b"w|DAAAA|").unwrap(), 1);
    let sent: TxRecord = serde_json::from_slice(&t.get(T_TX, spend.as_bytes()).unwrap().unwrap()).unwrap();
    assert_eq!(sent.parcels_from, vec!["DKbD8jBVQ8Q7hSQBzNrhm3zt5nNTanFAWB".to_string()]);
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
    // below PRINT_BLOCK_LOCK_END: the original gate, block lock included
    let h0 = 6_470_000u64;
    let insc = format!("{}i0", "ab".repeat(32));
    t.seq.insert(ii::seq_key(h0, 1), bincode::serialize(&SeqEntry { id: insc.clone(), kinds: 0, time: 0 }).unwrap()).unwrap();
    t.content.insert(insc.as_bytes(), bincode::serialize(&crate::InscriptionContentRecord { content_type: "application/wasm".into(), body, delegate: None }).unwrap()).unwrap();
    let mut st = State { next_height: h0 + 1, ..Default::default() };
    let mut txs = filler(1, h0);
    txs.push(txj(&"ab".repeat(32), serde_json::json!([{}]), serde_json::json!([{ "value": 0.001, "n": 0, "scriptPubKey": { "hex": "51" } }])));
    index_block(&db, &t, h0, &block(h0, txs), &HashMap::new(), &st).unwrap();
    let meta: DeployMeta = serde_json::from_slice(&t.get(T_CODE, &id_key((h0, 1))).unwrap().unwrap()).unwrap();
    assert_eq!(canon_of(&meta.code_hash).map(|c| c.0), Some("proof"));
    assert_eq!(
      canon_of("9a4e2f5e047393f4896436896fefc72531f50f8aa38f0bd32c59b7bf01eb70d8").map(|c| c.0),
      Some("launch")
    );


    let k1 = secp256k1::SecretKey::from_slice(&[7u8; 32]).unwrap();
    let k2 = secp256k1::SecretKey::from_slice(&[9u8; 32]).unwrap();
    let p2pkh = hex::decode("76a914000000000000000000000000000000000000000088ac").unwrap();
    let pull = |h: u64, target: Id, key: &secp256k1::SecretKey, st: &mut State| -> TxRecord {
      let raw = signed_call(key, target, &[77, 1], &p2pkh);
      let txid = format!("{:064x}", h);
      let mut txs = filler(1, h);
      txs.push(call_tx(&txid, &raw));
      let mut rawmap = HashMap::new();
      rawmap.insert(txid.clone(), raw);
      st.next_height = h + 1;
      index_block(&db, &t, h, &block(h, txs), &rawmap, st).unwrap();
      serde_json::from_slice(&t.get(T_TX, txid.as_bytes()).unwrap().unwrap()).unwrap()
    };
    let program = (h0, 1);
    let slot = |n: u32| t.get(T_STORAGE, &storage_key(program, &[&[0x11u8][..], &n.to_le_bytes()[..]].concat())).unwrap();
    // first pull: a print is born at (h0+1, 1), and the program records it at index 0
    let r = pull(h0 + 1, program, &k1, &mut st);
    let rc = r.receipt.unwrap();
    assert!(rc.ok, "{:?}", rc.error);
    assert!(r.sender.is_some());
    let born = fmt_id((h0 + 1, 1));
    assert_eq!(rc.born.as_deref(), Some(born.as_str()));
    assert_eq!((r.parcels_out[0].id.as_str(), r.parcels_out[0].amount.as_str(), r.parcels_out[0].vout), (born.as_str(), "1", 1));
    let pm: DeployMeta = serde_json::from_slice(&t.get(T_CODE, &id_key((h0 + 1, 1))).unwrap().unwrap()).unwrap();
    assert_eq!(pm.program.as_deref(), Some(fmt_id(program).as_str()));
    assert_eq!(t.get(T_STORAGE, &storage_key(program, &[0x10])).unwrap().map(|v| u64_le(&v)), Some(1));
    let mut child = (h0 + 1).to_le_bytes().to_vec();
    child.extend_from_slice(&1u64.to_le_bytes());
    assert_eq!(slot(0), Some(child));
    assert_eq!(t.get(T_STORAGE, &storage_key((h0 + 1, 1), &[0x13])).unwrap().map(|v| u64_le(&v)), Some(0));
    // the program, running as the print, wrote its parent (the caller) under 0x12
    let mut parent = h0.to_le_bytes().to_vec();
    parent.extend_from_slice(&1u64.to_le_bytes());
    assert_eq!(t.get(T_STORAGE, &storage_key((h0 + 1, 1), &[0x12])).unwrap(), Some(parent));
    // §20: the program remembers the block and the address, the address with the single byte 0x01
    assert_eq!(t.get(T_STORAGE, &storage_key(program, &[0x14])).unwrap().map(|v| u64_le(&v)), Some(h0 + 1));
    let k1h = sig::hash160(&secp256k1::PublicKey::from_secret_key(&secp256k1::Secp256k1::new(), &k1).serialize());
    assert_eq!(t.get(T_STORAGE, &storage_key(program, &[&[0x15u8][..], &k1h[..]].concat())).unwrap(), Some(vec![0x01]));
    // the same address again: refused before execution, no id
    let r = pull(h0 + 2, program, &k1, &mut st);
    let rc = r.receipt.unwrap();
    assert_eq!((rc.ok, rc.fuel_used, rc.error.as_deref(), rc.born.is_none()), (false, 0, Some("this address already pulled"), true));
    // another address births the second print, index 1
    let r = pull(h0 + 3, program, &k2, &mut st);
    assert_eq!(r.receipt.unwrap().born.as_deref(), Some(fmt_id((h0 + 3, 1)).as_str()));
    assert_eq!(t.get(T_STORAGE, &storage_key(program, &[0x10])).unwrap().map(|v| u64_le(&v)), Some(2));
    assert!(slot(1).is_some());
    // 77 on a print births nothing
    let r = pull(h0 + 4, (h0 + 1, 1), &k2, &mut st);
    let rc = r.receipt.unwrap();
    assert!(!rc.ok && rc.born.is_none(), "{rc:?}");
    // a reorg takes the second print back, slot and all
    undo_block(&t, h0 + 4, &st).unwrap();
    undo_block(&t, h0 + 3, &st).unwrap();
    assert!(t.get(T_CODE, &id_key((h0 + 3, 1))).unwrap().is_none());
    assert!(slot(1).is_none());
    assert_eq!(t.get(T_STORAGE, &storage_key(program, &[0x10])).unwrap().map(|v| u64_le(&v)), Some(1));

    // the dry run a wallet asks before a pull (§20): the gate, then the birth as the next block's id
    let k2h = sig::hash160(&secp256k1::PublicKey::from_secret_key(&secp256k1::Secp256k1::new(), &k2).serialize());
    let next = h0 + 3;
    let sim = simulate_at(&db, next, 0, program, &[77, 1], 0, Some(k2h), None).unwrap();
    assert!(sim.result.ok, "{:?}", sim.result.error);
    assert_eq!(sim.born, Some((next, 1)));
    assert_eq!(sim.result.outgoing, vec![((next, 1), 1, 1)]);
    // k1 already pulled: refused before execution, no id, no fuel
    let sim = simulate_at(&db, next, 0, program, &[77, 1], 0, Some(k1h), None).unwrap();
    assert_eq!((sim.result.ok, sim.result.fuel_used, sim.result.error.as_deref(), sim.born), (false, 0, Some("this address already pulled"), None));
    // the block that last pulled is refused too
    let sim = simulate_at(&db, h0 + 1, 0, program, &[77, 1], 0, Some(k2h), None).unwrap();
    assert_eq!(sim.result.error.as_deref(), Some("this block already pulled"));
    // 77 on a print is not a birth
    let sim = simulate_at(&db, next, 0, (h0 + 1, 1), &[77, 1], 0, Some(k2h), None).unwrap();
    assert!(!sim.result.ok && sim.born.is_none());
  }

  /// §24 (spec 0.4.2): a superseded Shibkane body (9e9bfc04) is not a print program: no label, no
  /// birth, and none of the §20.1 refusals.
  #[test]
  fn superseded_shibkane_is_not_a_print_program() {
    let db = store::Db::temporary().unwrap();
    let t = Trees::open(&db).unwrap();
    let body = hex::decode(include_str!("vectors/shibkane-deploy.hex").trim()).unwrap();
    let h0 = 6_490_000u64;
    let insc = format!("{}i0", "cd".repeat(32));
    t.seq.insert(ii::seq_key(h0, 1), bincode::serialize(&SeqEntry { id: insc.clone(), kinds: 0, time: 0 }).unwrap()).unwrap();
    t.content.insert(insc.as_bytes(), bincode::serialize(&crate::InscriptionContentRecord { content_type: "application/wasm".into(), body, delegate: None }).unwrap()).unwrap();
    let mut st = State { next_height: h0 + 1, ..Default::default() };
    let mut txs = filler(1, h0);
    txs.push(txj(&"cd".repeat(32), serde_json::json!([{}]), serde_json::json!([{ "value": 0.001, "n": 0, "scriptPubKey": { "hex": "51" } }])));
    index_block(&db, &t, h0, &block(h0, txs), &HashMap::new(), &st).unwrap();
    let meta: DeployMeta = serde_json::from_slice(&t.get(T_CODE, &id_key((h0, 1))).unwrap().unwrap()).unwrap();
    assert!(canon_of(&meta.code_hash).is_none());
    let k1 = secp256k1::SecretKey::from_slice(&[11u8; 32]).unwrap();
    let p2pkh = hex::decode("76a914000000000000000000000000000000000000000088ac").unwrap();
    let program = (h0, 1);
    for h in [h0 + 1, h0 + 2] {
      let raw = signed_call(&k1, program, &[77, 1], &p2pkh);
      let txid = format!("{:064x}", h + 7);
      let mut txs = filler(1, h);
      txs.push(call_tx(&txid, &raw));
      let mut rawmap = HashMap::new();
      rawmap.insert(txid.clone(), raw);
      st.next_height = h + 1;
      index_block(&db, &t, h, &block(h, txs), &rawmap, &st).unwrap();
      let r: TxRecord = serde_json::from_slice(&t.get(T_TX, txid.as_bytes()).unwrap().unwrap()).unwrap();
      let rc = r.receipt.unwrap();
      assert!(rc.born.is_none(), "{rc:?}");
      assert!(!matches!(rc.error.as_deref(), Some("this address already pulled" | "this block already pulled" | "the collection is full")), "{rc:?}");
    }
    assert!(t.get(T_CODE, &id_key((h0 + 1, 1))).unwrap().is_none());
    let sim = simulate_at(&db, h0 + 3, 0, program, &[77, 1], 0, None, None).unwrap();
    assert!(sim.born.is_none());
  }

  /// From PRINT_BLOCK_LOCK_END a print program takes several pulls in one block, in transaction order,
  /// with sequential indexes. Below it the second pull in a block is refused. One per address and the
  /// dry run follow the same heights.
  #[test]
  fn print_block_lock_ends() {
    let db = store::Db::temporary().unwrap();
    let t = Trees::open(&db).unwrap();
    let body = hex::decode(include_str!("vectors/proof-deploy.hex").trim()).unwrap();
    let end = PRINT_BLOCK_LOCK_END;
    let h0 = end - 2;
    let insc = format!("{}i0", "ef".repeat(32));
    t.seq.insert(ii::seq_key(h0, 1), bincode::serialize(&SeqEntry { id: insc.clone(), kinds: 0, time: 0 }).unwrap()).unwrap();
    t.content.insert(insc.as_bytes(), bincode::serialize(&crate::InscriptionContentRecord { content_type: "application/wasm".into(), body, delegate: None }).unwrap()).unwrap();
    let mut st = State { next_height: h0 + 1, ..Default::default() };
    let mut txs = filler(1, h0);
    txs.push(txj(&"ef".repeat(32), serde_json::json!([{}]), serde_json::json!([{ "value": 0.001, "n": 0, "scriptPubKey": { "hex": "51" } }])));
    index_block(&db, &t, h0, &block(h0, txs), &HashMap::new(), &st).unwrap();
    let program = (h0, 1);
    let p2pkh = hex::decode("76a914000000000000000000000000000000000000000088ac").unwrap();
    let key = |b: u8| secp256k1::SecretKey::from_slice(&[b; 32]).unwrap();
    let h160 = |k: &secp256k1::SecretKey| sig::hash160(&secp256k1::PublicKey::from_secret_key(&secp256k1::Secp256k1::new(), k).serialize());
    // one block with a pull from each key, in this order; the receipts in transaction order
    let block_of = |h: u64, keys: &[secp256k1::SecretKey], st: &mut State| -> Vec<Receipt> {
      let mut txs = filler(1, h);
      let mut rawmap = HashMap::new();
      let mut ids = Vec::new();
      for (n, k) in keys.iter().enumerate() {
        let raw = signed_call(k, program, &[77, 1], &p2pkh);
        let txid = format!("{:064x}", h * 100 + n as u64 + 50);
        txs.push(call_tx(&txid, &raw));
        rawmap.insert(txid.clone(), raw);
        ids.push(txid);
      }
      st.next_height = h + 1;
      index_block(&db, &t, h, &block(h, txs), &rawmap, st).unwrap();
      ids.iter().map(|id| serde_json::from_slice::<TxRecord>(&t.get(T_TX, id.as_bytes()).unwrap().unwrap()).unwrap().receipt.unwrap()).collect()
    };
    let count = || t.get(T_STORAGE, &storage_key(program, &[0x10])).unwrap().map(|v| u64_le(&v));
    let index_of = |id: Id| t.get(T_STORAGE, &storage_key(id, &[0x13])).unwrap().map(|v| u64_le(&v));
    // the last locked block: the first pull births, the second is refused before execution
    let r = block_of(end - 1, &[key(21), key(22)], &mut st);
    assert_eq!(r[0].born.as_deref(), Some(fmt_id((end - 1, 1)).as_str()), "{:?}", r[0]);
    assert_eq!((r[1].ok, r[1].fuel_used, r[1].error.as_deref(), r[1].born.is_none()), (false, 0, Some("this block already pulled"), true));
    assert_eq!(count(), Some(1));
    // the dry run in that block says the same; from `end` it does not
    assert_eq!(simulate_at(&db, end - 1, 0, program, &[77, 1], 0, Some(h160(&key(22))), None).unwrap().result.error.as_deref(), Some("this block already pulled"));
    // from `end`: two pulls in one block both birth, indexes 1 and 2, in transaction order
    let r = block_of(end, &[key(22), key(23)], &mut st);
    assert_eq!(r[0].born.as_deref(), Some(fmt_id((end, 1)).as_str()), "{:?}", r[0]);
    assert_eq!(r[1].born.as_deref(), Some(fmt_id((end, 2)).as_str()), "{:?}", r[1]);
    assert_eq!((index_of((end, 1)), index_of((end, 2))), (Some(1), Some(2)));
    assert_eq!(count(), Some(3));
    let slot = |n: u32| t.get(T_STORAGE, &storage_key(program, &[&[0x11u8][..], &n.to_le_bytes()[..]].concat())).unwrap();
    let mut child = end.to_le_bytes().to_vec();
    child.extend_from_slice(&2u64.to_le_bytes());
    assert_eq!(slot(2), Some(child));
    // a fresh address in the block that just pulled: the dry run births it
    let sim = simulate_at(&db, end, 0, program, &[77, 1], 0, Some(h160(&key(24))), None).unwrap();
    assert!(sim.result.ok, "{:?}", sim.result.error);
    // one per address still holds, in a later block and within one block
    let r = block_of(end + 1, &[key(23), key(24), key(24)], &mut st);
    assert_eq!((r[0].ok, r[0].fuel_used, r[0].error.as_deref()), (false, 0, Some("this address already pulled")));
    assert_eq!(r[1].born.as_deref(), Some(fmt_id((end + 1, 2)).as_str()), "{:?}", r[1]);
    assert_eq!(r[2].error.as_deref(), Some("this address already pulled"));
    assert_eq!(count(), Some(4));
    assert_eq!(simulate_at(&db, end + 2, 0, program, &[77, 1], 0, Some(h160(&key(21))), None).unwrap().result.error.as_deref(), Some("this address already pulled"));
  }

  /// §20.1: the cap and the address hold at every height; the block lock only below PRINT_BLOCK_LOCK_END.
  #[test]
  fn print_refusal_rules() {
    struct V(HashMap<Vec<u8>, Vec<u8>>);
    impl StateView for V {
      fn code(&self, _: Id, _: u64, _: u32) -> Option<Rc<Vec<u8>>> {
        None
      }
      fn storage(&self, _: Id, key: &[u8]) -> Option<Vec<u8>> {
        self.0.get(key).cloned()
      }
      fn ledger(&self, _: &[u8]) -> u128 {
        0
      }
    }
    let p = (1, 1);
    let s = [7u8; 20];
    let end = PRINT_BLOCK_LOCK_END;
    let mut m = HashMap::new();
    m.insert(vec![0x10], 419u64.to_le_bytes().to_vec());
    m.insert(vec![0x14], (end - 1).to_le_bytes().to_vec());
    let v = V(m.clone());
    assert_eq!(proof_refusal(&v, p, end - 1, Some(s)), Some("this block already pulled"));
    assert_eq!(proof_refusal(&v, p, end, Some(s)), None);
    m.insert(vec![0x14], end.to_le_bytes().to_vec());
    assert_eq!(proof_refusal(&V(m.clone()), p, end, Some(s)), None);
    m.insert([&[0x15u8][..], &s[..]].concat(), vec![0x01]);
    assert_eq!(proof_refusal(&V(m.clone()), p, end + 5, Some(s)), Some("this address already pulled"));
    assert_eq!(proof_refusal(&V(m.clone()), p, end + 5, Some([8u8; 20])), None);
    m.insert(vec![0x10], 420u64.to_le_bytes().to_vec());
    assert_eq!(proof_refusal(&V(m.clone()), p, end + 5, Some([8u8; 20])), Some("the collection is full"));
  }

  /// §22.1: the card body, under the schema.
  #[test]
  fn project_card_rules() {
    let img = format!("{}i0", "AB".repeat(32));
    let ok = format!(r#"{{"dalkane":"6474606:65","image":"{img}","name":"Kibble","links":[{{"label":"site","url":"https://doginals.store"}}]}}"#);
    let c = parse_card(ok.as_bytes()).unwrap();
    assert_eq!(c.image, format!("{}i0", "ab".repeat(32)));
    assert!(parse_card(format!(r#"{{"dalkane":"1:2","image":"{img}","extra":1}}"#).as_bytes()).is_none());
    assert!(parse_card(br#"{"dalkane":"1:2"}"#).is_none());
    assert!(parse_card(format!(r#"{{"dalkane":"1:2","image":"{img}","links":[{{"label":"x","url":"ftp://a.b"}}]}}"#).as_bytes()).is_none());
    assert!(parse_card(format!(r#"{{"dalkane":"1:2","image":"{img}","name":""}}"#).as_bytes()).is_none());
  }

  fn meta_at(h: u64, tx: u32, program: Option<&str>, hash: &str) -> DeployMeta {
    DeployMeta {
      id: fmt_id((h, tx)),
      height: h,
      tx_index: tx,
      txid: format!("{h:064x}"),
      inscription_id: format!("{:064x}i0", h),
      content_type: "application/wasm".into(),
      code_hash: hash.into(),
      code_len: 8,
      time: 0,
      program: program.map(str::to_string),
      deployer: None,
    }
  }

  /// Paging walks the code tree and only keeps the requested slice, including when prints are omitted.
  #[test]
  fn contracts_page_skips_then_takes() {
    let db = store::Db::temporary().unwrap();
    let t = Trees::open(&db).unwrap();
    let hash = "00".repeat(32);
    // five factories (10:0 .. 14:0) and two prints under the last one; ids increase so reverse order is newest first
    for h in 10u64..15 {
      t.t[T_CODE as usize].insert(id_key((h, 0)), serde_json::to_vec(&meta_at(h, 0, None, &hash)).unwrap()).unwrap();
    }
    t.t[T_CODE as usize].insert(id_key((14, 1)), serde_json::to_vec(&meta_at(14, 1, Some("14:0"), &hash)).unwrap()).unwrap();
    t.t[T_CODE as usize].insert(id_key((14, 2)), serde_json::to_vec(&meta_at(14, 2, Some("14:0"), &hash)).unwrap()).unwrap();
    let (page, total) = page_contract_metas(&t, 0, 2, false).unwrap();
    assert_eq!(total, 5, "prints are not counted when omitted");
    assert_eq!(page.iter().map(|m| m.id.as_str()).collect::<Vec<_>>(), ["14:0", "13:0"]);
    let (page, total) = page_contract_metas(&t, 4, 2, false).unwrap();
    assert_eq!(total, 5);
    assert_eq!(page.iter().map(|m| m.id.as_str()).collect::<Vec<_>>(), ["10:0"]);
    let (page, total) = page_contract_metas(&t, 0, 10, true).unwrap();
    assert_eq!(total, 7);
    assert_eq!(page[0].id, "14:2");
  }

  /// A print program's once-per-sender flag is the 0x15‖sender key, not a slice of recent txs.
  #[test]
  fn print_claimed_reads_the_sender_key() {
    let db = store::Db::temporary().unwrap();
    let t = Trees::open(&db).unwrap();
    let hash = "7c9b14ca1babaf1ee229f26a49b89e8d54e7ad86af6adc228492e273ec9e1694";
    let program = (1000u64, 7u32);
    t.t[T_CODE as usize].insert(id_key(program), serde_json::to_vec(&meta_at(1000, 7, None, hash)).unwrap()).unwrap();
    let a = [7u8; 20];
    let b = [8u8; 20];
    t.t[T_STORAGE as usize].insert(storage_key(program, &[&[0x15u8][..], &a[..]].concat()), vec![0x01]).unwrap();
    assert_eq!(sender_claimed_in(&t, None, program, a).unwrap(), Some(true));
    assert_eq!(sender_claimed_in(&t, None, program, b).unwrap(), Some(false));
    assert_eq!(sender_claimed_in(&t, None, (9, 9), a).unwrap(), None);
  }
}
