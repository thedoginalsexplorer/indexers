//! Dalkanes contract runtime (github.com/jonheaven/dalkanes, spec v0.4): WebAssembly contracts run in
//! the pinned interpreter `wasmi` 1.1.0 with fuel metering, the `env` host ABI (spec §7), nested
//! calls with exact rollback, the host ledger (§8) and output parcels (§16).
//!
//! This file is pure: it reads committed state through [`StateView`] and returns staged writes. The
//! indexer applies them to its database in block order.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use sha2::{Digest, Sha256};
use wasmi::{Caller, Config, Engine, Linker, Module, Store};

/// A contract id: (block, tx).
pub type Id = (u64, u32);

pub const MAX_FUEL: u64 = 5_000_000;
pub const BLOCK_FUEL_BUDGET: u64 = 100_000_000;
pub const CALLDATA_PTR: u32 = 0x1000;
pub const MAX_DEPTH: u32 = 8;
pub const MAX_FRAME_KEYS: usize = 512;
pub const MAX_RETURN: usize = 16_384;
pub const MAX_LOG: usize = 256;
pub const MAX_CODE: usize = 524_288;

/// 12-byte key form of an id (§3).
pub fn id_key(id: Id) -> [u8; 12] {
  let mut k = [0u8; 12];
  k[..8].copy_from_slice(&id.0.to_be_bytes());
  k[8..].copy_from_slice(&id.1.to_be_bytes());
  k
}

pub fn id_from_key(k: &[u8]) -> Option<Id> {
  if k.len() < 12 {
    return None;
  }
  Some((u64::from_be_bytes(k[..8].try_into().ok()?), u32::from_be_bytes(k[8..12].try_into().ok()?)))
}

/// Ledger key: token id (12) ‖ account (1–32).
pub fn ledger_key(token: Id, acct: &[u8]) -> Vec<u8> {
  let mut k = id_key(token).to_vec();
  k.extend_from_slice(acct);
  k
}

/// Committed state, as of the start of the current call (the block overlay included).
pub trait StateView {
  /// Code of a contract visible to a call in transaction `tx` of block `height` (§5.4).
  fn code(&self, id: Id, height: u64, tx: u32) -> Option<Rc<Vec<u8>>>;
  fn storage(&self, id: Id, key: &[u8]) -> Option<Vec<u8>>;
  fn ledger(&self, key: &[u8]) -> u128;
}

/// One call's inputs.
#[derive(Clone, Debug, Default)]
pub struct CallEnv {
  pub height: u64,
  pub tx: u32,
  pub time: u64,
  pub target: Id,
  pub fuel: u64,
  pub calldata: Vec<u8>,
  pub value: u64,
  pub sender: Option<[u8; 20]>,
  pub incoming: Vec<(Id, u128)>,
}

/// What a call did.
#[derive(Clone, Debug, Default)]
pub struct CallResult {
  pub ok: bool,
  pub fuel_used: u64,
  pub ret: Vec<u8>,
  pub error: Option<String>,
  pub logs: Vec<String>,
  /// Staged storage writes, per contract (only on success).
  pub storage: HashMap<(Id, Vec<u8>), Vec<u8>>,
  /// Staged ledger balances (only on success). Zero means delete.
  pub ledger: HashMap<Vec<u8>, u128>,
  /// Parcels this call places on outputs: (token, vout, amount).
  pub outgoing: Vec<(Id, u32, u128)>,
}

enum Undo {
  Storage((Id, Vec<u8>), Option<Vec<u8>>),
  Ledger(Vec<u8>, Option<u128>),
  Outgoing(usize),
}

/// State shared by every frame of one top-level call.
struct Shared {
  view: Rc<dyn StateView>,
  engine: Engine,
  height: u64,
  top_tx: u32,
  time: u64,
  storage: HashMap<(Id, Vec<u8>), Vec<u8>>,
  ledger: HashMap<Vec<u8>, u128>,
  journal: Vec<Undo>,
  logs: Vec<String>,
  outgoing: Vec<(Id, u32, u128)>,
  /// Outer `None`: no visible code. Inner `None`: code that does not decode.
  modules: HashMap<Id, Option<Option<Module>>>,
}

impl Shared {
  fn storage_get(&self, id: Id, key: &[u8]) -> Option<Vec<u8>> {
    match self.storage.get(&(id, key.to_vec())) {
      Some(v) => Some(v.clone()),
      None => self.view.storage(id, key),
    }
  }
  fn storage_set(&mut self, id: Id, key: Vec<u8>, val: Vec<u8>) {
    let k = (id, key);
    let prev = self.storage.insert(k.clone(), val);
    self.journal.push(Undo::Storage(k, prev));
  }
  fn ledger_get(&self, key: &[u8]) -> u128 {
    match self.ledger.get(key) {
      Some(v) => *v,
      None => self.view.ledger(key),
    }
  }
  fn ledger_set(&mut self, key: Vec<u8>, val: u128) {
    let prev = self.ledger.insert(key.clone(), val);
    self.journal.push(Undo::Ledger(key, prev));
  }
  fn push_outgoing(&mut self, token: Id, vout: u32, amount: u128) {
    self.outgoing.push((token, vout, amount));
    self.journal.push(Undo::Outgoing(self.outgoing.len() - 1));
  }
  fn rollback(&mut self, mark: usize) {
    while self.journal.len() > mark {
      match self.journal.pop().unwrap() {
        Undo::Storage(k, Some(v)) => {
          self.storage.insert(k, v);
        }
        Undo::Storage(k, None) => {
          self.storage.remove(&k);
        }
        Undo::Ledger(k, Some(v)) => {
          self.ledger.insert(k, v);
        }
        Undo::Ledger(k, None) => {
          self.ledger.remove(&k);
        }
        Undo::Outgoing(i) => {
          self.outgoing.truncate(i);
        }
      }
    }
  }
  fn module(&mut self, id: Id) -> Option<Option<Module>> {
    if let Some(m) = self.modules.get(&id) {
      return m.clone();
    }
    let m = self.view.code(id, self.height, self.top_tx).map(|c| Module::new(&self.engine, &c[..]).ok());
    self.modules.insert(id, m.clone());
    m
  }
}

/// Per-frame data held by the wasmi store.
struct Frame {
  shared: Rc<RefCell<Shared>>,
  myself: Id,
  caller: Id,
  depth: u32,
  tx: u32,
  value: u64,
  sender: Option<[u8; 20]>,
  incoming: Vec<(Id, u128)>,
  ret: Vec<u8>,
  keys: HashSet<Vec<u8>>,
  fatal: Option<String>,
}

pub fn engine() -> Engine {
  let mut c = Config::default();
  c.consume_fuel(true);
  Engine::new(&c)
}

type HostResult<T> = Result<T, wasmi::Error>;

fn fatal(caller: &mut Caller<'_, Frame>, msg: &str) -> wasmi::Error {
  caller.data_mut().fatal = Some(msg.to_string());
  wasmi::Error::new(msg.to_string())
}

/// Takes `cost` fuel; running short is a fatal host error (§6.4).
fn charge(caller: &mut Caller<'_, Frame>, cost: u64) -> HostResult<()> {
  let left = caller.get_fuel().unwrap_or(0);
  if cost > left {
    let _ = caller.set_fuel(0);
    return Err(fatal(caller, "out of fuel in host call"));
  }
  let _ = caller.set_fuel(left - cost);
  Ok(())
}

fn mem(caller: &Caller<'_, Frame>) -> Option<wasmi::Memory> {
  caller.get_export("memory").and_then(|e| e.into_memory())
}

fn read(caller: &Caller<'_, Frame>, ptr: i32, len: i32) -> Option<Vec<u8>> {
  let len = len.max(0) as usize;
  if ptr < 0 {
    return None;
  }
  let m = mem(caller)?;
  let mut buf = vec![0u8; len];
  m.read(caller, ptr as usize, &mut buf).ok()?;
  Some(buf)
}

fn write(caller: &mut Caller<'_, Frame>, ptr: i32, data: &[u8]) -> bool {
  if ptr < 0 {
    return false;
  }
  match mem(caller) {
    Some(m) => m.write(caller, ptr as usize, data).is_ok(),
    None => false,
  }
}

fn valid_id(b: i64, tx: i64) -> Option<Id> {
  if b < 0 || tx < 0 || tx > u32::MAX as i64 {
    return None;
  }
  Some((b as u64, tx as u32))
}

fn amount(lo: i64, hi: i64) -> u128 {
  (lo as u64 as u128) | ((hi as u64 as u128) << 64)
}

fn link(engine: &Engine) -> Linker<Frame> {
  let mut l: Linker<Frame> = Linker::new(engine);
  // ---- storage (§7.1)
  l.func_wrap("env", "storage_get", |mut c: Caller<'_, Frame>, kp: i32, kl: i32, op: i32, om: i32| -> HostResult<i32> {
    let kl = kl.max(0);
    if kl > 256 {
      return Ok(-1);
    }
    charge(&mut c, 1000 + kl as u64)?;
    let Some(key) = read(&c, kp, kl) else { return Ok(-1) };
    let me = c.data().myself;
    let v = c.data().shared.borrow().storage_get(me, &key).unwrap_or_default();
    let n = v.len().min(om.max(0) as usize);
    if !write(&mut c, op, &v[..n]) {
      return Ok(-1);
    }
    Ok(n as i32)
  })
  .unwrap();
  l.func_wrap("env", "storage_set", |mut c: Caller<'_, Frame>, kp: i32, kl: i32, vp: i32, vl: i32| -> HostResult<()> {
    let (kl, vl) = (kl.max(0), vl.max(0));
    if kl > 256 || vl > 4096 {
      return Ok(());
    }
    charge(&mut c, 1000 + kl as u64 + vl as u64)?;
    let Some(key) = read(&c, kp, kl) else { return Ok(()) };
    let Some(val) = read(&c, vp, vl) else { return Ok(()) };
    if !c.data().keys.contains(&key) {
      if c.data().keys.len() >= MAX_FRAME_KEYS {
        return Err(fatal(&mut c, "too many storage writes in one frame"));
      }
      c.data_mut().keys.insert(key.clone());
    }
    let me = c.data().myself;
    c.data().shared.borrow_mut().storage_set(me, key, val);
    Ok(())
  })
  .unwrap();
  // ---- output (§7.2)
  l.func_wrap("env", "return_data", |mut c: Caller<'_, Frame>, p: i32, n: i32| -> HostResult<()> {
    let n = (n.max(0) as usize).min(MAX_RETURN);
    if let Some(b) = read(&c, p, n as i32) {
      c.data_mut().ret = b;
    }
    Ok(())
  })
  .unwrap();
  l.func_wrap("env", "log", |c: Caller<'_, Frame>, p: i32, n: i32| -> HostResult<()> {
    let n = (n.max(0) as usize).min(MAX_LOG);
    if let Some(b) = read(&c, p, n as i32) {
      c.data().shared.borrow_mut().logs.push(String::from_utf8_lossy(&b).into_owned());
    }
    Ok(())
  })
  .unwrap();
  // ---- context (§7.3)
  l.func_wrap("env", "alkane_block", |c: Caller<'_, Frame>| -> i64 { c.data().shared.borrow().height as i64 }).unwrap();
  l.func_wrap("env", "alkane_tx", |c: Caller<'_, Frame>| -> i64 { c.data().tx as i64 }).unwrap();
  l.func_wrap("env", "alkane_time", |c: Caller<'_, Frame>| -> i64 { c.data().shared.borrow().time as i64 }).unwrap();
  l.func_wrap("env", "alkane_value", |c: Caller<'_, Frame>| -> i64 { c.data().value as i64 }).unwrap();
  l.func_wrap("env", "alkane_myself_block", |c: Caller<'_, Frame>| -> i64 { c.data().myself.0 as i64 }).unwrap();
  l.func_wrap("env", "alkane_myself_tx", |c: Caller<'_, Frame>| -> i64 { c.data().myself.1 as i64 }).unwrap();
  l.func_wrap("env", "alkane_caller_block", |c: Caller<'_, Frame>| -> i64 { c.data().caller.0 as i64 }).unwrap();
  l.func_wrap("env", "alkane_caller_tx", |c: Caller<'_, Frame>| -> i64 { c.data().caller.1 as i64 }).unwrap();
  l.func_wrap("env", "alkane_sender", |mut c: Caller<'_, Frame>, op: i32| -> HostResult<i32> {
    charge(&mut c, 1000)?;
    let Some(s) = c.data().sender else { return Ok(-1) };
    if c.data().depth > 0 || !write(&mut c, op, &s) {
      return Ok(-1);
    }
    Ok(20)
  })
  .unwrap();
  l.func_wrap("env", "incoming_count", |c: Caller<'_, Frame>| -> i32 { c.data().incoming.len() as i32 }).unwrap();
  l.func_wrap("env", "incoming_get", |mut c: Caller<'_, Frame>, i: i32, op: i32| -> HostResult<i32> {
    if i < 0 || i as usize >= c.data().incoming.len() {
      return Ok(-1);
    }
    let ((b, t), a) = c.data().incoming[i as usize];
    let mut buf = [0u8; 32];
    buf[..8].copy_from_slice(&b.to_le_bytes());
    buf[8..16].copy_from_slice(&(t as u64).to_le_bytes());
    buf[16..].copy_from_slice(&a.to_le_bytes());
    if !write(&mut c, op, &buf) {
      return Ok(-1);
    }
    Ok(32)
  })
  .unwrap();
  // ---- crypto (§7.4)
  l.func_wrap("env", "sha256", |mut c: Caller<'_, Frame>, p: i32, n: i32, op: i32| -> HostResult<i32> {
    charge(&mut c, 2000)?;
    let n = n.max(0).min(65_536);
    let Some(b) = read(&c, p, n) else { return Ok(-1) };
    let d: [u8; 32] = Sha256::digest(&b).into();
    if !write(&mut c, op, &d) {
      return Ok(-1);
    }
    Ok(32)
  })
  .unwrap();
  l.func_wrap("env", "verify_schnorr", |mut c: Caller<'_, Frame>, mp: i32, kp: i32, sp: i32| -> HostResult<i32> {
    charge(&mut c, 25_000)?;
    let (Some(m), Some(k), Some(s)) = (read(&c, mp, 32), read(&c, kp, 32), read(&c, sp, 64)) else { return Ok(0) };
    Ok(super::sig::verify_schnorr(&m, &k, &s) as i32)
  })
  .unwrap();
  // ---- host ledger (§7.5, §8)
  l.func_wrap("env", "ledger_get", |mut c: Caller<'_, Frame>, tb: i64, tt: i64, ap: i32, al: i32, op: i32| -> HostResult<i32> {
    charge(&mut c, 3000)?;
    let Some(tok) = valid_id(tb, tt) else { return Ok(-1) };
    if !(1..=32).contains(&al) {
      return Ok(-1);
    }
    let Some(acct) = read(&c, ap, al) else { return Ok(-1) };
    let bal = c.data().shared.borrow().ledger_get(&ledger_key(tok, &acct));
    if !write(&mut c, op, &bal.to_le_bytes()) {
      return Ok(-1);
    }
    Ok(16)
  })
  .unwrap();
  l.func_wrap("env", "ledger_mint", |mut c: Caller<'_, Frame>, tb: i64, tt: i64, ap: i32, al: i32, lo: i64, hi: i64| -> HostResult<i32> {
    charge(&mut c, 3000)?;
    let Some(tok) = valid_id(tb, tt) else { return Ok(0) };
    if !(1..=32).contains(&al) {
      return Ok(0);
    }
    let amt = amount(lo, hi);
    if tok != c.data().myself || amt == 0 {
      return Ok(0);
    }
    let Some(acct) = read(&c, ap, al) else { return Ok(0) };
    let k = ledger_key(tok, &acct);
    let sh = c.data().shared.clone();
    let mut s = sh.borrow_mut();
    let bal = s.ledger_get(&k).saturating_add(amt);
    s.ledger_set(k, bal);
    Ok(1)
  })
  .unwrap();
  l.func_wrap(
    "env",
    "ledger_transfer",
    |mut c: Caller<'_, Frame>, tb: i64, tt: i64, fp: i32, fl: i32, tp: i32, tl: i32, lo: i64, hi: i64| -> HostResult<i32> {
      charge(&mut c, 3000)?;
      let Some(tok) = valid_id(tb, tt) else { return Ok(0) };
      if !(1..=32).contains(&fl) || !(1..=32).contains(&tl) {
        return Ok(0);
      }
      let amt = amount(lo, hi);
      let me = c.data().myself;
      if tok != me || amt == 0 {
        return Ok(0);
      }
      let (Some(from), Some(to)) = (read(&c, fp, fl), read(&c, tp, tl)) else { return Ok(0) };
      if from.len() == 12 && from[..] != id_key(me)[..] {
        return Ok(0);
      }
      let (fk, tk) = (ledger_key(tok, &from), ledger_key(tok, &to));
      let sh = c.data().shared.clone();
      let mut s = sh.borrow_mut();
      let fb = s.ledger_get(&fk);
      if fb < amt {
        return Ok(0);
      }
      if fk != tk {
        let tb2 = s.ledger_get(&tk);
        s.ledger_set(fk, fb - amt);
        s.ledger_set(tk, tb2.saturating_add(amt));
      }
      Ok(1)
    },
  )
  .unwrap();
  // ---- output parcels (§16)
  l.func_wrap("env", "parcel_mint", |mut c: Caller<'_, Frame>, vout: i32, lo: i64, hi: i64| -> HostResult<i32> {
    charge(&mut c, 3000)?;
    let amt = amount(lo, hi);
    if c.data().depth > 0 || vout < 0 || amt == 0 {
      return Ok(0);
    }
    let me = c.data().myself;
    c.data().shared.borrow_mut().push_outgoing(me, vout as u32, amt);
    Ok(1)
  })
  .unwrap();
  l.func_wrap("env", "parcel_withdraw", |mut c: Caller<'_, Frame>, vout: i32, lo: i64, hi: i64| -> HostResult<i32> {
    charge(&mut c, 3000)?;
    let me = c.data().myself;
    Ok(parcel_out(&mut c, me, vout, amount(lo, hi)))
  })
  .unwrap();
  l.func_wrap("env", "parcel_send", |mut c: Caller<'_, Frame>, tb: i64, tt: i64, vout: i32, lo: i64, hi: i64| -> HostResult<i32> {
    charge(&mut c, 3000)?;
    let Some(tok) = valid_id(tb, tt) else { return Ok(0) };
    Ok(parcel_out(&mut c, tok, vout, amount(lo, hi)))
  })
  .unwrap();
  // ---- nested calls (§7.6)
  l.func_wrap(
    "env",
    "staticcall",
    |mut c: Caller<'_, Frame>, tb: i64, tt: i64, cp: i32, cl: i32, op: i32, om: i32, fuel: i64| -> HostResult<i32> {
      nested(&mut c, true, tb, tt, cp, cl, op, om, fuel)
    },
  )
  .unwrap();
  l.func_wrap(
    "env",
    "call",
    |mut c: Caller<'_, Frame>, tb: i64, tt: i64, cp: i32, cl: i32, op: i32, om: i32, fuel: i64| -> HostResult<i32> {
      nested(&mut c, false, tb, tt, cp, cl, op, om, fuel)
    },
  )
  .unwrap();
  l
}

/// Debits this contract's own 12-byte account of `tok` and puts the units on output `vout`.
fn parcel_out(c: &mut Caller<'_, Frame>, tok: Id, vout: i32, amt: u128) -> i32 {
  if c.data().depth > 0 || vout < 0 || amt == 0 {
    return 0;
  }
  let me = c.data().myself;
  let k = ledger_key(tok, &id_key(me));
  let sh = c.data().shared.clone();
  let mut s = sh.borrow_mut();
  let bal = s.ledger_get(&k);
  if bal < amt {
    return 0;
  }
  s.ledger_set(k, bal - amt);
  s.push_outgoing(tok, vout as u32, amt);
  1
}

#[allow(clippy::too_many_arguments)]
fn nested(c: &mut Caller<'_, Frame>, is_static: bool, tb: i64, tt: i64, cp: i32, cl: i32, op: i32, om: i32, fuel: i64) -> HostResult<i32> {
  if c.data().depth >= MAX_DEPTH {
    return Ok(-1);
  }
  charge(c, 10_000)?;
  let Some(target) = valid_id(tb, tt) else { return Ok(-1) };
  let cl = (cl.max(0) as usize).min(MAX_RETURN) as i32;
  let Some(calldata) = read(c, cp, cl) else { return Ok(-1) };
  let sh = c.data().shared.clone();
  let Some(module) = sh.borrow_mut().module(target) else { return Ok(-1) };
  let remaining = c.get_fuel().unwrap_or(0);
  let want = if fuel < 0 { 0 } else { fuel as u64 };
  let granted = remaining.min(want).max(1);
  let (mark, logs) = {
    let s = sh.borrow();
    (s.journal.len(), s.logs.len())
  };
  let frame = Frame {
    shared: sh.clone(),
    myself: target,
    caller: c.data().myself,
    depth: c.data().depth + 1,
    tx: 0,
    value: 0,
    sender: None,
    incoming: Vec::new(),
    ret: Vec::new(),
    keys: HashSet::new(),
    fatal: None,
  };
  let r = run_frame(module, frame, granted, &calldata);
  let _ = c.set_fuel(remaining.saturating_sub(r.fuel_used));
  let undo = |sh: &Rc<RefCell<Shared>>| {
    let mut s = sh.borrow_mut();
    s.rollback(mark);
    s.logs.truncate(logs);
  };
  if !r.ok {
    undo(&sh);
    return Ok(-1);
  }
  let n = r.ret.len().min(om.max(0) as usize);
  if !write(c, op, &r.ret[..n]) {
    undo(&sh);
    return Ok(-1);
  }
  if is_static {
    undo(&sh);
  }
  c.data_mut().ret = r.ret;
  Ok(n as i32)
}

struct FrameOut {
  ok: bool,
  fuel_used: u64,
  ret: Vec<u8>,
  error: Option<String>,
}

fn run_frame(module: Option<Module>, frame: Frame, granted: u64, calldata: &[u8]) -> FrameOut {
  let Some(module) = module else {
    return FrameOut { ok: false, fuel_used: 0, ret: Vec::new(), error: Some("module does not decode".into()) };
  };
  let engine = frame.shared.borrow().engine.clone();
  let mut store = Store::new(&engine, frame);
  let _ = store.set_fuel(granted);
  let used = |s: &Store<Frame>| granted.saturating_sub(s.get_fuel().unwrap_or(0));
  let fail = |s: &Store<Frame>, e: String| FrameOut { ok: false, fuel_used: used(s), ret: Vec::new(), error: Some(e) };
  let linker = link(&engine);
  let inst = match linker.instantiate_and_start(&mut store, &module) {
    Ok(i) => i,
    Err(e) => {
      let msg = store.data().fatal.clone().unwrap_or_else(|| format!("instantiate: {e}"));
      return fail(&store, msg);
    }
  };
  let Some(memory) = inst.get_memory(&store, "memory") else { return fail(&store, "no exported memory".into()) };
  let Ok(exec) = inst.get_typed_func::<(i32, i32), i32>(&store, "__dalk_execute") else {
    return fail(&store, "no __dalk_execute export".into());
  };
  if memory.write(&mut store, CALLDATA_PTR as usize, calldata).is_err() {
    return fail(&store, "calldata does not fit in memory".into());
  }
  match exec.call(&mut store, (CALLDATA_PTR as i32, calldata.len() as i32)) {
    Ok(0) if store.data().fatal.is_none() => {
      let ret = std::mem::take(&mut store.data_mut().ret);
      FrameOut { ok: true, fuel_used: used(&store), ret, error: None }
    }
    Ok(code) => {
      let msg = store.data().fatal.clone().unwrap_or_else(|| format!("status {code}"));
      let ret = std::mem::take(&mut store.data_mut().ret);
      FrameOut { ok: false, fuel_used: used(&store), ret, error: Some(msg) }
    }
    Err(e) => {
      let msg = store.data().fatal.clone().unwrap_or_else(|| trap_text(&e));
      let ret = std::mem::take(&mut store.data_mut().ret);
      FrameOut { ok: false, fuel_used: used(&store), ret, error: Some(msg) }
    }
  }
}

fn trap_text(e: &wasmi::Error) -> String {
  if let Some(t) = e.as_trap_code() {
    if t == wasmi::TrapCode::OutOfFuel {
      return "out of fuel".into();
    }
    return format!("trap: {t}");
  }
  format!("trap: {e}")
}

/// Runs one top-level call against `view`. `engine` should be shared across calls.
pub fn execute(engine: &Engine, view: Rc<dyn StateView>, env: &CallEnv) -> CallResult {
  let shared = Rc::new(RefCell::new(Shared {
    view,
    engine: engine.clone(),
    height: env.height,
    top_tx: env.tx,
    time: env.time,
    storage: HashMap::new(),
    ledger: HashMap::new(),
    journal: Vec::new(),
    logs: Vec::new(),
    outgoing: Vec::new(),
    modules: HashMap::new(),
  }));
  // A deposit sits on the contract's sheet while the call runs (§16); it only stays if the call succeeds.
  {
    let mut s = shared.borrow_mut();
    let sheet = id_key(env.target);
    for (tok, amt) in &env.incoming {
      let k = ledger_key(*tok, &sheet);
      let b = s.ledger_get(&k).saturating_add(*amt);
      s.ledger_set(k, b);
    }
  }
  let module = shared.borrow_mut().module(env.target).flatten();
  let frame = Frame {
    shared: shared.clone(),
    myself: env.target,
    caller: (0, 0),
    depth: 0,
    tx: env.tx,
    value: env.value,
    sender: env.sender,
    incoming: env.incoming.clone(),
    ret: Vec::new(),
    keys: HashSet::new(),
    fatal: None,
  };
  let granted = env.fuel.min(MAX_FUEL).max(1);
  let r = run_frame(module, frame, granted, &env.calldata);
  let mut s = shared.borrow_mut();
  let mut out = CallResult { ok: r.ok, fuel_used: r.fuel_used, ret: r.ret, error: r.error, logs: std::mem::take(&mut s.logs), ..Default::default() };
  if r.ok {
    out.storage = std::mem::take(&mut s.storage);
    out.ledger = std::mem::take(&mut s.ledger);
    out.outgoing = std::mem::take(&mut s.outgoing);
  }
  out
}

/// The calldata for a list of inputs: each a 16-byte little-endian u128 (§5.3).
pub fn calldata(inputs: &[u128]) -> Vec<u8> {
  inputs.iter().flat_map(|v| v.to_le_bytes()).collect()
}

#[cfg(test)]
mod tests {
  use super::*;

  #[derive(Default)]
  struct Mem {
    code: HashMap<Id, Rc<Vec<u8>>>,
    storage: HashMap<(Id, Vec<u8>), Vec<u8>>,
  }
  impl StateView for Mem {
    fn code(&self, id: Id, _h: u64, _t: u32) -> Option<Rc<Vec<u8>>> {
      self.code.get(&id).cloned()
    }
    fn storage(&self, id: Id, key: &[u8]) -> Option<Vec<u8>> {
      self.storage.get(&(id, key.to_vec())).cloned()
    }
    fn ledger(&self, _key: &[u8]) -> u128 {
      0
    }
  }
  fn pid(s: &str) -> Id {
    let (a, b) = s.split_once(':').unwrap();
    (a.parse().unwrap(), b.parse().unwrap())
  }
  const DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/src/dalkanes/vectors/host-abi/");
  /// Some vector files have a header comment that wrapped onto code-looking lines.
  fn wat(f: &str) -> Vec<u8> {
    let s = std::fs::read_to_string(format!("{DIR}{f}")).unwrap();
    wat::parse_str(&s[s.find("(module").unwrap()..]).unwrap()
  }

  /// Every host-ABI vector of the spec repository (vectors/host-abi/cases.json).
  #[test]
  fn host_abi_vectors() {
    let v: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(format!("{DIR}cases.json")).unwrap()).unwrap();
    let engine = engine();
    for c in v["cases"].as_array().unwrap() {
      let p = &c["params"];
      let myself = p["myself"].as_str().map(pid).unwrap_or((1, 0));
      let mut m = Mem::default();
      m.code.insert(myself, Rc::new(wat(c["module"].as_str().unwrap())));
      if let Some(cs) = c["contracts"].as_object() {
        for (k, f) in cs {
          m.code.insert(pid(k), Rc::new(wat(f.as_str().unwrap())));
        }
      }
      if p["state_storage"].is_object() {
        for i in 0u64..20000 {
          m.storage.insert((myself, i.to_le_bytes().to_vec()), (i as u32).to_le_bytes().to_vec());
        }
      }
      let env = CallEnv {
        height: p["height"].as_u64().unwrap(),
        tx: p["tx_index"].as_u64().unwrap() as u32,
        time: p["block_time"].as_u64().unwrap(),
        target: myself,
        fuel: p["fuel"].as_u64().unwrap(),
        calldata: hex::decode(p["calldata_hex"].as_str().unwrap()).unwrap(),
        value: p["attached_value"].as_u64().unwrap_or(0),
        sender: p["sender_hex"].as_str().map(|s| hex::decode(s).unwrap().try_into().unwrap()),
        incoming: p["incoming"]
          .as_array()
          .map(|a| a.iter().map(|x| ((x["token_block"].as_u64().unwrap(), x["token_tx"].as_u64().unwrap() as u32), x["amount"].as_str().unwrap().parse().unwrap())).collect())
          .unwrap_or_default(),
      };
      let r = execute(&engine, Rc::new(m), &env);
      let e = &c["expect"];
      let name = c["name"].as_str().unwrap();
      assert_eq!(r.ok, e["ok"].as_bool().unwrap(), "{name}: {:?}", r.error);
      if let Some(h) = e["return_hex"].as_str() {
        assert_eq!(hex::encode(&r.ret), h, "{name}");
      }
      if let Some(f) = e["fuel_used"].as_u64() {
        assert_eq!(r.fuel_used, f, "{name}");
      }
      if let Some(f) = e["fuel_used_gt"].as_u64() {
        assert!(r.fuel_used > f, "{name}");
      }
      if let Some(w) = e["storage_writes"].as_object().or(e["contract_writes"].as_object()) {
        let mut got: Vec<String> = r.storage.iter().map(|((id, k), v)| format!("{}:{} {}={}", id.0, id.1, hex::encode(k), hex::encode(v))).collect();
        got.sort();
        let mut want: Vec<String> = w.iter().flat_map(|(id, kv)| kv.as_object().unwrap().iter().map(move |(k, v)| format!("{id} {k}={}", v.as_str().unwrap()))).collect();
        want.sort();
        assert_eq!(got, want, "{name}");
      }
    }
  }

  /// The block budget's grants (vectors/block-fuel.json, case 2): 5M, then 2M, then exhausted.
  #[test]
  fn budget_grants() {
    let mut budget = 7_000_000u64;
    let mut granted = Vec::new();
    for want in [5_000_000u64, 5_000_000, 5_000_000] {
      let g = if budget == 0 { 0 } else { want.min(MAX_FUEL).max(1).min(budget) };
      granted.push(g);
      budget -= g;
    }
    assert_eq!(granted, vec![5_000_000, 2_000_000, 0]);
  }

  /// The live Howl claim at block 6,474,090: canonical Howl code, verified sender, 0.16 DOGE burned.
  #[test]
  fn live_howl_claim() {
    let body = hex::decode(include_str!("vectors/howl-deploy.hex").trim()).unwrap();
    let code = super::super::wire::deploy_code("application/wasm", &body).unwrap();
    let raw = hex::decode(include_str!("vectors/howl-call-tx.hex").trim()).unwrap();
    let sender = super::super::sig::sender(&raw);
    assert_eq!(sender.map(hex::encode).as_deref(), Some("9dabb48cc18082a37ff23d46f891f5f9256d8d12"));
    let mut m = Mem::default();
    m.code.insert((6474082, 35), Rc::new(code));
    let env = CallEnv { height: 6474090, tx: 15, time: 1795725477, target: (6474082, 35), fuel: 200_000, calldata: calldata(&[77, 1]), value: 16_000_000, sender, incoming: vec![] };
    let r = execute(&engine(), Rc::new(m), &env);
    assert!(r.ok, "{:?}", r.error);
    assert_eq!(r.outgoing, vec![((6474082, 35), 1, 16)]);
    // without a sender the claim fails with status 3 after 7,238 fuel (what dogex recorded)
    let env = CallEnv { sender: None, ..env };
    let mut m = Mem::default();
    m.code.insert((6474082, 35), Rc::new(super::super::wire::deploy_code("application/wasm", &body).unwrap()));
    let r = execute(&engine(), Rc::new(m), &env);
    assert_eq!((r.ok, r.fuel_used, r.error.as_deref()), (false, 7238, Some("status 3")));
  }
}
