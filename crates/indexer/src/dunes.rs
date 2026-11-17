//! Dunes, indexed the way the Dunes reference indexer does it.
//!
//! The reference is wonky-ord's Dune updater and dunestone parser (the copy
//! here is projects\wonky-ord-pepecoin, `src/index/updater/dune_updater.rs`
//! and `src/dunes/`), with Dogecoin's constants from the official etcher
//! (sirduney/dunes-cli): Dunes begin at block 5,084,000 and the shortest name
//! allowed shrinks from 13 letters over 2,100,000 blocks. Quirks are kept on
//! purpose, so balances here are the balances the protocol gives:
//!
//!  - a dune is referred to by its id, `height << 16 | tx index` (`BLOCK:TX`),
//!    in edicts and mints (with bit 48 set for a mint), never by name;
//!  - an etching is void if its name is taken, reserved or shorter than the
//!    minimum at that height; an unnamed one gets the next reserved name;
//!  - a premine is an extra edict (id 0, output 1) after the others, and id-0
//!    edicts draw on an unlimited balance; the premine is what they allocate;
//!  - an edict to an output past the last one, including "every output"
//!    (= number of outputs), is skipped;
//!  - a malformed message (an unknown even field, unknown flags, a bad edict,
//!    an overflowing premine + cap x limit) is a cenotaph: its etching has no
//!    mint terms, its edicts and mints do nothing, and every input dune burns;
//!  - leftovers go to the pointer output if valid, else the first output that
//!    is not OP_RETURN, else burn. Anything allocated to OP_RETURN burns.
//!
//! The rules run over a [`State`]: the live store (with the undo log) or the
//! replay's memory, so both apply exactly the same code.

use super::*;

pub(crate) const CLAIM_BIT: u128 = 1 << 48;
const MAX_DIVISIBILITY: u8 = 38;
const MAX_LIMIT: u128 = u64::MAX as u128;
const MAX_SPACERS: u32 = 0b0000_0111_1111_1111_1111_1111_1111_1111;
const RESERVED: u128 = 6_402_364_363_415_443_603_228_541_259_936_211_926;
/// bitcoin's SUBSIDY_HALVING_INTERVAL x 10, as the reference uses it.
const NAME_UNLOCK_SPAN: u64 = 2_100_000;

const STEPS: [u128; 28] = [
  0,
  26,
  702,
  18278,
  475254,
  12356630,
  321272406,
  8353082582,
  217180147158,
  5646683826134,
  146813779479510,
  3817158266467286,
  99246114928149462,
  2580398988131886038,
  67090373691429037014,
  1744349715977154962390,
  45353092615406029022166,
  1179180408000556754576342,
  30658690608014475618984918,
  797125955808376366093607894,
  20725274851017785518433805270,
  538857146126462423479278937046,
  14010285799288023010461252363222,
  364267430781488598271992561443798,
  9470953200318703555071806597538774,
  246244783208286292431866971536008150,
  6402364363415443603228541259936211926,
  166461473448801533683942072758341510102,
];

/// The smallest name value an etching may use at `height`.
pub(crate) fn minimum_at_height(first: u64, height: u64) -> u128 {
  let offset = height.saturating_add(1);
  let interval = NAME_UNLOCK_SPAN / 12;
  let end = first + NAME_UNLOCK_SPAN;
  if offset < first {
    return STEPS[12];
  }
  if offset >= end {
    return 0;
  }
  let progress = offset - first;
  let length = 12 - (progress / interval) as usize;
  let end = STEPS[length - 1];
  let start = STEPS[length];
  let remainder = u128::from(progress % interval);
  start - ((start - end) * remainder / u128::from(interval))
}

fn claim(id: u128) -> Option<u128> {
  (id & CLAIM_BIT != 0).then_some(id ^ CLAIM_BIT)
}

/// `BLOCK:TX`, the protocol's way of writing an id.
pub fn format_id(id: u128) -> String {
  format!("{}:{}", id >> 16, id & 0xFFFF)
}

// ---- dunestones ----

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Edict {
  pub id: u128,
  pub amount: u128,
  pub output: u128,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
pub(crate) struct Terms {
  pub cap: Option<u128>,
  pub height: (Option<u64>, Option<u64>),
  pub limit: Option<u128>,
  pub offset: (Option<u64>, Option<u64>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) struct Etching {
  pub divisibility: Option<u8>,
  pub dune: Option<u128>,
  pub spacers: Option<u32>,
  pub symbol: Option<char>,
  pub terms: Option<Terms>,
  pub premine: Option<u128>,
  pub turbo: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct Stone {
  pub edicts: Vec<Edict>,
  pub etching: Option<Etching>,
  pub pointer: Option<u32>,
  pub cenotaph: bool,
}

enum Ins<'a> {
  Op(u8),
  Push(&'a [u8]),
}

/// Script instructions as rust-bitcoin 0.29's `Script::instructions` reads
/// them (non-minimal pushes allowed): `Err` on a push running past the end,
/// after which there is nothing more.
fn instructions(script: &[u8]) -> impl Iterator<Item = Result<Ins<'_>, ()>> {
  let mut data = script;
  let mut done = false;
  std::iter::from_fn(move || {
    if done || data.is_empty() {
      return None;
    }
    let op = data[0];
    let (skip, len) = match op {
      0x00..=0x4b => (1usize, usize::from(op)),
      0x4c => match data.get(1) {
        Some(n) => (2, usize::from(*n)),
        None => {
          done = true;
          return Some(Err(()));
        }
      },
      0x4d => match data.get(1..3) {
        Some(b) => (3, usize::from(u16::from_le_bytes([b[0], b[1]]))),
        None => {
          done = true;
          return Some(Err(()));
        }
      },
      0x4e => match data.get(1..5) {
        Some(b) => (5, u32::from_le_bytes([b[0], b[1], b[2], b[3]]) as usize),
        None => {
          done = true;
          return Some(Err(()));
        }
      },
      _ => {
        data = &data[1..];
        return Some(Ok(Ins::Op(op)));
      }
    };
    if data.len() < skip + len {
      done = true;
      return Some(Err(()));
    }
    let push = &data[skip..skip + len];
    data = &data[skip + len..];
    Some(Ok(Ins::Push(push)))
  })
}

fn script_bytes(vout: &RpcVout) -> Vec<u8> {
  vout.script_pub_key.hex.as_deref().and_then(|h| hex::decode(h).ok()).unwrap_or_default()
}

fn is_op_return(vout: &RpcVout) -> bool {
  match vout.script_pub_key.hex.as_deref() {
    Some(h) => h.starts_with("6a"),
    None => super::is_op_return(vout),
  }
}

/// The first `OP_RETURN "D"` output's pushes, joined. `Err` (no dunestone at
/// all) if a script read on the way is malformed.
fn payload(tx: &RpcTx) -> Result<Option<Vec<u8>>, ()> {
  for vout in &tx.vout {
    let script = script_bytes(vout);
    let mut ins = instructions(&script);
    match ins.next().transpose()? {
      Some(Ins::Op(0x6a)) => {}
      _ => continue,
    }
    match ins.next().transpose()? {
      Some(Ins::Push(b"D")) => {}
      _ => continue,
    }
    let mut payload = Vec::new();
    for i in ins {
      if let Ins::Push(p) = i? {
        payload.extend_from_slice(p);
      }
    }
    return Ok(Some(payload));
  }
  Ok(None)
}

/// The reference's varint: a truncated one still yields what it read.
fn decode_varint(buffer: &[u8]) -> (u128, usize) {
  let mut n = 0u128;
  let mut i = 0;
  loop {
    let Some(&b) = buffer.get(i) else {
      return (n, i);
    };
    let b = u128::from(b);
    n = n.saturating_mul(128);
    if b < 128 {
      return (n.saturating_add(b), i + 1);
    }
    n = n.saturating_add(b - 127);
    i += 1;
  }
}

fn integers(payload: &[u8]) -> Vec<u128> {
  let mut out = Vec::new();
  let mut i = 0;
  while i < payload.len() {
    let (n, len) = decode_varint(&payload[i..]);
    out.push(n);
    i += len;
  }
  out
}

fn edict_from(tx: &RpcTx, id: u128, amount: u128, output: u128) -> Option<Edict> {
  let height = u64::try_from(id >> 16).ok()?;
  let index = id & 0xFFFF;
  if height == 0 && index > 0 {
    return None;
  }
  if output > tx.vout.len() as u128 {
    return None;
  }
  Some(Edict { id, amount, output })
}

impl Stone {
  pub(crate) fn from_tx(tx: &RpcTx) -> Option<Self> {
    let payload = payload(tx).ok()??;
    let ints = integers(&payload);

    let mut edicts = Vec::new();
    let mut fields: HashMap<u128, u128> = HashMap::new();
    let mut cenotaph = false;
    let mut i = 0;
    while i < ints.len() {
      let tag = ints[i];
      if tag == 0 {
        let mut id = 0u128;
        for chunk in ints[i + 1..].chunks_exact(3) {
          id = id.saturating_add(chunk[0]);
          match edict_from(tx, id, chunk[1], chunk[2]) {
            Some(e) => edicts.push(e),
            None => cenotaph = true,
          }
        }
        break;
      }
      let Some(&value) = ints.get(i + 1) else {
        break;
      };
      fields.entry(tag).or_insert(value);
      i += 2;
    }

    let mut take = |tag: u128| fields.remove(&tag);
    // Deadline (10) is not read, so it stays and makes a cenotaph.
    let pointer = take(12).and_then(|v| u32::try_from(v).ok());
    let divisibility = take(1).and_then(|v| u8::try_from(v).ok()).filter(|d| *d <= MAX_DIVISIBILITY);
    let limit = take(6).map(|v| v.min(MAX_LIMIT));
    let dune = take(4);
    let cap = take(20);
    let premine = take(22);
    if premine.unwrap_or_default() > 0 {
      edicts.push(Edict { id: 0, amount: premine.unwrap_or_default(), output: 1 });
    }
    let spacers = take(3).and_then(|v| u32::try_from(v).ok()).filter(|s| *s <= MAX_SPACERS);
    let symbol = take(5).and_then(|v| u32::try_from(v).ok()).and_then(char::from_u32);
    let height = (take(14).and_then(|v| u64::try_from(v).ok()), take(18).and_then(|v| u64::try_from(v).ok()));
    let offset = (take(16).and_then(|v| u64::try_from(v).ok()), take(8).and_then(|v| u64::try_from(v).ok()));
    let mut flags = take(2).unwrap_or_default();
    let mut flag = |bit: u32| {
      let set = flags & (1 << bit) != 0;
      flags &= !(1 << bit);
      set
    };
    let etch = flag(0);
    let terms = flag(1);
    let turbo = flag(2);

    let overflow = cap
      .unwrap_or_default()
      .checked_mul(limit.unwrap_or_default())
      .and_then(|m| premine.unwrap_or_default().checked_add(m))
      .is_none();

    let etching = etch.then_some(Etching {
      divisibility,
      dune,
      spacers,
      symbol,
      terms: terms.then_some(Terms { cap, height, limit, offset }),
      premine,
      turbo,
    });

    Some(Stone {
      cenotaph: cenotaph || overflow || flags != 0 || fields.keys().any(|tag| tag % 2 == 0),
      pointer,
      edicts,
      etching,
    })
  }
}

// ---- state ----

/// A dune as the reference stores it. `supply` is the reference's own field:
/// what was minted (plus what an id-0 edict of amount 0 claimed); the total
/// ever made is `premine + supply`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Entry {
  pub id: u128,
  pub dune: u128,
  pub spacers: u32,
  pub symbol: Option<char>,
  pub divisibility: u8,
  pub block: u64,
  pub etching: String,
  pub number: u64,
  pub premine: u128,
  pub supply: u128,
  pub burned: u128,
  pub mints: u128,
  pub(crate) terms: Option<Terms>,
  pub turbo: bool,
  pub timestamp: u64,
}

impl Entry {
  /// The explorer's id for it, as the API and pages use.
  pub fn public_id(&self) -> String {
    format!("DOGECOIN:{}", dune_name(self.dune))
  }

  pub fn spaced_name(&self) -> String {
    apply_spacers(&dune_name(self.dune), self.spacers)
  }

  fn start(&self) -> Option<u64> {
    let t = self.terms?;
    let relative = t.offset.0.map(|o| self.block.saturating_add(o));
    relative.zip(t.height.0).map(|(r, a)| r.max(a)).or(relative).or(t.height.0)
  }

  fn end(&self) -> Option<u64> {
    let t = self.terms?;
    let relative = t.offset.1.map(|o| self.block.saturating_add(o));
    relative.zip(t.height.1).map(|(r, a)| r.min(a)).or(relative).or(t.height.1)
  }

  /// What one mint may make at `height`, if minting is open.
  pub(crate) fn mintable(&self, height: u64) -> Option<u128> {
    let terms = self.terms?;
    if self.start().is_some_and(|s| height < s) || self.end().is_some_and(|e| height >= e) {
      return None;
    }
    if self.mints >= terms.cap.unwrap_or(u128::MAX) {
      return None;
    }
    Some(terms.limit.unwrap_or_default())
  }

  fn lite(&self) -> (DuneMeta, DuneEntryLite) {
    let id = self.public_id();
    (
      DuneMeta {
        id: id.clone(),
        name: self.spaced_name(),
        symbol: self.symbol.map(|c| c.to_string()).unwrap_or_default(),
        divisibility: self.divisibility,
      },
      DuneEntryLite {
        id,
        etched_height: self.block,
        premine: self.premine,
        supply: self.premine.wrapping_add(self.supply),
        burned: self.burned,
        mints: self.mints,
        terms: self.terms.map(|t| DuneTerms {
          cap: t.cap,
          limit: t.limit,
          height_start: t.height.0,
          height_end: t.height.1,
          offset_start: t.offset.0,
          offset_end: t.offset.1,
        }),
      },
    )
  }
}

/// Where the rules read and write dune state.
pub(crate) trait State {
  /// Takes (removes) the balances an output held: (dune id, amount).
  fn take(&mut self, outpoint: &str) -> Result<Vec<(u128, u128)>>;
  /// Gives an output balances; `address` is who owns the output ("" for none).
  fn put(&mut self, outpoint: &str, address: &str, balances: Vec<(u128, u128)>) -> Result<()>;
  fn entry(&mut self, id: u128) -> Result<Option<Entry>>;
  fn save(&mut self, entry: Entry) -> Result<()>;
  fn name_taken(&mut self, dune: u128) -> Result<bool>;
  /// Returns a counter's value and adds one to it.
  fn bump(&mut self, counter: &'static str) -> Result<u64>;
}

/// Something a transaction did to a dune, for the activity record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Event {
  pub id: u128,
  pub kind: &'static str,
  pub amount: u128,
}

struct Allocation {
  balance: u128,
  id: u128,
  dune: u128,
  divisibility: u8,
  spacers: u32,
  symbol: Option<char>,
  terms: Option<Terms>,
  turbo: bool,
}

/// One transaction, as the reference's `index_dunes`.
pub(crate) fn index_tx(
  st: &mut impl State,
  tx: &RpcTx,
  tx_index: usize,
  height: u64,
  time: u64,
  first_height: u64,
  events: &mut Vec<Event>,
) -> Result<()> {
  let stone = Stone::from_tx(tx);

  let mut unallocated: HashMap<u128, u128> = HashMap::new();
  for vin in &tx.vin {
    let (Some(txid), Some(vout)) = (&vin.txid, vin.vout) else {
      continue;
    };
    for (id, amount) in st.take(&outpoint_key(txid, vout))? {
      let slot = unallocated.entry(id).or_default();
      *slot = slot.wrapping_add(amount);
    }
  }
  if stone.is_none() && unallocated.is_empty() {
    return Ok(());
  }

  let cenotaph = stone.as_ref().is_some_and(|s| s.cenotaph);
  let default_output = stone.as_ref().and_then(|s| s.pointer).and_then(|p| usize::try_from(p).ok());
  let mut spent: Vec<(u128, u128)> = unallocated.iter().filter(|(_, a)| **a > 0).map(|(i, a)| (*i, *a)).collect();
  spent.sort();
  let mut allocated: Vec<HashMap<u128, u128>> = vec![HashMap::new(); tx.vout.len()];

  if let Some(stone) = stone {
    let mut allocation = match stone.etching {
      Some(etching) => {
        let minimum = minimum_at_height(first_height, height);
        let void = match etching.dune {
          Some(d) => d < minimum || d >= RESERVED || st.name_taken(d)?,
          None => false,
        };
        if void {
          None
        } else {
          let dune = match etching.dune {
            Some(d) => d,
            None => RESERVED + u128::from(st.bump("reserved")?),
          };
          u16::try_from(tx_index).ok().map(|index| Allocation {
            balance: u128::MAX,
            id: u128::from(height) << 16 | u128::from(index),
            dune,
            divisibility: etching.divisibility.unwrap_or_default(),
            spacers: etching.spacers.unwrap_or_default(),
            symbol: etching.symbol,
            terms: etching.terms.map(|t| Terms { limit: t.limit.map(|l| l.min(MAX_LIMIT)), ..t }),
            turbo: etching.turbo,
          })
        }
      }
      None => None,
    };

    let mut premine: u128 = 0;
    if !cenotaph {
      let mut claims: Vec<u128> = stone.edicts.iter().filter_map(|e| claim(e.id)).collect();
      claims.sort();
      claims.dedup();
      let mut mintable: HashMap<u128, u128> = HashMap::new();
      for id in claims {
        if u64::try_from(id >> 16).is_err() {
          continue;
        }
        if let Some(entry) = st.entry(id)?
          && let Some(limit) = entry.mintable(height)
        {
          mintable.insert(id, limit);
        }
      }
      let limits = mintable.clone();

      for Edict { id, amount, output } in stone.edicts.iter().copied() {
        let Ok(output) = usize::try_from(output) else {
          continue;
        };
        if output >= tx.vout.len() {
          continue;
        }
        let (balance, id) = if id == 0 {
          match allocation.as_mut() {
            Some(a) => {
              premine = premine.wrapping_add(amount);
              (&mut a.balance, a.id)
            }
            None => continue,
          }
        } else if let Some(target) = claim(id) {
          match mintable.get_mut(&target) {
            Some(b) => (b, target),
            None => continue,
          }
        } else {
          match unallocated.get_mut(&id) {
            Some(b) => (b, id),
            None => continue,
          }
        };
        let amount = if amount == 0 { *balance } else { amount.min(*balance) };
        if amount > 0 {
          *balance -= amount;
          let slot = allocated[output].entry(id).or_default();
          *slot = slot.wrapping_add(amount);
        }
      }

      let mut minted: Vec<(u128, u128)> = mintable.iter().map(|(id, left)| (*id, limits[id] - left)).filter(|(_, m)| *m > 0).collect();
      minted.sort();
      for (id, amount) in minted {
        let mut entry = st.entry(id)?.ok_or_else(|| anyhow!("minted dune {} has no entry", format_id(id)))?;
        entry.supply = entry.supply.wrapping_add(amount);
        entry.mints = entry.mints.wrapping_add(1);
        st.save(entry)?;
        events.push(Event { id, kind: "mint", amount });
      }
    }

    if let Some(a) = allocation {
      let number = st.bump("dunes")?;
      st.save(Entry {
        id: a.id,
        dune: a.dune,
        spacers: a.spacers,
        symbol: a.symbol,
        divisibility: a.divisibility,
        block: height,
        etching: tx.txid.clone(),
        number,
        premine,
        supply: u128::MAX.wrapping_sub(a.balance).wrapping_sub(premine),
        burned: 0,
        mints: 0,
        terms: a.terms.filter(|_| !cenotaph),
        turbo: a.turbo,
        timestamp: time,
      })?;
      events.push(Event { id: a.id, kind: "etch", amount: premine });
    }
  }

  let mut burned: HashMap<u128, u128> = HashMap::new();
  if cenotaph {
    for (id, amount) in unallocated {
      let slot = burned.entry(id).or_default();
      *slot = slot.wrapping_add(amount);
    }
  } else {
    let to = default_output
      .filter(|v| *v < allocated.len())
      .or_else(|| tx.vout.iter().position(|v| !is_op_return(v)));
    for (id, amount) in unallocated {
      if amount == 0 {
        continue;
      }
      let slot = match to {
        Some(v) => allocated[v].entry(id).or_default(),
        None => burned.entry(id).or_default(),
      };
      *slot = slot.wrapping_add(amount);
    }
  }

  for (vout, balances) in allocated.into_iter().enumerate() {
    if balances.is_empty() {
      continue;
    }
    if is_op_return(&tx.vout[vout]) {
      for (id, amount) in balances {
        let slot = burned.entry(id).or_default();
        *slot = slot.wrapping_add(amount);
      }
      continue;
    }
    let mut balances: Vec<(u128, u128)> = balances.into_iter().collect();
    balances.sort();
    let address = tx.vout[vout].script_pub_key.addresses.as_ref().and_then(|a| a.first()).map(String::as_str).unwrap_or("");
    st.put(&outpoint_key(&tx.txid, tx.vout[vout].n), address, balances)?;
  }

  let mut burned: Vec<(u128, u128)> = burned.into_iter().filter(|(_, a)| *a > 0).collect();
  burned.sort();
  for (id, amount) in &burned {
    if let Some(mut entry) = st.entry(*id)? {
      entry.burned = entry.burned.wrapping_add(*amount);
      st.save(entry)?;
    }
  }

  // What moved in from the inputs, and what burned.
  if !cenotaph {
    for (id, amount) in spent {
      events.push(Event { id, kind: "transfer", amount });
    }
  }
  for (id, amount) in burned {
    events.push(Event { id, kind: "burn", amount });
  }
  Ok(())
}

// ---- the live store ----

/// Live state: the explorer's trees (`dune_meta_by_id`, `dune_entry_by_id`,
/// `dune_balances_by_outpoint`, keyed by public id) kept for the API, and
/// `dune_index` for the rules: `N` + id (16 bytes BE) -> entry, `I|` + public
/// id -> id, `S|` + counter -> u64. Every write goes through the undo log.
pub(crate) struct TreeState<'a> {
  pub meta: &'a store::Tree,
  pub entries: &'a store::Tree,
  pub balances: &'a store::Tree,
  pub index: &'a store::Tree,
  pub undo: &'a mut UndoRecorder,
}

fn entry_key(id: u128) -> Vec<u8> {
  let mut k = vec![b'N'];
  k.extend_from_slice(&id.to_be_bytes());
  k
}

fn name_key(public_id: &str) -> Vec<u8> {
  format!("I|{public_id}").into_bytes()
}

fn counter_key(name: &str) -> Vec<u8> {
  format!("S|{name}").into_bytes()
}

// ---- holders ----
//
// So that nothing has to walk every output holding a dune (18.7M of them),
// `dune_index` also keeps, per holding output and per (dune, owner):
//   `O|` + outpoint            -> owner address ("" for none)
//   `H|` + public id `|` owner -> balance (u128 BE) + outputs (u64 BE)
//   `A|` + owner `|` public id -> the same, by owner
//   `C|` + public id           -> distinct owners (u64)
// Live indexing keeps them as it goes; `build_holders` makes them from the
// balances (once, and after a replay).

fn outpoint_owner_key(outpoint: &str) -> Vec<u8> {
  format!("O|{outpoint}").into_bytes()
}

fn holder_key(public_id: &str, address: &str) -> Vec<u8> {
  format!("H|{public_id}|{address}").into_bytes()
}

fn holding_key(address: &str, public_id: &str) -> Vec<u8> {
  format!("A|{address}|{public_id}").into_bytes()
}

fn holder_count_key(public_id: &str) -> Vec<u8> {
  format!("C|{public_id}").into_bytes()
}

fn holder_value(balance: u128, outputs: u64) -> Vec<u8> {
  let mut v = balance.to_be_bytes().to_vec();
  v.extend_from_slice(&outputs.to_be_bytes());
  v
}

fn decode_holder(v: &[u8]) -> Result<(u128, u64)> {
  if v.len() != 24 {
    bail!("dune holder value of {} bytes", v.len());
  }
  Ok((
    u128::from_be_bytes(v[..16].try_into().expect("16 bytes")),
    u64::from_be_bytes(v[16..].try_into().expect("8 bytes")),
  ))
}

impl TreeState<'_> {
  /// Adds (or takes away) one output's `amount` of a dune to its owner.
  fn holder_change(&mut self, public_id: &str, address: &str, amount: u128, add: bool) -> Result<()> {
    let hk = holder_key(public_id, address);
    let ak = holding_key(address, public_id);
    let ck = holder_count_key(public_id);
    let (balance, outputs) = match self.index.get(&hk)? {
      Some(v) => decode_holder(v.as_ref())?,
      None => (0, 0),
    };
    let was_holder = outputs > 0;
    let (balance, outputs) = if add {
      (balance.wrapping_add(amount), outputs + 1)
    } else {
      (balance.wrapping_sub(amount), outputs.saturating_sub(1))
    };
    let count = self.index.get(&ck)?.map(|v| decode_u64(v.as_ref())).transpose()?.unwrap_or(0);
    if outputs == 0 {
      self.undo.remove("dune_index", self.index, &hk)?;
      self.undo.remove("dune_index", self.index, &ak)?;
      if was_holder {
        self.undo.insert("dune_index", self.index, &ck, encode_u64(count.saturating_sub(1)).to_vec())?;
      }
    } else {
      let value = holder_value(balance, outputs);
      self.undo.insert("dune_index", self.index, &hk, value.clone())?;
      self.undo.insert("dune_index", self.index, &ak, value)?;
      if !was_holder {
        self.undo.insert("dune_index", self.index, &ck, encode_u64(count + 1).to_vec())?;
      }
    }
    Ok(())
  }
}

impl State for TreeState<'_> {
  fn take(&mut self, outpoint: &str) -> Result<Vec<(u128, u128)>> {
    let mut out = Vec::new();
    let mut taken = Vec::new();
    for item in self.balances.scan_prefix(format!("{outpoint}|").as_bytes())? {
      let (k, v) = item?;
      let key = String::from_utf8(k.to_vec()).context("dune balance key utf8")?;
      let public_id = key.split_once('|').map(|(_, id)| id).unwrap_or_default().to_string();
      let raw = self.index.get(name_key(&public_id))?.ok_or_else(|| anyhow!("no id for dune {public_id}"))?;
      let id = u128::from_be_bytes(raw.as_ref().try_into().context("dune id bytes")?);
      let amount = decode_u128(v.as_ref())?;
      out.push((id, amount));
      taken.push((public_id, amount));
      self.undo.remove_known("dune_balances_by_outpoint", self.balances, k.as_ref(), Some(v.to_vec()))?;
    }
    if !taken.is_empty() {
      let ok = outpoint_owner_key(outpoint);
      let owner = self.index.get(&ok)?;
      let address = owner.as_ref().map(|v| String::from_utf8_lossy(v.as_ref()).to_string()).unwrap_or_default();
      self.undo.remove_known("dune_index", self.index, &ok, owner.map(|v| v.to_vec()))?;
      for (public_id, amount) in taken {
        self.holder_change(&public_id, &address, amount, false)?;
      }
    }
    Ok(out)
  }

  fn put(&mut self, outpoint: &str, address: &str, balances: Vec<(u128, u128)>) -> Result<()> {
    if balances.is_empty() {
      return Ok(());
    }
    // A new output: nothing can be stored under its key yet.
    self.undo.insert_new("dune_index", self.index, &outpoint_owner_key(outpoint), address.as_bytes().to_vec())?;
    for (id, amount) in balances {
      let public_id = self.entry(id)?.ok_or_else(|| anyhow!("no entry for dune {}", format_id(id)))?.public_id();
      let key = format!("{outpoint}|{public_id}");
      self.undo.insert("dune_balances_by_outpoint", self.balances, key.as_bytes(), encode_u128(amount).to_vec())?;
      self.holder_change(&public_id, address, amount, true)?;
    }
    Ok(())
  }

  fn entry(&mut self, id: u128) -> Result<Option<Entry>> {
    match self.index.get(entry_key(id))? {
      Some(raw) => Ok(Some(bincode::deserialize(raw.as_ref())?)),
      None => Ok(None),
    }
  }

  fn save(&mut self, entry: Entry) -> Result<()> {
    let (meta, lite) = entry.lite();
    self.undo.insert("dune_index", self.index, &entry_key(entry.id), bincode::serialize(&entry)?)?;
    self.undo.insert("dune_index", self.index, &name_key(&meta.id), entry.id.to_be_bytes().to_vec())?;
    self.undo.insert("dune_meta_by_id", self.meta, meta.id.as_bytes(), bincode::serialize(&meta)?)?;
    self.undo.insert("dune_entry_by_id", self.entries, lite.id.as_bytes(), bincode::serialize(&lite)?)?;
    Ok(())
  }

  fn name_taken(&mut self, dune: u128) -> Result<bool> {
    Ok(self.index.get(name_key(&format!("DOGECOIN:{}", dune_name(dune))))?.is_some())
  }

  fn bump(&mut self, counter: &'static str) -> Result<u64> {
    let key = counter_key(counter);
    let n = self.index.get(&key)?.map(|v| decode_u64(v.as_ref())).transpose()?.unwrap_or(0);
    self.undo.insert("dune_index", self.index, &key, encode_u64(n + 1).to_vec())?;
    Ok(n)
  }
}

// ---- in memory (the replay) ----

#[derive(Default)]
pub(crate) struct MemState {
  pub balances: HashMap<String, Vec<(u128, u128)>>,
  pub entries: HashMap<u128, Entry>,
  pub names: HashSet<u128>,
  pub counters: HashMap<&'static str, u64>,
}

impl State for MemState {
  fn take(&mut self, outpoint: &str) -> Result<Vec<(u128, u128)>> {
    Ok(self.balances.remove(outpoint).unwrap_or_default())
  }

  /// Owners are not kept in memory (18.7M outputs); `build_holders` reads
  /// them from the UTXO set after the state is written.
  fn put(&mut self, outpoint: &str, _address: &str, balances: Vec<(u128, u128)>) -> Result<()> {
    if !balances.is_empty() {
      self.balances.insert(outpoint.to_string(), balances);
    }
    Ok(())
  }

  fn entry(&mut self, id: u128) -> Result<Option<Entry>> {
    Ok(self.entries.get(&id).cloned())
  }

  fn save(&mut self, entry: Entry) -> Result<()> {
    self.names.insert(entry.dune);
    self.entries.insert(entry.id, entry);
    Ok(())
  }

  fn name_taken(&mut self, dune: u128) -> Result<bool> {
    Ok(self.names.contains(&dune))
  }

  fn bump(&mut self, counter: &'static str) -> Result<u64> {
    let n = self.counters.entry(counter).or_default();
    *n += 1;
    Ok(*n - 1)
  }
}

impl MemState {
  /// Writes this state over the live Dune trees (cleared first).
  pub(crate) fn write_live(&self, db: &store::Db) -> Result<()> {
    let meta_tree = db.open_tree("meta")?;
    let trees = [
      db.open_tree("dune_meta_by_id")?,
      db.open_tree("dune_entry_by_id")?,
      db.open_tree("dune_balances_by_outpoint")?,
      db.open_tree("dune_index")?,
    ];
    for t in &trees {
      t.delete_range(Vec::new(), vec![0xff; 256])?;
    }
    let [meta, lite_tree, balances, index] = &trees;
    let mut batch = store::Batch::default();
    let mut pending = 0usize;
    let flush = |batch: &mut store::Batch, pending: &mut usize, force: bool| -> Result<()> {
      if force || *pending >= 50_000 {
        std::mem::take(batch).commit(&meta_tree)?;
        *pending = 0;
      }
      Ok(())
    };
    for entry in self.entries.values() {
      let (m, lite) = entry.lite();
      batch.insert(index, entry_key(entry.id), bincode::serialize(entry)?);
      batch.insert(index, name_key(&m.id), entry.id.to_be_bytes().to_vec());
      batch.insert(meta, m.id.clone().into_bytes(), bincode::serialize(&m)?);
      batch.insert(lite_tree, lite.id.clone().into_bytes(), bincode::serialize(&lite)?);
      pending += 4;
      flush(&mut batch, &mut pending, false)?;
    }
    for (name, n) in &self.counters {
      batch.insert(index, counter_key(name), encode_u64(*n).to_vec());
    }
    for (outpoint, list) in &self.balances {
      for (id, amount) in list {
        let entry = self.entries.get(id).ok_or_else(|| anyhow!("balance of unknown dune {}", format_id(*id)))?;
        batch.insert(balances, format!("{outpoint}|{}", entry.public_id()).into_bytes(), encode_u128(*amount).to_vec());
        pending += 1;
      }
      flush(&mut batch, &mut pending, false)?;
    }
    flush(&mut batch, &mut pending, true)
  }
}

/// The protocol id of a dune by its explorer id, once the new index has it.
pub fn dune_number(config: &Config, public_id: &str) -> Result<Option<u128>> {
  let db = open_db(&config.db_path())?;
  Ok(match db.open_tree("dune_index")?.get(name_key(public_id))? {
    Some(raw) => Some(u128::from_be_bytes(raw.as_ref().try_into().context("dune id bytes")?)),
    None => None,
  })
}

/// One dune's full entry, by explorer id.
pub fn dune_entry(config: &Config, public_id: &str) -> Result<Option<Entry>> {
  let Some(id) = dune_number(config, public_id)? else {
    return Ok(None);
  };
  let db = open_db(&config.db_path())?;
  match db.open_tree("dune_index")?.get(entry_key(id))? {
    Some(raw) => Ok(Some(bincode::deserialize(raw.as_ref())?)),
    None => Ok(None),
  }
}

/// Every dune's full entry, by explorer id.
pub fn dune_entries(config: &Config) -> Result<HashMap<String, Entry>> {
  let db = open_db(&config.db_path())?;
  let mut out = HashMap::new();
  db.open_tree("dune_index")?.for_each_prefix(b"N", |_, v| {
    let e: Entry = bincode::deserialize(v)?;
    out.insert(e.public_id(), e);
    Ok(true)
  })?;
  Ok(out)
}

/// Set once the holder rows are built (see "holders" above).
pub(crate) const HOLDERS_KEY: &[u8] = b"dune_holders_v1";

pub fn dune_holders_built(config: &Config) -> Result<bool> {
  Ok(open_db(&config.db_path())?.open_tree("meta")?.get(HOLDERS_KEY)?.is_some())
}

/// Makes the holder rows from the balances, with owners from the UTXO set,
/// replacing any there. Run it with live indexing held off (INDEX_WRITE).
/// Returns (outputs, owner rows).
pub(crate) fn build_holders(db: &store::Db) -> Result<(u64, u64)> {
  let index = db.open_tree("dune_index")?;
  let balances = db.open_tree("dune_balances_by_outpoint")?;
  let utxos = db.open_tree("utxo_by_outpoint")?;
  let meta = db.open_tree("meta")?;
  for p in [b'O', b'H', b'A', b'C'] {
    index.delete_range(vec![p, b'|'], vec![p, b'}'])?;
  }
  let mut holders: HashMap<String, HashMap<String, (u128, u64)>> = HashMap::new();
  let mut batch = store::Batch::default();
  let mut pending = 0usize;
  let mut outputs = 0u64;
  let mut last = String::new();
  let mut owner = String::new();
  balances.for_each_prefix(b"", |k, v| {
    let key = std::str::from_utf8(k).context("dune balance key utf8")?;
    let Some((outpoint, public_id)) = key.split_once('|') else {
      return Ok(true);
    };
    if outpoint != last {
      last = outpoint.to_string();
      owner = match utxos.get(outpoint.as_bytes())? {
        Some(raw) => bincode::deserialize::<UtxoRecord>(raw.as_ref()).map(|u| u.address).unwrap_or_default(),
        None => String::new(),
      };
      batch.insert(&index, outpoint_owner_key(outpoint), owner.as_bytes().to_vec());
      pending += 1;
      outputs += 1;
      if pending >= 50_000 {
        std::mem::take(&mut batch).commit(&meta)?;
        pending = 0;
      }
      if outputs % 2_000_000 == 0 {
        info!("dune holders: {outputs} outputs read");
      }
    }
    let amount = decode_u128(v)?;
    if !holders.contains_key(public_id) {
      holders.insert(public_id.to_string(), HashMap::new());
    }
    let by_owner = holders.get_mut(public_id).expect("just inserted");
    let slot = match by_owner.get_mut(owner.as_str()) {
      Some(s) => s,
      None => by_owner.entry(owner.clone()).or_insert((0, 0)),
    };
    slot.0 = slot.0.wrapping_add(amount);
    slot.1 += 1;
    Ok(true)
  })?;
  let mut rows = 0u64;
  for (public_id, by_owner) in &holders {
    batch.insert(&index, holder_count_key(public_id), encode_u64(by_owner.len() as u64).to_vec());
    for (address, (balance, n)) in by_owner {
      let value = holder_value(*balance, *n);
      batch.insert(&index, holder_key(public_id, address), value.clone());
      batch.insert(&index, holding_key(address, public_id), value);
      pending += 2;
      rows += 1;
      if pending >= 50_000 {
        std::mem::take(&mut batch).commit(&meta)?;
        pending = 0;
      }
    }
  }
  batch.insert(&meta, HOLDERS_KEY.to_vec(), encode_u64(1).to_vec());
  batch.commit(&meta)?;
  Ok((outputs, rows))
}

/// Everyone holding a dune: (address, balance, outputs), unordered.
pub fn dune_holders(config: &Config, public_id: &str) -> Result<Vec<(String, u128, u64)>> {
  let db = open_db(&config.db_path())?;
  let prefix = holder_key(public_id, "");
  let mut out = Vec::new();
  db.open_tree("dune_index")?.for_each_prefix(&prefix, |k, v| {
    let address = String::from_utf8_lossy(&k[prefix.len()..]).to_string();
    let (balance, outputs) = decode_holder(v)?;
    out.push((address, balance, outputs));
    Ok(true)
  })?;
  Ok(out)
}

/// Owner count of every dune, by explorer id.
pub fn dune_owner_counts(config: &Config) -> Result<HashMap<String, u32>> {
  let db = open_db(&config.db_path())?;
  let mut out = HashMap::new();
  db.open_tree("dune_index")?.for_each_prefix(b"C|", |k, v| {
    out.insert(String::from_utf8_lossy(&k[2..]).to_string(), decode_u64(v)? as u32);
    Ok(true)
  })?;
  Ok(out)
}

/// What an address holds: (explorer id, balance).
pub fn dune_holdings(config: &Config, address: &str) -> Result<Vec<(String, u128)>> {
  let db = open_db(&config.db_path())?;
  let prefix = holding_key(address, "");
  let mut out = Vec::new();
  db.open_tree("dune_index")?.for_each_prefix(&prefix, |k, v| {
    out.push((String::from_utf8_lossy(&k[prefix.len()..]).to_string(), decode_holder(v)?.0));
    Ok(true)
  })?;
  Ok(out)
}

/// Which of `outpoints` hold any dune.
pub(crate) fn holding_outpoints(db: &store::Db, outpoints: &[&str]) -> Result<Vec<bool>> {
  let keys: Vec<Vec<u8>> = outpoints.iter().map(|o| outpoint_owner_key(o)).collect();
  Ok(db.open_tree("dune_index")?.multi_get(&keys)?.into_iter().map(|v| v.is_some()).collect())
}

#[cfg(test)]
mod tests {
  use super::*;

  fn varint(mut n: u128, v: &mut Vec<u8>) {
    let mut out = [0u8; 19];
    let mut i = 18;
    loop {
      let mut byte = n.to_le_bytes()[0] & 0x7f;
      if i < 18 {
        byte |= 0x80;
      }
      out[i] = byte;
      if n < 0x80 {
        break;
      }
      n = n / 128 - 1;
      i -= 1;
    }
    v.extend_from_slice(&out[i..]);
  }

  /// OP_RETURN "D" <payload>, as hex.
  fn stone_script(ints: &[u128]) -> String {
    let mut payload = Vec::new();
    for n in ints {
      varint(*n, &mut payload);
    }
    let mut s = vec![0x6a, 0x01, b'D', payload.len() as u8];
    s.extend(payload);
    hex::encode(s)
  }

  fn out(n: u32, hex: &str) -> RpcVout {
    RpcVout { value: 0.01, n, script_pub_key: RpcScriptPubKey { asm: None, hex: Some(hex.into()), addresses: None } }
  }

  const P2PKH: &str = "76a914000000000000000000000000000000000000000088ac";

  fn tx(txid: &str, spends: &[(&str, u32)], outs: Vec<RpcVout>) -> RpcTx {
    RpcTx {
      txid: txid.into(),
      vin: spends.iter().map(|(t, v)| RpcVin { txid: Some((*t).into()), vout: Some(*v), script_sig: None }).collect(),
      vout: outs,
    }
  }

  fn name(s: &str) -> u128 {
    let mut x = 0u128;
    for (i, c) in s.chars().enumerate() {
      if i > 0 {
        x += 1;
      }
      x = x * 26 + (c as u128 - 'A' as u128);
    }
    x
  }

  const FIRST: u64 = 5_084_000;
  const H: u64 = 6_400_000;

  /// Etches WOWSUCHDUNEX at (H, 1): premine 1000 to output 1, mintable 10
  /// times for 50 each.
  fn etch(st: &mut MemState) -> u128 {
    let t = tx("etch", &[("fund", 0)], vec![
      out(0, &stone_script(&[2, 0b11, 4, name("WOWSUCHDUNEX"), 22, 1000, 20, 10, 6, 50, 1, 2])),
      out(1, P2PKH),
    ]);
    let mut ev = Vec::new();
    index_tx(st, &t, 1, H, 0, FIRST, &mut ev).unwrap();
    assert_eq!(ev, [Event { id: (u128::from(H) << 16) | 1, kind: "etch", amount: 1000 }]);
    (u128::from(H) << 16) | 1
  }

  /// Checks an etch and a mint built elsewhere (the DPAYMARKET test runner) the way the
  /// indexer will read them. Run with DUNE_CHECK_ETCH / DUNE_CHECK_MINT set to
  /// `decoderawtransaction` JSON files: `cargo test -p dogeord-indexer external_dune -- --ignored --nocapture`.
  #[test]
  #[ignore]
  fn external_dune_etch_and_mint() {
    let read = |var: &str| -> RpcTx { serde_json::from_str(&std::fs::read_to_string(std::env::var(var).unwrap()).unwrap()).unwrap() };
    let etch_tx = read("DUNE_CHECK_ETCH");
    let mint_tx = read("DUNE_CHECK_MINT");
    let (h, index) = (6_455_000u64, 1usize);
    let stone = Stone::from_tx(&etch_tx).expect("no dunestone in the etch");
    println!("etch stone: {stone:?}");
    assert!(!stone.cenotaph, "etch is a cenotaph");
    let mut st = MemState::default();
    let mut ev = Vec::new();
    index_tx(&mut st, &etch_tx, index, h, 0, FIRST, &mut ev).unwrap();
    let id = (u128::from(h) << 16) | index as u128;
    assert_eq!(ev, [Event { id, kind: "etch", amount: 100_000 }], "etch events");
    let e = &st.entries[&id];
    println!("entry: {} spaced {} symbol {:?} div {} premine {} terms {:?}", e.public_id(), e.spaced_name(), e.symbol, e.divisibility, e.premine, e.terms);
    assert!(e.spaced_name().starts_with("DPAY•MARKET•TEST•"), "spaced name {}", e.spaced_name());
    assert_eq!((e.divisibility, e.premine, e.symbol), (0, 100_000, Some('Ð')));
    let t = e.terms.expect("no mint terms");
    assert_eq!((t.cap, t.limit), (Some(100), Some(1000)));
    assert_eq!(st.balances[&format!("{}:1", etch_tx.txid)], [(id, 100_000)], "premine on output 1");
    assert!(!st.balances.contains_key(&format!("{}:2", etch_tx.txid)), "change carries no dunes");

    let mint_stone = Stone::from_tx(&mint_tx).expect("no dunestone in the mint");
    println!("mint stone: {mint_stone:?}");
    assert!(!mint_stone.cenotaph, "mint is a cenotaph");
    let mut ev = Vec::new();
    index_tx(&mut st, &mint_tx, 3, h + 1, 0, FIRST, &mut ev).unwrap();
    assert_eq!(ev, [Event { id, kind: "mint", amount: 1000 }], "mint events");
    assert_eq!(st.balances[&format!("{}:1", mint_tx.txid)], [(id, 1000)], "minted to output 1");
    assert_eq!(st.entries[&id].mints, 1);
    println!("OK: etch and mint read as intended");
  }

  #[test]
  fn minimum_name_length_follows_the_reference() {
    assert_eq!(dune_name(minimum_at_height(FIRST, 0)), "AAAAAAAAAAAAA");
    assert_eq!(dune_name(minimum_at_height(FIRST, FIRST - 2)), "AAAAAAAAAAAAA");
    // One interval in, twelve letters are allowed.
    assert_eq!(dune_name(minimum_at_height(FIRST, FIRST + 175_000 - 1)), "AAAAAAAAAAAA");
    assert_eq!(minimum_at_height(FIRST, FIRST + 2_100_000), 0);
  }

  #[test]
  fn premine_goes_to_output_one_and_mints_use_the_id() {
    let mut st = MemState::default();
    let id = etch(&mut st);
    assert_eq!(st.balances["etch:1"], [(id, 1000)]);
    let e = &st.entries[&id];
    assert_eq!((e.premine, e.supply, e.mints), (1000, 0, 0));
    assert_eq!(e.public_id(), "DOGECOIN:WOWSUCHDUNEX");

    // Mint by id with the claim bit: edict (id | CLAIM_BIT, 0, output 0).
    let mint = tx("mint", &[("fund2", 0)], vec![out(0, P2PKH), out(1, &stone_script(&[0, id | CLAIM_BIT, 0, 0]))]);
    let mut ev = Vec::new();
    index_tx(&mut st, &mint, 2, H + 1, 0, FIRST, &mut ev).unwrap();
    assert_eq!(ev, [Event { id, kind: "mint", amount: 50 }]);
    assert_eq!(st.balances["mint:0"], [(id, 50)]);
    let e = &st.entries[&id];
    assert_eq!((e.supply, e.mints, e.premine.wrapping_add(e.supply)), (50, 1, 1050));
  }

  #[test]
  fn transfers_follow_edicts_by_id_and_the_rest_goes_to_the_first_output() {
    let mut st = MemState::default();
    let id = etch(&mut st);
    // Send 300 to output 1; the other 700 stay with output 0.
    let send = tx("send", &[("etch", 1)], vec![out(0, P2PKH), out(1, P2PKH), out(2, &stone_script(&[0, id, 300, 1]))]);
    let mut ev = Vec::new();
    index_tx(&mut st, &send, 3, H + 2, 0, FIRST, &mut ev).unwrap();
    assert_eq!(st.balances["send:1"], [(id, 300)]);
    assert_eq!(st.balances["send:0"], [(id, 700)]);
    assert!(!st.balances.contains_key("etch:1"));
    assert_eq!(ev, [Event { id, kind: "transfer", amount: 1000 }]);
  }

  #[test]
  fn a_taken_name_does_not_etch_again_or_premine() {
    let mut st = MemState::default();
    etch(&mut st);
    let again = tx("again", &[("fund3", 0)], vec![
      out(0, &stone_script(&[2, 1, 4, name("WOWSUCHDUNEX"), 22, 300_000_000])),
      out(1, P2PKH),
    ]);
    let mut ev = Vec::new();
    index_tx(&mut st, &again, 4, H + 3, 0, FIRST, &mut ev).unwrap();
    assert!(ev.is_empty());
    assert_eq!(st.entries.len(), 1);
    assert!(!st.balances.contains_key("again:1"), "no second premine");
  }

  #[test]
  fn short_names_are_void_and_unnamed_etchings_get_reserved_names() {
    let mut st = MemState::default();
    let short = tx("short", &[], vec![out(0, &stone_script(&[2, 1, 4, name("DOGE"), 22, 5])), out(1, P2PKH)]);
    index_tx(&mut st, &short, 1, FIRST + 10, 0, FIRST, &mut Vec::new()).unwrap();
    assert!(st.entries.is_empty(), "four letters are under the minimum at the start");

    let unnamed = tx("unnamed", &[], vec![out(0, &stone_script(&[2, 1, 22, 5])), out(1, P2PKH)]);
    index_tx(&mut st, &unnamed, 2, FIRST + 10, 0, FIRST, &mut Vec::new()).unwrap();
    let e = st.entries.values().next().unwrap();
    assert_eq!(e.dune, RESERVED);
  }

  #[test]
  fn a_cenotaph_burns_its_inputs() {
    let mut st = MemState::default();
    let id = etch(&mut st);
    // Tag 10 (deadline) is an even field the reference does not read.
    let bad = tx("bad", &[("etch", 1)], vec![out(0, P2PKH), out(1, &stone_script(&[10, 5, 0, id, 1, 0]))]);
    let mut ev = Vec::new();
    index_tx(&mut st, &bad, 5, H + 4, 0, FIRST, &mut ev).unwrap();
    assert!(st.balances.is_empty());
    assert_eq!(st.entries[&id].burned, 1000);
    assert_eq!(ev, [Event { id, kind: "burn", amount: 1000 }]);
  }

  #[test]
  fn edicts_to_every_output_are_skipped_as_in_the_reference() {
    let mut st = MemState::default();
    let id = etch(&mut st);
    // output == number of outputs: the reference skips it, so all 1000 stay
    // together on the first output.
    let split = tx("split", &[("etch", 1)], vec![out(0, P2PKH), out(1, P2PKH), out(2, &stone_script(&[0, id, 10, 3]))]);
    index_tx(&mut st, &split, 6, H + 5, 0, FIRST, &mut Vec::new()).unwrap();
    assert_eq!(st.balances["split:0"], [(id, 1000)]);
    assert!(!st.balances.contains_key("split:1"));
  }

  #[test]
  fn a_plain_spend_moves_balances_to_the_first_output() {
    let mut st = MemState::default();
    let id = etch(&mut st);
    let plain = tx("plain", &[("etch", 1)], vec![out(0, "6a0100"), out(1, P2PKH)]);
    index_tx(&mut st, &plain, 7, H + 6, 0, FIRST, &mut Vec::new()).unwrap();
    assert_eq!(st.balances["plain:1"], [(id, 1000)], "past the OP_RETURN");
  }

  #[test]
  fn tree_and_memory_state_agree() {
    let db = store::Db::temporary().unwrap();
    let (meta, entries, balances, index) = (
      db.open_tree("dune_meta_by_id").unwrap(),
      db.open_tree("dune_entry_by_id").unwrap(),
      db.open_tree("dune_balances_by_outpoint").unwrap(),
      db.open_tree("dune_index").unwrap(),
    );
    let mut undo = UndoRecorder::default();
    let mut live = TreeState { meta: &meta, entries: &entries, balances: &balances, index: &index, undo: &mut undo };
    let mut mem = MemState::default();
    let id = etch(&mut mem);
    let t = tx("etch", &[("fund", 0)], vec![
      out(0, &stone_script(&[2, 0b11, 4, name("WOWSUCHDUNEX"), 22, 1000, 20, 10, 6, 50, 1, 2])),
      out(1, P2PKH),
    ]);
    index_tx(&mut live, &t, 1, H, 0, FIRST, &mut Vec::new()).unwrap();
    let send = tx("send", &[("etch", 1)], vec![out(0, P2PKH), out(1, P2PKH), out(2, &stone_script(&[0, id, 300, 1]))]);
    index_tx(&mut live, &send, 3, H + 2, 0, FIRST, &mut Vec::new()).unwrap();
    index_tx(&mut mem, &send, 3, H + 2, 0, FIRST, &mut Vec::new()).unwrap();

    assert_eq!(live.entry(id).unwrap().as_ref(), mem.entries.get(&id));
    assert_eq!(decode_u128(balances.get(b"send:1|DOGECOIN:WOWSUCHDUNEX").unwrap().unwrap().as_ref()).unwrap(), 300);
    assert!(balances.get(b"etch:1|DOGECOIN:WOWSUCHDUNEX").unwrap().is_none());

    // Written out, the memory state reads back the same.
    let db2 = store::Db::temporary().unwrap();
    mem.write_live(&db2).unwrap();
    let b2 = db2.open_tree("dune_balances_by_outpoint").unwrap();
    assert_eq!(decode_u128(b2.get(b"send:0|DOGECOIN:WOWSUCHDUNEX").unwrap().unwrap().as_ref()).unwrap(), 700);
    let lite: DuneEntryLite = bincode::deserialize(db2.open_tree("dune_entry_by_id").unwrap().get(b"DOGECOIN:WOWSUCHDUNEX").unwrap().unwrap().as_ref()).unwrap();
    assert_eq!((lite.premine, lite.supply, lite.mints), (1000, 1000, 0));
  }

  fn to(n: u32, address: &str) -> RpcVout {
    let mut v = out(n, P2PKH);
    v.script_pub_key.addresses = Some(vec![address.to_string()]);
    v
  }

  fn holder_rows(index: &store::Tree) -> Vec<(String, Vec<u8>)> {
    let mut rows = Vec::new();
    index
      .for_each_prefix(b"", |k, v| {
        if k.len() > 1 && k[1] == b'|' && b"OHAC".contains(&k[0]) {
          rows.push((String::from_utf8_lossy(k).to_string(), v.to_vec()));
        }
        Ok(true)
      })
      .unwrap();
    rows
  }

  #[test]
  fn holders_follow_the_outputs_and_match_a_fresh_build() {
    let db = store::Db::temporary().unwrap();
    let (meta, entries, balances, index) = (
      db.open_tree("dune_meta_by_id").unwrap(),
      db.open_tree("dune_entry_by_id").unwrap(),
      db.open_tree("dune_balances_by_outpoint").unwrap(),
      db.open_tree("dune_index").unwrap(),
    );
    let mut undo = UndoRecorder::default();
    let mut live = TreeState { meta: &meta, entries: &entries, balances: &balances, index: &index, undo: &mut undo };
    let etching = tx("etch", &[("fund", 0)], vec![
      out(0, &stone_script(&[2, 0b11, 4, name("WOWSUCHDUNEX"), 22, 1000, 20, 10, 6, 50, 1, 2])),
      to(1, "DAlice"),
    ]);
    index_tx(&mut live, &etching, 1, H, 0, FIRST, &mut Vec::new()).unwrap();
    let id = (H as u128) << 16 | 1;
    // Alice sends 300 to Bob and keeps 700 in two outputs.
    let send = tx("send", &[("etch", 1)], vec![
      to(0, "DAlice"),
      to(1, "DBob"),
      out(2, &stone_script(&[0, id, 300, 1, 0, 200, 3])),
      to(3, "DAlice"),
    ]);
    index_tx(&mut live, &send, 3, H + 2, 0, FIRST, &mut Vec::new()).unwrap();

    let config_free = |address: &str| -> Option<(u128, u64)> {
      index.get(holder_key("DOGECOIN:WOWSUCHDUNEX", address)).unwrap().map(|v| decode_holder(v.as_ref()).unwrap())
    };
    assert_eq!(config_free("DAlice"), Some((700, 2)));
    assert_eq!(config_free("DBob"), Some((300, 1)));
    assert_eq!(decode_u64(index.get(holder_count_key("DOGECOIN:WOWSUCHDUNEX")).unwrap().unwrap().as_ref()).unwrap(), 2);
    assert!(index.get(outpoint_owner_key("etch:1")).unwrap().is_none());

    // Bob spends his to Alice: Bob is no longer a holder.
    let back = tx("back", &[("send", 1)], vec![to(0, "DAlice")]);
    index_tx(&mut live, &back, 1, H + 3, 0, FIRST, &mut Vec::new()).unwrap();
    assert_eq!(config_free("DAlice"), Some((1000, 3)));
    assert_eq!(config_free("DBob"), None);
    assert!(index.get(holding_key("DBob", "DOGECOIN:WOWSUCHDUNEX")).unwrap().is_none());
    assert_eq!(decode_u64(index.get(holder_count_key("DOGECOIN:WOWSUCHDUNEX")).unwrap().unwrap().as_ref()).unwrap(), 1);

    // Built afresh from the balances and the UTXO set, the rows are the same.
    let live_rows = holder_rows(&index);
    let utxos = db.open_tree("utxo_by_outpoint").unwrap();
    for (op, address) in [("send:0", "DAlice"), ("send:3", "DAlice"), ("back:0", "DAlice")] {
      utxos.insert(op, bincode::serialize(&UtxoRecord { satoshis: 1, address: address.into() }).unwrap()).unwrap();
    }
    db.open_tree("meta").unwrap();
    let (outputs, rows) = build_holders(&db).unwrap();
    assert_eq!((outputs, rows), (3, 1));
    assert_eq!(holder_rows(&index), live_rows);
  }
}
