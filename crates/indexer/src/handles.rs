//! Handles: `@name` minted as a plain-text inscription. The first inscription
//! of a handle (chain order) owns it; whoever holds that inscription holds the
//! handle. Later inscriptions of the same handle are kept as missed claims.
//!
//! A handle inscription is `text/plain` (any parameters) whose whole body,
//! trimmed of whitespace, is `@` followed by 1 to 32 of `a-z`, `0-9` and `_`.
//! Letters are folded to lower case, so `@Doge` and `@doge` are one handle.
//! Anything else in the body (`@doge hello`) is not a handle.
//!
//! Built like the DNS index ([`super::dns`]): its own trees and task, it
//! follows `inscription_seq` in chain order as far as numbering has gone,
//! each step is one atomic batch with its cursor, and steps near the tip keep
//! an undo record so a reorg ([`undo_from`]) can take them back.

use super::*;
use crate::insc_index as ii;
use crate::store::{Batch, Tree};
use std::sync::Mutex;

/// Confirmations a block needs before its handles are read.
pub const HANDLE_CONFIRMATIONS: u64 = 1;
/// How many blocks back a reorg can be undone.
const UNDO_BLOCKS: u64 = 100;
/// Longest handle, in characters (after the `@`).
pub const HANDLE_MAX_LEN: usize = 32;

static HANDLE_WRITE: Mutex<()> = Mutex::new(());
const STATE_KEY: &[u8] = b"handles_index_v1";
const REORG_GEN_KEY: &[u8] = b"handles_reorg_gen";
const TREES: [&str; 6] = ["handle_name", "handle_by_inscription", "handle_index", "handle_claims", "handle_stats", "handle_undo"];

fn reorg_gen(meta: &Tree) -> Result<u64> {
  Ok(ii::meta_u64(meta, REORG_GEN_KEY)?.unwrap_or(0))
}

/// `@name` → `name`, folded; None when it is not a valid handle.
pub fn normalize_handle(input: &str) -> Option<String> {
  let s = input.trim();
  let h = s.strip_prefix('@')?;
  if h.is_empty() || h.len() > HANDLE_MAX_LEN || !h.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_') {
    return None;
  }
  Some(h.to_ascii_lowercase())
}

/// The handle a `text/plain` inscription mints, if it is one.
pub fn parse_handle(content_type: &str, body: &[u8]) -> Option<String> {
  let ct = content_type.split(';').next().unwrap_or("").trim().to_ascii_lowercase();
  if ct != "text/plain" || body.len() > HANDLE_MAX_LEN + 64 {
    return None;
  }
  normalize_handle(std::str::from_utf8(body).ok()?)
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HandleEntry {
  pub handle: String,
  pub inscription_id: String,
  pub number: u64,
  pub height: u64,
  pub tx_index: u32,
  pub time: u64,
  /// Later inscriptions of the same handle.
  pub lost: u64,
  /// Position in minting order (0 = first handle ever).
  pub index: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HandleClaim {
  pub inscription_id: String,
  pub number: u64,
  pub height: u64,
  pub time: u64,
}

/// What an inscription is to the handles index: "handle" (it owns the handle)
/// or "claim" (an earlier inscription minted it first).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HandleRole {
  pub role: String,
  pub handle: String,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct HandleState {
  cursor: Vec<u8>,
  handles: u64,
  claims: u64,
  scanned: u64,
  cursor_height: u64,
}

#[derive(Serialize, Deserialize)]
struct HandleUndo {
  last_height: u64,
  ops: Vec<(String, Vec<u8>, Option<Vec<u8>>)>,
}

struct Trees {
  meta: Tree,
  seq: Tree,
  genesis: Tree,
  content: Tree,
  name: Tree,
  by_inscription: Tree,
  index: Tree,
  claims: Tree,
  undo: Tree,
}

impl Trees {
  fn open(db: &store::Db) -> Result<Self> {
    Ok(Trees {
      meta: db.open_tree("meta")?,
      seq: db.open_tree("inscription_seq")?,
      genesis: db.open_tree("inscription_genesis")?,
      content: db.open_tree("inscription_content")?,
      name: db.open_tree("handle_name")?,
      by_inscription: db.open_tree("handle_by_inscription")?,
      index: db.open_tree("handle_index")?,
      claims: db.open_tree("handle_claims")?,
      undo: db.open_tree("handle_undo")?,
    })
  }
}

fn state(meta: &Tree) -> Result<HandleState> {
  Ok(match meta.get(STATE_KEY)? {
    Some(raw) => bincode::deserialize(raw.as_ref()).context("decode handles state")?,
    None => HandleState::default(),
  })
}

fn claim_key(handle: &str, n: u64) -> Vec<u8> {
  let mut k = handle.as_bytes().to_vec();
  k.push(0);
  k.extend_from_slice(&n.to_be_bytes());
  k
}

fn get_entry(tree: &Tree, handle: &str) -> Result<Option<HandleEntry>> {
  tree.get(handle.as_bytes())?.map(|v| bincode::deserialize(v.as_ref()).context("decode handle")).transpose()
}

struct Candidate {
  key: Vec<u8>,
  pos: (u64, u32),
  number: u64,
  time: u64,
  id: String,
  handle: String,
}

/// The next stretch of chain order up to what is numbered and settled: the
/// handle inscriptions in it, the last key read and how many rows were read.
fn scan(t: &Trees, st: &HandleState, max: usize) -> Result<(Vec<Candidate>, Option<Vec<u8>>, u64)> {
  let mut numbered_through = ii::numbering_state(&t.meta)?.cursor;
  let indexed = ii::meta_u64(&t.meta, b"indexed_height")?.unwrap_or(0);
  let Some(settled) = (indexed + 1).checked_sub(HANDLE_CONFIRMATIONS) else {
    return Ok((Vec::new(), None, 0));
  };
  let settled_key = ii::seq_key(settled, u32::MAX).to_vec();
  if numbered_through > settled_key {
    numbered_through = settled_key;
  }
  if numbered_through.is_empty() || st.cursor.as_slice() >= numbered_through.as_slice() {
    return Ok((Vec::new(), None, 0));
  }
  let mut start = st.cursor.clone();
  if !start.is_empty() {
    start.push(0);
  }
  let mut rows: Vec<(Vec<u8>, ii::SeqEntry)> = Vec::new();
  let mut last: Option<Vec<u8>> = None;
  let mut scanned = 0u64;
  t.seq.for_each_from(&start, |k, v| {
    if k > numbered_through.as_slice() || scanned as usize >= max {
      return Ok(false);
    }
    scanned += 1;
    last = Some(k.to_vec());
    let e: ii::SeqEntry = bincode::deserialize(v).context("decode seq entry")?;
    // `@name` in text/plain always classifies as plain text.
    if e.kinds & ii::K_TEXT != 0 {
      rows.push((k.to_vec(), e));
    }
    Ok(true)
  })?;
  let found: Vec<Result<Option<Candidate>>> = rows
    .into_par_iter()
    .map(|(key, e)| -> Result<Option<Candidate>> {
      // The numbered sighting only (a Doginal in several transactions can be
      // in chain order twice; numbering keeps the first).
      let Some(g) = t.genesis.get(e.id.as_bytes())? else { return Ok(None) };
      let g: ii::Genesis = bincode::deserialize(g.as_ref()).context("decode genesis")?;
      let height = ii::seq_height(&key);
      if g.height != height {
        return Ok(None);
      }
      let Some(raw) = t.content.get(e.id.as_bytes())? else { return Ok(None) };
      let c = decode_inscription_content(raw.as_ref())?;
      let Some(handle) = parse_handle(&c.content_type, &c.body) else { return Ok(None) };
      let tx_index = u32::from_be_bytes(key[8..12].try_into().unwrap());
      Ok(Some(Candidate { pos: (height, tx_index), number: g.number, time: e.time, id: e.id, handle, key }))
    })
    .collect();
  let mut out = Vec::new();
  for f in found {
    if let Some(c) = f? {
      out.push(c);
    }
  }
  out.sort_by(|a, b| a.key.cmp(&b.key));
  Ok((out, last, scanned))
}

const REORGED: &str = "a reorg changed the chain under this stretch";

/// Applies one stretch in chain order as one batch.
fn apply(t: &Trees, mut st: HandleState, cands: Vec<Candidate>, last: Vec<u8>, scanned: u64, era: u64) -> Result<HandleState> {
  let mut batch = Batch::default();
  let mut seen: HashMap<String, HandleEntry> = HashMap::new();
  for c in cands {
    let existing = match seen.get(&c.handle) {
      Some(e) => Some(e.clone()),
      None => get_entry(&t.name, &c.handle)?,
    };
    let role = match existing {
      Some(mut e) => {
        e.lost += 1;
        st.claims += 1;
        batch.insert(&t.claims, claim_key(&c.handle, c.number), bincode::serialize(&HandleClaim {
          inscription_id: c.id.clone(),
          number: c.number,
          height: c.pos.0,
          time: c.time,
        })?);
        batch.insert(&t.name, c.handle.as_bytes().to_vec(), bincode::serialize(&e)?);
        seen.insert(c.handle.clone(), e);
        "claim"
      }
      None => {
        let e = HandleEntry {
          handle: c.handle.clone(),
          inscription_id: c.id.clone(),
          number: c.number,
          height: c.pos.0,
          tx_index: c.pos.1,
          time: c.time,
          lost: 0,
          index: st.handles,
        };
        batch.insert(&t.name, c.handle.as_bytes().to_vec(), bincode::serialize(&e)?);
        batch.insert(&t.index, st.handles.to_be_bytes().to_vec(), c.handle.as_bytes().to_vec());
        seen.insert(c.handle.clone(), e);
        st.handles += 1;
        "handle"
      }
    };
    batch.insert(&t.by_inscription, c.id.as_bytes().to_vec(), bincode::serialize(&HandleRole { role: role.to_string(), handle: c.handle.clone() })?);
  }
  st.cursor_height = ii::seq_height(&last);
  st.cursor = last.clone();
  st.scanned += scanned;
  batch.insert(&t.meta, STATE_KEY.to_vec(), bincode::serialize(&st)?);

  let indexed = ii::meta_u64(&t.meta, b"indexed_height")?.unwrap_or(0);
  let _w = HANDLE_WRITE.lock().unwrap_or_else(|e| e.into_inner());
  if reorg_gen(&t.meta)? != era {
    bail!("{REORGED}");
  }
  if st.cursor_height + UNDO_BLOCKS >= indexed {
    let ops = batch.previous(&t.meta)?;
    batch.insert(&t.undo, last, bincode::serialize(&HandleUndo { last_height: st.cursor_height, ops })?);
  }
  let floor = ii::seq_key(indexed.saturating_sub(UNDO_BLOCKS), 0);
  t.undo.for_each_from(b"", |k, _| {
    if k >= floor.as_slice() {
      return Ok(false);
    }
    batch.remove(&t.undo, k.to_vec());
    Ok(true)
  })?;
  batch.commit(&t.meta)?;
  Ok(st)
}

/// Clears the handles index so it is read again from the first numbered
/// inscription (after numbering itself starts over).
pub(crate) fn reset(db: &store::Db) -> Result<()> {
  let _w = HANDLE_WRITE.lock().unwrap_or_else(|e| e.into_inner());
  for tree in TREES {
    db.open_tree(tree)?.delete_range(Vec::new(), vec![0xff; 64])?;
  }
  let meta = db.open_tree("meta")?;
  meta.remove(STATE_KEY)?;
  meta.insert(REORG_GEN_KEY, encode_u64(reorg_gen(&meta)? + 1).to_vec())?;
  Ok(())
}

/// Undoes every step that read blocks at `height` and above, newest first.
/// Called by a reorg's rollback.
pub(crate) fn undo_from(db: &store::Db, height: u64) -> Result<()> {
  let _w = HANDLE_WRITE.lock().unwrap_or_else(|e| e.into_inner());
  let meta = db.open_tree("meta")?;
  meta.insert(REORG_GEN_KEY, encode_u64(reorg_gen(&meta)? + 1).to_vec())?;
  let undo = db.open_tree("handle_undo")?;
  let st = state(&meta)?;
  if st.cursor.is_empty() || st.cursor_height < height {
    return Ok(());
  }
  let mut steps: Vec<(Vec<u8>, HandleUndo)> = Vec::new();
  undo.for_each_from(&ii::seq_key(height, 0), |k, v| {
    steps.push((k.to_vec(), bincode::deserialize(v).context("decode handles undo")?));
    Ok(true)
  })?;
  let undone = steps.len();
  for (key, step) in steps.into_iter().rev() {
    let mut batch = Batch::default();
    for (tree, k, previous) in step.ops {
      batch.put_raw(tree, k, previous);
    }
    batch.remove(&undo, key);
    batch.commit(&meta)?;
  }
  let st = state(&meta)?;
  if !st.cursor.is_empty() && st.cursor_height >= height {
    warn!("handles index: the reorg at block {height} is deeper than its undo history; handles from block {height} on may be wrong");
  } else {
    warn!("handles index: reorg at block {height}: undid {undone} steps, reading again from block {}", st.cursor_height);
  }
  Ok(())
}

/// The handles indexer: catches up over every numbered inscription, then
/// follows numbering as it goes.
pub async fn run_handles_index(config: Config) -> Result<()> {
  let db = ii::db_of(&config)?;
  let t = Arc::new(Trees::open(&db)?);
  let mut st = state(&t.meta)?;
  info!("handles index: starting at block {}, {} handles so far", st.cursor_height, st.handles);
  let (mut last_log, mut caught_up, mut failures) = (Instant::now(), false, 0u32);
  let mut seen_era = reorg_gen(&t.meta)?;
  loop {
    let era = reorg_gen(&t.meta)?;
    if era != seen_era {
      seen_era = era;
      st = state(&t.meta)?;
    }
    let (t2, st2) = (t.clone(), st.clone());
    let (cands, last, scanned) = tokio::task::spawn_blocking(move || scan(&t2, &st2, 200_000)).await.context("handles scan")??;
    let Some(last) = last else {
      if !caught_up {
        caught_up = true;
        info!("handles index: caught up at block {}, {} handles, {} missed claims", st.cursor_height, st.handles, st.claims);
      }
      sleep(Duration::from_secs(2)).await;
      continue;
    };
    let (t2, st2) = (t.clone(), st.clone());
    match tokio::task::spawn_blocking(move || apply(&t2, st2, cands, last, scanned, era)).await.context("handles apply")? {
      Ok(next) => {
        st = next;
        failures = 0;
      }
      Err(_) if reorg_gen(&t.meta).unwrap_or(era) != era => continue,
      Err(e) => {
        failures += 1;
        warn!("handles index: stretch after block {} failed (try {failures}): {e:#}", st.cursor_height);
        sleep(Duration::from_secs(20)).await;
        continue;
      }
    }
    if last_log.elapsed() > Duration::from_secs(60) {
      last_log = Instant::now();
      info!("handles index: at block {}, {} inscriptions read, {} handles, {} missed claims", st.cursor_height, st.scanned, st.handles, st.claims);
    }
  }
}

// ----------------------------------------------------------------- readers --

#[derive(Debug, Clone, Serialize)]
pub struct HandlesStatus {
  pub caught_up: bool,
  pub height: u64,
  pub scanned: u64,
  pub handles: u64,
  pub claims: u64,
}

pub fn handles_status(config: &Config) -> Result<HandlesStatus> {
  let db = ii::db_of(config)?;
  let meta = db.open_tree("meta")?;
  let st = state(&meta)?;
  let numbered = ii::numbering_state(&meta)?.cursor;
  let backfilled = ii::inscription_seq_backfill_done(config)?;
  let indexed = ii::meta_u64(&meta, b"indexed_height")?.unwrap_or(0);
  let settled = ii::seq_key((indexed + 1).saturating_sub(HANDLE_CONFIRMATIONS), u32::MAX).to_vec();
  let readable = if numbered > settled { settled } else { numbered.clone() };
  let mut start = st.cursor.clone();
  if !start.is_empty() {
    start.push(0);
  }
  let mut unread = false;
  db.open_tree("inscription_seq")?.for_each_from(&start, |k, _| {
    unread = k <= readable.as_slice();
    Ok(false)
  })?;
  let caught_up = backfilled && !numbered.is_empty() && !unread && st.cursor_height + HANDLE_CONFIRMATIONS + 3 >= indexed;
  Ok(HandlesStatus { caught_up, height: st.cursor_height, scanned: st.scanned, handles: st.handles, claims: st.claims })
}

#[derive(Debug, Clone, Serialize)]
pub struct HandleListed {
  pub handle: String,
  pub inscription_id: String,
  pub number: u64,
  pub height: u64,
  pub time: u64,
  pub owner: String,
  pub claims: u64,
}

#[derive(Debug, Clone, Serialize)]
pub struct HandlePage {
  pub total: u64,
  pub items: Vec<HandleListed>,
}

fn listed(t_name: &Tree, by_id: &Tree, handles: Vec<Vec<u8>>) -> Result<Vec<HandleListed>> {
  let mut out = Vec::new();
  let mut ids = Vec::new();
  for raw in t_name.multi_get(&handles)?.into_iter().flatten() {
    let e: HandleEntry = bincode::deserialize(raw.as_ref()).context("decode handle")?;
    ids.push(e.inscription_id.clone());
    out.push(e);
  }
  let recs = by_id.multi_get(&ids)?;
  Ok(out
    .into_iter()
    .zip(recs)
    .map(|(e, r)| HandleListed {
      owner: r.and_then(|r| decode_inscription_record(r.as_ref()).ok()).map(|r| r.address).unwrap_or_default(),
      handle: e.handle,
      inscription_id: e.inscription_id,
      number: e.number,
      height: e.height,
      time: e.time,
      claims: e.lost,
    })
    .collect())
}

/// Handles in minting order (newest first unless `oldest_first`); `page` from 1.
pub fn handles_list(config: &Config, page: u64, limit: u64, oldest_first: bool) -> Result<HandlePage> {
  let db = ii::db_of(config)?;
  let total = state(&db.open_tree("meta")?)?.handles;
  let skip = page.saturating_sub(1).saturating_mul(limit);
  if skip >= total {
    return Ok(HandlePage { total, items: Vec::new() });
  }
  let take = limit.min(total - skip);
  let indexes: Vec<u64> = if oldest_first { (skip..skip + take).collect() } else { (0..take).map(|i| total - 1 - skip - i).collect() };
  let keys: Vec<Vec<u8>> = indexes.iter().map(|i| i.to_be_bytes().to_vec()).collect();
  let handles: Vec<Vec<u8>> = db.open_tree("handle_index")?.multi_get(&keys)?.into_iter().flatten().map(|v| v.to_vec()).collect();
  Ok(HandlePage { total, items: listed(&db.open_tree("handle_name")?, &db.open_tree("inscriptions_by_id")?, handles)? })
}

/// Several handles at once (folded names), those that exist.
pub fn handles_get_many(config: &Config, handles: &[String]) -> Result<Vec<HandleListed>> {
  let db = ii::db_of(config)?;
  listed(&db.open_tree("handle_name")?, &db.open_tree("inscriptions_by_id")?, handles.iter().map(|h| h.as_bytes().to_vec()).collect())
}

/// Later inscriptions of a handle, oldest first.
pub fn handle_claims(config: &Config, handle: &str, limit: usize) -> Result<Vec<HandleClaim>> {
  let mut out = Vec::new();
  let mut start = handle.as_bytes().to_vec();
  start.push(0);
  ii::db_of(config)?.open_tree("handle_claims")?.for_each_prefix(&start, |_, v| {
    if out.len() >= limit {
      return Ok(false);
    }
    out.push(bincode::deserialize(v).context("decode handle claim")?);
    Ok(true)
  })?;
  Ok(out)
}

pub fn handle_role(config: &Config, inscription_id: &str) -> Result<Option<HandleRole>> {
  ii::db_of(config)?
    .open_tree("handle_by_inscription")?
    .get(inscription_id.as_bytes())?
    .map(|v| bincode::deserialize(v.as_ref()).context("decode handle role"))
    .transpose()
}

/// Handles an address holds now, oldest first.
pub fn handles_of(config: &Config, address: &str) -> Result<Vec<HandleListed>> {
  let db = ii::db_of(config)?;
  let mut ids: Vec<String> = Vec::new();
  let prefix = format!("{address}|");
  db.open_tree("inscriptions_by_address")?.for_each_prefix(prefix.as_bytes(), |k, _| {
    ids.push(String::from_utf8_lossy(&k[prefix.len()..]).into_owned());
    Ok(true)
  })?;
  let roles = db.open_tree("handle_by_inscription")?;
  let mut handles = Vec::new();
  for chunk in ids.chunks(10_000) {
    for raw in roles.multi_get(chunk)?.into_iter().flatten() {
      let r: HandleRole = bincode::deserialize(raw.as_ref()).context("decode handle role")?;
      if r.role == "handle" {
        handles.push(r.handle.into_bytes());
      }
    }
  }
  let mut out = listed(&db.open_tree("handle_name")?, &db.open_tree("inscriptions_by_id")?, handles)?;
  out.retain(|h| h.owner == address);
  out.sort_by_key(|h| h.number);
  Ok(out)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn what_counts_as_a_handle() {
    assert_eq!(parse_handle("text/plain; charset=utf-8", b"@xxx"), Some("xxx".into()));
    assert_eq!(parse_handle("text/plain", b"  @Doge_42\n"), Some("doge_42".into()));
    assert_eq!(parse_handle("text/plain;charset=utf8", b"@a"), Some("a".into()));
    assert_eq!(parse_handle("text/plain", b"@doge hello"), None);
    assert_eq!(parse_handle("text/plain", b"doge"), None);
    assert_eq!(parse_handle("text/plain", b"@"), None);
    assert_eq!(parse_handle("text/plain", b"@doge.dog"), None);
    assert_eq!(parse_handle("text/plain", b"@d\xc3\xb6ge"), None);
    assert_eq!(parse_handle("text/html", b"@doge"), None);
    assert_eq!(parse_handle("application/json", b"@doge"), None);
    assert_eq!(parse_handle("text/plain", format!("@{}", "a".repeat(32)).as_bytes()), Some("a".repeat(32)));
    assert_eq!(parse_handle("text/plain", format!("@{}", "a".repeat(33)).as_bytes()), None);
  }
}
