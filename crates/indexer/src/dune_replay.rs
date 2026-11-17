//! One-off rebuild of Dune state under the reference's rules (dunes.rs).
//!
//! The first Dune code here looked dunes up by name where the protocol uses
//! their id, so mints never happened and edicts never moved anything; it
//! re-credited the premine of every etching of a name already taken; and it
//! read Dune messages before Dunes began. Balances, holders and mint counts
//! were all wrong as a result.
//!
//! This replays every block from the first Dune block with the new rules, in
//! memory, writing activity to `duner_activity` as it goes. At the live tip,
//! between two live blocks and after checking the blocks it read are still
//! the chain, it writes its state over the live Dune trees and puts its
//! activity in place of the old Dune activity. Until then live indexing
//! leaves Dunes alone, and the old figures stay up, flagged as rebuilding.
//! A restart starts it over.

use super::*;
use serde::Serialize;
use std::sync::Mutex;
use std::sync::atomic::AtomicBool;
use tokio::task::JoinSet;

const STATE_KEY: &[u8] = b"dune_rules_v2";
const WINDOW: u64 = 32;
const ACTIVITY: &str = "duner_activity";
/// Dune events in `token_activity` are under `D|`.
const ACTIVITY_START: &[u8] = b"D|";
const ACTIVITY_END: &[u8] = b"D}";

static REBUILT: AtomicBool = AtomicBool::new(false);
static STATUS: Mutex<DuneReplayStatus> =
  Mutex::new(DuneReplayStatus { running: false, from: 0, height: 0, target: 0, dunes: 0, error: None });

#[derive(Debug, Clone, Serialize)]
pub struct DuneReplayStatus {
  pub running: bool,
  pub from: u64,
  /// Next block to replay.
  pub height: u64,
  /// The live tip it is catching up to.
  pub target: u64,
  pub dunes: u64,
  pub error: Option<String>,
}

pub fn dune_replay_status() -> DuneReplayStatus {
  STATUS.lock().unwrap_or_else(|e| e.into_inner()).clone()
}

fn set_status(f: impl FnOnce(&mut DuneReplayStatus)) {
  f(&mut STATUS.lock().unwrap_or_else(|e| e.into_inner()));
}

pub fn dunes_rebuilt(config: &Config) -> Result<bool> {
  Ok(open_db(&config.db_path())?.open_tree("meta")?.get(STATE_KEY)?.is_some())
}

/// As `dunes_rebuilt`, without a read once it is true.
pub(crate) fn dunes_rebuilt_cached(config: &Config) -> Result<bool> {
  if REBUILT.load(AtomicOrdering::Relaxed) {
    return Ok(true);
  }
  let done = dunes_rebuilt(config)?;
  if done {
    REBUILT.store(true, AtomicOrdering::Relaxed);
  }
  Ok(done)
}

fn indexed_height(meta: &store::Tree) -> Result<u64> {
  Ok(meta.get(b"indexed_height")?.map(|v| decode_u64(v.as_ref())).transpose()?.unwrap_or(0))
}

/// Applies one block to the replay's state; its events go into `batch`.
fn apply_block(
  st: &mut dunes::MemState,
  activity: &store::Tree,
  batch: &mut store::Batch,
  first: u64,
  height: u64,
  block: &RpcBlock,
) -> Result<usize> {
  let time = block.time.unwrap_or(0);
  let mut written = 0;
  for (tx_index, tx) in block.tx.iter().enumerate() {
    let mut events = Vec::new();
    dunes::index_tx(st, tx, tx_index, height, time, first, &mut events)?;
    for e in events {
      let Some(entry) = st.entries.get(&e.id) else { continue };
      let event = ActivityEvent {
        kind: e.kind.to_string(),
        amount: e.amount.to_string(),
        from: String::new(),
        to: String::new(),
        inscription_id: String::new(),
        txid: tx.txid.clone(),
        height,
        time,
      };
      let key = activity_key(&dune_scope(&entry.public_id()), height, tx_index, e.kind);
      batch.insert(activity, key.into_bytes(), bincode::serialize(&event)?);
      written += 1;
    }
  }
  Ok(written)
}

/// The replay; see the module notes. Does nothing once done.
pub async fn run_dune_replay(config: Config) -> Result<()> {
  if dunes_rebuilt(&config)? {
    REBUILT.store(true, AtomicOrdering::Relaxed);
    if !dunes::dune_holders_built(&config)? {
      // Rebuilt before holder rows existed: make them once, from the balances.
      let cfg = config.clone();
      tokio::task::spawn_blocking(move || -> Result<()> {
        let db = open_db(&cfg.db_path())?;
        let _w = repair::INDEX_WRITE.lock().unwrap_or_else(|e| e.into_inner());
        info!("dune holders: building holder rows from the balances, live indexing waits");
        let t = Instant::now();
        let (outputs, rows) = dunes::build_holders(&db)?;
        db.flush()?;
        info!("dune holders: done in {:.0?}; {outputs} outputs, {rows} holder rows", t.elapsed());
        Ok(())
      })
      .await
      .context("join dune holder build")??;
    }
    return Ok(());
  }
  let client = indexer_rpc_client()?;
  let db = open_db(&config.db_path())?;
  let meta = db.open_tree("meta")?;
  let blocks = db.open_tree("blocks")?;
  let activity = db.open_tree(ACTIVITY)?;
  drc20_replay::clear(&activity)?;

  let first = config.first_dune_height;
  let mut st = dunes::MemState::default();
  let mut recent: VecDeque<(u64, String)> = VecDeque::new();
  let mut batch = store::Batch::default();
  let mut pending = 0usize;
  let mut next = first;
  let mut requested = first;
  let mut inflight: JoinSet<(u64, Result<RpcBlock>)> = JoinSet::new();
  let mut ready: std::collections::BTreeMap<u64, RpcBlock> = std::collections::BTreeMap::new();
  let started = Instant::now();
  let mut since_log = 0u64;
  set_status(|s| *s = DuneReplayStatus { running: true, from: first, height: next, target: 0, dunes: 0, error: None });
  info!("dune replay: replaying from block {next} under the reference rules");

  loop {
    let live = indexed_height(&meta)?;
    set_status(|s| {
      s.height = next;
      s.target = live;
      s.dunes = st.entries.len() as u64;
    });
    if next > live {
      std::mem::take(&mut batch).commit(&meta)?;
      pending = 0;
      let unbalanced = check(&st);
      if !unbalanced.is_empty() {
        bail!(
          "{} dunes do not add up (held + burned != premine + minted), first {}; the old Dune data stays",
          unbalanced.len(),
          unbalanced[0]
        );
      }
      let swapped = {
        let _w = repair::INDEX_WRITE.lock().unwrap_or_else(|e| e.into_inner());
        if indexed_height(&meta)? + 1 != next {
          None
        } else {
          let mut same = true;
          for (h, hash) in &recent {
            let stored = blocks.get(encode_u64(*h))?.map(|v| String::from_utf8_lossy(v.as_ref()).to_string());
            if stored.as_deref() != Some(hash.as_str()) {
              same = false;
              break;
            }
          }
          if same {
            st.write_live(&db)?;
            let (outputs, rows) = dunes::build_holders(&db)?;
            info!("dune replay: holder rows for {outputs} outputs, {rows} holders");
            let live_activity = db.open_tree("token_activity")?;
            live_activity.delete_range(ACTIVITY_START, ACTIVITY_END)?;
            let n = drc20_replay::copy(&db, &activity, &live_activity)?;
            drc20_replay::clear(&activity)?;
            meta.insert(STATE_KEY, encode_u64(1).to_vec())?;
            db.flush()?;
            REBUILT.store(true, AtomicOrdering::Relaxed);
            info!("dune replay: {n} activity events in place");
          }
          Some(same)
        }
      };
      match swapped {
        Some(true) => {
          let holders: usize = st.balances.len();
          info!(
            "dune replay: done in {:.0?}; {} dunes, {} outputs holding dunes, now live",
            started.elapsed(),
            st.entries.len(),
            holders
          );
          set_status(|s| s.running = false);
          return Ok(());
        }
        Some(false) => bail!("a reorg changed blocks the Dune replay had read; starting it over"),
        None => {
          tokio::time::sleep(Duration::from_millis(200)).await;
          continue;
        }
      }
    }

    // A sliding window: up to WINDOW fetches always in flight, applied
    // strictly in height order as they arrive. (Waiting for a whole batch
    // left the node idle behind its slowest block: ~23 blocks/s in 2024.)
    while requested <= live && requested < next + WINDOW {
      let (cfg, h) = (config.clone(), requested);
      inflight.spawn(async move { (h, repair::fetch_block(client, &cfg, h).await) });
      requested += 1;
    }
    if let Some(res) = inflight.join_next().await {
      let (h, b) = res.context("join block fetch")?;
      ready.insert(h, b.with_context(|| format!("block {h}"))?);
    }
    let before = next;
    while let Some(block) = ready.remove(&next) {
      pending += apply_block(&mut st, &activity, &mut batch, first, next, &block)?;
      recent.push_back((next, block.hash.clone()));
      if recent.len() > 100 {
        recent.pop_front();
      }
      next += 1;
    }
    if pending >= 50_000 {
      std::mem::take(&mut batch).commit(&meta)?;
      pending = 0;
    }
    since_log += next - before;
    if since_log >= 50_000 {
      since_log = 0;
      info!(
        "dune replay: at block {next} of {live}, {} dunes, {} outputs holding dunes, {:.0?} so far",
        st.entries.len(),
        st.balances.len(),
        started.elapsed()
      );
    }
  }
}

/// Dunes whose units do not add up: everything held plus everything burned
/// must be what the premine and mints made (in the reference's wrapping
/// arithmetic). Units are only ever made by those two, so any other result
/// is a bug, and the replay refuses to put it live.
fn check(st: &dunes::MemState) -> Vec<String> {
  let mut held: HashMap<u128, u128> = HashMap::new();
  for list in st.balances.values() {
    for (id, amount) in list {
      let slot = held.entry(*id).or_default();
      *slot = slot.wrapping_add(*amount);
    }
  }
  let mut bad: Vec<String> = st
    .entries
    .values()
    .filter(|e| held.get(&e.id).copied().unwrap_or(0).wrapping_add(e.burned) != e.premine.wrapping_add(e.supply))
    .map(|e| format!("{} ({})", e.spaced_name(), dunes::format_id(e.id)))
    .collect();
  if held.keys().any(|id| !st.entries.contains_key(id)) {
    bad.push("balances of a dune with no entry".to_string());
  }
  bad.sort();
  bad
}

/// Records why the replay stopped, for the status endpoint.
pub fn dune_replay_failed(e: &anyhow::Error) {
  set_status(|s| {
    s.running = false;
    s.error = Some(format!("{e:#}"));
  });
}

#[cfg(test)]
mod tests {
  use super::*;

  /// Replays the first `DUNE_SAMPLE_BLOCKS` Dune blocks from the node into
  /// memory (no store) and prints what it found. Needs the node's RPC
  /// settings in the environment.
  #[tokio::test]
  #[ignore]
  async fn sample_replay_from_the_node() {
    let config = Config::from_env();
    let n: u64 = std::env::var("DUNE_SAMPLE_BLOCKS").ok().and_then(|v| v.parse().ok()).unwrap_or(20_000);
    let client = indexer_rpc_client().unwrap();
    let db = store::Db::temporary().unwrap();
    let activity = db.open_tree(ACTIVITY).unwrap();
    let mut st = dunes::MemState::default();
    let first = config.first_dune_height;
    let mut h = first;
    let mut events = 0usize;
    while h < first + n {
      let to = (h + WINDOW).min(first + n);
      let mut set = JoinSet::new();
      for x in h..to {
        let cfg = config.clone();
        set.spawn(async move { (x, repair::fetch_block(client, &cfg, x).await.unwrap()) });
      }
      let mut got = Vec::new();
      while let Some(r) = set.join_next().await {
        got.push(r.unwrap());
      }
      got.sort_by_key(|(x, _)| *x);
      for (x, b) in &got {
        let mut batch = store::Batch::default();
        events += apply_block(&mut st, &activity, &mut batch, first, *x, b).unwrap();
      }
      h = to;
    }
    let mut holders: HashMap<u128, usize> = HashMap::new();
    for list in st.balances.values() {
      for (id, _) in list {
        *holders.entry(*id).or_default() += 1;
      }
    }
    let mut top: Vec<&dunes::Entry> = st.entries.values().collect();
    top.sort_by_key(|e| std::cmp::Reverse(e.mints));
    println!("{} blocks from {first}: {} dunes, {} outputs holding, {events} events", n, st.entries.len(), st.balances.len());
    for e in top.iter().take(12) {
      println!(
        "{:>14} {:<28} premine {} minted {} mints {} burned {} outputs {}",
        dunes::format_id(e.id), e.spaced_name(), e.premine, e.supply, e.mints, e.burned, holders.get(&e.id).copied().unwrap_or(0)
      );
    }
    println!("unbalanced: {:?}", check(&st));
  }
}
