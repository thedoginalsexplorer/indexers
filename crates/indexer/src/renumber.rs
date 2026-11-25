//! One-off correction of the inscription archive, then a full renumber in
//! ord-dogecoin's order.
//!
//! The inscription repair re-created every inscription it found missing, but
//! it did not apply ord-dogecoin's rule that a transaction carrying an
//! existing inscription in at offset 0 creates no new one, so it also added
//! inscriptions that ord-dogecoin (and this indexer, live) correctly skip.
//! And blocks indexed before `inscription_seq` existed put a multi-part
//! inscription in chain order at its first piece, where ord-dogecoin numbers
//! it at the piece that completes it.
//!
//! Both are worked out offline by replaying the chain (repair tests
//! `classify_chain_losses` and `export_recovered`). The results go in
//! `renumber/` in the data directory:
//!
//!  - `remove.tsv`: id, height, position in block. Inscriptions to take out
//!    of the index again: wherever they are now, their content, their place
//!    in chain order.
//!  - `multi.tsv`: id, height, position in block, block time. Where each
//!    multi-part inscription completes; its place in chain order moves there.
//!
//! Then every number is cleared, so numbering gives them again from the
//! start in the corrected order, and DNS is cleared, so it is read again in
//! that order. Runs once, at start-up, when the directory is there.

use super::*;
use crate::insc_index::{self as ii, SeqEntry};
use crate::store::Batch;
use std::io::BufRead;

const DONE_KEY: &[u8] = b"inscription_renumber_v1";
/// Later corrections, run once each in this order after the renumber (see
/// `run_fix`): the plan's directory in the data directory, and its done key.
const FIXES: &[(&str, &[u8])] = &[
  // The three found by checking numbers (two made on a sat that already
  // carried an inscription, one taken out by mistake).
  ("renumber2", b"inscription_renumber_fix_v2"),
  // Reveals ord-dogecoin's push reading makes nothing of (see
  // `decode_push_datas`), found by `classify_push_reading`.
  ("renumber3", b"inscription_renumber_fix_v3"),
];

fn lines(path: &std::path::Path) -> Result<Vec<Vec<String>>> {
  let f = std::fs::File::open(path).with_context(|| format!("open {}", path.display()))?;
  let mut out = Vec::new();
  for line in std::io::BufReader::new(f).lines() {
    let line = line?;
    if !line.trim().is_empty() {
      out.push(line.split('\t').map(str::to_string).collect());
    }
  }
  Ok(out)
}

fn num<T: std::str::FromStr>(row: &[String], i: usize) -> Result<T> {
  row
    .get(i)
    .and_then(|v| v.parse().ok())
    .ok_or_else(|| anyhow!("bad column {i} in {row:?}"))
}

/// Takes inscriptions out of the index: their record, where they sit, the
/// address list, content and place in chain order. Returns how many it found.
pub(crate) fn remove_inscriptions(db: &store::Db, rows: &[(String, u64, u32)]) -> Result<u64> {
  let meta = db.open_tree("meta")?;
  let by_id = db.open_tree("inscriptions_by_id")?;
  let by_outpoint = db.open_tree("inscriptions_by_outpoint")?;
  let by_address = db.open_tree("inscriptions_by_address")?;
  let content = db.open_tree("inscription_content")?;
  let seq = db.open_tree("inscription_seq")?;
  let genesis = db.open_tree("inscription_genesis")?;
  let mut removed = 0u64;
  for chunk in rows.chunks(5000) {
    let mut batch = Batch::default();
    // Outpoint lists touched more than once in a chunk are edited in memory.
    let mut lists: HashMap<String, Vec<(u64, String)>> = HashMap::new();
    for (id, height, tx_index) in chunk {
      let Some(raw) = by_id.get(id.as_bytes())? else { continue };
      let rec = decode_inscription_record(raw.as_ref())?;
      if rec.vout != u32::MAX && !rec.txid.is_empty() {
        let okey = outpoint_key(&rec.txid, rec.vout);
        if !lists.contains_key(&okey) {
          let list = match by_outpoint.get(okey.as_bytes())? {
            Some(r) => bincode::deserialize(r.as_ref()).context("decode inscriptions_by_outpoint")?,
            None => Vec::new(),
          };
          lists.insert(okey.clone(), list);
        }
        lists.get_mut(&okey).expect("just inserted").retain(|(_, i)| i != id);
      }
      if !rec.address.is_empty() {
        batch.remove(&by_address, format!("{}|{id}", rec.address).into_bytes());
      }
      batch.remove(&by_id, id.as_bytes().to_vec());
      batch.remove(&content, id.as_bytes().to_vec());
      batch.remove(&genesis, id.as_bytes().to_vec());
      // Its place in chain order: where the plan says, else wherever it is
      // in that block, so no row is left behind to be numbered.
      let key = ii::seq_key(*height, *tx_index);
      if let Some(v) = seq.get(key)?
        && bincode::deserialize::<SeqEntry>(v.as_ref()).is_ok_and(|e| &e.id == id)
      {
        batch.remove(&seq, key.to_vec());
      } else {
        let mut stray = Vec::new();
        seq.for_each_prefix(height.to_be_bytes(), |k, v| {
          if bincode::deserialize::<SeqEntry>(v).is_ok_and(|e| &e.id == id) {
            stray.push(k.to_vec());
          }
          Ok(true)
        })?;
        for k in stray {
          batch.remove(&seq, k);
        }
      }
      removed += 1;
    }
    for (okey, list) in lists {
      if list.is_empty() {
        batch.remove(&by_outpoint, okey.into_bytes());
      } else {
        batch.insert(&by_outpoint, okey.into_bytes(), bincode::serialize(&list)?);
      }
    }
    batch.commit(&meta)?;
  }
  Ok(removed)
}

/// Moves each multi-part inscription's place in chain order to the piece
/// that completes it. Rows elsewhere for the same id (its first piece) go.
/// Returns how many moved.
pub(crate) fn move_to_completion(db: &store::Db, rows: &[(String, u64, u32, u64)]) -> Result<u64> {
  let meta = db.open_tree("meta")?;
  let by_id = db.open_tree("inscriptions_by_id")?;
  let seq = db.open_tree("inscription_seq")?;
  let genesis = db.open_tree("inscription_genesis")?;
  // Where each is now: the height its number was given at, when numbered.
  let mut by_height: HashMap<u64, Vec<usize>> = HashMap::new();
  let mut target_only = Vec::new();
  for (n, (id, ..)) in rows.iter().enumerate() {
    if by_id.get(id.as_bytes())?.is_none() {
      continue;
    }
    match genesis.get(id.as_bytes())? {
      Some(raw) => {
        let g: ii::Genesis = bincode::deserialize(raw.as_ref()).context("decode genesis")?;
        by_height.entry(g.height).or_default().push(n);
      }
      None => target_only.push(n),
    }
  }
  let mut moved = 0u64;
  let mut heights: Vec<u64> = by_height.keys().copied().collect();
  heights.sort_unstable();
  let mut batch = Batch::default();
  let mut pending = 0usize;
  for h in heights {
    let wanted: HashMap<&str, usize> = by_height[&h].iter().map(|n| (rows[*n].0.as_str(), *n)).collect();
    let prefix = h.to_be_bytes();
    let mut found: Vec<(Vec<u8>, SeqEntry)> = Vec::new();
    seq.for_each_prefix(prefix, |k, v| {
      let e: SeqEntry = bincode::deserialize(v).context("decode seq entry")?;
      if wanted.contains_key(e.id.as_str()) {
        found.push((k.to_vec(), e));
      }
      Ok(true)
    })?;
    for (key, entry) in found {
      let n = wanted[entry.id.as_str()];
      let (_, th, ti, time) = &rows[n];
      let target = ii::seq_key(*th, *ti);
      if key.as_slice() == target.as_slice() {
        continue;
      }
      batch.remove(&seq, key);
      if seq.get(target)?.is_none() {
        batch.insert(&seq, target.to_vec(), ii::seq_value(&entry.id, entry.kinds, *time)?);
      }
      moved += 1;
      pending += 1;
    }
    if pending >= 20_000 {
      std::mem::take(&mut batch).commit(&meta)?;
      pending = 0;
    }
  }
  // Not numbered yet (added by the repair): make sure the row is at the end.
  for n in target_only {
    let (id, th, ti, time) = &rows[n];
    let target = ii::seq_key(*th, *ti);
    if seq.get(target)?.is_none() {
      let kinds = match db.open_tree("inscription_content")?.get(id.as_bytes())? {
        Some(r) => {
          let c = decode_inscription_content(r.as_ref())?;
          ii::kinds_of(&c.content_type, Some(&c.body))
        }
        None => 0,
      };
      batch.insert(&seq, target.to_vec(), ii::seq_value(id, kinds, *time)?);
      moved += 1;
    }
  }
  batch.commit(&meta)?;
  Ok(moved)
}

/// Dogemap claims from chain order, as live indexing makes them: the first
/// inscription whose content reads `N.dogemap`, for a block that exists by
/// then, claims N for good; whoever holds it owns the dogemap. Reads rows of
/// chain order from `start` (inclusive) to `end` (exclusive). Content type is
/// not checked by the claim rule, but only text, JSON and untyped
/// inscriptions are read: a claim is a few bytes of text.
fn dogemap_claims(db: &store::Db, start: &[u8], end: &[u8], claimed: &mut HashSet<u64>) -> Result<Vec<DogemapEntry>> {
  let seq = db.open_tree("inscription_seq")?;
  let content = db.open_tree("inscription_content")?;
  let by_id = db.open_tree("inscriptions_by_id")?;
  let maybe = ii::K_DOGEMAP | ii::K_OTHER | ii::K_TEXT | ii::K_JSON;
  let mut candidates: Vec<(u64, SeqEntry)> = Vec::new();
  seq.for_each_from(start, |k, v| {
    if k >= end {
      return Ok(false);
    }
    let e: SeqEntry = bincode::deserialize(v).context("decode seq entry")?;
    if e.kinds & maybe != 0 {
      candidates.push((ii::seq_height(k), e));
    }
    Ok(true)
  })?;
  let mut out = Vec::new();
  for (height, e) in candidates {
    let Some(raw) = content.get(e.id.as_bytes())? else { continue };
    let c = decode_inscription_content(raw.as_ref())?;
    let Some(number) = parse_dogemap_number(&c.body) else { continue };
    if number > height || !claimed.insert(number) {
      continue;
    }
    let owner = match by_id.get(e.id.as_bytes())? {
      Some(r) => decode_inscription_record(r.as_ref())?.address,
      None => String::new(),
    };
    out.push(DogemapEntry {
      number,
      txid: e.id.trim_end_matches("i0").to_string(),
      inscription_id: e.id,
      owner,
      block_height: height,
      block_time: e.time,
    });
  }
  Ok(out)
}

/// Rebuilds every dogemap claim from the corrected chain order. The long read
/// runs while blocks keep being indexed; the swap, and the few blocks
/// indexed meanwhile, happen between two blocks.
pub(crate) fn rebuild_dogemaps(db: &store::Db) -> Result<u64> {
  let meta = db.open_tree("meta")?;
  let by_number = db.open_tree("dogemap_by_number")?;
  let by_inscription = db.open_tree("dogemap_by_inscription")?;
  let by_address = db.open_tree("dogemap_by_address")?;
  let through = ii::meta_u64(&meta, b"indexed_height")?.unwrap_or(0);
  let cut = (through + 1).to_be_bytes().to_vec();
  let mut claimed = HashSet::new();
  let mut claims = dogemap_claims(db, &[], &cut, &mut claimed)?;
  let _w = repair::INDEX_WRITE.lock().unwrap_or_else(|e| e.into_inner());
  claims.extend(dogemap_claims(db, &cut, &[0xff; 13], &mut claimed)?);
  by_number.delete_range(Vec::new(), vec![0xff; 9])?;
  by_inscription.delete_range(Vec::new(), vec![0xff; 1])?;
  by_address.delete_range(Vec::new(), vec![0xff; 1])?;
  for chunk in claims.chunks(20_000) {
    let mut batch = Batch::default();
    for e in chunk {
      let key = encode_u64(e.number).to_vec();
      batch.insert(&by_number, key.clone(), bincode::serialize(e)?);
      batch.insert(&by_inscription, e.inscription_id.as_bytes().to_vec(), key);
      if !e.owner.is_empty() {
        batch.insert(&by_address, dogemap_address_key(&e.owner, e.number).into_bytes(), Vec::new());
      }
    }
    batch.commit(&meta)?;
  }
  Ok(claims.len() as u64)
}

/// Whether the archive correction is complete: the renumber has run, and no
/// later fix plan is waiting.
pub fn renumber_done(config: &Config) -> Result<bool> {
  let meta = open_db(&config.db_path())?.open_tree("meta")?;
  if meta.get(DONE_KEY)?.is_none() {
    return Ok(false);
  }
  for (dir, key) in FIXES {
    if fix_pending(config, &meta, dir, key)? {
      return Ok(false);
    }
  }
  Ok(true)
}

fn fix_pending(config: &Config, meta: &store::Tree, dir: &str, key: &[u8]) -> Result<bool> {
  Ok(std::path::Path::new(&config.data_dir).join(dir).join("remove.tsv").exists() && meta.get(key)?.is_none())
}

/// The one-off correction and renumber; see the module notes. Does nothing
/// once done, or when there is no plan in the data directory. Then the fix
/// plan, if one is waiting.
pub async fn run_renumber(config: Config) -> Result<()> {
  run_first(config.clone()).await?;
  let meta = open_db(&config.db_path())?.open_tree("meta")?;
  if meta.get(DONE_KEY)?.is_some() {
    for (dir, key) in FIXES {
      if fix_pending(&config, &meta, dir, key)? {
        run_fix(config.clone(), dir, key).await?;
      }
    }
  }
  Ok(())
}

/// The second correction, found by checking numbers against doggy.market
/// (an ord-dogecoin index): `renumber2/` in the data directory holds
///
///  - `remove.tsv`: id, height, position. Inscriptions the live indexer made
///    while the inscription already on that sat was missing from the index
///    (the repair put it back later). ord-dogecoin makes no inscription where
///    one already sits at offset 0, so these go.
///  - `restore.tsv`: id. Inscriptions the repair recovered that the first
///    correction took out by mistake: they go back where the repair placed
///    them, which must still be unspent.
///
/// Then numbers and DNS are cleared, as by the renumber. Neither list holds
/// a dogemap claim, so dogemaps stay as they are.
///
/// `renumber3/` has only `remove.tsv`: reveals that made an inscription here
/// but none in ord-dogecoin, which cannot read their pushes over 255 bytes.
async fn run_fix(config: Config, name: &'static str, key: &'static [u8]) -> Result<()> {
  let dir = std::path::Path::new(&config.data_dir).join(name);
  let remove: Vec<(String, u64, u32)> = lines(&dir.join("remove.tsv"))?
    .iter()
    .map(|r| Ok((r[0].clone(), num(r, 1)?, num(r, 2)?)))
    .collect::<Result<_>>()?;
  let restore: Vec<String> = if dir.join("restore.tsv").exists() {
    lines(&dir.join("restore.tsv"))?.into_iter().map(|r| r[0].clone()).collect()
  } else {
    Vec::new()
  };
  info!("renumber fix {name}: plan read: {} inscriptions to remove, {} to restore", remove.len(), restore.len());
  // Each one restored must still sit where the repair placed it.
  let db = open_db(&config.db_path())?;
  let client = indexer_rpc_client()?;
  for id in &restore {
    match repair::recovered_place(&db, id)? {
      None => bail!("renumber fix {name}: {id} was never recovered by the repair, so there is nothing to restore"),
      Some(None) => {}
      Some(Some((txid, vout))) => {
        let out: Option<serde_json::Value> = rpc_call(client, &config, "gettxout", serde_json::json!([txid, vout, false])).await?;
        if out.is_none() {
          bail!("renumber fix {name}: {id} was at {txid}:{vout}, which has been spent since; where it is now is not known");
        }
      }
    }
  }
  let cfg = config.clone();
  tokio::task::spawn_blocking(move || -> Result<()> {
    let db = open_db(&cfg.db_path())?;
    let started = Instant::now();
    {
      let _w = repair::INDEX_WRITE.lock().unwrap_or_else(|e| e.into_inner());
      let removed = remove_inscriptions(&db, &remove)?;
      let mut restored = 0u64;
      for id in &restore {
        restored += repair::restore_recovered(&cfg, &db, id)? as u64;
      }
      info!("renumber fix {name}: removed {removed}, restored {restored} ({:.0?})", started.elapsed());
    }
    ii::reset_numbering(&db)?;
    dns::reset(&db)?;
    crate::handles::reset(&db)?;
    let meta = db.open_tree("meta")?;
    meta.insert(key, encode_u64(1).to_vec())?;
    db.flush()?;
    info!("renumber fix {name}: numbers and DNS cleared; numbering starts again from the first inscription ({:.0?})", started.elapsed());
    Ok(())
  })
  .await
  .context("renumber fix task")??;
  Ok(())
}

async fn run_first(config: Config) -> Result<()> {
  let dir = std::path::Path::new(&config.data_dir).join("renumber");
  let done = open_db(&config.db_path())?.open_tree("meta")?.get(DONE_KEY)?.is_some();
  if done || !dir.join("remove.tsv").exists() || !dir.join("multi.tsv").exists() {
    return Ok(());
  }
  let remove: Vec<(String, u64, u32)> = lines(&dir.join("remove.tsv"))?
    .iter()
    .map(|r| Ok((r[0].clone(), num(r, 1)?, num(r, 2)?)))
    .collect::<Result<_>>()?;
  let multi: Vec<(String, u64, u32, u64)> = lines(&dir.join("multi.tsv"))?
    .iter()
    .map(|r| Ok((r[0].clone(), num(r, 1)?, num(r, 2)?, num(r, 3)?)))
    .collect::<Result<_>>()?;
  info!("renumber: plan read: {} inscriptions to remove, {} multi-part to move", remove.len(), multi.len());

  let cfg = config.clone();
  tokio::task::spawn_blocking(move || -> Result<()> {
    let db = open_db(&cfg.db_path())?;
    let started = Instant::now();
    {
      // Between two live blocks, so nothing moves under it.
      let _w = repair::INDEX_WRITE.lock().unwrap_or_else(|e| e.into_inner());
      let removed = remove_inscriptions(&db, &remove)?;
      info!("renumber: removed {removed} inscriptions ord-dogecoin does not make ({:.0?})", started.elapsed());
      let moved = move_to_completion(&db, &multi)?;
      info!("renumber: moved {moved} multi-part inscriptions to where they complete ({:.0?})", started.elapsed());
    }
    let claims = rebuild_dogemaps(&db)?;
    info!("renumber: dogemaps rebuilt from the corrected chain order: {claims} claimed ({:.0?})", started.elapsed());
    ii::reset_numbering(&db)?;
    dns::reset(&db)?;
    crate::handles::reset(&db)?;
    let meta = db.open_tree("meta")?;
    meta.insert(DONE_KEY, encode_u64(1).to_vec())?;
    db.flush()?;
    info!("renumber: numbers and DNS cleared; numbering starts again from the first inscription ({:.0?})", started.elapsed());
    Ok(())
  })
  .await
  .context("renumber task")??;
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;

  fn rec(id: &str, txid: &str, vout: u32, address: &str) -> InscriptionRecord {
    InscriptionRecord {
      id: id.to_string(),
      txid: txid.to_string(),
      vout,
      offset: 0,
      satoshis: 100_000,
      content_type: "text/plain".to_string(),
      address: address.to_string(),
      delegate: None,
    }
  }

  #[test]
  fn removal_takes_an_inscription_out_everywhere_and_leaves_its_neighbour() {
    let db = store::Db::temporary().unwrap();
    let by_id = db.open_tree("inscriptions_by_id").unwrap();
    let by_outpoint = db.open_tree("inscriptions_by_outpoint").unwrap();
    let by_address = db.open_tree("inscriptions_by_address").unwrap();
    let content = db.open_tree("inscription_content").unwrap();
    let seq = db.open_tree("inscription_seq").unwrap();
    // An older inscription and a wrongly added one on the same output, as
    // when a reveal carried the older one in at offset 0.
    let (old, bad) = ("aa".repeat(32) + "i0", "bb".repeat(32) + "i0");
    by_id.insert(old.as_bytes(), bincode::serialize(&rec(&old, "cc", 0, "DOWNER")).unwrap()).unwrap();
    by_id.insert(bad.as_bytes(), bincode::serialize(&rec(&bad, "cc", 0, "DOWNER")).unwrap()).unwrap();
    by_outpoint.insert("cc:0", bincode::serialize(&vec![(0u64, old.clone()), (0u64, bad.clone())]).unwrap()).unwrap();
    by_address.insert(format!("DOWNER|{old}"), Vec::<u8>::new()).unwrap();
    by_address.insert(format!("DOWNER|{bad}"), Vec::<u8>::new()).unwrap();
    content.insert(bad.as_bytes(), b"x".to_vec()).unwrap();
    seq.insert(ii::seq_key(100, 4), ii::seq_value(&bad, 0, 1).unwrap()).unwrap();
    seq.insert(ii::seq_key(100, 5), ii::seq_value(&old, 0, 1).unwrap()).unwrap();

    let n = remove_inscriptions(&db, &[(bad.clone(), 100, 4), ("dd".repeat(32) + "i0", 1, 1)]).unwrap();
    assert_eq!(n, 1, "an id not in the index is passed over");
    assert!(by_id.get(bad.as_bytes()).unwrap().is_none() && content.get(bad.as_bytes()).unwrap().is_none());
    assert!(by_address.get(format!("DOWNER|{bad}")).unwrap().is_none());
    assert!(by_address.get(format!("DOWNER|{old}")).unwrap().is_some());
    let list: Vec<(u64, String)> = bincode::deserialize(by_outpoint.get("cc:0").unwrap().unwrap().as_ref()).unwrap();
    assert_eq!(list, vec![(0, old.clone())]);
    assert!(seq.get(ii::seq_key(100, 4)).unwrap().is_none() && seq.get(ii::seq_key(100, 5)).unwrap().is_some());
  }

  /// Replays every reveal from the start height with the push reading the
  /// index used until now (correct lengths) and with ord-dogecoin's (see
  /// `decode_push_datas`), and writes what changes, for `renumber3/`:
  ///  - `remove.tsv`: id, height, position: completed before, not now.
  ///  - `add.tsv`: id, height, position: completed now, not before.
  ///  - `moved.tsv`: id, old height, old position, new height, new position.
  ///  - `unblock.tsv`: txid, height, position, removed id: a transaction that
  ///    carries a removed inscription in at offset 0 and is a reveal by
  ///    ord-dogecoin's reading. The index skipped it for the inscription
  ///    already there; without it, ord-dogecoin may make one. Checked by hand.
  /// Both readings use the same chain rule as the live indexer. Reads only
  /// the node. Skipped by default: `PLAN_OUT=<dir> [FROM=] [TO=] cargo test
  /// -p dogeord-indexer classify_push_reading -- --ignored --nocapture`
  #[tokio::test(flavor = "multi_thread")]
  #[ignore]
  async fn classify_push_reading() {
    use std::io::Write;
    let config = Config::from_env();
    let client = indexer_rpc_client().unwrap();
    let from: u64 = std::env::var("FROM").ok().and_then(|v| v.parse().ok()).unwrap_or(config.first_inscription_height);
    let to: u64 = match std::env::var("TO").ok().and_then(|v| v.parse().ok()) {
      Some(t) => t,
      None => rpc_call::<u64>(client, &config, "getblockcount", serde_json::json!([])).await.unwrap(),
    };
    let dir = std::path::PathBuf::from(std::env::var("PLAN_OUT").expect("PLAN_OUT"));
    std::fs::create_dir_all(&dir).unwrap();
    let file = |n: &str| std::io::BufWriter::new(std::fs::File::create(dir.join(n)).unwrap());
    let (mut remove_f, mut add_f, mut moved_f, mut unblock_f) = (file("remove.tsv"), file("add.tsv"), file("moved.tsv"), file("unblock.tsv"));
    type Decode = fn(&[u8]) -> Option<Vec<Vec<u8>>>;
    // One reading's reveal chains: the live indexer's rule (a spend that does
    // not continue a chain leaves it where it was).
    fn step(chains: &mut HashMap<String, PartialInscriptionChain>, txid: &str, prev: Option<&str>, script: &[u8], decode: Decode) -> Option<String> {
      let taken = prev.and_then(|p| chains.remove(p));
      let continues = taken.is_some();
      let mut chain = taken.unwrap_or_else(|| PartialInscriptionChain { start_txid: txid.to_string(), scripts: Vec::new() });
      chain.scripts.push(script.to_vec());
      match crate::parse_inscription_outcome_with(&chain.scripts, decode) {
        InscriptionParseOutcome::Complete(..) => Some(format!("{}i0", chain.start_txid)),
        InscriptionParseOutcome::Partial => {
          chains.insert(txid.to_string(), chain);
          None
        }
        InscriptionParseOutcome::None => {
          if continues {
            chain.scripts.pop();
            chains.insert(prev.unwrap().to_string(), chain);
          }
          None
        }
      }
    }
    let (mut old, mut new): (HashMap<String, PartialInscriptionChain>, HashMap<String, PartialInscriptionChain>) = Default::default();
    // Where each inscription completed under each reading, until both agree.
    let (mut old_only, mut new_only): (HashMap<String, (u64, u32)>, HashMap<String, (u64, u32)>) = Default::default();
    // Removed inscriptions, followed sat by sat: outpoint -> (offset, id).
    let mut tracked: HashMap<String, Vec<(u64, String)>> = HashMap::new();
    let mut values: HashMap<String, Vec<u64>> = HashMap::new();
    let (mut both, mut unblocks) = (0u64, 0u64);
    let started = Instant::now();
    let mut next = from;
    while next <= to {
      let end = (next + 64).min(to + 1);
      let mut set = tokio::task::JoinSet::new();
      for h in next..end {
        let cfg = config.clone();
        set.spawn(async move {
          // Rides out a node restart: tries again for up to an hour.
          for attempt in 0.. {
            match repair::fetch_block(client, &cfg, h).await {
              Ok(b) => return (h, b),
              Err(e) if attempt < 360 => {
                if attempt % 6 == 0 {
                  println!("block {h}: {e:#}; trying again");
                }
                tokio::time::sleep(Duration::from_secs(10)).await;
              }
              Err(e) => panic!("block {h}: {e:#}"),
            }
          }
          unreachable!()
        });
      }
      let mut blocks = Vec::new();
      while let Some(r) = set.join_next().await {
        blocks.push(r.unwrap());
      }
      blocks.sort_by_key(|(h, _)| *h);
      for (h, block) in &blocks {
        for (i, tx) in block.tx.iter().enumerate() {
          let i = i as u32;
          let prep = prepare_tx(tx).unwrap();
          // Removed inscriptions this transaction spends move on.
          let mut carried: Vec<(u64, String)> = Vec::new();
          if prep.vin_outpoints.iter().flatten().any(|o| tracked.contains_key(o)) {
            let mut input_value = 0u64;
            for (k, vin) in tx.vin.iter().enumerate() {
              let (Some(ptxid), Some(pvout)) = (&vin.txid, vin.vout) else { continue };
              if let Some(ids) = prep.vin_outpoints[k].as_deref().and_then(|o| tracked.remove(o)) {
                carried.extend(ids.into_iter().map(|(o, id)| (input_value + o, id)));
              }
              input_value += loop {
                match repair::prev_value(client, &config, &mut values, ptxid, pvout).await {
                  Ok(v) => break v,
                  Err(e) => {
                    println!("{ptxid}:{pvout}: {e:#}; trying again");
                    tokio::time::sleep(Duration::from_secs(10)).await;
                  }
                }
              };
            }
          }
          let Some(script) = prep.script_sig.as_deref() else {
            continue;
          };
          let prev = tx.vin.first().and_then(|v| v.txid.as_deref());
          let o = step(&mut old, &tx.txid, prev, script, crate::decode_push_datas_lenient);
          let n = step(&mut new, &tx.txid, prev, script, crate::decode_push_datas);
          // A removed inscription at offset 0 of a transaction ord-dogecoin
          // reads as a reveal (or a step of one).
          let ord_reveal = n.is_some() || new.contains_key(&tx.txid) || crate::decode_push_datas(script).is_some_and(|p| p.first().is_some_and(|f| f.as_slice() == b"ord"));
          if let Some((_, id)) = carried.iter().find(|(o, _)| *o == 0)
            && ord_reveal
          {
            writeln!(unblock_f, "{}\t{h}\t{i}\t{id}", tx.txid).unwrap();
            unblocks += 1;
          }
          match (&o, &n) {
            (Some(a), Some(b)) if a == b => both += 1,
            _ => {
              if let Some(a) = &o {
                match new_only.remove(a) {
                  Some((nh, ni)) => writeln!(moved_f, "{a}\t{h}\t{i}\t{nh}\t{ni}").unwrap(),
                  None => {
                    old_only.insert(a.clone(), (*h, i));
                  }
                }
              }
              if let Some(b) = &n {
                match old_only.remove(b) {
                  Some((oh, oi)) => writeln!(moved_f, "{b}\t{oh}\t{oi}\t{h}\t{i}").unwrap(),
                  None => {
                    new_only.insert(b.clone(), (*h, i));
                  }
                }
              }
              // A new inscription that will be removed sits on offset 0 of
              // this transaction's outputs: follow it.
              if let Some(a) = &o
                && n.as_ref() != Some(a)
              {
                carried.push((0, a.clone()));
              }
            }
          }
          if carried.is_empty() {
            continue;
          }
          let mut start = 0u64;
          for out in &prep.outs {
            let end = start + out.satoshis;
            for (abs, id) in &carried {
              if *abs >= start && *abs < end {
                tracked.entry(out.outpoint.clone()).or_default().push((abs - start, id.clone()));
              }
            }
            start = end;
          }
        }
        if h % 10_000 == 0 {
          println!(
            "block {h}: {both} read the same, {} only before, {} only now, {unblocks} to check, {:.0?}",
            old_only.len(),
            new_only.len(),
            started.elapsed()
          );
        }
      }
      next = end;
    }
    for (id, (h, i)) in &old_only {
      writeln!(remove_f, "{id}\t{h}\t{i}").unwrap();
    }
    for (id, (h, i)) in &new_only {
      writeln!(add_f, "{id}\t{h}\t{i}").unwrap();
    }
    for f in [&mut remove_f, &mut add_f, &mut moved_f, &mut unblock_f] {
      f.flush().unwrap();
    }
    println!(
      "done {from}..={to}: {both} read the same, {} to remove, {} to add, {unblocks} to check, {:.0?}",
      old_only.len(),
      new_only.len(),
      started.elapsed()
    );
  }

  #[test]
  fn removal_finds_its_place_in_chain_order_anywhere_in_the_block() {
    let db = store::Db::temporary().unwrap();
    let by_id = db.open_tree("inscriptions_by_id").unwrap();
    let seq = db.open_tree("inscription_seq").unwrap();
    let (bad, other) = ("bb".repeat(32) + "i0", "cc".repeat(32) + "i0");
    by_id.insert(bad.as_bytes(), bincode::serialize(&rec(&bad, "dd", 0, "D")).unwrap()).unwrap();
    // The plan says position 4, but its row is at 9 (as after a move).
    seq.insert(ii::seq_key(100, 4), ii::seq_value(&other, 0, 1).unwrap()).unwrap();
    seq.insert(ii::seq_key(100, 9), ii::seq_value(&bad, 0, 1).unwrap()).unwrap();
    assert_eq!(remove_inscriptions(&db, &[(bad.clone(), 100, 4)]).unwrap(), 1);
    assert!(seq.get(ii::seq_key(100, 9)).unwrap().is_none(), "no row left to be numbered");
    assert!(seq.get(ii::seq_key(100, 4)).unwrap().is_some(), "another inscription's row stays");
  }

  #[test]
  fn a_multi_part_inscription_moves_to_where_it_completes() {
    let db = store::Db::temporary().unwrap();
    let by_id = db.open_tree("inscriptions_by_id").unwrap();
    let seq = db.open_tree("inscription_seq").unwrap();
    let genesis = db.open_tree("inscription_genesis").unwrap();
    let (multi, single) = ("aa".repeat(32) + "i0", "bb".repeat(32) + "i0");
    for id in [&multi, &single] {
      by_id.insert(id.as_bytes(), bincode::serialize(&rec(id, "cc", 0, "D")).unwrap()).unwrap();
    }
    // Numbered at its first piece (block 100), completes in block 102.
    seq.insert(ii::seq_key(100, 3), ii::seq_value(&multi, 1, 1000).unwrap()).unwrap();
    seq.insert(ii::seq_key(101, 0), ii::seq_value(&single, 1, 1010).unwrap()).unwrap();
    genesis.insert(multi.as_bytes(), bincode::serialize(&ii::Genesis { number: 0, height: 100, time: 1000, kinds: 1 }).unwrap()).unwrap();
    genesis.insert(single.as_bytes(), bincode::serialize(&ii::Genesis { number: 1, height: 101, time: 1010, kinds: 1 }).unwrap()).unwrap();

    assert_eq!(move_to_completion(&db, &[(multi.clone(), 102, 7, 1020)]).unwrap(), 1);
    assert!(seq.get(ii::seq_key(100, 3)).unwrap().is_none());
    let e: SeqEntry = bincode::deserialize(seq.get(ii::seq_key(102, 7)).unwrap().unwrap().as_ref()).unwrap();
    assert_eq!((e.id.as_str(), e.kinds, e.time), (multi.as_str(), 1, 1020));
    // Run again: already there, nothing moves.
    assert_eq!(move_to_completion(&db, &[(multi.clone(), 102, 7, 1020)]).unwrap(), 0);

    // Renumbered from scratch, the single one now comes first.
    ii::reset_numbering(&db).unwrap();
    assert!(genesis.get(multi.as_bytes()).unwrap().is_none());
    ii::number_all_for_test(&db, 200).unwrap();
    let g = |id: &str| -> ii::Genesis { bincode::deserialize(genesis.get(id.as_bytes()).unwrap().unwrap().as_ref()).unwrap() };
    assert_eq!((g(&single).number, g(&multi).number, g(&multi).height), (0, 1, 102));
  }

  #[test]
  fn dogemaps_are_rebuilt_from_chain_order_with_current_owners() {
    let db = store::Db::temporary().unwrap();
    let meta = db.open_tree("meta").unwrap();
    let by_id = db.open_tree("inscriptions_by_id").unwrap();
    let seq = db.open_tree("inscription_seq").unwrap();
    let content = db.open_tree("inscription_content").unwrap();
    let by_number = db.open_tree("dogemap_by_number").unwrap();
    let by_address = db.open_tree("dogemap_by_address").unwrap();
    meta.insert(b"indexed_height", encode_u64(100).to_vec()).unwrap();
    // A stale claim from before the correction.
    by_number.insert(encode_u64(9), b"stale".to_vec()).unwrap();
    let rows = [
      (1u32, "aa", "5.dogemap", "text/plain", "DFIRST"),
      (2, "bb", "5.dogemap", "text/plain", "DSECOND"),
      (3, "cc", "200.dogemap", "text/plain", "DFUTURE"),
      (4, "dd", "7.dogemap", "", "DUNTYPED"),
    ];
    for (pos, t, body, ct, owner) in rows {
      let id = t.repeat(32) + "i0";
      by_id.insert(id.as_bytes(), bincode::serialize(&rec(&id, "ee", 0, owner)).unwrap()).unwrap();
      seq.insert(ii::seq_key(100, pos), ii::seq_value(&id, ii::kinds_of(ct, Some(body.as_bytes())), 1100).unwrap()).unwrap();
      let c = InscriptionContentRecord { content_type: ct.to_string(), body: body.as_bytes().to_vec(), delegate: None };
      content.insert(id.as_bytes(), bincode::serialize(&c).unwrap()).unwrap();
    }
    assert_eq!(rebuild_dogemaps(&db).unwrap(), 2, "5 (first claim) and 7 (untyped); 200 does not exist yet");
    let entry = |n: u64| -> Option<DogemapEntry> { by_number.get(encode_u64(n)).unwrap().map(|r| bincode::deserialize(r.as_ref()).unwrap()) };
    assert_eq!(entry(5).unwrap().owner, "DFIRST");
    assert_eq!(entry(7).unwrap().owner, "DUNTYPED");
    assert!(entry(9).is_none() && entry(200).is_none());
    assert!(by_address.get(dogemap_address_key("DFIRST", 5)).unwrap().is_some());
  }
}
