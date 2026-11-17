//! Bootstrap: hand a finished index to a new operator, so they skip the weeks
//! a full index takes (the main sync, then the DRC-20, Dune and numbering
//! passes).
//!
//! snapshot → pack → (put the files on any web host) → download → apply
//!
//! - **snapshot** takes a consistent copy of the store at a block boundary.
//!   With an indexer running, the indexer takes it itself right after its next
//!   flush (a `snapshot-to` file in the data directory asks for it), so
//!   indexing never stops. Without one, the store is opened directly.
//! - **pack** writes that copy as one tar stream, zstd-compressed and split
//!   into parts, plus `bootstrap.json`: the height and block hash it ends at,
//!   which one-off passes are done, and each part's size and SHA-256.
//! - **download** fetches the manifest and parts, resuming partial parts and
//!   checking every hash.
//! - **apply** checks the snapshot's block hash against the operator's own
//!   node, unpacks it into the data directory (checking each part's hash as it
//!   streams), and checks the result. The indexer then carries on from the
//!   next block like after any restart.
//!
//! Only the RocksDB store goes into a snapshot. Nothing else in the data
//! directory (API keys, admin tokens, caches) is ever read.

use anyhow::{Context, Result, anyhow, bail};
use dogeord_core::{Config, DB_DIR, LEGACY_DB_DIR};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use tracing::{info, warn};

/// Written into the data directory to ask a running indexer for a snapshot;
/// holds the output directory.
pub const TRIGGER_FILE: &str = "snapshot-to";
/// Written into the data directory when a requested snapshot failed.
pub const FAILED_FILE: &str = "snapshot-failed";
/// Written beside the store copy by `snapshot`.
pub const INFO_FILE: &str = "snapshot-info.json";
/// The manifest `pack` writes and `download`/`apply` read.
pub const MANIFEST_FILE: &str = "bootstrap.json";
/// Bump when the archive layout changes.
pub const FORMAT: u32 = 1;
/// Default part size: under the 2 GiB per-file limit of common hosts.
pub const DEFAULT_PART_BYTES: u64 = 1_900 * 1024 * 1024;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SnapshotInfo {
  pub format: u32,
  /// The node's chain name ("main", "test", ...).
  pub chain: String,
  /// The last block in the snapshot; indexing continues from the next one.
  pub height: u64,
  pub block_hash: String,
  pub created_unix: u64,
  /// Version of the indexer that made it.
  pub indexer_version: String,
  /// One-off passes already done in this index, so they do not run again.
  pub done: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Part {
  pub name: String,
  pub bytes: u64,
  pub sha256: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Manifest {
  #[serde(flatten)]
  pub info: SnapshotInfo,
  /// "tar+zstd": the parts, joined in order, are one zstd stream of one tar.
  pub archive: String,
  /// Size of the store once unpacked.
  pub unpacked_bytes: u64,
  pub parts: Vec<Part>,
}

impl Manifest {
  pub fn packed_bytes(&self) -> u64 {
    self.parts.iter().map(|p| p.bytes).sum()
  }
}

fn now_unix() -> u64 {
  SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

fn gib(b: u64) -> String {
  format!("{:.1} GiB", b as f64 / (1u64 << 30) as f64)
}

/// Which one-off passes are done in the index `config` points at.
fn done_tasks(config: &Config) -> Vec<String> {
  let checks: [(&str, fn(&Config) -> Result<bool>); 5] = [
    ("inscription_repair", crate::inscription_repair_done),
    ("renumber", crate::renumber_done),
    ("drc20_replay", crate::drc20_replay_done),
    ("dune_replay", crate::dunes_rebuilt),
    ("dune_holders", crate::dune_holders_built),
  ];
  checks.iter().filter(|(_, f)| f(config).unwrap_or(false)).map(|(n, _)| n.to_string()).collect()
}

fn write_snapshot(config: &Config, db: &crate::store::Db, out: &Path, chain: &str, height: u64, block_hash: &str) -> Result<SnapshotInfo> {
  fs::create_dir_all(out).with_context(|| format!("create {}", out.display()))?;
  let target = out.join(DB_DIR);
  if target.exists() || out.join(INFO_FILE).exists() {
    bail!("{} already holds a snapshot", out.display());
  }
  let t = Instant::now();
  db.checkpoint(&target)?;
  let info = SnapshotInfo {
    format: FORMAT,
    chain: chain.to_string(),
    height,
    block_hash: block_hash.to_string(),
    created_unix: now_unix(),
    indexer_version: env!("CARGO_PKG_VERSION").to_string(),
    done: done_tasks(config),
  };
  fs::write(out.join(INFO_FILE), serde_json::to_vec_pretty(&info)?).context("write snapshot info")?;
  info!("snapshot: block {height} ({block_hash}) written to {} in {:.1}s", out.display(), t.elapsed().as_secs_f64());
  Ok(info)
}

/// Called by the indexer between blocks, right after a flush: takes the
/// snapshot a `snapshot-to` file asks for. A failure is logged and written to
/// `snapshot-failed`; it never stops indexing.
pub(crate) fn serve_snapshot_request(config: &Config, db: &crate::store::Db, chain: &str, height: u64, block_hash: &str) {
  let dir = Path::new(&config.data_dir);
  let trigger = dir.join(TRIGGER_FILE);
  if !trigger.exists() {
    return;
  }
  let out = fs::read_to_string(&trigger).map(|s| PathBuf::from(s.trim()));
  // one attempt per request, whatever happens
  let _ = fs::remove_file(&trigger);
  let result = out.map_err(anyhow::Error::from).and_then(|out| {
    if out.as_os_str().is_empty() || !out.is_absolute() {
      bail!("{TRIGGER_FILE} must hold an absolute directory path");
    }
    write_snapshot(config, db, &out, chain, height, block_hash)
  });
  if let Err(e) = result {
    warn!("snapshot request failed: {e:#}");
    let _ = fs::write(dir.join(FAILED_FILE), format!("{e:#}"));
  }
}

/// Snapshot the index in `config.data_dir` into `out`. With an indexer
/// running on that data directory, it is asked to take it (and this waits up
/// to `wait`); otherwise the store is opened here.
pub fn snapshot(config: &Config, out: &Path, wait: Duration) -> Result<SnapshotInfo> {
  let out = std::path::absolute(out).context("resolve the output directory")?;
  if out.join(INFO_FILE).exists() || out.join(DB_DIR).exists() {
    bail!("{} already holds a snapshot", out.display());
  }
  let db_path = config.db_path();
  if !Path::new(&db_path).exists() {
    bail!("no index at {db_path}");
  }
  match crate::open_db(&db_path) {
    Ok(db) => {
      let meta = db.open_tree("meta")?;
      let height = match meta.get(b"indexed_height")? {
        Some(v) => crate::decode_u64(v.as_ref())?,
        None => bail!("the index at {db_path} has no blocks yet"),
      };
      let hash = db
        .open_tree("blocks")?
        .get(crate::encode_u64(height))?
        .map(|v| String::from_utf8_lossy(v.as_ref()).to_string())
        .ok_or_else(|| anyhow!("block {height} has no recorded hash"))?;
      let chain = node_chain(config).unwrap_or_else(|e| {
        warn!("could not ask the node for its chain ({e:#}); recording \"unknown\"");
        "unknown".to_string()
      });
      write_snapshot(config, &db, &out, &chain, height, &hash)
    }
    Err(e) if format!("{e:#}").to_ascii_lowercase().contains("lock") => {
      info!("an indexer is running on {}; asking it for the snapshot after its next flush", config.data_dir);
      request_snapshot(config, &out, wait)
    }
    Err(e) => Err(e),
  }
}

fn request_snapshot(config: &Config, out: &Path, wait: Duration) -> Result<SnapshotInfo> {
  let dir = Path::new(&config.data_dir);
  let failed = dir.join(FAILED_FILE);
  let _ = fs::remove_file(&failed);
  fs::write(dir.join(TRIGGER_FILE), out.to_string_lossy().as_bytes()).context("write the snapshot request")?;
  let start = Instant::now();
  loop {
    if let Ok(raw) = fs::read(out.join(INFO_FILE)) {
      return serde_json::from_slice(&raw).context("read the snapshot info");
    }
    if let Ok(msg) = fs::read_to_string(&failed) {
      let _ = fs::remove_file(&failed);
      bail!("the indexer could not take the snapshot: {msg}");
    }
    if start.elapsed() > wait {
      let _ = fs::remove_file(dir.join(TRIGGER_FILE));
      bail!(
        "the running indexer did not take the snapshot within {}s. It checks after each flush (every block at the tip); \
         is it this version and still indexing?",
        wait.as_secs()
      );
    }
    std::thread::sleep(Duration::from_millis(500));
  }
}

// ---------- pack ----------

/// Writes one stream as numbered part files, hashing each.
struct SplitWriter {
  dir: PathBuf,
  base: String,
  part_bytes: u64,
  cur: Option<(BufWriter<File>, Sha256, u64, String)>,
  parts: Vec<Part>,
}

impl SplitWriter {
  fn close(&mut self) -> io::Result<()> {
    if let Some((mut w, h, n, name)) = self.cur.take() {
      w.flush()?;
      w.get_ref().sync_all()?;
      info!("pack: wrote {name} ({})", gib(n));
      self.parts.push(Part { name, bytes: n, sha256: hex::encode(h.finalize()) });
    }
    Ok(())
  }
  fn finish(mut self) -> io::Result<Vec<Part>> {
    self.close()?;
    Ok(self.parts)
  }
}

impl Write for SplitWriter {
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
    if buf.is_empty() {
      return Ok(0);
    }
    if self.cur.is_none() {
      let name = format!("{}.{:04}", self.base, self.parts.len());
      let f = OpenOptions::new().write(true).create_new(true).open(self.dir.join(&name))?;
      self.cur = Some((BufWriter::with_capacity(8 << 20, f), Sha256::new(), 0, name));
    }
    let (w, h, n, _) = self.cur.as_mut().unwrap();
    let take = buf.len().min((self.part_bytes - *n) as usize);
    w.write_all(&buf[..take])?;
    h.update(&buf[..take]);
    *n += take as u64;
    if *n >= self.part_bytes {
      self.close()?;
    }
    Ok(take)
  }
  fn flush(&mut self) -> io::Result<()> {
    match self.cur.as_mut() {
      Some((w, ..)) => w.flush(),
      None => Ok(()),
    }
  }
}

/// Packs the snapshot in `snapshot_dir` into parts and a manifest in `out_dir`.
pub fn pack(snapshot_dir: &Path, out_dir: &Path, part_bytes: u64, level: i32) -> Result<Manifest> {
  if part_bytes < 1 << 20 {
    bail!("parts must be at least 1 MiB");
  }
  let info: SnapshotInfo = serde_json::from_slice(&fs::read(snapshot_dir.join(INFO_FILE)).with_context(|| {
    format!("{} has no {INFO_FILE}; make it with `bootstrap snapshot`", snapshot_dir.display())
  })?)
  .context("read the snapshot info")?;
  let db_dir = snapshot_dir.join(DB_DIR);
  let mut files: Vec<(String, PathBuf, u64)> = Vec::new();
  for e in fs::read_dir(&db_dir).with_context(|| format!("read {}", db_dir.display()))? {
    let e = e?;
    let meta = e.metadata()?;
    if !meta.is_file() {
      bail!("unexpected entry in the store copy: {}", e.path().display());
    }
    files.push((e.file_name().to_string_lossy().to_string(), e.path(), meta.len()));
  }
  files.sort();
  let unpacked: u64 = files.iter().map(|f| f.2).sum();
  fs::create_dir_all(out_dir)?;
  if out_dir.join(MANIFEST_FILE).exists() {
    bail!("{} already holds a packed bootstrap", out_dir.display());
  }
  info!("pack: block {} — {} files, {} to compress", info.height, files.len(), gib(unpacked));

  let base = format!("dogeord-bootstrap-{}.tar.zst", info.height);
  let split = SplitWriter { dir: out_dir.to_path_buf(), base, part_bytes, cur: None, parts: Vec::new() };
  let mut enc = zstd::stream::write::Encoder::new(split, level).context("start zstd")?;
  let threads = std::thread::available_parallelism().map(|n| n.get() as u32).unwrap_or(4);
  enc.multithread(threads).context("zstd threads")?;
  enc.include_checksum(true)?;
  let t = Instant::now();
  let mut done_bytes = 0u64;
  let mut last = Instant::now();
  {
    let mut tar = tar::Builder::new(&mut enc);
    tar.mode(tar::HeaderMode::Deterministic);
    tar.follow_symlinks(false);
    for (name, path, len) in &files {
      let mut f = File::open(path).with_context(|| format!("open {}", path.display()))?;
      let mut h = tar::Header::new_gnu();
      h.set_size(*len);
      h.set_mode(0o644);
      h.set_entry_type(tar::EntryType::Regular);
      h.set_mtime(info.created_unix);
      tar.append_data(&mut h, format!("{DB_DIR}/{name}"), &mut f).with_context(|| format!("pack {name}"))?;
      done_bytes += len;
      if last.elapsed() > Duration::from_secs(30) {
        last = Instant::now();
        let rate = done_bytes as f64 / t.elapsed().as_secs_f64().max(1.0);
        info!(
          "pack: {} of {} ({:.0}%), {:.0} MiB/s, about {} min left",
          gib(done_bytes),
          gib(unpacked),
          done_bytes as f64 * 100.0 / unpacked.max(1) as f64,
          rate / (1 << 20) as f64,
          ((unpacked - done_bytes) as f64 / rate.max(1.0) / 60.0).ceil()
        );
      }
    }
    tar.finish().context("finish the tar stream")?;
  }
  let parts = enc.finish().context("finish zstd")?.finish().context("close the last part")?;
  let manifest = Manifest { info, archive: "tar+zstd".into(), unpacked_bytes: unpacked, parts };
  fs::write(out_dir.join(MANIFEST_FILE), serde_json::to_vec_pretty(&manifest)?).context("write the manifest")?;
  info!(
    "pack: done in {:.0} min — {} parts, {} (from {})",
    t.elapsed().as_secs_f64() / 60.0,
    manifest.parts.len(),
    gib(manifest.packed_bytes()),
    gib(unpacked)
  );
  Ok(manifest)
}

// ---------- download / verify ----------

fn is_url(s: &str) -> bool {
  s.starts_with("https://") || s.starts_with("http://")
}

/// `https://host/dir/` or `https://host/dir/bootstrap.json` → `https://host/dir`
fn base_url(s: &str) -> String {
  let s = s.trim_end_matches('/');
  if s.ends_with(".json") { s.rsplit_once('/').map(|(b, _)| b.to_string()).unwrap_or_default() } else { s.to_string() }
}

fn http() -> Result<reqwest::blocking::Client> {
  reqwest::blocking::Client::builder()
    .connect_timeout(Duration::from_secs(30))
    .timeout(None)
    .user_agent(concat!("doginals-indexer-bootstrap/", env!("CARGO_PKG_VERSION")))
    .build()
    .context("build the HTTP client")
}

fn check_manifest(m: &Manifest) -> Result<()> {
  if m.info.format != FORMAT {
    bail!("bootstrap format {} is not supported by this indexer (it reads format {FORMAT}); update the indexer", m.info.format);
  }
  if m.archive != "tar+zstd" {
    bail!("unknown archive type {:?}", m.archive);
  }
  if m.parts.is_empty() {
    bail!("the manifest lists no parts");
  }
  for p in &m.parts {
    // part names are joined onto paths and URLs: plain file names only
    if p.name.is_empty() || p.name.contains(['/', '\\', ':']) || p.name.starts_with('.') || p.sha256.len() != 64 {
      bail!("bad part entry in the manifest: {:?}", p.name);
    }
  }
  Ok(())
}

fn read_manifest(source: &str) -> Result<Manifest> {
  let m: Manifest = if is_url(source) {
    let url = format!("{}/{MANIFEST_FILE}", base_url(source));
    http()?.get(&url).send().and_then(|r| r.error_for_status()).with_context(|| format!("fetch {url}"))?.json().context("read the manifest")?
  } else {
    let p = Path::new(source);
    let p = if p.is_dir() { p.join(MANIFEST_FILE) } else { p.to_path_buf() };
    serde_json::from_slice(&fs::read(&p).with_context(|| format!("read {}", p.display()))?).context("read the manifest")?
  };
  check_manifest(&m)?;
  Ok(m)
}

fn file_sha256(path: &Path) -> Result<(u64, String)> {
  let mut f = BufReader::with_capacity(8 << 20, File::open(path)?);
  let mut h = Sha256::new();
  let n = io::copy(&mut f, &mut h)?;
  Ok((n, hex::encode(h.finalize())))
}

/// Checks every part in `dir` against its manifest. Returns the bad ones.
pub fn verify(dir: &Path) -> Result<Vec<String>> {
  let m = read_manifest(&dir.to_string_lossy())?;
  let mut bad = Vec::new();
  for p in &m.parts {
    let path = dir.join(&p.name);
    match file_sha256(&path) {
      Ok((n, h)) if n == p.bytes && h == p.sha256 => info!("verify: {} ok", p.name),
      Ok(_) => {
        warn!("verify: {} does not match the manifest", p.name);
        bad.push(p.name.clone());
      }
      Err(e) => {
        warn!("verify: {}: {e}", p.name);
        bad.push(p.name.clone());
      }
    }
  }
  Ok(bad)
}

/// Downloads the manifest and every part into `dir`, resuming partial parts
/// and checking each hash.
pub fn download(source: &str, dir: &Path) -> Result<Manifest> {
  if !is_url(source) {
    bail!("download needs an http(s) address");
  }
  let base = base_url(source);
  let m = read_manifest(&base)?;
  fs::create_dir_all(dir)?;
  fs::write(dir.join(MANIFEST_FILE), serde_json::to_vec_pretty(&m)?)?;
  info!("download: block {} — {} parts, {}", m.info.height, m.parts.len(), gib(m.packed_bytes()));
  let client = http()?;
  for (i, p) in m.parts.iter().enumerate() {
    let path = dir.join(&p.name);
    for attempt in 1..=5 {
      let have = fs::metadata(&path).map(|x| x.len()).unwrap_or(0);
      if have == p.bytes {
        let (_, h) = file_sha256(&path)?;
        if h == p.sha256 {
          info!("download: part {}/{} ok", i + 1, m.parts.len());
          break;
        }
        warn!("download: {} has the wrong hash; fetching it again", p.name);
        fs::remove_file(&path)?;
        continue;
      }
      if have > p.bytes {
        fs::remove_file(&path)?;
        continue;
      }
      let url = format!("{base}/{}", p.name);
      let mut req = client.get(&url);
      if have > 0 {
        req = req.header(reqwest::header::RANGE, format!("bytes={have}-"));
      }
      let res = req.send().and_then(|r| r.error_for_status());
      let mut res = match res {
        Ok(r) => r,
        Err(e) => {
          warn!("download: {url}: {e} (attempt {attempt} of 5)");
          std::thread::sleep(Duration::from_secs(5 * attempt));
          continue;
        }
      };
      // a server that ignores Range sends the whole file again
      let resume = have > 0 && res.status() == reqwest::StatusCode::PARTIAL_CONTENT;
      let f = OpenOptions::new().create(true).write(true).append(resume).truncate(!resume).open(&path)?;
      let mut w = BufWriter::with_capacity(8 << 20, f);
      info!("download: part {}/{} {}{}", i + 1, m.parts.len(), p.name, if resume { format!(" from {}", gib(have)) } else { String::new() });
      if let Err(e) = io::copy(&mut res, &mut w).and_then(|_| w.flush()) {
        warn!("download: {}: {e} (attempt {attempt} of 5; it resumes)", p.name);
        std::thread::sleep(Duration::from_secs(5 * attempt));
        continue;
      }
    }
    let (n, h) = file_sha256(&path).with_context(|| format!("{} did not download", p.name))?;
    if n != p.bytes || h != p.sha256 {
      bail!("{} still does not match the manifest after 5 attempts", p.name);
    }
  }
  info!("download: all {} parts present and checked", m.parts.len());
  Ok(m)
}

// ---------- apply ----------

enum Source {
  Dir(PathBuf),
  Http(reqwest::blocking::Client, String),
}

/// The parts read in order as one stream, each checked against its size and
/// hash when it ends.
struct PartsReader {
  parts: Vec<Part>,
  src: Source,
  i: usize,
  cur: Option<Box<dyn Read>>,
  hasher: Sha256,
  got: u64,
  total: u64,
  read: u64,
  started: Instant,
  last_log: Instant,
}

impl PartsReader {
  fn open(&self, p: &Part) -> io::Result<Box<dyn Read>> {
    Ok(match &self.src {
      Source::Dir(d) => Box::new(BufReader::with_capacity(8 << 20, File::open(d.join(&p.name))?)),
      Source::Http(c, base) => {
        let r = c.get(format!("{base}/{}", p.name)).send().and_then(|r| r.error_for_status()).map_err(io::Error::other)?;
        Box::new(BufReader::with_capacity(8 << 20, r))
      }
    })
  }
  fn all_read(&self) -> bool {
    self.i == self.parts.len()
  }
}

impl Read for PartsReader {
  fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
    loop {
      if self.i == self.parts.len() {
        return Ok(0);
      }
      if self.cur.is_none() {
        let p = self.parts[self.i].clone();
        self.cur = Some(self.open(&p)?);
        self.hasher = Sha256::new();
        self.got = 0;
      }
      let n = self.cur.as_mut().unwrap().read(buf)?;
      if n == 0 {
        let p = &self.parts[self.i];
        let h = hex::encode(std::mem::take(&mut self.hasher).finalize());
        if self.got != p.bytes || h != p.sha256 {
          return Err(io::Error::other(format!("{} does not match the manifest (size or SHA-256)", p.name)));
        }
        self.i += 1;
        self.cur = None;
        continue;
      }
      self.hasher.update(&buf[..n]);
      self.got += n as u64;
      self.read += n as u64;
      if self.last_log.elapsed() > Duration::from_secs(30) {
        self.last_log = Instant::now();
        let rate = self.read as f64 / self.started.elapsed().as_secs_f64().max(1.0);
        info!(
          "apply: part {}/{}, {} of {} ({:.0}%), {:.0} MiB/s",
          self.i + 1,
          self.parts.len(),
          gib(self.read),
          gib(self.total),
          self.read as f64 * 100.0 / self.total.max(1) as f64,
          rate / (1 << 20) as f64
        );
      }
      return Ok(n);
    }
  }
}

/// Blocking JSON-RPC call to the node in `config`.
fn node_rpc(config: &Config, method: &str, params: serde_json::Value) -> Result<serde_json::Value> {
  let client = reqwest::blocking::Client::builder().timeout(Duration::from_secs(30)).build()?;
  let mut req = client.post(&config.rpc_url).json(&serde_json::json!({"jsonrpc": "1.0", "id": "bootstrap", "method": method, "params": params}));
  if !config.rpc_user.is_empty() {
    req = req.basic_auth(&config.rpc_user, Some(&config.rpc_password));
  }
  let v: serde_json::Value = req.send().with_context(|| format!("reach the node at {}", config.rpc_url))?.json().context("read the node's answer")?;
  if !v["error"].is_null() {
    bail!("node {method}: {}", v["error"]);
  }
  Ok(v["result"].clone())
}

fn node_chain(config: &Config) -> Result<String> {
  Ok(node_rpc(config, "getblockchaininfo", serde_json::json!([]))?["chain"].as_str().unwrap_or("unknown").to_string())
}

/// Is the snapshot on the same chain as the node? Err if not; Ok(false) if the
/// node has not reached its height yet.
fn check_against_node(config: &Config, info: &SnapshotInfo) -> Result<bool> {
  let chain = node_chain(config)?;
  if info.chain != "unknown" && chain != info.chain {
    bail!("this snapshot is for the {:?} chain, but the node is on {chain:?}", info.chain);
  }
  let count = node_rpc(config, "getblockcount", serde_json::json!([]))?.as_u64().unwrap_or(0);
  if count < info.height {
    return Ok(false);
  }
  let hash = node_rpc(config, "getblockhash", serde_json::json!([info.height]))?;
  if hash.as_str() != Some(info.block_hash.as_str()) {
    bail!(
      "the node's block {} is {}, not the snapshot's {}; this snapshot is not on your node's chain",
      info.height,
      hash,
      info.block_hash
    );
  }
  Ok(true)
}

pub struct ApplyOptions {
  /// Unpack even when the node cannot be reached to confirm the block hash.
  pub skip_node_check: bool,
}

/// Unpacks a bootstrap (a directory with `bootstrap.json`, or its web
/// address) into `config.data_dir`, which must not hold an index yet.
pub fn apply(config: &Config, source: &str, opts: &ApplyOptions) -> Result<SnapshotInfo> {
  let data_dir = PathBuf::from(&config.data_dir);
  for name in [DB_DIR, LEGACY_DB_DIR] {
    if data_dir.join(name).exists() {
      bail!("{} already holds an index ({name}); move it away first", data_dir.display());
    }
  }
  let m = read_manifest(source)?;
  let info = m.info.clone();
  info!(
    "apply: block {} ({}) on {}, {} packed, {} unpacked, done: {}",
    info.height,
    info.block_hash,
    info.chain,
    gib(m.packed_bytes()),
    gib(m.unpacked_bytes),
    if info.done.is_empty() { "-".to_string() } else { info.done.join(", ") }
  );

  match check_against_node(config, &info) {
    Ok(true) => info!("apply: the node has block {} with the same hash", info.height),
    Ok(false) => warn!("apply: the node has not reached block {} yet, so its hash could not be checked; let the node sync past it before starting the indexer", info.height),
    Err(e) if opts.skip_node_check => warn!("apply: node check skipped: {e:#}"),
    Err(e) => return Err(e.context("checking the snapshot against your node (use --skip-node-check to unpack anyway)")),
  }

  fs::create_dir_all(&data_dir)?;
  let tmp = data_dir.join(".bootstrap-unpack");
  if tmp.exists() {
    fs::remove_dir_all(&tmp).context("clear an earlier unfinished unpack")?;
  }
  fs::create_dir_all(&tmp)?;

  let src = if is_url(source) { Source::Http(http()?, base_url(source)) } else {
    let p = Path::new(source);
    Source::Dir(if p.is_dir() { p.to_path_buf() } else { p.parent().map(Path::to_path_buf).unwrap_or_default() })
  };
  let total = m.packed_bytes();
  let reader = PartsReader {
    parts: m.parts.clone(),
    src,
    i: 0,
    cur: None,
    hasher: Sha256::new(),
    got: 0,
    total,
    read: 0,
    started: Instant::now(),
    last_log: Instant::now(),
  };
  let result = (|| -> Result<PartsReader> {
    let dec = zstd::stream::read::Decoder::new(reader).context("start zstd")?;
    let mut ar = tar::Archive::new(dec);
    let prefix = format!("{DB_DIR}/");
    let mut files = 0u64;
    for entry in ar.entries().context("read the archive")? {
      let mut entry = entry.context("read the archive")?;
      let path = entry.path()?.to_string_lossy().replace('\\', "/");
      let name = path.strip_prefix(&prefix).unwrap_or("");
      if entry.header().entry_type() != tar::EntryType::Regular || name.is_empty() || name.contains('/') || name.starts_with('.') {
        bail!("unexpected entry in the archive: {path:?}");
      }
      let dest = tmp.join(DB_DIR);
      fs::create_dir_all(&dest)?;
      entry.unpack(dest.join(name)).with_context(|| format!("unpack {name}"))?;
      files += 1;
    }
    info!("apply: {files} files unpacked");
    // read to the very end, so the last part's hash is checked too
    let mut dec = ar.into_inner();
    io::copy(&mut dec, &mut io::sink()).context("read the end of the archive")?;
    Ok(dec.finish().into_inner())
  })();
  let reader = match result {
    Ok(r) => r,
    Err(e) => {
      let _ = fs::remove_dir_all(&tmp);
      return Err(e);
    }
  };
  if !reader.all_read() {
    let _ = fs::remove_dir_all(&tmp);
    bail!("the archive ended before its last part");
  }

  fs::rename(tmp.join(DB_DIR), data_dir.join(DB_DIR)).context("move the index into place")?;
  let _ = fs::remove_dir_all(&tmp);

  // open what was unpacked and check it ends where the manifest says
  let db = crate::open_db(&config.db_path())?;
  let height = db.open_tree("meta")?.get(b"indexed_height")?.map(|v| crate::decode_u64(v.as_ref())).transpose()?;
  let hash = db.open_tree("blocks")?.get(crate::encode_u64(info.height))?.map(|v| String::from_utf8_lossy(v.as_ref()).to_string());
  db.flush()?;
  if height != Some(info.height) || hash.as_deref() != Some(info.block_hash.as_str()) {
    bail!("the unpacked index ends at {height:?} / {hash:?}, not block {} {}; do not use it", info.height, info.block_hash);
  }
  info!("apply: index in place at {}, ending at block {}. Start the indexer to carry on from block {}.", config.db_path(), info.height, info.height + 1);
  Ok(info)
}

#[cfg(test)]
mod tests {
  use super::*;

  fn info() -> SnapshotInfo {
    SnapshotInfo { format: FORMAT, chain: "main".into(), height: 1, block_hash: "00".repeat(32), created_unix: 0, indexer_version: "t".into(), done: vec![] }
  }

  #[test]
  fn parts_split_at_the_size_and_hash_what_they_hold() {
    let dir = std::env::temp_dir().join(format!("bootstrap-split-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let data: Vec<u8> = (0..2_500_000u32).map(|i| (i % 251) as u8).collect();
    let mut w = SplitWriter { dir: dir.clone(), base: "x".into(), part_bytes: 1 << 20, cur: None, parts: vec![] };
    w.write_all(&data).unwrap();
    let parts = w.finish().unwrap();
    assert_eq!(parts.iter().map(|p| p.bytes).collect::<Vec<_>>(), vec![1 << 20, 1 << 20, 2_500_000 - (2 << 20)]);
    let mut joined = Vec::new();
    for p in &parts {
      let b = fs::read(dir.join(&p.name)).unwrap();
      assert_eq!(hex::encode(Sha256::digest(&b)), p.sha256);
      joined.extend(b);
    }
    assert_eq!(joined, data);
    let _ = fs::remove_dir_all(&dir);
  }

  #[test]
  fn a_manifest_cannot_name_files_outside_its_folder() {
    let part = |name: &str| Part { name: name.into(), bytes: 1, sha256: "a".repeat(64) };
    let m = |p: Part| Manifest { info: info(), archive: "tar+zstd".into(), unpacked_bytes: 1, parts: vec![p] };
    assert!(check_manifest(&m(part("dogeord-bootstrap-1.tar.zst.0000"))).is_ok());
    for bad in ["../x", "a/b", r"a\b", "C:x", ".hidden", ""] {
      assert!(check_manifest(&m(part(bad))).is_err(), "{bad:?} accepted");
    }
    let mut future = m(part("ok"));
    future.info.format = FORMAT + 1;
    assert!(check_manifest(&future).is_err());
  }

  #[test]
  fn the_manifest_address_can_be_the_folder_or_the_file() {
    assert_eq!(base_url("https://h/b/"), "https://h/b");
    assert_eq!(base_url("https://h/b"), "https://h/b");
    assert_eq!(base_url("https://h/b/bootstrap.json"), "https://h/b");
  }
}
