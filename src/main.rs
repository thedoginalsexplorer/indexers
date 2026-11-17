//! Runs every indexer against a Dogecoin Core node, with no web server.
//!
//! Settings come from the environment (see the README). The index is written
//! to `DOGEORD_DATA_DIR`; read it with the `dogeord-indexer` library.

use anyhow::Result;
use dogeord_core::Config;
use dogeord_indexer::{SharedState, run_indexer};
use std::time::Duration;
use tokio::sync::watch;
use tracing::{error, info};
use tracing_subscriber::EnvFilter;

#[tokio::main]
async fn main() -> Result<()> {
  tracing_subscriber::fmt()
    .with_env_filter(EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info")))
    .init();

  let cfg = Config::from_env();
  std::fs::create_dir_all(&cfg.data_dir)?;
  info!("indexing from {} into {}", cfg.rpc_url, cfg.data_dir);

  let (shutdown_tx, shutdown_rx) = watch::channel(false);

  // One-off and resumable: details for DRC-20 tokens deployed before deploys
  // were recorded. Does nothing once it has completed.
  let c = cfg.clone();
  tokio::spawn(async move {
    if let Err(e) = dogeord_indexer::backfill_drc20_deploys(c).await {
      error!("drc20 deploy backfill failed (it retries on the next start): {e:#}");
    }
  });

  // One-off and resumable: chain order for inscriptions indexed before it
  // was recorded. Numbering then follows the chain, one block behind.
  let c = cfg.clone();
  tokio::spawn(async move {
    if let Err(e) = dogeord_indexer::backfill_inscription_seq(c).await {
      error!("inscription order backfill stopped (it resumes on the next start): {e:#}");
    }
  });
  let c = cfg.clone();
  tokio::spawn(async move {
    loop {
      if let Err(e) = dogeord_indexer::run_inscription_numbering(c.clone()).await {
        error!("inscription numbering failed, retrying in a minute: {e:#}");
      }
      tokio::time::sleep(Duration::from_secs(60)).await;
    }
  });

  // DNS names follow inscription numbering. A failure retries the same
  // stretch, since nothing is written until a stretch is done.
  let c = cfg.clone();
  tokio::spawn(async move {
    loop {
      if let Err(e) = dogeord_indexer::run_dns_index(c.clone()).await {
        error!("dns index failed, retrying in a minute: {e:#}");
      }
      tokio::time::sleep(Duration::from_secs(60)).await;
    }
  });

  // D:// (DogeFeed's protocol): posts, comments, quotes and their payments,
  // checked against the registrar, following the main index.
  let c = cfg.clone();
  tokio::spawn(async move {
    loop {
      if let Err(e) = dogeord_indexer::run_dfeed_index(c.clone()).await {
        error!("d:// index stopped, restarting in a minute: {e:#}");
      }
      tokio::time::sleep(Duration::from_secs(60)).await;
    }
  });

  // TAP tokens, copied from Trac's own index through a local tap-reader
  // (DOGEORD_TAP_READER_URL). It waits quietly while no reader is running.
  let c = cfg.clone();
  tokio::spawn(async move {
    loop {
      if let Err(e) = dogeord_indexer::run_tap_sync(c.clone()).await {
        error!("tap sync stopped, restarting in a minute: {e:#}");
      }
      tokio::time::sleep(Duration::from_secs(60)).await;
    }
  });

  // One-off: recover inscriptions the old reveal-chain rule lost (see the
  // repair module). Does nothing once it has completed.
  let c = cfg.clone();
  tokio::spawn(async move {
    loop {
      match dogeord_indexer::run_inscription_repair(c.clone()).await {
        Ok(()) => break,
        Err(e) => {
          error!("inscription repair stopped (it resumes where it was), retrying in a minute: {e:#}");
          tokio::time::sleep(Duration::from_secs(60)).await;
        }
      }
    }
  });

  // One-off: renumber to match ord-dogecoin (see the renumber module). Only
  // when a plan is in the data directory; does nothing once done.
  let c = cfg.clone();
  tokio::spawn(async move {
    if let Err(e) = dogeord_indexer::run_renumber(c).await {
      error!("renumber failed (nothing is marked done, so it runs again at the next start): {e:#}");
    }
  });

  // One-off: rebuild DRC-20 balances by replaying blocks, then swap them in
  // at the tip (see the drc20_replay module). It saves its place on a clean
  // stop and resumes on the next start.
  let c = cfg.clone();
  tokio::spawn(async move {
    loop {
      match dogeord_indexer::run_drc20_replay(c.clone()).await {
        Ok(()) => break,
        Err(e) => {
          error!("drc20 replay stopped, starting it over in a minute: {e:#}");
          tokio::time::sleep(Duration::from_secs(60)).await;
        }
      }
    }
  });

  // One-off: rebuild Dune state under the reference rules by replaying
  // blocks from the first Dune block, then swap it in at the tip (see the
  // dune_replay module). Live indexing skips Dunes until it is done.
  let c = cfg.clone();
  tokio::spawn(async move {
    loop {
      match dogeord_indexer::run_dune_replay(c.clone()).await {
        Ok(()) => break,
        Err(e) => {
          dogeord_indexer::dune_replay_failed(&e);
          error!("dune replay stopped, starting it over in a minute: {e:#}");
          tokio::time::sleep(Duration::from_secs(60)).await;
        }
      }
    }
  });

  let mut indexer = tokio::spawn(run_indexer(cfg, SharedState::new(), shutdown_rx));

  #[cfg(unix)]
  let shutdown = async {
    let mut term = tokio::signal::unix::signal(tokio::signal::unix::SignalKind::terminate())?;
    tokio::select! {
      r = tokio::signal::ctrl_c() => r,
      _ = term.recv() => Ok(()),
    }
  };
  #[cfg(not(unix))]
  let shutdown = tokio::signal::ctrl_c();

  tokio::select! {
    res = &mut indexer => res??,
    _ = shutdown => {
      info!("stopping: finishing the current block");
      let _ = shutdown_tx.send(true);
      // Let the DRC-20 rebuild finish its block and save its place, so the
      // next start resumes it.
      if dogeord_indexer::pause_drc20_replay(Duration::from_secs(90)).await {
        info!("DRC-20 rebuild at rest");
      } else {
        error!("DRC-20 rebuild did not save its place in time; it starts over next time");
      }
      // and let the main index finish its block and flush before exiting
      match tokio::time::timeout(Duration::from_secs(120), indexer).await {
        Ok(Ok(Ok(()))) => info!("index flushed"),
        Ok(Ok(Err(e))) => error!("indexer stopped with an error: {e:#}"),
        Ok(Err(e)) => error!("indexer task failed: {e}"),
        Err(_) => error!("indexer did not stop within 2 minutes; exiting anyway"),
      }
    }
  }
  Ok(())
}
