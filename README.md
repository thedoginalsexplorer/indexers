# DogeOrd indexers

The indexers of DogeOrd, the Dogecoin indexer behind [The Doginals Explorer](https://thedoginalsexplorer.com), for Dogecoin's metaprotocols. They read a Dogecoin Core node block by block and keep the results in a local RocksDB store.

> DogeOrd is a fork of [SpookyOrd](https://github.com/tylordius/SpookyOrd). See [Fork of SpookyOrd](#fork-of-spookyord).

| Indexer | What it records |
|---|---|
| Doginals inscriptions | Every inscription: where it is now, its content type and bytes, and its number in chain order, overall and per kind (text, JSON, images and so on). |
| DRC-20 | Deploys, mints and transfers; balances per address; holders per token; activity per token. A transfer inscription carries tokens only until its first move; one spent as a fee returns them to the sender. Deploys over u64 whole tokens are invalid and tickers fold Unicode case, as in ord-dogecoin. |
| Dunes | Etchings, mints and transfers under the reference rules (a port of wonky-ord's updater and dunestone parser, with Dogecoin's constants: first Dune at block 5,084,000). Balances and UTXOs per address, holders and holder counts per dune, activity per dune. |
| TAP | Deployments, holders and activity, copied from Trac Systems' own Dogecoin TAP index through a local [tap-reader](https://github.com/Trac-Systems/tap-reader). Without a reader running it waits. |
| Dogemaps | `N.dogemap` claims, first come first served. |
| DNS names | Dogecoin Names System names (`label.namespace`), registered as plain text or as JSON, following [spec v1.2](https://github.com/jonheaven/dns). The first valid inscription of a name owns it, and the name moves with that inscription. Records and chosen names only count when they come from the holder at the time, which is checked against the node. |
| D:// (DogeFeed) | Posts, comments, quotes, edits and key links (signed JSON inscriptions) and likes, branches, follows, tips, reveals, deletes and key revocations (payments with a signed 80-byte OP_RETURN), from block 6,440,000. Every signature and payout is checked with the `dproto` crate; invalid records are kept with the reason. A standalone version is at [thedoginalsexplorer/dogefeed-indexer](https://github.com/thedoginalsexplorer/dogefeed-indexer). |

The DNS index reads inscriptions in the numbered order, so it starts once inscription numbering has caught up.

### One-off rebuilds

Some fixes need history replayed. Each runs once in the background, then marks itself done in the store:

| Task | What it does |
|---|---|
| DRC-20 replay | Rebuilds every DRC-20 balance from block 4,600,000 in memory, then swaps it in at the tip. Until then the earlier balances stay in place. It saves its place on a clean stop and resumes. |
| Dune replay | Rebuilds Dunes from block 5,084,000 and swaps them in at the tip. It refuses to swap if any dune fails held + burned = premine + minted. Live indexing skips Dunes until it is done. |
| Inscription repair | Recovers inscriptions an older reveal-chain rule lost. |
| Renumber | Runs only when a plan is in the data directory, to match ord-dogecoin's numbering. |
## Requirements

- A Dogecoin Core node with `server=1`, `txindex=1` and RPC enabled. It must be fully synced.
- Rust 1.85 or newer (the crates use the 2024 edition).
- A C++ toolchain and Clang, which the `rocksdb` crate needs to build.
- Plenty of disk space, more so with inscription content kept (`DOGEORD_CONTENT_STORE=full`).

## Run

```bash
cargo build --release
DOGEORD_RPC_URL=http://127.0.0.1:22555 \
DOGEORD_RPC_USER=your_rpc_user \
DOGEORD_RPC_PASSWORD=your_rpc_password \
DOGEORD_DATA_DIR=./data \
./target/release/doginals-indexer
```

Ctrl-C stops it after the current block and flushes the index (it waits up to two minutes). It resumes where it left off.

| Setting | Default | Meaning |
|---|---|---|
| `DOGEORD_RPC_URL` | from `dogecoin.conf`, else `http://127.0.0.1:22555` | Node RPC address |
| `DOGEORD_RPC_USER`, `DOGEORD_RPC_PASSWORD` | from `dogecoin.conf` | Node RPC login |
| `DOGEORD_DOGECOIN_CONF` | the node's usual location | Where to read `dogecoin.conf` |
| `DOGEORD_RPC_CONCURRENCY` | `4` | Parallel RPC requests |
| `DOGEORD_DATA_DIR` | `./data` | Where the index is written |
| `DOGEORD_FIRST_INSCRIPTION_HEIGHT` | `4600000` | First block read for inscriptions |
| `DOGEORD_FIRST_DUNE_HEIGHT` | `5084000` | First block read for Dunes |
| `DOGEORD_STOP_HEIGHT` | none | Stop at this height (for tests) |
| `DOGEORD_CONTENT_STORE` | `full` | `full` keeps inscription bytes |
| `DOGEORD_FLUSH_INTERVAL` | `64` | Blocks between flushes to disk |
| `DOGEORD_TAP_READER_URL` | `http://localhost:5099` | Where to read TAP from (a running tap-reader) |

Each setting also works with the old `SPOOKY_` prefix from SpookyOrd. An index SpookyOrd made (`spookyord.rocksdb`) is used where it is.

Set `RUST_LOG` (for example `RUST_LOG=info`) to change how much is logged.

### Rolling back

To take the index back to an earlier height, write that height to a file named `rollback-to` in the data directory and start the indexer. It undoes every later block through its undo log, as for a reorg, re-indexes them and deletes the file. It refuses if a block in that range has no undo log.

## Use as a library

`crates/indexer` (`dogeord-indexer`) has the indexing tasks and the read functions, for example `get_inscription`, `list_inscriptions`, `list_drc20_holdings`, `list_dune_holdings`, `get_dogemap`, `dns_get` and `dns_list`. Each takes the same `Config` (`crates/core`) and reads the store the indexer writes.

## Tests

```bash
cargo test --workspace
```

One test follows real inscriptions through a live node and is skipped by default. To run it, set `DOGEORD_DOGECOIN_CONF` and `DNS_TRACE` (the format is in the test's comment in `crates/indexer/src/dns.rs`), then run `cargo test --workspace -- --ignored`.

## Fork of SpookyOrd

DogeOrd is a fork of [SpookyOrd](https://github.com/tylordius/SpookyOrd), split off and renamed in November 2026. These crates started as SpookyOrd's `spookyord-core` and `spookyord-indexer`.

## License

MIT, as SpookyOrd is. See [LICENSE](LICENSE).
