//! Commit-first priority, shared by the DNS index (DNS spec v1.3 §5.7) and the @ handles index
//! (@ spec v1.1 §5.6): which of two registers of the same name or handle wins.
//!
//! A register's **key** is `(commit_height, commit_tx_index, commit_vout)` when its reveal is a
//! single-transaction inscription whose `vin[0]` is **bound** by the committed redeem
//! (committed-envelope.md §3, in github.com/jonheaven/dmaps) and the P2SH output it spends
//! confirmed at most [`W`] blocks before the reveal; otherwise `(reveal_height, reveal_tx_index, 0)`.
//! A register takes a name that is already taken only when its key is lower than the holder's and
//! the holder's row is still **pending** — the newcomer's reveal is at most `W` blocks after the
//! holder's key. After that the row is **final**.
//!
//! A JSON register may claim `bitworkc` (a prefix of its commit txid) and/or `bitworkr` (of its
//! reveal txid); a claim the txid does not meet voids the register: not a name, not a missed claim.
//!
//! Only races inside the window need the node: a register more than `W` blocks after the holder's
//! reveal can never win, so it is a missed claim without looking anything up.

use super::*;
use crate::dns::{Pos, Tracer};
use sha2::{Digest, Sha256};

/// The window, in blocks.
pub const W: u64 = 30;
/// `(height, tx_index, vout)`; a reveal key has vout 0.
pub type Key = (u64, u32, u32);

pub(crate) fn reveal_key(p: Pos) -> Key {
  (p.0, p.1, 0)
}

/// Whether a register revealed at `new_reveal_height` with key `new_key` takes the name from a
/// holder whose key is `holder_key` (the rule of §5.7, in block order).
pub fn displaces(holder_key: Key, new_key: Key, new_reveal_height: u64) -> bool {
  new_key < holder_key && new_reveal_height <= holder_key.0 + W
}

/// `pending` while a lower key could still take the name, then `final`.
pub fn status(key: Key, tip: u64) -> &'static str {
  if tip <= key.0 + W { "pending" } else { "final" }
}

// ---------------------------------------------------------------- scripts --

fn hash160(b: &[u8]) -> [u8; 20] {
  use ripemd::Ripemd160;
  let sha = Sha256::digest(b);
  Ripemd160::digest(sha).into()
}

/// One push of a script and the bytes after it: the value it leaves on the stack (`OP_0` empty,
/// `OP_1NEGATE` 0x81, `OP_1`..`OP_16` one byte), or `None` when the next opcode is not a push.
fn next_push(s: &[u8]) -> Option<(Vec<u8>, &[u8])> {
  let (&op, rest) = s.split_first()?;
  match op {
    0x00 => Some((Vec::new(), rest)),
    0x01..=0x4b => {
      let n = op as usize;
      (rest.len() >= n).then(|| (rest[..n].to_vec(), &rest[n..]))
    }
    0x4c => {
      let (&n, rest) = rest.split_first()?;
      let n = n as usize;
      (rest.len() >= n).then(|| (rest[..n].to_vec(), &rest[n..]))
    }
    0x4d => {
      if rest.len() < 2 {
        return None;
      }
      let n = u16::from_le_bytes([rest[0], rest[1]]) as usize;
      let rest = &rest[2..];
      (rest.len() >= n).then(|| (rest[..n].to_vec(), &rest[n..]))
    }
    0x4e => {
      if rest.len() < 4 {
        return None;
      }
      let n = u32::from_le_bytes([rest[0], rest[1], rest[2], rest[3]]) as usize;
      let rest = &rest[4..];
      (rest.len() >= n).then(|| (rest[..n].to_vec(), &rest[n..]))
    }
    0x4f => Some((vec![0x81], rest)),
    0x51..=0x60 => Some((vec![op - 0x50], rest)),
    _ => None,
  }
}

/// Every value a push-only script leaves, or `None` when it has anything but pushes.
fn pushes(mut s: &[u8]) -> Option<Vec<Vec<u8>>> {
  let mut out = Vec::new();
  while !s.is_empty() {
    let (v, rest) = next_push(s)?;
    out.push(v);
    s = rest;
  }
  Some(out)
}

/// A small number as a push leaves it (empty = 0).
fn small_number(v: &[u8]) -> Option<u64> {
  match v.len() {
    0 => Some(0),
    1..=4 if v.last().is_some_and(|&b| b & 0x80 == 0) => Some(v.iter().rev().fold(0u64, |n, &b| (n << 8) | b as u64)),
    _ => None,
  }
}

/// The envelope pushes hold a whole inscription: `ord <parts> <mime> (<countdown> <chunk>)×parts`
/// with the countdown going down to 0, or the classic `ord <mime> 0 <body>`.
fn whole_envelope(data: &[Vec<u8>]) -> bool {
  if data.first().map(Vec::as_slice) != Some(b"ord".as_slice()) {
    return false;
  }
  if let Some(parts) = data.get(1).and_then(|v| small_number(v)) {
    let parts = parts as usize;
    if parts >= 1 && data.len() == 3 + 2 * parts {
      let downs_ok = (0..parts).all(|i| small_number(&data[3 + 2 * i]) == Some((parts - 1 - i) as u64));
      if downs_ok {
        return true;
      }
    }
  }
  data.len() == 4 && small_number(&data[2]) == Some(0)
}

/// committed-envelope.md §2–§3: `<pubkey33> OP_CHECKSIGVERIFY`, then for each data push, last
/// pushed first, `<literal> OP_EQUALVERIFY` (0–20 bytes) or `OP_HASH160 <h> OP_EQUALVERIFY`
/// (longer), each matching, then `OP_TRUE`.
fn committed_redeem(redeem: &[u8], data: &[Vec<u8>]) -> bool {
  if redeem.len() < 36 || redeem[0] != 0x21 || redeem[34] != 0xad {
    return false;
  }
  let mut rest = &redeem[35..];
  for item in data.iter().rev() {
    if item.len() <= 20 {
      let Some((v, after)) = next_push(rest) else { return false };
      if &v != item || after.first() != Some(&0x88) {
        return false;
      }
      rest = &after[1..];
    } else {
      if rest.len() < 23 || rest[0] != 0xa9 || rest[1] != 0x14 || rest[22] != 0x88 || rest[2..22] != hash160(item) {
        return false;
      }
      rest = &rest[23..];
    }
  }
  rest == [0x51]
}

/// committed-envelope.md §3: `vin[0].scriptSig` is push-only, ends `<sig> <redeem>`, holds the whole
/// inscription, and the redeem is the committed lock over exactly the pushes before `<sig>`.
pub fn is_bound(script_sig: &[u8]) -> bool {
  let Some(items) = pushes(script_sig) else { return false };
  if items.len() < 3 {
    return false;
  }
  let (data, tail) = items.split_at(items.len() - 2);
  whole_envelope(data) && committed_redeem(&tail[1], data)
}

// ---------------------------------------------------------------- bitwork --

/// What a JSON register claims about its txids (absent: no claim).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Bitwork {
  pub c: Option<String>,
  pub r: Option<String>,
}

impl Bitwork {
  /// `bitworkc` / `bitworkr` of a JSON body; a value that isn't a string is a claim nothing meets.
  pub(crate) fn of(obj: &serde_json::Map<String, Value>) -> Bitwork {
    let get = |k: &str| obj.get(k).map(|v| v.as_str().map(str::to_string).unwrap_or_default());
    Bitwork { c: get("bitworkc"), r: get("bitworkr") }
  }
  pub fn is_empty(&self) -> bool {
    self.c.is_none() && self.r.is_none()
  }
}

/// Does `txid` meet a bitwork claim: a lowercase hex prefix, optionally `.N` (0–15), the hex digit
/// after the prefix being at least N (the Atomicals form). Anything else is a claim nothing meets.
pub fn bitwork_meets(claim: &str, txid: &str) -> bool {
  let (prefix, ext) = match claim.split_once('.') {
    Some((p, n)) => match n.parse::<u32>() {
      Ok(n) if n <= 15 && !n.to_string().is_empty() => (p, Some(n)),
      _ => return false,
    },
    None => (claim, None),
  };
  if prefix.is_empty() || prefix.len() > 64 || !prefix.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)) {
    return false;
  }
  let txid = txid.to_ascii_lowercase();
  if !txid.starts_with(prefix) {
    return false;
  }
  match ext {
    None => true,
    Some(n) => txid[prefix.len()..].chars().next().and_then(|c| c.to_digit(16)).is_some_and(|d| d >= n),
  }
}

// ------------------------------------------------------------ with a node --

fn reveal_txid(id: &str) -> &str {
  id.split('i').next().unwrap_or(id)
}

/// Tests: reveal transactions by txid (`vin[0]` scriptSig, the commit it spends, where that
/// commit is), read instead of the node. A txid not here is a classic reveal.
#[cfg(test)]
pub(crate) static TEST_REVEALS: std::sync::Mutex<Option<HashMap<String, (Vec<u8>, u32, Pos)>>> = std::sync::Mutex::new(None);

/// A register's key (and whether it came from its commit). `made` is where the inscription was
/// made (its reveal; for one in several pieces, its last piece — never bound).
pub(crate) async fn key_of(tracer: &mut Tracer<'_>, id: &str, made: Pos) -> Result<(Key, bool)> {
  #[cfg(test)]
  {
    let _ = &tracer;
    let found = TEST_REVEALS.lock().unwrap().as_ref().and_then(|m| m.get(reveal_txid(id)).cloned());
    return Ok(match found {
      Some((sig, vout, commit)) if is_bound(&sig) && commit.0 <= made.0 && made.0 - commit.0 <= W => ((commit.0, commit.1, vout), true),
      _ => (reveal_key(made), false),
    });
  }
  #[allow(unreachable_code)]
  let tx = tracer.tx(reveal_txid(id)).await?;
  let Some((Some(prev), Some(vout), Some(sig_hex))) = tx.vin.first().cloned() else { return Ok((reveal_key(made), false)) };
  let Ok(sig) = hex::decode(&sig_hex) else { return Ok((reveal_key(made), false)) };
  if !is_bound(&sig) {
    return Ok((reveal_key(made), false));
  }
  let commit = tracer.position(&prev).await?;
  if commit.0 <= made.0 && made.0 - commit.0 <= W {
    Ok(((commit.0, commit.1, vout), true))
  } else {
    Ok((reveal_key(made), false))
  }
}

/// Whether a JSON register's bitwork claims hold (true when it makes none).
pub(crate) async fn bitwork_ok(tracer: &mut Tracer<'_>, id: &str, bw: &Bitwork) -> Result<bool> {
  if bw.is_empty() {
    return Ok(true);
  }
  let txid = reveal_txid(id);
  if let Some(r) = &bw.r {
    if !bitwork_meets(r, txid) {
      return Ok(false);
    }
  }
  if let Some(c) = &bw.c {
    let tx = tracer.tx(txid).await?;
    let commit = tx.vin.first().and_then(|v| v.0.clone()).unwrap_or_default();
    if !bitwork_meets(c, &commit) {
      return Ok(false);
    }
  }
  Ok(true)
}

/// A register made at `new_made` meets the one holding the name (made at `holder_made`, key
/// `holder_key` if known — filled in here when it had to be looked up). The newcomer's key when it
/// takes the name, `None` when it is a missed claim.
pub(crate) async fn contest(
  tracer: &mut Tracer<'_>,
  holder_id: &str,
  holder_made: Pos,
  holder_key: &mut Option<Key>,
  new_id: &str,
  new_made: Pos,
) -> Result<Option<Key>> {
  // the holder's key is at most its reveal, so after W more blocks it is final
  if new_made.0 > holder_made.0 + W {
    return Ok(None);
  }
  let (nk, _) = key_of(tracer, new_id, new_made).await?;
  if nk >= reveal_key(holder_made) {
    return Ok(None);
  }
  let hk = match *holder_key {
    Some(k) => k,
    None => {
      let k = key_of(tracer, holder_id, holder_made).await?.0;
      *holder_key = Some(k);
      k
    }
  };
  Ok(displaces(hk, nk, new_made.0).then_some(nk))
}

/// A name's key and whether it came from its commit, for the API: from the row when known,
/// looked up while the row could still be pending, otherwise its reveal (final either way).
pub(crate) async fn key_for_view(config: &Config, id: &str, made: Pos, stored: Option<Key>, tip: u64) -> (Key, bool) {
  if let Some(k) = stored {
    return (k, k != reveal_key(made));
  }
  if tip > made.0 + W {
    return (reveal_key(made), false);
  }
  let mut tracer = Tracer::new(config);
  key_of(&mut tracer, id, made).await.unwrap_or((reveal_key(made), false))
}

#[cfg(test)]
pub(crate) mod tests {
  use super::*;

  /// A committed reveal scriptSig for `pushes` (pubkey/signature placeholders: only the shape counts).
  pub(crate) fn committed_sig(data: &[Vec<u8>], tamper: bool) -> Vec<u8> {
    let push = |v: &[u8]| -> Vec<u8> {
      match v.len() {
        0 => vec![0x00],
        1 if (1..=16).contains(&v[0]) => vec![0x50 + v[0]],
        n if n <= 75 => [vec![n as u8], v.to_vec()].concat(),
        n => [vec![0x4c, n as u8], v.to_vec()].concat(),
      }
    };
    let mut redeem = vec![0x21];
    redeem.extend([2u8; 33]);
    redeem.push(0xad);
    for (i, item) in data.iter().enumerate().rev() {
      if item.len() <= 20 {
        let mut lit = item.clone();
        if tamper && i == data.len() - 1 {
          lit.push(b'x');
        }
        redeem.extend(push(&lit));
        redeem.push(0x88);
      } else {
        redeem.extend([0xa9, 0x14]);
        redeem.extend(hash160(item));
        redeem.push(0x88);
      }
    }
    redeem.push(0x51);
    let mut s = Vec::new();
    for d in data {
      s.extend(push(d));
    }
    s.extend(push(&[0x30; 71]));
    s.extend(push(&redeem));
    s
  }

  #[test]
  fn bound_reveals() {
    // multipart, one chunk: ord, parts 1, mime, countdown 0, body
    let one = vec![b"ord".to_vec(), vec![1], b"text/plain".to_vec(), vec![], b"@jon".to_vec()];
    assert!(is_bound(&committed_sig(&one, false)));
    assert!(!is_bound(&committed_sig(&one, true)), "a literal that doesn't match its push");
    // a long body is checked by its hash
    let long = vec![b"ord".to_vec(), vec![1], b"application/json".to_vec(), vec![], br#"{"p":"at","op":"reg","name":"jon","url":"https://dogecoin.dog"}"#.to_vec()];
    assert!(is_bound(&committed_sig(&long, false)));
    // classic single chunk: ord, mime, 0, body
    let classic = vec![b"ord".to_vec(), b"text/plain".to_vec(), vec![], b"jon.doge".to_vec()];
    assert!(is_bound(&committed_sig(&classic, false)));
    // only part of a body in this reveal: parts 2 with one chunk
    let partial = vec![b"ord".to_vec(), vec![2], b"text/plain".to_vec(), vec![1], b"@jo".to_vec()];
    assert!(!is_bound(&committed_sig(&partial, false)));
    // the classic doginals.js redeem (<pubkey> CHECKSIGVERIFY DROP×n TRUE) is not bound
    let mut s = Vec::new();
    for d in &one {
      s.extend(match d.len() { 0 => vec![0], 1 => vec![0x50 + d[0]], n => [vec![n as u8], d.clone()].concat() });
    }
    let mut redeem = vec![0x21];
    redeem.extend([2u8; 33]);
    redeem.push(0xad);
    redeem.extend([0x75; 5]);
    redeem.push(0x51);
    s.extend([71u8]);
    s.extend([0x30; 71]);
    s.push(redeem.len() as u8);
    s.extend(redeem);
    assert!(!is_bound(&s));
    assert!(!is_bound(&[0x6a, 0x01, 0x02]), "not push-only");
  }

  #[test]
  fn bitwork() {
    let tx = "0000a1b2c3d4e5f60718293a4b5c6d7e8f90a1b2c3d4e5f60718293a4b5c6d7e";
    assert!(bitwork_meets("0", tx));
    assert!(bitwork_meets("0000", tx));
    assert!(!bitwork_meets("0000000000", tx), "the spec's void vector");
    assert!(bitwork_meets("0000.10", tx), "next digit a (10) >= 10");
    assert!(!bitwork_meets("0000.11", tx));
    assert!(!bitwork_meets("", tx) && !bitwork_meets("zz", tx) && !bitwork_meets("0.16", tx) && !bitwork_meets("00X", tx));
  }

  /// The ranking table of DNS spec §5.7 and the sequences of its conformance vectors.
  #[test]
  fn ranking_vectors() {
    let commit = |h: u64, tx: u32| (h, tx, 0);
    let reveal = |h: u64, tx: u32| reveal_key((h, tx));
    // a committed reveal ranks by its commit when it came within W blocks
    let key = |commit_h: u64, commit_tx: u32, reveal_h: u64, reveal_tx: u32, bound: bool| {
      if bound && reveal_h - commit_h <= W { commit(commit_h, commit_tx) } else { reveal(reveal_h, reveal_tx) }
    };
    // Mempool copy: A commits at 1 (committed), B copies with a classic reveal at 2, A reveals at 3
    assert!(displaces(reveal(2, 0), key(1, 0, 3, 0, true), 3), "A wins");
    // Late commit: A commits+reveals at 1, B at 2
    assert!(!displaces(key(1, 0, 1, 1, true), key(2, 0, 2, 1, true), 2));
    // Slow reveal: A commits at 1, reveals at 33 (> W): ranks by its reveal; B revealed at 2
    assert!(!displaces(reveal(2, 0), key(1, 0, 33, 0, true), 33));
    // Classic vs classic
    assert!(!displaces(reveal(1, 0), reveal(2, 0), 2));
    // Same block commits: A at tx 1, B at tx 2, both reveal at 2 (A first in the block)
    assert!(!displaces(key(1, 1, 2, 0, true), key(1, 2, 2, 1, true), 2));
    // B revealed first in the block but A's commit is earlier
    assert!(displaces(key(1, 2, 2, 0, true), key(1, 1, 2, 1, true), 2));
    // Window edge: commit 1, reveal 31 = 1 + W ranks by commit; reveal 32 by its reveal
    assert_eq!(key(1, 0, 31, 0, true), commit(1, 0));
    assert_eq!(key(1, 0, 32, 0, true), reveal(32, 0));
    // Replay, committed (vector replay-committed-reveal-wins): B classic at 100, A commit 99 reveal 110
    assert!(displaces(reveal(100, 5), key(99, 2, 110, 3, true), 110));
    // replay-classic-reveal-ranks-by-reveal
    assert!(!displaces(reveal(100, 5), key(99, 2, 110, 3, false), 110));
    // slow-committed-reveal-ranks-by-reveal: A commit 99 reveal 131
    assert!(!displaces(reveal(100, 5), key(99, 2, 131, 3, true), 131));
    // a final row is never displaced, whatever the key
    assert!(!displaces(reveal(100, 5), commit(1, 0), 131));
    assert_eq!(status(reveal(100, 5), 130), "pending");
    assert_eq!(status(reveal(100, 5), 131), "final");
  }
}
