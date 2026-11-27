//! The verified sender of a call (spec §6.5) and BIP-340 checks for `verify_schnorr` (§7.4).

use ripemd::Ripemd160;
use secp256k1::{ecdsa, schnorr, Message, PublicKey, Secp256k1, XOnlyPublicKey};
use sha2::{Digest, Sha256};

pub struct TxIn {
  pub prev: [u8; 36],
  pub script_sig: Vec<u8>,
  pub sequence: u32,
}

pub struct RawTx {
  pub version: i32,
  pub inputs: Vec<TxIn>,
  /// Serialized outputs (value ‖ script), exactly as in the transaction.
  pub outputs_raw: Vec<u8>,
  pub n_outputs: u64,
  pub lock_time: u32,
}

fn varint(b: &[u8], i: &mut usize) -> Option<u64> {
  let f = *b.get(*i)?;
  *i += 1;
  let n = match f {
    0xfd => 2,
    0xfe => 4,
    0xff => 8,
    _ => return Some(f as u64),
  };
  let s = b.get(*i..*i + n)?;
  *i += n;
  let mut v = [0u8; 8];
  v[..n].copy_from_slice(s);
  Some(u64::from_le_bytes(v))
}

pub(crate) fn put_varint(out: &mut Vec<u8>, n: u64) {
  match n {
    0..=0xfc => out.push(n as u8),
    0xfd..=0xffff => {
      out.push(0xfd);
      out.extend_from_slice(&(n as u16).to_le_bytes());
    }
    0x10000..=0xffff_ffff => {
      out.push(0xfe);
      out.extend_from_slice(&(n as u32).to_le_bytes());
    }
    _ => {
      out.push(0xff);
      out.extend_from_slice(&n.to_le_bytes());
    }
  }
}

pub fn parse_tx(b: &[u8]) -> Option<RawTx> {
  let mut i = 0;
  let version = i32::from_le_bytes(b.get(0..4)?.try_into().ok()?);
  i += 4;
  let nin = varint(b, &mut i)?;
  let mut inputs = Vec::new();
  for _ in 0..nin {
    let prev: [u8; 36] = b.get(i..i + 36)?.try_into().ok()?;
    i += 36;
    let l = varint(b, &mut i)? as usize;
    let script_sig = b.get(i..i + l)?.to_vec();
    i += l;
    let sequence = u32::from_le_bytes(b.get(i..i + 4)?.try_into().ok()?);
    i += 4;
    inputs.push(TxIn { prev, script_sig, sequence });
  }
  let n_outputs = varint(b, &mut i)?;
  let start = i;
  for _ in 0..n_outputs {
    i += 8;
    let l = varint(b, &mut i)? as usize;
    i += l;
  }
  let outputs_raw = b.get(start..i)?.to_vec();
  let lock_time = u32::from_le_bytes(b.get(i..i + 4)?.try_into().ok()?);
  Some(RawTx { version, inputs, outputs_raw, n_outputs, lock_time })
}

/// Legacy signature hash for input 0 with `script_code`, for SIGHASH_ALL with or without ANYONECANPAY.
pub(crate) fn sighash_all_input0(tx: &RawTx, script_code: &[u8], hash_type: u32) -> [u8; 32] {
  let anyone = hash_type & 0x80 != 0;
  let mut s = Vec::with_capacity(256);
  s.extend_from_slice(&tx.version.to_le_bytes());
  let ins: Vec<&TxIn> = if anyone { tx.inputs.iter().take(1).collect() } else { tx.inputs.iter().collect() };
  put_varint(&mut s, ins.len() as u64);
  for (n, inp) in ins.iter().enumerate() {
    s.extend_from_slice(&inp.prev);
    if n == 0 {
      put_varint(&mut s, script_code.len() as u64);
      s.extend_from_slice(script_code);
    } else {
      s.push(0);
    }
    s.extend_from_slice(&inp.sequence.to_le_bytes());
  }
  put_varint(&mut s, tx.n_outputs);
  s.extend_from_slice(&tx.outputs_raw);
  s.extend_from_slice(&tx.lock_time.to_le_bytes());
  s.extend_from_slice(&hash_type.to_le_bytes());
  let h1 = Sha256::digest(&s);
  Sha256::digest(h1).into()
}

/// Exactly two pushes, `<sig> <pubkey>`.
fn two_pushes(script: &[u8]) -> Option<(Vec<u8>, Vec<u8>)> {
  let mut out = Vec::new();
  let mut i = 0;
  while i < script.len() {
    let op = script[i];
    let (len, hdr) = match op {
      0x01..=0x4b => (op as usize, 1),
      0x4c => (*script.get(i + 1)? as usize, 2),
      0x4d => (u16::from_le_bytes([*script.get(i + 1)?, *script.get(i + 2)?]) as usize, 3),
      _ => return None,
    };
    let s = script.get(i + hdr..i + hdr + len)?;
    out.push(s.to_vec());
    i += hdr + len;
  }
  if out.len() != 2 {
    return None;
  }
  let k = out.pop()?;
  let s = out.pop()?;
  Some((s, k))
}

pub fn hash160(b: &[u8]) -> [u8; 20] {
  Ripemd160::digest(Sha256::digest(b)).into()
}

/// The verified sender (§6.5): HASH160 of the key that signed input 0 as a P2PKH spend, SIGHASH_ALL.
pub fn sender(raw: &[u8]) -> Option<[u8; 20]> {
  let tx = parse_tx(raw)?;
  let (sig, key) = two_pushes(&tx.inputs.first()?.script_sig)?;
  if key.len() != 33 && key.len() != 65 {
    return None;
  }
  let (&ht, der) = sig.split_last()?;
  if ht & 0x1f != 0x01 || ht & !0x9f != 0 {
    return None;
  }
  let pk = PublicKey::from_slice(&key).ok()?;
  let mut s = ecdsa::Signature::from_der_lax(der).ok()?;
  s.normalize_s();
  let h = hash160(&key);
  let mut code = vec![0x76, 0xa9, 0x14];
  code.extend_from_slice(&h);
  code.extend_from_slice(&[0x88, 0xac]);
  let digest = sighash_all_input0(&tx, &code, ht as u32);
  let msg = Message::from_digest_slice(&digest).ok()?;
  Secp256k1::verification_only().verify_ecdsa(&msg, &s, &pk).ok()?;
  Some(h)
}

/// BIP-340 verification of a 64-byte signature over a 32-byte message.
pub fn verify_schnorr(msg: &[u8], pk: &[u8], sig: &[u8]) -> bool {
  let (Ok(m), Ok(k), Ok(s)) = (Message::from_digest_slice(msg), XOnlyPublicKey::from_slice(pk), schnorr::Signature::from_slice(sig)) else {
    return false;
  };
  Secp256k1::verification_only().verify_schnorr(&s, &m, &k).is_ok()
}
