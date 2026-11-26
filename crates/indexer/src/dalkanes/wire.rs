//! Dalkanes wire format: `0xD1` OP_RETURN messages (spec §5, §16) and deploy bodies (§4).

use std::io::Read;

use super::vm::Id;

pub const MAGIC: u8 = 0xD1;
/// Edict output meaning "deposit into the call" (§16).
pub const DEPOSIT_VOUT: u32 = u32::MAX - 1;
pub const NO_POINTER: u32 = u32::MAX;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cellpack {
  pub target: Id,
  pub fuel: u64,
  pub inputs: Vec<u128>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Edict {
  pub token: Id,
  pub amount: u128,
  pub output: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Message {
  /// Version 0x01: a contract call.
  Call(Cellpack),
  /// Version 0x02: parcel edicts, with an optional call.
  Parcel { pointer: u32, edicts: Vec<Edict>, call: Option<Cellpack> },
}

/// What a transaction's outputs say (§5.1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TxMessage {
  /// No `0xD1` output.
  None,
  /// Exactly one, and it decodes.
  One { vout: u32, message: Message },
  /// One that does not decode, or more than one: no call, input parcels burn.
  Ambiguous,
}

/// Data pushes after OP_RETURN. `Err(true)` when a push runs past the end, with the pushes read so
/// far (the first one may be partial, which still marks a `0xD1` output).
fn pushes(script: &[u8]) -> (Vec<Vec<u8>>, bool, Option<Vec<u8>>) {
  let mut out = Vec::new();
  let mut i = 1;
  while i < script.len() {
    let op = script[i];
    let (len, hdr) = match op {
      0x00..=0x4b => (op as usize, 1),
      0x4c => match script.get(i + 1) {
        Some(&n) => (n as usize, 2),
        None => return (out, true, Some(Vec::new())),
      },
      0x4d => match script.get(i + 1..i + 3) {
        Some(b) => (u16::from_le_bytes([b[0], b[1]]) as usize, 3),
        None => return (out, true, Some(Vec::new())),
      },
      _ => break,
    };
    let start = i + hdr;
    if start + len > script.len() {
      let partial = script.get(start..).unwrap_or(&[]).to_vec();
      return (out, true, Some(partial));
    }
    out.push(script[start..start + len].to_vec());
    i = start + len;
  }
  (out, false, None)
}

/// Whether this output is a `0xD1` output: OP_RETURN whose first push is `D1` or begins with it.
pub fn is_d1_output(script: &[u8]) -> bool {
  if script.first() != Some(&0x6a) {
    return false;
  }
  let (ps, _, partial) = pushes(script);
  let first = ps.first().cloned().or(partial);
  matches!(first, Some(p) if p.first() == Some(&MAGIC))
}

/// Version byte and the bytes after it, for forms A, B and C.
fn version_and_body(script: &[u8]) -> Option<(u8, Vec<u8>)> {
  let (ps, truncated, _) = pushes(script);
  if truncated {
    return None;
  }
  let p0 = ps.first()?;
  if p0.first() != Some(&MAGIC) {
    return None;
  }
  if p0.len() > 1 {
    // form A: D1 ver ‖ body
    return Some((p0[1], p0[2..].to_vec()));
  }
  let p1 = ps.get(1)?;
  if p1.len() == 1 {
    // form B: D1, ver, body
    return Some((p1[0], ps.get(2)?.clone()));
  }
  // form C: D1, ver ‖ body
  Some((*p1.first()?, p1[1..].to_vec()))
}

struct Reader<'a> {
  b: &'a [u8],
  i: usize,
}

impl Reader<'_> {
  /// An unsigned LEB128 of at most 128 bits (§5.2).
  fn varint(&mut self) -> Option<u128> {
    let mut v: u128 = 0;
    for n in 0..19 {
      let byte = *self.b.get(self.i)?;
      self.i += 1;
      if n == 18 && (byte & 0x80 != 0 || byte & 0x7f > 0x03) {
        return None;
      }
      v |= ((byte & 0x7f) as u128) << (7 * n);
      if byte & 0x80 == 0 {
        return Some(v);
      }
    }
    None
  }
  fn u64(&mut self) -> Option<u64> {
    u64::try_from(self.varint()?).ok()
  }
  fn u32(&mut self) -> Option<u32> {
    u32::try_from(self.varint()?).ok()
  }
}

fn cellpack(r: &mut Reader) -> Option<Cellpack> {
  let block = r.u64()?;
  let tx = r.u32()?;
  let fuel = r.varint()?.min(u64::MAX as u128) as u64;
  let n = r.varint()?;
  if n > 256 {
    return None;
  }
  let mut inputs = Vec::with_capacity(n as usize);
  for _ in 0..n {
    inputs.push(r.varint()?);
  }
  Some(Cellpack { target: (block, tx), fuel, inputs })
}

pub fn decode_cellpack(b: &[u8]) -> Option<Cellpack> {
  cellpack(&mut Reader { b, i: 0 })
}

/// Decodes one `0xD1` output into a message, or `None` if it does not decode.
pub fn decode_message(script: &[u8]) -> Option<Message> {
  let (ver, body) = version_and_body(script)?;
  let mut r = Reader { b: &body, i: 0 };
  match ver {
    0x01 => Some(Message::Call(cellpack(&mut r)?)),
    0x02 => {
      let pointer = r.u32()?;
      let n = r.varint()?;
      if n > 16 {
        return None;
      }
      let mut edicts = Vec::new();
      for _ in 0..n {
        let block = r.u64()?;
        let tx = r.u32()?;
        let amount = r.varint()?;
        let output = r.u32()?;
        edicts.push(Edict { token: (block, tx), amount, output });
      }
      let call = match r.varint()? {
        0 => None,
        1 => Some(cellpack(&mut r)?),
        _ => return None,
      };
      Some(Message::Parcel { pointer, edicts, call })
    }
    _ => None,
  }
}

/// Reads a transaction's message from its output scripts (§5.1).
pub fn tx_message(outputs: &[&[u8]]) -> TxMessage {
  let d1: Vec<usize> = outputs.iter().enumerate().filter(|(_, s)| is_d1_output(s)).map(|(i, _)| i).collect();
  match d1.len() {
    0 => TxMessage::None,
    1 => match decode_message(outputs[d1[0]]) {
      Some(message) => TxMessage::One { vout: d1[0] as u32, message },
      None => TxMessage::Ambiguous,
    },
    _ => TxMessage::Ambiguous,
  }
}

// ---- deploys (§4)

const ALK: &[u8] = b"\0ALK";
const ASM: &[u8] = b"\0asm";
const GZ: &[u8] = &[0x1f, 0x8b];

fn find(h: &[u8], n: &[u8]) -> Option<usize> {
  h.windows(n.len()).position(|w| w == n)
}

/// Whether an inscription is a deploy candidate (§4.1).
pub fn is_candidate(content_type: &str, body: &[u8]) -> bool {
  let ct = content_type.to_ascii_lowercase();
  ct.contains("wasm") || ct.contains("alkane") || find(body, ALK).is_some() || find(body, ASM).is_some()
}

/// Decodes a deploy body into code (§4.2), or `None` if it is not a deploy.
pub fn deploy_code(content_type: &str, body: &[u8]) -> Option<Vec<u8>> {
  if !is_candidate(content_type, body) {
    return None;
  }
  let start = if body.starts_with(ALK) || body.starts_with(ASM) || body.starts_with(GZ) {
    0
  } else {
    match (find(body, ALK), find(body, ASM)) {
      (Some(a), Some(b)) => a.min(b),
      (Some(a), None) => a,
      (None, Some(b)) => b,
      (None, None) => return None,
    }
  };
  let s = &body[start..];
  let payload = if s.starts_with(ALK) && s.len() >= 5 {
    if s[4] != 0x01 {
      return None;
    }
    &s[5..]
  } else {
    s
  };
  let code = if content_type.to_ascii_lowercase().contains("gzip") || payload.starts_with(GZ) {
    let mut out = Vec::new();
    let mut d = flate2::read::GzDecoder::new(payload).take(MAX_INFLATE as u64 + 1);
    d.read_to_end(&mut out).ok()?;
    if out.len() > MAX_INFLATE {
      return None;
    }
    out
  } else {
    payload.to_vec()
  };
  if code.len() < 4 || code.len() > MAX_INFLATE || !code.starts_with(ASM) {
    return None;
  }
  Some(code)
}

const MAX_INFLATE: usize = super::vm::MAX_CODE;

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn parser_vectors() {
    let v: serde_json::Value = serde_json::from_str(include_str!("vectors/parser.json")).unwrap();
    for c in v["cases"].as_array().unwrap() {
      let s = hex::decode(c["script_hex"].as_str().unwrap()).unwrap();
      let m = decode_message(&s);
      let valid = c["valid"].as_bool().unwrap();
      assert_eq!(matches!(m, Some(Message::Call(_))), valid, "{}", c["name"]);
      if let Some(Message::Call(cp)) = m {
        assert_eq!(format!("{}:{}", cp.target.0, cp.target.1), c["target"].as_str().unwrap());
        assert_eq!(cp.fuel.to_string(), c["fuel"].as_str().unwrap());
      }
    }
  }

  #[test]
  fn wire_vectors() {
    let v: serde_json::Value = serde_json::from_str(include_str!("vectors/wire.json")).unwrap();
    for c in v["cellpacks"].as_array().unwrap() {
      let s = hex::decode(c["script_hex"].as_str().unwrap()).unwrap();
      let Some(Message::Call(cp)) = decode_message(&s) else { panic!("{}", c["name"]) };
      let want = &c["cellpack"];
      assert_eq!(cp.target.0.to_string(), want["target_block"].as_str().unwrap());
      assert_eq!(cp.fuel.to_string(), want["fuel"].as_str().unwrap());
      let cd = crate::dalkanes::vm::calldata(&cp.inputs);
      assert_eq!(hex::encode(cd), c["calldata_hex"].as_str().unwrap());
    }
  }

  #[test]
  fn live_howl_call() {
    let s = hex::decode("6a0dd101e2928b0323c09a0c024d01").unwrap();
    let Some(Message::Call(cp)) = decode_message(&s) else { panic!() };
    assert_eq!(cp.target, (6474082, 35));
    assert_eq!(cp.fuel, 200_000);
    assert_eq!(cp.inputs, vec![77, 1]);
  }
}
