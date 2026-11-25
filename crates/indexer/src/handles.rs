//! @ — Dogecoin handles, following <https://github.com/jonheaven/at>
//! (`spec.md`, launch draft of 2026-11-24), checked against that spec's
//! `vectors/conformance.json` in the tests below.
//!
//! `@jon` is a Doginal. The first valid register of a handle wins; whoever
//! holds that inscription's output owns the handle, and spending the output
//! transfers it. A sibling of DNS, with its own `at_*` trees: DNS, Ð𝕏 and ÐN05
//! bodies never make an @ row and an @ body never makes one of theirs.
//!
//! Three kinds of inscription matter (spec §5):
//!
//!  - a register: the plain-text body `@jon` and nothing else (one trailing
//!    newline allowed, fullwidth folded, 1–15 of `a-z 0-9 _`), or JSON
//!    `{"p":"at","op":"register"|"reg","name":"@jon"|"jon",...records}`;
//!  - a config: JSON `{"p":"at","op":"config"|"update"|"upd",...}` (or `p`, a
//!    name and record fields with no `op`), counted only when made by the
//!    handle's holder, after every spend in its transaction;
//!  - a primary: JSON `{"p":"at","op":"primary","name":...}`, the one handle an
//!    address wears (`""` clears it), counted only from the holder.
//!
//! Emoji (spec ba673a0, 2026-11-25): a localpart is 1 to 15 characters, each `a-z 0-9 _`, one
//! Extended_Pictographic scalar, or a flag (two regional indicators, one character), mixed in any
//! order: `@jon🐕`, `@🐕🐕`, `@🇺🇸`. Variation selectors (U+FE0E/FE0F) are stripped.
//!
//! **Extension (DPAYMARKET, the operator's call):** this index also takes ZWJ sequences (`@👨‍🚀`),
//! skin tones (`@👍🏽`), keycaps and subdivision flags, each counted as one symbol. The spec says
//! those are not handles, so other @ indexers don't count them: responses mark them
//! `inSpec: false`. Letters of other scripts are refused either way.
//!
//! Order (§5.6): registers rank by where their reveal is in the chain (height,
//! then place in block); a register made in several pieces counts from its
//! last. The spec's commit-first key for "committed reveals" points at DNS
//! §5.7, which is not published (DNS stops at v1.2), and no committed redeem
//! format is defined, so every register ranks by its reveal — the "every
//! other register" case of §5.6 — and every row is final. `bitworkc` /
//! `bitworkr` (also defined by that missing section) are not checked.
//!
//! Built like the DNS index: follows `inscription_seq` in chain order as far
//! as numbering has gone, one atomic batch per step with its cursor, undo
//! records near the tip ([`undo_from`]), cleared when numbering starts over.
//! Who held an inscription at a past point comes from DNS's tracer.

use super::*;
use crate::dns::{self, ClaimEntry, ConfigEntry, DnsRecords, Pos, PrimaryEntry, RecordPatch, Tracer};
use crate::insc_index as ii;
use crate::store::{Batch, Tree};
use std::sync::Mutex;
use unicode_properties::emoji::UnicodeEmoji;
use crate::ext_pict::is_extended_pictographic;
use crate::priority::{self, Bitwork, Key};

/// Confirmations a block needs before its handles are read.
pub const AT_CONFIRMATIONS: u64 = 1;
/// How many blocks back a reorg can be undone.
const UNDO_BLOCKS: u64 = 100;
/// Longest localpart (spec §3).
pub const HANDLE_MAX_LEN: usize = 15;

static AT_WRITE: Mutex<()> = Mutex::new(());
/// v6: spec v1.1 (5c8dcc2) with commit-first priority and bitwork (§5.6), plus the wider character extension; earlier rows are read again.
const STATE_KEY: &[u8] = b"at_index_v6";
const REORG_GEN_KEY: &[u8] = b"at_reorg_gen";
const TREES: [&str; 9] = ["at_name", "at_by_inscription", "at_index", "at_len_index", "at_claims", "at_config", "at_primary", "at_stats", "at_undo"];
/// The first handles index (2026-11-24, before this spec was followed): its
/// trees are emptied once.
const OLD_TREES: [&str; 6] = ["handle_name", "handle_by_inscription", "handle_index", "handle_claims", "handle_stats", "handle_undo"];
const OLD_KEYS: [&[u8]; 2] = [b"handles_index_v1", b"handles_reorg_gen"];
/// Earlier @ index rules: read again from the start under these.
const EARLIER_KEYS: [&[u8]; 5] = [b"at_index_v1", b"at_index_v2", b"at_index_v3", b"at_index_v4", b"at_index_v5"];

fn reorg_gen(meta: &Tree) -> Result<u64> {
  Ok(ii::meta_u64(meta, REORG_GEN_KEY)?.unwrap_or(0))
}

// ---------------------------------------------------------------- handles --

fn fold_fullwidth(s: &str) -> String {
  s.chars()
    .map(|c| {
      let u = c as u32;
      if (0xFF01..=0xFF5E).contains(&u) { char::from_u32(u - 0xFEE0).unwrap_or(c) } else { c }
    })
    .collect()
}

/// Spec §6: fullwidth fold, ASCII lowercase, one leading `@`, localpart
/// `[a-z0-9_]{1,15}`. Returns the canonical `@jon`. `missing_at_ok`: the JSON
/// `name` field (and lookups) may leave the `@` out; plain text may not.
///
/// The spec's rules (and the emoji extension) are tried first, exactly as before. Only what
/// they turn down is read under the wider extension ([`fold_wide`]), and a spelling that the
/// wider rules would fold into a handle of the spec (a Kelvin sign for `k`, say) is refused:
/// the extension adds handles, it never claims one the spec defines.
pub fn normalize_handle(input: &str, missing_at_ok: bool) -> Option<String> {
  let s = fold_fullwidth(input);
  let local = match s.strip_prefix('@') {
    Some(l) => l,
    None if missing_at_ok => s.as_str(),
    None => return None,
  };
  if let Some((folded, units)) = fold_localpart(local) {
    return (1..=HANDLE_MAX_LEN).contains(&units).then(|| format!("@{folded}"));
  }
  let (folded, units) = fold_wide(local)?;
  let h = format!("@{folded}");
  ((1..=HANDLE_MAX_LEN).contains(&units) && !handle_in_spec(&h)).then_some(h)
}

/// Most combining marks one letter may carry (no stacks of marks).
const MAX_MARKS: usize = 4;

/// The wider extension (DPAYMARKET, 2026-11-25): every kind of character a name is written
/// with, not only `a-z 0-9 _` and emoji —
///  - letters of any script, lowercased (`@Élodie` → `@élodie`, `@жон`, `@太郎`), all from one
///    script (plus `a-z`, which is Latin): `@bіlly` with a Cyrillic `і` is refused;
///  - combining marks on a letter (at most [`MAX_MARKS`]), counted with it;
///  - digits and numbers of any script (`@٣`, `@Ⅻ`), symbols (`@₿illy`, `@€uro`, `@∞`, `@♛`)
///    and non-ASCII punctuation (`@「jon」`);
///  - emoji as in [`fold_localpart`].
/// Never: spaces, invisible or control characters, ASCII other than `a-z 0-9 _`, anything that
/// reads as `.`, `/` or `@`, or a letter whose lowercase is ASCII. NFC first, so `é` typed as
/// `e` + accent and as one character are the same handle.
fn fold_wide(local: &str) -> Option<(String, usize)> {
  use unicode_normalization::UnicodeNormalization;
  use unicode_properties::general_category::{GeneralCategory as G, GeneralCategoryGroup as GG, UnicodeGeneralCategory};
  use unicode_script::{Script, UnicodeScript};
  let nfc: String = local.nfc().collect();
  let chars: Vec<char> = nfc.chars().filter(|&c| c != '\u{FE0F}' && c != '\u{FE0E}').collect();
  if chars.len() > 64 {
    return None;
  }
  let (mut out, mut units) = (String::with_capacity(nfc.len()), 0usize);
  let mut script: Option<Script> = None;
  let mut same = |sc: Script| -> bool {
    match script {
      Some(s) if s != sc => false,
      _ => {
        script = Some(sc);
        true
      }
    }
  };
  let (mut open_flag, mut marks) = (false, 0usize);
  for (i, &c) in chars.iter().enumerate() {
    let prev = i.checked_sub(1).map(|j| chars[j]);
    let next = chars.get(i + 1).copied();
    let flag_half = is_regional(c) && open_flag;
    open_flag = is_regional(c) && !open_flag;
    if c.general_category_group() != GG::Mark {
      marks = 0;
    }
    if c.is_ascii() {
      if !(c.is_ascii_alphanumeric() || c == '_') {
        return None;
      }
      if c.is_ascii_alphabetic() && !same(Script::Latin) {
        return None;
      }
      out.push(c.to_ascii_lowercase());
      units += 1;
    } else if c == '\u{200D}' {
      if !(prev.is_some_and(is_emoji) && next.is_some_and(is_emoji)) {
        return None;
      }
      out.push(c);
    } else if c == '\u{20E3}' {
      if !prev.is_some_and(|p| p.is_ascii_digit()) {
        return None;
      }
      out.push(c);
    } else if is_skin_tone(c) && prev.is_some_and(|p| is_emoji(p) && !is_skin_tone(p)) {
      out.push(c);
    } else if is_tag(c) {
      if !prev.is_some_and(|p| is_emoji(p) || is_tag(p)) {
        return None;
      }
      out.push(c);
    } else if is_emoji(c) {
      out.push(c);
      if !flag_half && prev != Some('\u{200D}') {
        units += 1;
      }
    } else {
      if c.is_whitespace() || dns::is_default_ignorable(c) || dns::is_dot_or_slash_lookalike(c) || matches!(c, '\u{FE6B}' | '\u{FF20}' | '\u{E0040}') {
        return None;
      }
      match c.general_category_group() {
        GG::Letter => {
          let sc = c.script();
          if !matches!(sc, Script::Common | Script::Inherited | Script::Unknown) && !same(sc) {
            return None;
          }
          let lower: String = c.to_lowercase().collect();
          if lower.chars().any(|l| l.is_ascii()) {
            return None;
          }
          out.push_str(&lower);
          units += 1;
        }
        GG::Mark => {
          // only on something drawn before it
          marks += 1;
          if prev.is_none() || marks > MAX_MARKS {
            return None;
          }
          out.push(c);
        }
        GG::Number | GG::Symbol | GG::Punctuation => {
          // some have a lowercase too (Ⅻ → ⅻ, Ⓐ → ⓐ)
          let lower: String = c.to_lowercase().collect();
          if lower.chars().any(|l| l.is_ascii()) {
            return None;
          }
          out.push_str(&lower);
          units += 1;
        }
        // spaces, controls, format, private use, unassigned
        _ => return None,
      }
      if matches!(c.general_category(), G::PrivateUse | G::Unassigned | G::Surrogate) {
        return None;
      }
    }
  }
  if out.is_empty() || units == 0 {
    return None;
  }
  Some((out, units))
}

/// A handle with letters that look like plain `a-z` but aren't (all-Cyrillic `@аре`, say): kept,
/// and flagged so wallets and pages can warn before anyone pays it.
pub fn handle_confusable(handle: &str) -> bool {
  let l = handle.trim_start_matches('@');
  l.chars().any(|c| !c.is_ascii() && dns::ascii_lookalike(c)) && l.chars().all(|c| c.is_ascii() || dns::ascii_lookalike(c))
}

fn is_emoji(c: char) -> bool {
  !c.is_ascii() && (c.is_emoji_char() || is_extended_pictographic(c))
}
fn is_regional(c: char) -> bool {
  ('\u{1F1E6}'..='\u{1F1FF}').contains(&c)
}
fn is_skin_tone(c: char) -> bool {
  ('\u{1F3FB}'..='\u{1F3FF}').contains(&c)
}
fn is_tag(c: char) -> bool {
  ('\u{E0020}'..='\u{E007F}').contains(&c)
}

/// A localpart folded (ASCII lowercase, variation selectors dropped) and how many symbols it has:
/// `a-z 0-9 _` count one each (the spec), and so does each emoji with what joins onto it (the
/// extension). None when anything else is in it.
fn fold_localpart(local: &str) -> Option<(String, usize)> {
  let chars: Vec<char> = local.chars().filter(|&c| c != '\u{FE0F}' && c != '\u{FE0E}').collect();
  let (mut out, mut units) = (String::with_capacity(local.len()), 0usize);
  let mut open_flag = false;
  for (i, &c) in chars.iter().enumerate() {
    let prev = i.checked_sub(1).map(|j| chars[j]);
    let next = chars.get(i + 1).copied();
    let flag_half = is_regional(c) && open_flag;
    open_flag = is_regional(c) && !open_flag;
    if c.is_ascii() {
      if !(c.is_ascii_alphanumeric() || c == '_') {
        return None;
      }
      out.push(c.to_ascii_lowercase());
      units += 1;
    } else if c == '\u{200D}' {
      // a zero-width joiner only inside an emoji sequence
      if !(prev.is_some_and(is_emoji) && next.is_some_and(is_emoji)) {
        return None;
      }
      out.push(c);
    } else if c == '\u{20E3}' {
      // keycap: a digit before it (counted already)
      if !prev.is_some_and(|p| p.is_ascii_digit()) {
        return None;
      }
      out.push(c);
    } else if is_skin_tone(c) && prev.is_some_and(|p| is_emoji(p) && !is_skin_tone(p)) {
      out.push(c);
    } else if is_tag(c) {
      // subdivision flags: tag characters after a waving black flag
      if !prev.is_some_and(|p| is_emoji(p) || is_tag(p)) {
        return None;
      }
      out.push(c);
    } else if is_emoji(c) {
      out.push(c);
      // the second half of a flag, or the emoji after a joiner, belongs to the symbol before it
      if !flag_half && prev != Some('\u{200D}') {
        units += 1;
      }
    } else {
      return None;
    }
  }
  if out.is_empty() {
    return None;
  }
  Some((out, units))
}

/// A handle with emoji in it (spec or extension).
pub fn handle_is_emoji(handle: &str) -> bool {
  !handle.is_ascii()
}

/// Is a canonical handle one the spec defines (§6, ba673a0)? Each character `a-z 0-9 _`, one
/// Extended_Pictographic scalar, or a flag (two regional indicators); 1 to 15 of them. ZWJ
/// sequences, skin tones, keycaps and tag flags are this index's extension.
pub fn handle_in_spec(handle: &str) -> bool {
  let cs: Vec<char> = handle.trim_start_matches('@').chars().collect();
  let (mut i, mut count) = (0, 0usize);
  while i < cs.len() {
    let c = cs[i];
    if c.is_ascii() {
      if !(c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_') {
        return false;
      }
      i += 1;
    } else if is_regional(c) {
      if !cs.get(i + 1).is_some_and(|&d| is_regional(d)) {
        return false;
      }
      i += 2;
    } else if is_extended_pictographic(c) {
      i += 1;
    } else {
      return false;
    }
    count += 1;
  }
  (1..=HANDLE_MAX_LEN).contains(&count)
}

/// The localpart's length, in symbols, of a canonical handle.
fn len_of(handle: &str) -> usize {
  let l = handle.trim_start_matches('@');
  fold_localpart(l).or_else(|| fold_wide(l)).map(|(_, n)| n).unwrap_or(0)
}

/// Bucket of the per-length index: `a-z 0-9 _` handles by length (1..=15), handles of the spec
/// with emoji or flags in [`EMOJI_BUCKET`], the extension's in [`EXTENDED_BUCKET`].
pub const EMOJI_BUCKET: usize = 0;
pub const EXTENDED_BUCKET: usize = 99;
fn bucket_of(handle: &str) -> usize {
  if !handle_is_emoji(handle) {
    len_of(handle)
  } else if handle_in_spec(handle) {
    EMOJI_BUCKET
  } else {
    EXTENDED_BUCKET
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AtOp {
  /// `bitwork`: what a JSON register claims about its txids (§5.6); a claim not met voids it.
  Register { handle: String, records: RecordPatch, bitwork: Bitwork },
  Config { handle: String, patch: RecordPatch },
  /// `None` clears the address's choice.
  Primary { handle: Option<String> },
}

/// Records of an @ inscription: DNS §7's checks, `cname` a handle, no
/// `subdomains` (spec §7).
fn records_of(top: &dns::Obj, nested: Option<&dns::Obj>) -> RecordPatch {
  let mut p = dns::parse_patch_with(top, nested, &|s| normalize_handle(s, true));
  p.subdomains = None;
  p
}

/// Reads an @ operation out of an inscription's content, if it is one (§5).
pub fn parse_at_op(_content_type: &str, body: &[u8]) -> Option<AtOp> {
  // v1.1 §5: the content type is never consulted; the body bytes decide.
  if body.len() > 64 * 1024 {
    return None;
  }
  let text = std::str::from_utf8(body).ok()?;
  let text = text.strip_prefix('\u{FEFF}').unwrap_or(text);
  // Classification uses the body, not the type: an object is JSON.
  if text.trim_start().starts_with('{') {
    return parse_json_op(&dns::parse_json_object(text)?);
  }
  // Plain text: the whole body is the handle, one trailing newline allowed.
  let line = text.strip_suffix("\r\n").or_else(|| text.strip_suffix('\n')).unwrap_or(text);
  if line.chars().any(char::is_whitespace) {
    return None;
  }
  Some(AtOp::Register { handle: normalize_handle(line, false)?, records: RecordPatch::default(), bitwork: Bitwork::default() })
}

fn parse_json_op(obj: &dns::Obj) -> Option<AtOp> {
  // v1.1: a JSON string equal to `at` under ASCII case folding; `"p":"@"` and the rest are not this protocol.
  if !obj.get("p").and_then(Value::as_str).is_some_and(|p| p.eq_ignore_ascii_case("at")) {
    return None;
  }
  let name_str = obj.get("name").and_then(Value::as_str);
  let handle = || name_str.and_then(|n| normalize_handle(n, true));
  let nested = obj.get("config").and_then(Value::as_object);
  match obj.get("op") {
    Some(Value::String(op)) => match op.as_str() {
      "register" | "reg" => Some(AtOp::Register { handle: handle()?, records: records_of(obj, None), bitwork: Bitwork::of(obj) }),
      "config" | "update" | "upd" => Some(AtOp::Config { handle: handle()?, patch: records_of(obj, nested) }),
      "primary" => match name_str? {
        "" => Some(AtOp::Primary { handle: None }),
        _ => Some(AtOp::Primary { handle: Some(handle()?) }),
      },
      // transfer, renew, revoke and anything else are undefined: ignored.
      _ => None,
    },
    Some(_) => None,
    None => {
      let has_fields = dns::RECORD_KEYS.iter().any(|k| obj.contains_key(*k))
        || nested.is_some_and(|n| dns::RECORD_KEYS.iter().any(|k| n.contains_key(*k)));
      if !has_fields {
        return None;
      }
      Some(AtOp::Config { handle: handle()?, patch: records_of(obj, nested) })
    }
  }
}

// ------------------------------------------------------------------ store --

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct HandleEntry {
  /// canonical, with the `@`
  pub handle: String,
  pub inscription_id: String,
  pub number: u64,
  pub height: u64,
  pub tx_index: u32,
  pub time: u64,
  /// Records set by the register itself (JSON registers).
  pub records: RecordPatch,
  /// Later registers of the same handle (missed claims).
  pub lost: u64,
  /// Place among all handles, and among those of its length, in register order.
  pub index: u64,
  pub len_index: u64,
  /// Where the register was made (its reveal), once known.
  pub made_at: Option<Pos>,
  /// Its commit-first priority key (§5.6), once looked up.
  pub key: Option<Key>,
}

/// What an inscription is to the @ index: register, claim (too late), config
/// or primary, and whether it counted.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct HandleRole {
  pub role: String,
  pub handle: String,
  pub counted: bool,
  pub note: String,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct AtState {
  cursor: Vec<u8>,
  handles: u64,
  claims: u64,
  configs: u64,
  configs_ignored: u64,
  primaries: u64,
  primaries_ignored: u64,
  scanned: u64,
  cursor_height: u64,
}

#[derive(Serialize, Deserialize)]
struct AtUndo {
  last_height: u64,
  ops: Vec<(String, Vec<u8>, Option<Vec<u8>>)>,
}

struct Trees {
  meta: Tree,
  seq: Tree,
  genesis: Tree,
  content: Tree,
  by_id: Tree,
  name: Tree,
  by_inscription: Tree,
  index: Tree,
  len_index: Tree,
  claims: Tree,
  configs: Tree,
  primary: Tree,
  stats: Tree,
  undo: Tree,
}

impl Trees {
  fn open(db: &store::Db) -> Result<Self> {
    Ok(Trees {
      meta: db.open_tree("meta")?,
      seq: db.open_tree("inscription_seq")?,
      genesis: db.open_tree("inscription_genesis")?,
      content: db.open_tree("inscription_content")?,
      by_id: db.open_tree("inscriptions_by_id")?,
      name: db.open_tree("at_name")?,
      by_inscription: db.open_tree("at_by_inscription")?,
      index: db.open_tree("at_index")?,
      len_index: db.open_tree("at_len_index")?,
      claims: db.open_tree("at_claims")?,
      configs: db.open_tree("at_config")?,
      primary: db.open_tree("at_primary")?,
      stats: db.open_tree("at_stats")?,
      undo: db.open_tree("at_undo")?,
    })
  }
}

fn at_state(meta: &Tree) -> Result<AtState> {
  Ok(match meta.get(STATE_KEY)? {
    Some(raw) => bincode::deserialize(raw.as_ref()).context("decode at state")?,
    None => AtState::default(),
  })
}

/// `handle \0 n` keys, for a handle's claims and configs in order.
fn handle_key(handle: &str, n: u64) -> Vec<u8> {
  let mut k = handle.as_bytes().to_vec();
  k.push(0);
  k.extend_from_slice(&n.to_be_bytes());
  k
}

fn len_key(len: usize, n: u64) -> Vec<u8> {
  let mut k = vec![len as u8];
  k.extend_from_slice(&n.to_be_bytes());
  k
}

fn len_count_key(len: usize) -> Vec<u8> {
  format!("len|{len:02}").into_bytes()
}

fn get_u64(tree: &Tree, key: &[u8]) -> Result<u64> {
  Ok(tree.get(key)?.map(|v| decode_u64(v.as_ref())).transpose()?.unwrap_or(0))
}

fn get_entry(tree: &Tree, handle: &str) -> Result<Option<HandleEntry>> {
  tree.get(handle.as_bytes())?.map(|v| bincode::deserialize(v.as_ref()).context("decode handle")).transpose()
}

struct Candidate {
  key: Vec<u8>,
  pos: Pos,
  number: u64,
  time: u64,
  id: String,
  op: AtOp,
}

/// The next stretch of chain order up to what is numbered and settled: the @
/// operations in it, the last key read and how many rows were read.
fn scan(t: &Trees, st: &AtState, max: usize) -> Result<(Vec<Candidate>, Option<Vec<u8>>, u64)> {
  let mut numbered_through = ii::numbering_state(&t.meta)?.cursor;
  let indexed = ii::meta_u64(&t.meta, b"indexed_height")?.unwrap_or(0);
  let Some(settled) = (indexed + 1).checked_sub(AT_CONFIRMATIONS) else {
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
    // v1.1: the content type doesn't matter, only the body. Text, JSON, code, HTML and untyped
    // bodies are read; images, video, audio, models, PDFs and fonts are not (a body that is
    // exactly `@jon` under one of those types is not worth reading every picture on the chain).
    if e.kinds & (ii::K_TEXT | ii::K_JSON | ii::K_OTHER | ii::K_CODE | ii::K_HTML) != 0 {
      rows.push((k.to_vec(), e));
    }
    Ok(true)
  })?;
  let found: Vec<Result<Option<Candidate>>> = rows
    .into_par_iter()
    .map(|(key, e)| -> Result<Option<Candidate>> {
      // The numbered sighting only.
      let Some(g) = t.genesis.get(e.id.as_bytes())? else { return Ok(None) };
      let g: ii::Genesis = bincode::deserialize(g.as_ref()).context("decode genesis")?;
      let height = ii::seq_height(&key);
      if g.height != height {
        return Ok(None);
      }
      let Some(raw) = t.content.get(e.id.as_bytes())? else { return Ok(None) };
      let c = decode_inscription_content(raw.as_ref())?;
      let Some(op) = parse_at_op(&c.content_type, &c.body) else { return Ok(None) };
      let tx_index = u32::from_be_bytes(key[8..12].try_into().unwrap());
      Ok(Some(Candidate { pos: (height, tx_index), number: g.number, time: e.time, id: e.id, op, key }))
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

/// A register's bitwork claims hold (true for one that makes none). When the node can't say and
/// the stretch is being read leniently, the claim is taken as not met.
async fn bitwork_holds(tracer: &mut Tracer<'_>, c: &Candidate, lenient: bool) -> Result<bool> {
  let AtOp::Register { bitwork, .. } = &c.op else { return Ok(true) };
  match priority::bitwork_ok(tracer, &c.id, bitwork).await {
    Ok(ok) => Ok(ok),
    Err(e) if lenient => {
      warn!("at index: could not check the bitwork of {}: {e:#}", c.id);
      Ok(false)
    }
    Err(e) => Err(e),
  }
}

/// Applies one stretch in chain order as one batch. `lenient`: after a stretch
/// failed a few times, what the node cannot settle is recorded as unchecked
/// instead of stopping the index.
async fn apply(config: &Config, t: &Trees, mut st: AtState, cands: Vec<Candidate>, last: Vec<u8>, scanned: u64, lenient: bool, era: u64) -> Result<AtState> {
  let mut batch = Batch::default();
  let mut handles: HashMap<String, HandleEntry> = HashMap::new();
  let mut counters: HashMap<Vec<u8>, u64> = HashMap::new();
  let mut tracer = Tracer::new(config);

  fn counter(t: &Trees, counters: &mut HashMap<Vec<u8>, u64>, key: Vec<u8>) -> Result<u64> {
    if let Some(v) = counters.get(&key) {
      return Ok(*v);
    }
    let v = get_u64(&t.stats, &key)?;
    counters.insert(key, v);
    Ok(v)
  }

  for c in cands {
    let role = |role: &str, handle: &str, counted: bool, note: &str| HandleRole { role: role.to_string(), handle: handle.to_string(), counted, note: note.to_string() };
    let lookup = |handles: &HashMap<String, HandleEntry>, h: &str| -> Result<Option<HandleEntry>> {
      match handles.get(h) {
        Some(e) => Ok(Some(e.clone())),
        None => get_entry(&t.name, h),
      }
    };
    let r = match &c.op {
      AtOp::Register { handle, .. } if !bitwork_holds(&mut tracer, &c, lenient).await? => {
        // §5.6: a bitwork claim the txid does not meet voids the register: not even a missed claim
        role("void", handle, false, "its bitwork claim is not met by its txid")
      }
      AtOp::Register { handle, records, .. } => match lookup(&handles, handle)? {
        Some(mut existing) => {
          // Chain order of first pieces puts this one later, unless the
          // handle's register was made in several pieces and finished after
          // this one was made: where each was made, then the priority key (§5.6).
          let order: Result<(Pos, Pos)> = async {
            let winner_made = match existing.made_at {
              Some(p) => p,
              None => {
                let rec = dns::get_record(&t.by_id, &existing.inscription_id)?.context("register inscription missing")?;
                dns::made_by(&mut tracer, &rec, (existing.height, existing.tx_index)).await?.0
              }
            };
            let newcomer_made = if c.pos > winner_made {
              c.pos
            } else {
              let rec = dns::get_record(&t.by_id, &c.id)?.context("register inscription missing")?;
              dns::made_by(&mut tracer, &rec, c.pos).await?.0
            };
            Ok((winner_made, newcomer_made))
          }
          .await;
          let (winner_made, newcomer_made) = match order {
            Ok(o) => {
              existing.made_at = Some(o.0);
              o
            }
            Err(e) if lenient => {
              warn!("at index: could not compare {} with the register of {}: {e:#}", c.id, handle);
              ((existing.height, existing.tx_index), c.pos)
            }
            Err(e) => return Err(e),
          };
          // commit-first (§5.6): the newcomer takes the handle only with a lower key while the
          // holder's row is still pending; the node is asked only inside that window
          let mut holder_key = existing.key;
          let won = match priority::contest(&mut tracer, &existing.inscription_id, winner_made, &mut holder_key, &c.id, newcomer_made).await {
            Ok(k) => k,
            Err(e) if lenient => {
              warn!("at index: could not rank {} against the register of {}: {e:#}", c.id, handle);
              (newcomer_made < winner_made).then(|| priority::reveal_key(newcomer_made))
            }
            Err(e) => return Err(e),
          };
          existing.key = holder_key;
          existing.lost += 1;
          st.claims += 1;
          if let Some(new_key) = won {
            // This one was made first: it takes the handle, the old row is the claim.
            batch.insert(&t.claims, handle_key(handle, existing.number), bincode::serialize(&ClaimEntry {
              inscription_id: existing.inscription_id.clone(),
              number: existing.number,
              height: existing.height,
              time: existing.time,
            })?);
            batch.insert(
              &t.by_inscription,
              existing.inscription_id.as_bytes().to_vec(),
              bincode::serialize(&role("claim", handle, false, "an earlier inscription registered this handle first"))?,
            );
            existing.inscription_id = c.id.clone();
            existing.number = c.number;
            existing.height = c.pos.0;
            existing.tx_index = c.pos.1;
            existing.time = c.time;
            existing.records = records.clone();
            existing.made_at = Some(newcomer_made);
            existing.key = Some(new_key);
            batch.insert(&t.name, handle.as_bytes().to_vec(), bincode::serialize(&existing)?);
            handles.insert(handle.clone(), existing);
            role("register", handle, true, "")
          } else {
            batch.insert(&t.claims, handle_key(handle, c.number), bincode::serialize(&ClaimEntry {
              inscription_id: c.id.clone(),
              number: c.number,
              height: c.pos.0,
              time: c.time,
            })?);
            batch.insert(&t.name, handle.as_bytes().to_vec(), bincode::serialize(&existing)?);
            handles.insert(handle.clone(), existing);
            role("claim", handle, false, "an earlier inscription registered this handle first")
          }
        }
        None => {
          let len = bucket_of(handle);
          let lk = len_count_key(len);
          let len_index = counter(t, &mut counters, lk.clone())?;
          let entry = HandleEntry {
            handle: handle.clone(),
            inscription_id: c.id.clone(),
            number: c.number,
            height: c.pos.0,
            tx_index: c.pos.1,
            time: c.time,
            records: records.clone(),
            lost: 0,
            index: st.handles,
            len_index,
            made_at: None,
            key: None,
          };
          batch.insert(&t.name, handle.as_bytes().to_vec(), bincode::serialize(&entry)?);
          batch.insert(&t.index, st.handles.to_be_bytes().to_vec(), handle.as_bytes().to_vec());
          batch.insert(&t.len_index, len_key(len, len_index), handle.as_bytes().to_vec());
          counters.insert(lk.clone(), len_index + 1);
          batch.insert(&t.stats, lk, encode_u64(len_index + 1).to_vec());
          handles.insert(handle.clone(), entry);
          st.handles += 1;
          role("register", handle, true, "")
        }
      },
      AtOp::Config { handle, patch } => {
        let verdict = match lookup(&handles, handle)? {
          None => Err("the handle is not registered"),
          Some(entry) => {
            let check: Result<std::result::Result<(Pos, String), &'static str>> = async {
              let rec = dns::get_record(&t.by_id, &c.id)?.context("config inscription missing")?;
              let (made_at, owner) = dns::made_by(&mut tracer, &rec, c.pos).await?;
              let reg = dns::get_record(&t.by_id, &entry.inscription_id)?.context("register inscription missing")?;
              let holder = dns::holder_after(&mut tracer, &reg, made_at).await?;
              Ok(if owner.is_empty() || holder.as_deref() != Some(owner.as_str()) { Err("not made by the handle's holder") } else { Ok((made_at, owner)) })
            }
            .await;
            match check {
              Ok(v) => v,
              Err(e) if lenient => {
                warn!("at index: could not check config {}: {e:#}", c.id);
                Err("its holder could not be checked against the node")
              }
              Err(e) => return Err(e),
            }
          }
        };
        match verdict {
          Ok((made_at, owner)) => {
            batch.insert(&t.configs, handle_key(handle, c.number), bincode::serialize(&ConfigEntry {
              inscription_id: c.id.clone(),
              number: c.number,
              height: made_at.0,
              tx_index: made_at.1,
              time: c.time,
              owner,
              patch: patch.clone(),
            })?);
            st.configs += 1;
            role("config", handle, true, if patch.is_empty() { "sets no valid record" } else { "" })
          }
          Err(why) => {
            st.configs_ignored += 1;
            role("config", handle, false, why)
          }
        }
      }
      AtOp::Primary { handle } => {
        let check: Result<std::result::Result<(Pos, String), &'static str>> = async {
          let rec = dns::get_record(&t.by_id, &c.id)?.context("primary inscription missing")?;
          let (made_at, owner) = dns::made_by(&mut tracer, &rec, c.pos).await?;
          if owner.is_empty() {
            return Ok(Err("the inscription has no owner address"));
          }
          if let Some(h) = handle {
            let Some(entry) = lookup(&handles, h)? else { return Ok(Err("the handle is not registered")) };
            let reg = dns::get_record(&t.by_id, &entry.inscription_id)?.context("register inscription missing")?;
            if dns::holder_after(&mut tracer, &reg, made_at).await?.as_deref() != Some(owner.as_str()) {
              return Ok(Err("its owner does not hold the handle"));
            }
          }
          Ok(Ok((made_at, owner)))
        }
        .await;
        let verdict = match check {
          Ok(v) => v,
          Err(e) if lenient => {
            warn!("at index: could not check primary {}: {e:#}", c.id);
            Err("its owner could not be checked against the node")
          }
          Err(e) => return Err(e),
        };
        let shown = handle.clone().unwrap_or_default();
        match verdict {
          Ok((made_at, owner)) => {
            batch.insert(&t.primary, owner.as_bytes().to_vec(), bincode::serialize(&PrimaryEntry {
              inscription_id: c.id.clone(),
              number: c.number,
              height: made_at.0,
              tx_index: made_at.1,
              time: c.time,
              name: handle.clone(),
            })?);
            st.primaries += 1;
            role("primary", &shown, true, "")
          }
          Err(why) => {
            st.primaries_ignored += 1;
            role("primary", &shown, false, why)
          }
        }
      }
    };
    batch.insert(&t.by_inscription, c.id.as_bytes().to_vec(), bincode::serialize(&r)?);
  }
  st.cursor_height = ii::seq_height(&last);
  st.cursor = last.clone();
  st.scanned += scanned;
  batch.insert(&t.meta, STATE_KEY.to_vec(), bincode::serialize(&st)?);

  let indexed = ii::meta_u64(&t.meta, b"indexed_height")?.unwrap_or(0);
  let _w = AT_WRITE.lock().unwrap_or_else(|e| e.into_inner());
  if reorg_gen(&t.meta)? != era {
    bail!("{REORGED}");
  }
  if st.cursor_height + UNDO_BLOCKS >= indexed {
    let ops = batch.previous(&t.meta)?;
    batch.insert(&t.undo, last, bincode::serialize(&AtUndo { last_height: st.cursor_height, ops })?);
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

/// Clears the @ index so it is read again from the first numbered inscription.
pub(crate) fn reset(db: &store::Db) -> Result<()> {
  let _w = AT_WRITE.lock().unwrap_or_else(|e| e.into_inner());
  for tree in TREES {
    db.open_tree(tree)?.delete_range(Vec::new(), vec![0xff; 64])?;
  }
  let meta = db.open_tree("meta")?;
  meta.remove(STATE_KEY)?;
  meta.insert(REORG_GEN_KEY, encode_u64(reorg_gen(&meta)? + 1).to_vec())?;
  Ok(())
}

/// The first handles index used other rules (up to 32 characters, trimmed
/// bodies): its data goes, once.
fn drop_old_index(db: &store::Db) -> Result<()> {
  let meta = db.open_tree("meta")?;
  let mut earlier = false;
  for k in EARLIER_KEYS {
    earlier |= meta.get(k)?.is_some();
  }
  if earlier {
    // earlier rules: same trees, read again from the start
    let _w = AT_WRITE.lock().unwrap_or_else(|e| e.into_inner());
    for tree in TREES {
      db.open_tree(tree)?.delete_range(Vec::new(), vec![0xff; 64])?;
    }
    for k in EARLIER_KEYS {
      meta.remove(k)?;
    }
    meta.insert(REORG_GEN_KEY, encode_u64(reorg_gen(&meta)? + 1).to_vec())?;
    info!("at index: rules changed (spec v1.1 commit-first priority + every character type): reading every handle again");
  }
  if meta.get(OLD_KEYS[0])?.is_none() && meta.get(OLD_KEYS[1])?.is_none() {
    return Ok(());
  }
  for tree in OLD_TREES {
    if let Ok(t) = db.open_tree(tree) {
      t.delete_range(Vec::new(), vec![0xff; 64])?;
    }
  }
  for k in OLD_KEYS {
    meta.remove(k)?;
  }
  info!("at index: the earlier handles index (pre-spec rules) was cleared");
  Ok(())
}

/// Undoes every step that read blocks at `height` and above, newest first.
/// Called by a reorg's rollback.
pub(crate) fn undo_from(db: &store::Db, height: u64) -> Result<()> {
  let _w = AT_WRITE.lock().unwrap_or_else(|e| e.into_inner());
  let meta = db.open_tree("meta")?;
  meta.insert(REORG_GEN_KEY, encode_u64(reorg_gen(&meta)? + 1).to_vec())?;
  let undo = db.open_tree("at_undo")?;
  let st = at_state(&meta)?;
  if st.cursor.is_empty() || st.cursor_height < height {
    return Ok(());
  }
  let mut steps: Vec<(Vec<u8>, AtUndo)> = Vec::new();
  undo.for_each_from(&ii::seq_key(height, 0), |k, v| {
    steps.push((k.to_vec(), bincode::deserialize(v).context("decode at undo")?));
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
  let st = at_state(&meta)?;
  if !st.cursor.is_empty() && st.cursor_height >= height {
    warn!("at index: the reorg at block {height} is deeper than its undo history; handles from block {height} on may be wrong");
  } else {
    warn!("at index: reorg at block {height}: undid {undone} steps, reading again from block {}", st.cursor_height);
  }
  Ok(())
}

/// The @ indexer: catches up over every numbered inscription, then follows
/// numbering as it goes.
pub async fn run_handles_index(config: Config) -> Result<()> {
  let db = ii::db_of(&config)?;
  drop_old_index(&db)?;
  let t = Arc::new(Trees::open(&db)?);
  let mut st = at_state(&t.meta)?;
  info!("at index: starting at block {}, {} handles so far", st.cursor_height, st.handles);
  let (mut last_log, mut caught_up, mut failures) = (Instant::now(), false, 0u32);
  let mut seen_era = reorg_gen(&t.meta)?;
  loop {
    let era = reorg_gen(&t.meta)?;
    if era != seen_era {
      seen_era = era;
      st = at_state(&t.meta)?;
    }
    let (t2, st2) = (t.clone(), st.clone());
    let (cands, last, scanned) = tokio::task::spawn_blocking(move || scan(&t2, &st2, 200_000)).await.context("at scan")??;
    let Some(last) = last else {
      if !caught_up {
        caught_up = true;
        info!("at index: caught up at block {}, {} handles, {} missed claims, {} configs", st.cursor_height, st.handles, st.claims, st.configs);
      }
      sleep(Duration::from_secs(2)).await;
      continue;
    };
    match apply(&config, &t, st.clone(), cands, last, scanned, failures >= 3, era).await {
      Ok(next) => {
        st = next;
        failures = 0;
      }
      Err(_) if reorg_gen(&t.meta).unwrap_or(era) != era => continue,
      Err(e) => {
        failures += 1;
        warn!("at index: stretch after block {} failed (try {failures}): {e:#}", st.cursor_height);
        sleep(Duration::from_secs(20)).await;
        continue;
      }
    }
    if last_log.elapsed() > Duration::from_secs(60) {
      last_log = Instant::now();
      info!("at index: at block {}, {} inscriptions read, {} handles, {} missed claims", st.cursor_height, st.scanned, st.handles, st.claims);
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
  pub configs: u64,
  pub configs_ignored: u64,
  pub primaries: u64,
  pub primaries_ignored: u64,
  /// `a-z 0-9 _` handles taken at each localpart length 1..=15
  pub by_length: Vec<(usize, u64)>,
  /// one-emoji handles (in the spec)
  pub emoji: u64,
  /// the extension: several emoji, emoji mixed with letters, flags, sequences
  pub extended: u64,
}

pub fn handles_status(config: &Config) -> Result<HandlesStatus> {
  let db = ii::db_of(config)?;
  let meta = db.open_tree("meta")?;
  let st = at_state(&meta)?;
  let numbered = ii::numbering_state(&meta)?.cursor;
  let backfilled = ii::inscription_seq_backfill_done(config)?;
  let indexed = ii::meta_u64(&meta, b"indexed_height")?.unwrap_or(0);
  let settled = ii::seq_key((indexed + 1).saturating_sub(AT_CONFIRMATIONS), u32::MAX).to_vec();
  let readable = if numbered > settled { settled.clone() } else { numbered.clone() };
  let mut start = st.cursor.clone();
  if !start.is_empty() {
    start.push(0);
  }
  let mut unread = false;
  db.open_tree("inscription_seq")?.for_each_from(&start, |k, _| {
    unread = k <= readable.as_slice();
    Ok(false)
  })?;
  // Caught up = nothing settled is left to read here, and numbering has every settled row too.
  // (Not "the last inscription read is near the tip": blocks with no inscriptions in them are
  // nothing to wait for.)
  let numbering_behind = numbered < settled && ii::seq_rows_between(&db, &numbered, &settled)?;
  let caught_up = backfilled && !numbered.is_empty() && !unread && !numbering_behind;
  // the height read through: the settled tip once caught up, even if its last blocks were empty
  let read_through = if caught_up { st.cursor_height.max((indexed + 1).saturating_sub(AT_CONFIRMATIONS)) } else { st.cursor_height };
  let stats = db.open_tree("at_stats")?;
  let by_length = (1..=HANDLE_MAX_LEN).map(|l| Ok((l, get_u64(&stats, &len_count_key(l))?))).collect::<Result<Vec<_>>>()?;
  let emoji = get_u64(&stats, &len_count_key(EMOJI_BUCKET))?;
  let extended = get_u64(&stats, &len_count_key(EXTENDED_BUCKET))?;
  Ok(HandlesStatus {
    caught_up,
    height: read_through,
    scanned: st.scanned,
    handles: st.handles,
    claims: st.claims,
    configs: st.configs,
    configs_ignored: st.configs_ignored,
    primaries: st.primaries,
    primaries_ignored: st.primaries_ignored,
    by_length,
    emoji,
    extended,
  })
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
  /// §5.6: `pending` while a lower key could still take it (from the stored key, else its reveal)
  pub status: &'static str,
}

#[derive(Debug, Clone, Serialize)]
pub struct HandlePage {
  pub total: u64,
  pub items: Vec<HandleListed>,
}

fn listed(db: &store::Db, handles: Vec<Vec<u8>>) -> Result<Vec<HandleListed>> {
  let (t_name, by_id) = (db.open_tree("at_name")?, db.open_tree("inscriptions_by_id")?);
  let tip = ii::meta_u64(&db.open_tree("meta")?, b"indexed_height")?.unwrap_or(0);
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
      status: priority::status(e.key.unwrap_or_else(|| priority::reveal_key(e.made_at.unwrap_or((e.height, e.tx_index)))), tip),
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

/// Handles in register order, all or one length's (newest first unless
/// `oldest_first`), from `offset`.
pub fn handles_list(config: &Config, len: Option<usize>, offset: u64, limit: u64, oldest_first: bool) -> Result<HandlePage> {
  let db = ii::db_of(config)?;
  let total = match len {
    Some(l) => get_u64(&db.open_tree("at_stats")?, &len_count_key(l))?,
    None => at_state(&db.open_tree("meta")?)?.handles,
  };
  if offset >= total {
    return Ok(HandlePage { total, items: Vec::new() });
  }
  let take = limit.min(total - offset);
  let indexes: Vec<u64> = if oldest_first { (offset..offset + take).collect() } else { (0..take).map(|i| total - 1 - offset - i).collect() };
  let keys: Vec<Vec<u8>> = match len {
    Some(l) => indexes.iter().map(|&i| len_key(l, i)).collect(),
    None => indexes.iter().map(|i| i.to_be_bytes().to_vec()).collect(),
  };
  let tree = db.open_tree(if len.is_some() { "at_len_index" } else { "at_index" })?;
  let handles: Vec<Vec<u8>> = tree.multi_get(&keys)?.into_iter().flatten().map(|v| v.to_vec()).collect();
  Ok(HandlePage { total, items: listed(&db, handles)? })
}

/// Several handles at once (canonical, with `@`), those that exist.
pub fn handles_get_many(config: &Config, handles: &[String]) -> Result<Vec<HandleListed>> {
  let db = ii::db_of(config)?;
  listed(&db, handles.iter().map(|h| h.as_bytes().to_vec()).collect())
}

#[derive(Debug, Clone, Serialize)]
pub struct HandleConfigView {
  pub inscription_id: String,
  pub number: u64,
  pub height: u64,
  pub time: u64,
  pub owner: String,
  /// Made by the current holder, and they have held it ever since, so part of the records now.
  pub applies: bool,
  #[serde(skip)]
  pos: Pos,
  #[serde(skip)]
  patch: RecordPatch,
}

#[derive(Debug, Clone, Serialize)]
pub struct HandleView {
  pub handle: String,
  pub inscription_id: String,
  pub number: u64,
  pub height: u64,
  pub time: u64,
  pub owner: String,
  pub records: DnsRecords,
  pub configs: Vec<HandleConfigView>,
  pub claims: u64,
  /// Where wallets send for `@jon` (spec §8): the `address` record, else the owner; `None` when
  /// no address can spend the register output (burned).
  pub pay_to: Option<String>,
  /// Letters that only look like `a-z` (see [`handle_confusable`]).
  pub confusable: bool,
  /// Commit-first priority (§5.6): the key, whether it came from the commit, and
  /// `pending` (a lower key could still take it, until `final_after`) or `final`.
  pub key: Key,
  pub from_commit: bool,
  pub status: &'static str,
  pub final_after: u64,
  #[serde(skip)]
  stored_key: Option<Key>,
  #[serde(skip)]
  reg_pos: Pos,
  #[serde(skip)]
  reg_patch: RecordPatch,
}

/// A Dogecoin address an output can be paid to (P2PKH `D…`, P2SH `A…`/`9…`); burned outputs
/// (OP_RETURN, scripts with no address) are stored without one.
fn spendable_address(a: &str) -> bool {
  (33..=35).contains(&a.len()) && matches!(a.as_bytes()[0], b'D' | b'A' | b'9') && a.chars().all(|c| c.is_ascii_alphanumeric() && !matches!(c, '0' | 'O' | 'I' | 'l'))
}

/// A handle as stored, with the records its current holder wrote. Records count only while the
/// address that wrote them still holds the handle (see [`handle_view`], which checks the moves).
pub fn handle_get(config: &Config, handle: &str) -> Result<Option<HandleView>> {
  let db = ii::db_of(config)?;
  let Some(e) = get_entry(&db.open_tree("at_name")?, handle)? else { return Ok(None) };
  let owner = dns::get_record(&db.open_tree("inscriptions_by_id")?, &e.inscription_id)?.map(|r| r.address).unwrap_or_default();
  let mut configs = Vec::new();
  let mut start = handle.as_bytes().to_vec();
  start.push(0);
  db.open_tree("at_config")?.for_each_prefix(&start, |_, v| {
    let c: ConfigEntry = bincode::deserialize(v).context("decode at config")?;
    let applies = !owner.is_empty() && c.owner == owner;
    configs.push(HandleConfigView { inscription_id: c.inscription_id, number: c.number, height: c.height, time: c.time, owner: c.owner, applies, pos: (c.height, c.tx_index), patch: c.patch });
    Ok(true)
  })?;
  let mut v = HandleView {
    confusable: handle_confusable(&e.handle),
    handle: e.handle,
    inscription_id: e.inscription_id,
    number: e.number,
    height: e.height,
    time: e.time,
    owner,
    records: DnsRecords::default(),
    configs,
    claims: e.lost,
    pay_to: None,
    key: priority::reveal_key(e.made_at.unwrap_or((e.height, e.tx_index))),
    from_commit: false,
    status: "final",
    final_after: 0,
    stored_key: e.key,
    reg_pos: e.made_at.unwrap_or((e.height, e.tx_index)),
    reg_patch: e.records,
  };
  let tip = ii::meta_u64(&db.open_tree("meta")?, b"indexed_height")?.unwrap_or(0);
  let k = e.key.unwrap_or(v.key);
  v.set_priority(k, e.key.is_some_and(|k| k != v.key), tip);
  v.settle(|_| true);
  Ok(Some(v))
}

impl HandleView {
  fn set_priority(&mut self, key: Key, from_commit: bool, tip: u64) {
    self.key = key;
    self.from_commit = from_commit;
    self.status = priority::status(key, tip);
    self.final_after = key.0 + priority::W;
  }

  /// Records and pay-to from what counts: the register's own records and each config by the
  /// owner, when `held(pos)` says the owner has held the handle without a break since `pos`.
  fn settle(&mut self, mut held: impl FnMut(Pos) -> bool) {
    let burned = !spendable_address(&self.owner);
    let mut r = DnsRecords::default();
    if !burned && held(self.reg_pos) {
      r.apply(&self.reg_patch);
    }
    for c in &mut self.configs {
      c.applies = !burned && c.owner == self.owner && held(c.pos);
      if c.applies {
        r.apply(&c.patch);
      }
    }
    self.pay_to = if burned { None } else { Some(r.address.clone().unwrap_or_else(|| self.owner.clone())) };
    self.records = if burned { DnsRecords::default() } else { r };
  }
}

/// [`handle_get`], with records reset by every change of holder (spec v1.1 §5.3): a sale, a gift
/// or a move to another address of the same wallet empties them, so a buyer never pays into the
/// seller's `address` record. A move that pays the same address keeps them.
pub async fn handle_view(config: &Config, handle: &str) -> Result<Option<HandleView>> {
  static HELD: Mutex<Option<HashMap<(String, String, Pos), bool>>> = Mutex::new(None);
  let (c2, h2) = (config.clone(), handle.to_string());
  let Some(mut v) = tokio::task::spawn_blocking(move || handle_get(&c2, &h2)).await.context("handle lookup")?? else { return Ok(None) };
  let db = ii::db_of(config)?;
  // while it could still be pending, its key from the node (a committed reveal ranks by its commit)
  let tip = ii::meta_u64(&db.open_tree("meta")?, b"indexed_height")?.unwrap_or(0);
  let (k, from_commit) = priority::key_for_view(config, &v.inscription_id, v.reg_pos, v.stored_key, tip).await;
  v.set_priority(k, from_commit, tip);
  let Some(reg) = dns::get_record(&db.open_tree("inscriptions_by_id")?, &v.inscription_id)? else { return Ok(Some(v)) };
  if dns::unmoved(&reg) || !spendable_address(&v.owner) {
    // never left the address it was made to (or burned: settle() already emptied it)
    return Ok(Some(v));
  }
  // positions worth asking about: the register's, and each config the owner made
  let mut asks: Vec<Pos> = vec![v.reg_pos];
  asks.extend(v.configs.iter().filter(|c| c.owner == v.owner).map(|c| c.pos));
  let at = format!("{}:{}", reg.txid, reg.vout);
  let mut answers: HashMap<Pos, bool> = HashMap::new();
  let mut tracer = Tracer::new(config);
  for p in asks {
    let key = (v.inscription_id.clone(), at.clone(), p);
    if let Some(ok) = HELD.lock().unwrap_or_else(|e| e.into_inner()).as_ref().and_then(|m| m.get(&key).copied()) {
      answers.insert(p, ok);
      continue;
    }
    let ok = match tracer.holders_since(&reg, p).await {
      Ok(Some(holders)) => holders.iter().all(|h| *h == v.owner),
      // not made yet right after p (can't be for these), or the trace failed: don't trust old records
      _ => false,
    };
    answers.insert(p, ok);
    let mut g = HELD.lock().unwrap_or_else(|e| e.into_inner());
    let m = g.get_or_insert_with(HashMap::new);
    if m.len() > 20_000 {
      m.clear();
    }
    m.insert(key, ok);
  }
  v.settle(|p| answers.get(&p).copied().unwrap_or(false));
  Ok(Some(v))
}

/// Later registers of a handle, oldest first.
pub fn handle_claims(config: &Config, handle: &str, limit: usize) -> Result<Vec<ClaimEntry>> {
  let mut out = Vec::new();
  let mut start = handle.as_bytes().to_vec();
  start.push(0);
  ii::db_of(config)?.open_tree("at_claims")?.for_each_prefix(&start, |_, v| {
    if out.len() >= limit {
      return Ok(false);
    }
    out.push(bincode::deserialize(v).context("decode at claim")?);
    Ok(true)
  })?;
  Ok(out)
}

pub fn handle_role(config: &Config, inscription_id: &str) -> Result<Option<HandleRole>> {
  ii::db_of(config)?
    .open_tree("at_by_inscription")?
    .get(inscription_id.as_bytes())?
    .map(|v| bincode::deserialize(v.as_ref()).context("decode at role"))
    .transpose()
}

/// Handles an address holds now, oldest register first.
pub fn handles_of(config: &Config, address: &str) -> Result<Vec<HandleListed>> {
  let db = ii::db_of(config)?;
  let mut ids: Vec<String> = Vec::new();
  let prefix = format!("{address}|");
  db.open_tree("inscriptions_by_address")?.for_each_prefix(prefix.as_bytes(), |k, _| {
    ids.push(String::from_utf8_lossy(&k[prefix.len()..]).into_owned());
    Ok(true)
  })?;
  let roles = db.open_tree("at_by_inscription")?;
  let mut handles = Vec::new();
  for chunk in ids.chunks(10_000) {
    for raw in roles.multi_get(chunk)?.into_iter().flatten() {
      let r: HandleRole = bincode::deserialize(raw.as_ref()).context("decode at role")?;
      if r.role == "register" && r.counted {
        handles.push(r.handle.into_bytes());
      }
    }
  }
  let mut out = listed(&db, handles)?;
  out.retain(|h| h.owner == address);
  out.sort_by_key(|h| h.number);
  Ok(out)
}

/// The handle an address wears (spec §5.4), if it still holds it and has held
/// it ever since choosing. A handle sent away clears the choice for good.
pub async fn handle_primary(config: &Config, address: &str) -> Result<Option<String>> {
  static CHECKED: Mutex<Option<HashMap<(String, String, String), bool>>> = Mutex::new(None);
  let db = ii::db_of(config)?;
  let Some(raw) = db.open_tree("at_primary")?.get(address.as_bytes())? else { return Ok(None) };
  let p: PrimaryEntry = bincode::deserialize(raw.as_ref()).context("decode at primary")?;
  let Some(handle) = p.name else { return Ok(None) };
  let Some(e) = get_entry(&db.open_tree("at_name")?, &handle)? else { return Ok(None) };
  let Some(reg) = dns::get_record(&db.open_tree("inscriptions_by_id")?, &e.inscription_id)? else { return Ok(None) };
  if reg.address != address {
    return Ok(None);
  }
  if dns::unmoved(&reg) {
    return Ok(Some(handle));
  }
  let key = (address.to_string(), format!("{}:{}", reg.txid, reg.vout), p.inscription_id.clone());
  if let Some(ok) = CHECKED.lock().unwrap_or_else(|e| e.into_inner()).as_ref().and_then(|m| m.get(&key).copied()) {
    return Ok(ok.then_some(handle));
  }
  let mut tracer = Tracer::new(config);
  let ok = match tracer.holders_since(&reg, (p.height, p.tx_index)).await? {
    Some(holders) => holders.iter().all(|h| h == address),
    None => false,
  };
  let mut guard = CHECKED.lock().unwrap_or_else(|e| e.into_inner());
  let map = guard.get_or_insert_with(HashMap::new);
  if map.len() > 10_000 {
    map.clear();
  }
  map.insert(key, ok);
  Ok(ok.then_some(handle))
}

#[cfg(test)]
mod tests {
  use super::*;

  /// spec `vectors/conformance.json` (version 1.1, 5c8dcc2), verbatim.
  #[test]
  fn conformance_vectors() {
    let reg = |b: &str| match parse_at_op("text/plain", b.as_bytes()) {
      Some(AtOp::Register { handle, .. }) => Some(("register", handle)),
      Some(AtOp::Config { handle, .. }) => Some(("config", handle)),
      Some(AtOp::Primary { handle }) => Some(("primary", handle.unwrap_or_default())),
      None => None,
    };
    let ok: &[(&str, &str, &str)] = &[
      ("@jon", "register", "@jon"),
      ("@jon\n", "register", "@jon"),
      ("@Jon", "register", "@jon"),
      ("＠ｊｏｎ", "register", "@jon"),
      ("@_jon", "register", "@_jon"),
      ("@abcdefghijklmno", "register", "@abcdefghijklmno"),
      (r#"{"p":"at","op":"register","name":"@jon"}"#, "register", "@jon"),
      (r#"{"p":"at","op":"reg","name":"jon"}"#, "register", "@jon"),
      (r#"{"p":"at","op":"config","name":"@jon","content":"hi"}"#, "config", "@jon"),
      (r#"{"p":"at","op":"upd","name":"jon","url":"https://dogecoin.dog"}"#, "config", "@jon"),
      (r#"{"p":"at","op":"primary","name":"@jon"}"#, "primary", "@jon"),
      // v1.1
      (r#"{"p":"AT","op":"reg","name":"jon"}"#, "register", "@jon"),
      (r#"{"p":"dns","p":"at","op":"reg","name":"jon"}"#, "register", "@jon"),
      ("@jon
", "register", "@jon"),
      ("﻿@jon", "register", "@jon"),
      (r#"{"p":"at","op":"config","name":"@jon","address":"D8mZsgKwmSQWYRPEMCcm8KzNFj1JVF5UpA"}"#, "config", "@jon"),
      (r#"{"p":"at","op":"primary","name":""}"#, "primary", ""),
    ];
    for (body, op, handle) in ok {
      assert_eq!(reg(body), Some((*op, handle.to_string())), "{body}");
    }
    let bad = [
      "jon",
      "@jon is mine",
      "follow @jon on chain",
      "@jon.doge",
      "jon.doge",
      r#"{"p":"dns","op":"register","name":"@jon"}"#,
      r#"{"p":"dx","op":"register","x_handle":"@jon","tweet_id":"1"}"#,
      "@jon-heaven",
      "@abcdefghijklmnop",
      "@",
      "AT1|reg|@jon|D8mZsgKwmSQWYRPEMCcm8KzNFj1JVF5UpA",
      r#"{"p":"at","op":"transfer","name":"@jon"}"#,
      r#"{"p":"at","op":"revoke","name":"@jon"}"#,
      r#"{"p":"at","op":"reg","name":"jon.doge"}"#,
      // v1.1
      r#"{"p":"@","op":"reg","name":"jon"}"#,
      r#"{"p":"handle","op":"reg","name":"@jon"}"#,
      r#"{"p":1,"op":"reg","name":"@jon"}"#,
      r#"{"p":"at","p":"dns","op":"reg","name":"jon"}"#,
      "@jon

",
      " @jon",
    ];
    for body in bad {
      assert_eq!(reg(body), None, "{body}");
    }
    // v1.1: the content type is never consulted
    assert!(matches!(parse_at_op("image/png", b"@jon"), Some(AtOp::Register { handle, .. }) if handle == "@jon"), "plain-content-type-ignored");
    // the record values the vectors give
    match parse_at_op("application/json", br#"{"p":"at","op":"config","name":"@jon","content":"hi"}"#) {
      Some(AtOp::Config { patch, .. }) => assert_eq!(patch.content.as_deref(), Some("hi")),
      other => panic!("{other:?}"),
    }
    match parse_at_op("application/json", br#"{"p":"at","op":"upd","name":"jon","url":"https://dogecoin.dog"}"#) {
      Some(AtOp::Config { patch, .. }) => assert_eq!(patch.url.as_deref(), Some("https://dogecoin.dog")),
      other => panic!("{other:?}"),
    }
  }

  #[test]
  fn body_rules_from_the_spec_text() {
    let h = |b: &[u8]| match parse_at_op("text/plain;charset=utf-8", b) {
      Some(AtOp::Register { handle, .. }) => Some(handle),
      _ => None,
    };
    assert_eq!(h(b"@jon\r\n"), Some("@jon".into()));
    assert_eq!(h("\u{FEFF}@jon".as_bytes()), Some("@jon".into()), "one leading BOM is stripped");
    assert_eq!(h(b" @jon"), None, "no whitespace");
    assert_eq!(h(b"@jon "), None);
    assert_eq!(h(b"@jon\n\n"), None, "only one trailing newline");
    assert_eq!(h(b"@jon\n@bob"), None, "one line");
    assert_eq!(h(b"@@jon"), None, "a second @");
    assert_eq!(h(b"@j\x01on"), None, "controls");
    assert_eq!(h(b"\xff@jon"), None, "invalid UTF-8");
    // a JSON body counts even as text/plain; a JSON name may omit the @
    assert_eq!(h(br#"  {"p":"at","op":"reg","name":"JON",}"#), Some("@jon".into()), "trailing comma accepted");
    // records: cname is a handle, a DNS cname is ignored, aliases work
    match parse_at_op("application/json", br#"{"p":"at","op":"register","name":"@jon","cname":"jon.doge","website":"https://x.dog","rev":"D7gFdhQo6YPVGWW3fyXgLYbDKhuUBZqmDk"}"#) {
      Some(AtOp::Register { records, .. }) => {
        assert_eq!(records.cname, None);
        assert_eq!(records.url.as_deref(), Some("https://x.dog"));
        assert_eq!(records.address.as_deref(), Some("D7gFdhQo6YPVGWW3fyXgLYbDKhuUBZqmDk"));
      }
      other => panic!("{other:?}"),
    }
    match parse_at_op("application/json", br#"{"p":"at","op":"config","name":"@jon","cname":"@Bob"}"#) {
      Some(AtOp::Config { patch, .. }) => assert_eq!(patch.cname.as_deref(), Some("@bob")),
      other => panic!("{other:?}"),
    }
    assert_eq!(parse_at_op("application/json", br#"{"p":"at","op":"primary","name":""}"#), Some(AtOp::Primary { handle: None }));
    assert!(parse_at_op("text/html", b"@jon").is_some(), "v1.1: the type doesn't matter");
    assert!(parse_at_op("", b"@jon").is_some(), "nor does a missing one");
    assert_eq!(normalize_handle("jon", true), Some("@jon".into()));
  }

  /// Emoji: the spec's vectors (c3cd509: `@🐕`, `@🐕\u{FE0F}` ok; `@🐕🐕` not in the spec, a handle
  /// of this index's extension) and the extension.
  #[test]
  fn emoji_handles() {
    let n = |s: &str| normalize_handle(s, false);
    assert_eq!(n("@🐕"), Some("@🐕".into()));
    assert_eq!(n("@🐕\u{FE0F}"), Some("@🐕".into()), "variation selectors are dropped");
    assert_eq!(n("@Doge🐕"), Some("@doge🐕".into()), "mixed with a-z");
    assert_eq!(n("@👍🏽"), Some("@👍🏽".into()), "skin tone");
    assert_eq!(n("@👨\u{200D}👩\u{200D}👧"), Some("@👨\u{200D}👩\u{200D}👧".into()), "ZWJ family");
    assert_eq!(n("@1\u{FE0F}\u{20E3}"), Some("@1\u{20E3}".into()), "keycap");
    assert_eq!(n("@🇺🇸"), Some("@🇺🇸".into()), "flag");
    assert_eq!(len_of("@👨\u{200D}👩\u{200D}👧"), 1);
    assert_eq!(len_of("@🇺🇸🇯🇵"), 2);
    assert_eq!(len_of("@a👍🏽"), 2);
    assert_eq!(n(&format!("@{}", "🐕".repeat(15))), Some(format!("@{}", "🐕".repeat(15))));
    assert_eq!(n(&format!("@{}", "🐕".repeat(16))), None, "16 symbols");
    assert_eq!(n("@\u{200D}🐕"), None, "a joiner not inside a sequence");
    assert_eq!(n("@🐕 🐕"), None, "a space");
    assert_eq!(n("@жон"), Some("@жон".into()), "other scripts: the wider extension");
    assert_eq!(n("@é"), Some("@é".into()));
    assert_eq!(n("@🐕.doge"), None);
    assert!(handle_is_emoji("@🐕") && !handle_is_emoji("@jon"));
    // spec ba673a0: emoji and flags are characters, mixed with letters, up to 15
    for (body, handle) in [("@🐕", "@🐕"), ("@🐕\u{FE0F}", "@🐕"), ("@🐕🐕", "@🐕🐕"), ("@Jon🐕", "@jon🐕"), ("@🇺🇸", "@🇺🇸"), ("@jon🇺🇸", "@jon🇺🇸"), ("@©", "@©")] {
      let h = n(body).unwrap_or_else(|| panic!("{body} is a handle"));
      assert_eq!(h, handle);
      assert!(handle_in_spec(&h), "{body} is in the spec");
    }
    assert!(handle_in_spec(&format!("@{}", "🐕".repeat(15))) && handle_in_spec(&format!("@{}", "🇺🇸".repeat(15))));
    // the extension: still handles here, not in the spec
    for ext in ["@👍🏽", "@👨\u{200D}👩\u{200D}👧", "@1\u{20E3}", "@🐕\u{200D}🦺"] {
      let h = n(ext).unwrap_or_else(|| panic!("{ext} is a handle of the extension"));
      assert!(!handle_in_spec(&h), "{ext} is the extension");
    }
    assert_eq!(n("@\u{1F1FA}"), Some("@\u{1F1FA}".into()), "a lone regional indicator: kept by the extension");
    assert!(!handle_in_spec("@\u{1F1FA}"), "a lone regional indicator is not in the spec");
    assert_eq!(bucket_of("@🐕"), EMOJI_BUCKET);
    assert_eq!(bucket_of("@🐕🐕"), EMOJI_BUCKET);
    assert_eq!(bucket_of("@jon🇺🇸"), EMOJI_BUCKET);
    assert_eq!(bucket_of("@👍🏽"), EXTENDED_BUCKET);
    assert_eq!(bucket_of("@jon"), 3);
    // a plain-text register of an emoji handle
    assert!(matches!(parse_at_op("text/plain", "@🐕".as_bytes()), Some(AtOp::Register { handle, .. }) if handle == "@🐕"));
    assert_eq!(normalize_handle("jon", false), None);
  }

  /// The wider extension: every kind of character, never at the spec's expense.
  #[test]
  fn every_character_type() {
    let n = |s: &str| normalize_handle(s, false);
    let wide = |body: &str, handle: &str| {
      let h = n(body).unwrap_or_else(|| panic!("{body} should be a handle"));
      assert_eq!(h, handle, "{body}");
      assert!(!handle_in_spec(&h), "{body} is the extension, not the spec");
    };
    wide("@₿illy", "@₿illy"); // the example: a currency sign
    wide("@€uro", "@€uro");
    wide("@∞", "@∞");
    wide("@Élodie", "@élodie"); // lowercased
    wide("@élodie", "@élodie"); // NFC: an accent typed apart is the same handle
    wide("@ЖОН", "@жон");
    wide("@太郎", "@太郎");
    wide("@محمد", "@محمد");
    wide("@שלום", "@שלום");
    wide("@ñandú", "@ñandú");
    wide("@٣", "@٣");
    wide("@Ⅻ", "@ⅻ");
    wide("@「jon」", "@「jon」");
    wide("@jon¡", "@jon¡");
    assert_eq!(parse_at_op("text/plain", "@₿illy".as_bytes()).map(|o| matches!(o, AtOp::Register { .. })), Some(true));
    // the spec's handles are read exactly as before
    assert_eq!(n("@Jon"), Some("@jon".into()));
    assert!(handle_in_spec("@jon🐕"));
    // never: mixed scripts, look-alikes of a spec handle, spaces, invisibles, ASCII punctuation, dots
    for bad in ["@bіlly", "@Kate", "@jon doe", "@jo​n", "@jon$", "@jon-doe", "@jon.doge", "@jon․doge", "@jon／x", "@jon﹫x", "@́jon", "@", "@á́́́́́", "@jon·"] {
      assert_eq!(n(bad), None, "{bad:?}");
    }
    assert_eq!(n(&format!("@{}", "ж".repeat(15))), Some(format!("@{}", "ж".repeat(15))));
    assert_eq!(n(&format!("@{}", "ж".repeat(16))), None, "16 symbols");
    assert_eq!(len_of("@élodie"), 6);
    assert_eq!(bucket_of("@₿illy"), EXTENDED_BUCKET);
    assert!(handle_confusable("@аре"), "all-Cyrillic letters that read as ape");
    assert!(!handle_confusable("@жон") && !handle_confusable("@jon") && !handle_confusable("@₿illy"));
  }

  /// Records belong to a holding (v1.1 §5.3): a move to another address resets them; a burned
  /// handle pays nobody.
  #[test]
  fn records_reset_when_the_holder_changes() {
    let me = "D8mZsgKwmSQWYRPEMCcm8KzNFj1JVF5UpA".to_string();
    let other = "D7gFdhQo6YPVGWW3fyXgLYbDKhuUBZqmDk".to_string();
    let patch = |a: &str| RecordPatch { address: Some(a.to_string()), ..RecordPatch::default() };
    let cfg = |owner: &str, pos: Pos, a: &str| HandleConfigView { inscription_id: String::new(), number: 0, height: pos.0, time: 0, owner: owner.into(), applies: false, pos, patch: patch(a) };
    let view = |owner: &str| HandleView {
      handle: "@jon".into(), inscription_id: String::new(), number: 0, height: 10, time: 0, owner: owner.into(), records: DnsRecords::default(),
      configs: vec![cfg(&me, (20, 0), "D9kTcGVqHLnBgmKrW9CvB7TrJ6tqC7wHXk"), cfg(&other, (30, 0), "DBXu2kgc3xtvCUWFcxFE3r9hEYgmuaaCyD")],
      claims: 0, pay_to: None, confusable: false, key: (10, 0, 0), from_commit: false, status: "final", final_after: 40, stored_key: None, reg_pos: (10, 0), reg_patch: RecordPatch::default(),
    };
    // held since before its config: the record counts
    let mut v = view(&me);
    v.settle(|_| true);
    assert_eq!(v.pay_to.as_deref(), Some("D9kTcGVqHLnBgmKrW9CvB7TrJ6tqC7wHXk"));
    // sold to `other`: my config never applies to them, and theirs counts once they hold it
    let mut v = view(&other);
    v.settle(|p| p >= (30, 0));
    assert_eq!(v.pay_to.as_deref(), Some("DBXu2kgc3xtvCUWFcxFE3r9hEYgmuaaCyD"));
    // it came back to me after a sale: my old config is from before the break, so it's gone
    let mut v = view(&me);
    v.settle(|p| p >= (40, 0));
    assert_eq!(v.pay_to.as_deref(), Some(me.as_str()), "pays the holder, not the old record");
    // burned: no pay-to at all
    let mut v = view("");
    v.settle(|_| true);
    assert_eq!(v.pay_to, None);
    assert!(v.records.address.is_none());
  }
}
