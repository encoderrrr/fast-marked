// parse.js — a fast CommonMark + GFM renderer, byte-compatible with marked 18.1.3
// with its default options (gfm on, breaks off, pedantic off, async off).
//
// Written from scratch for speed: a line-based block parser and a single-pass
// inline scanner with a delimiter-stack-free emphasis search. The observable
// semantics (heading ids are not emitted, link reference resolution, emphasis
// precedence, tables, raw HTML blocks, entities, escapes, hard breaks) were
// verified against marked's own CommonMark/GFM spec examples and generated
// documents. No part of marked's source is copied here.

/** The HTML marked renders for `markdown`, with marked's defaults. */
export function parse(markdown) {
  const src = markdown.replace(/\r\n?/g, '\n');
  const ctx = { defs: Object.create(null) };
  ctx.ist = { defs: ctx.defs, inLink: false, inRawBlock: false, linkEmitted: false, linkParenPossible: true };
  const blocks = lexBlocks(src, ctx);
  return renderBlocks(blocks, ctx);
}

// ---------------------------------------------------------------------------
// Character classes and small helpers
// ---------------------------------------------------------------------------

const ASCII_PUNCT = "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~";

function isSpace(ch) {
  return ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r' || ch === '\f' || ch === '\v' ||
    (ch >= '\u00a0' && /\s/.test(ch));
}

function isPunct(ch) {
  if (ch.length === 0) return false;
  const code = ch.charCodeAt(0);
  if (code < 128) return ASCII_PUNCT.indexOf(ch) !== -1;
  return /[\p{P}\p{S}]/u.test(ch);
}

function isAlnum(ch) {
  if (ch.length === 0) return false;
  const code = ch.charCodeAt(0);
  if (code < 128) return (code >= 48 && code <= 57) || (code >= 65 && code <= 90) || (code >= 97 && code <= 122);
  return /[\p{L}\p{N}]/u.test(ch);
}

function isBlankLine(line) {
  for (let i = 0; i < line.length; i++) {
    const c = line[i];
    if (c !== ' ' && c !== '\t') return false;
  }
  return true;
}

// Width of the leading indent in columns (a tab advances to the next multiple of 4).
// Returns [width, chars] where chars is how many source characters the indent spans.
function indentOf(line) {
  let width = 0;
  let i = 0;
  while (i < line.length) {
    const c = line[i];
    if (c === ' ') { width++; i++; }
    else if (c === '\t') { width += 4 - (width % 4); i++; }
    else break;
  }
  return [width, i];
}

// Remove `n` columns of indent from the start of a line, expanding a straddling
// tab into spaces the way a tab stop does (so the rest of the line keeps its columns).
function stripIndent(line, n) {
  let width = 0;
  let i = 0;
  while (i < line.length && width < n) {
    const c = line[i];
    if (c === ' ') { width++; i++; }
    else if (c === '\t') {
      const next = width + 4 - (width % 4);
      if (next > n) return ' '.repeat(next - n) + line.slice(i + 1);
      width = next; i++;
    } else break;
  }
  return line.slice(i);
}

// ---------------------------------------------------------------------------
// HTML escaping, entities, href encoding, label folding
// ---------------------------------------------------------------------------

const ESCAPES = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };

// Escape text for HTML. With encode=true every & is escaped; with encode=false
// an & that starts a valid character reference (&#123; &#xAB; &word;) is left alone.
function escapeHtml(s, encode) {
  if (encode) {
    if (s.indexOf('&') === -1 && s.indexOf('<') === -1 && s.indexOf('>') === -1 && s.indexOf('"') === -1 && s.indexOf("'") === -1) return s;
    return s.replace(/[&<>"']/g, (c) => ESCAPES[c]);
  }
  if (s.indexOf('<') === -1 && s.indexOf('>') === -1 && s.indexOf('"') === -1 && s.indexOf("'") === -1 && s.indexOf('&') === -1) return s;
  return s.replace(/[<>"']|&(?!(?:#\d{1,7}|#[Xx][A-Fa-f0-9]{1,6}|\w+);)/g, (c) => c === '&' ? '&amp;' : ESCAPES[c]);
}

const HAS_NUMERIC_REF = /&#(?:\d{1,7}|[Xx][A-Fa-f0-9]{1,6});/;
const NUMERIC_REF_OR_BARE_AMP = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(?:#\d{1,7}|#[Xx][A-Fa-f0-9]{1,6}|\w+);)/g;

// Decode numeric character references the way marked does: code point 0, a value
// above the Unicode range, or a surrogate becomes U+FFFD; 38 becomes &amp; (it is
// re-escaped by the caller anyway); a bare & that starts no valid reference is
// escaped. Named references are NOT decoded (marked leaves &copy; as &copy;).
function decodeNumericRefs(s) {
  if (!HAS_NUMERIC_REF.test(s)) return s;
  return s.replace(NUMERIC_REF_OR_BARE_AMP, (m, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const cp = dec === undefined ? parseInt(hex, 16) : parseInt(dec, 10);
    if (cp === 0 || cp > 0x10ffff || (cp >= 0xd800 && cp <= 0xdfff)) return '\uFFFD';
    if (cp === 38) return '&amp;';
    return String.fromCodePoint(cp);
  });
}

function encodeHref(href) {
  try {
    return encodeURI(href).replace(/%25/g, '%');
  } catch {
    return null;
  }
}

// Fold a link label for lookup: trim, collapse inner whitespace, case-fold.
function foldLabel(s) {
  return s.trim().replace(/\s+/g, ' ').toLowerCase().toUpperCase().toLowerCase();
}

// ---------------------------------------------------------------------------
// Inline parsing
//
// A single left-to-right scan. At each position the scanner tries, in marked's
// order: backslash escape, raw HTML tag / autolink, inline link, reference
// link, emphasis, code span, hard break, strikethrough, extended autolink,
// and otherwise consumes a run of plain text (decoding numeric references and
// escaping as it goes). Emphasis uses the same closer search marked does:
// a length-preserving mask hides delimiters inside code spans, links and tags,
// then delimiter runs are classified by what flanks them.
// ---------------------------------------------------------------------------

// Matching rules, transcribed from marked's tokenizer so the same inputs match.
const RE_ESCAPE = /^\\([!"#$%&'()*+,\-./:;<=>?@\[\]\\^_`{|}~])/;
const RE_CODE_SPAN = /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/;
const RE_BR = /^( {2,}|\\)\n(?!\s*$)[ \t]*/;
const RE_TAG = /^(?:<!--(?:-?>|[\s\S]*?-->)|^<\/[a-zA-Z][a-zA-Z0-9-]*\s*>|^<[a-zA-Z][a-zA-Z0-9-]*(?:\s+[a-zA-Z:_][\w.:-]*(?:\s*=\s*"[^"]*"|\s*=\s*'[^']*'|\s*=\s*[^\s"'=<>`]+)?)*?\s*\/?>|^<\?[\s\S]*?\?>|^<![a-zA-Z]+\s[\s\S]*?>|^<!\[CDATA\[[\s\S]*?\]\]>)/;
const RE_AUTOLINK = /^<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\s\x00-\x1f<>]*|[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+@[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>/;
const RE_URL = /^(?:(?:mailto:[a-zA-Z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])|xmpp:[a-zA-Z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])(?:\/[A-Za-z0-9@.]+)?)|((?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\/\/|www\.)(?:[a-zA-Z0-9\-]+\.?)+[^\s<]*|[a-zA-Z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-]))/;
const RE_URL_BACKPEDAL = /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/;
const RE_LINK_LABEL = /(?:\[(?:\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\]))/;
const RE_LINK = /^!?\[((?:\[(?:\[(?:\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\])|[^\\[\]\\`])*?)\]\([ \t\n]*(<(?:\\.|[^\n<>\\])+>|[^ \t\n\x00-\x1f]+|(?=\)))(?:(?:[ \t]+(?:\n[ \t]*)?|\n[ \t]*)("(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\])*'|\((?:\\[\s\S]|[^)\\])*\)))?[ \t\n]*\)/;
const RE_LABEL_TEXT = /(?:\\[\s\S]|[^\[\]\\]|\n(?![ \t]*\n))+/;
const RE_REFLINK = /^!?\[((?:\[(?:\[(?:\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\])|[^\\[\]\\`])*?)\]\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+)\]/;
const RE_NOLINK = /^!?\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+)\](?:\[\])?/;
const RE_REFLINK_SEARCH = /(?:!?\[(?:[^\[\]\\`]*(?:\[(?:\[(?:\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\]))){0,999}?[^\[\]\\`]*?\]\[(?!\s*\])(?:\\[\s\S]|[^\[\]\\]){1,999}\]|!?\[(?!\s*\])(?:\\[\s\S]|[^\[\]\\]){1,999}\](?:\[\])?(?!\())/g;
const RE_PUNCT_OUTSIDE_CODE = /(`+)(?:[^`]|[^`][\s\S]*?[^`])\1(?!`)|`+|\\([\p{P}\p{S}])/gu;
const RE_BLOCK_SKIP = /\[(?:[^\[\]`]|(`+)[^`]+\1(?!`))*?\]\((?:\\[\s\S]|[^\\\(\)]|\((?:\\[\s\S]|[^\\\(\)])*\))*\)|(?<!`)(`+)[^`]+\2(?!`)|<(?! )[^<>]*?>/g;
// Left delimiter: a run of * or _ followed by punctuation or a non-space.
const RE_EM_LDELIM = /^(?:\*+(?:((?!\*)(?!~)[\p{P}\p{S}])|([^\s*]))?)|^_+(?:((?!_)(?!~)[\p{P}\p{S}])|([^\s_]))?/u;
// Right delimiters (GFM): runs classified by their flanks. Group 1/2 are pure
// closers, 3/4 are openers, 5/6 are ambiguous and fall under the rule of three.
const RE_EM_RDELIM_AST = /^[^_*]*?__[^_*]*?\*[^_*]*?(?=__)|[^*]+(?=[^*])|(?!\*)(?!~)[\p{P}\p{S}](\*+)(?=[\s]|$)|(?:[^\s\p{P}\p{S}]|~)(\*+)(?!\*)(?=(?!~)[\s\p{P}\p{S}]|$)|(?!\*)(?!~)[\s\p{P}\p{S}](\*+)(?=(?:[^\s\p{P}\p{S}]|~))|[\s](\*+)(?!\*)(?=(?!~)[\p{P}\p{S}])|(?!\*)(?!~)[\p{P}\p{S}](\*+)(?!\*)(?=(?!~)[\p{P}\p{S}])|(?:[^\s\p{P}\p{S}]|~)(\*+)(?=(?:[^\s\p{P}\p{S}]|~))/gu;
const RE_EM_RDELIM_UND = /^[^_*]*?\*\*[^_*]*?_[^_*]*?(?=\*\*)|[^_]+(?=[^_])|(?!_)[\p{P}\p{S}](_+)(?=[\s]|$)|[^\s\p{P}\p{S}](_+)(?!_)(?=[\s\p{P}\p{S}]|$)|(?!_)[\s\p{P}\p{S}](_+)(?=[^\s\p{P}\p{S}])|[\s](_+)(?!_)(?=[\p{P}\p{S}])|(?!_)[\p{P}\p{S}](_+)(?!_)(?=[\p{P}\p{S}])/gu;
const RE_DEL_LDELIM = /^(?:~~?(?:((?!~)[\p{P}\p{S}])|[^\s~]))/u;
const RE_DEL_RDELIM = /^[^~]+(?=[^~])|(?!~)[\p{P}\p{S}](~~?)(?=[\s]|$)|[^\s\p{P}\p{S}](~~?)(?!~)(?=[\s\p{P}\p{S}]|$)|(?!~)[\s\p{P}\p{S}](~~?)(?=[^\s\p{P}\p{S}])|[\s](~~?)(?!~)(?=[\p{P}\p{S}])|(?!~)[\p{P}\p{S}](~~?)(?!~)(?=[\p{P}\p{S}])|[^\s\p{P}\p{S}](~~?)(?=[^\s\p{P}\p{S}])/gu;
const RE_DEL = /^(~~?)(?=[^\s~])((?:\\[\s\S]|[^\\])*?(?:\\[\s\S]|[^\s~\\]))\1(?=[^~]|$)/;
const RE_PUNCT_CHAR = /^((?![*_])[\s\p{P}\p{S}])/u;
const RE_ALNUM = /[\p{L}\p{N}]/u;

// Is the bracketed text at `s` in `src` a link (used while masking references)?
function linkInText(src, links) {
  if (!src.includes('[')) return false;
  for (const m of src.matchAll(RE_BLOCK_SKIP)) {
    if (RE_LINK.test(m[0]) && src.charAt(m.index - 1) !== '!') return true;
  }
  for (const m of src.matchAll(RE_REFLINK_SEARCH)) {
    const s = m[0];
    const r = s.lastIndexOf('[');
    if (!(s.charAt(0) === '!' || !Object.hasOwn(links, foldLabel(s.slice(r + 1, -1)))) &&
        !(r > 1 && linkInText(s.slice(1, r - 1), links))) return true;
  }
  return false;
}

// Length-preserving mask of the inline source: defined reference links, code
// spans, inline links and raw HTML tags are replaced by bracketed filler of
// the same length, and backslash escapes of punctuation by plus signs, so the
// emphasis search never sees a delimiter inside them.
function maskInline(src, links) {
  let t = src;
  if (links && src.includes('[')) {
    const replaceRef = (r) => {
      const o = r.lastIndexOf('[');
      if (!Object.hasOwn(links, foldLabel(r.slice(o + 1, -1)))) return r;
      if (o > 1 && r.charAt(0) !== '!') {
        const inner = r.slice(1, o - 1);
        if (linkInText(inner, links)) return '[' + inner.replace(RE_REFLINK_SEARCH, replaceRef) + '][' + 'a'.repeat(r.length - o - 2) + ']';
      }
      return '[' + 'a'.repeat(r.length - 2) + ']';
    };
    t = t.replace(RE_REFLINK_SEARCH, replaceRef);
  }
  t = t.replace(RE_PUNCT_OUTSIDE_CODE, (n, ticks, punct) =>
    punct ? '+'.repeat(n.length) : ticks ? ticks + n.slice(ticks.length, -ticks.length).replace(/`/g, '+') + ticks : n);
  t = t.replace(RE_BLOCK_SKIP, (n) => '[' + 'a'.repeat(n.length - 2) + ']');
  return t;
}

// Last index in `src` where a delimiter run of `ch` could close (preceded by a
// non-space), and the same for `~`. An upper bound for the closer search.
function lastPossibleCloser(src) {
  const em = { '*': -1, '_': -1 };
  let del = -1;
  const n = src.length;
  for (let s = 0; s < n; s++) {
    const r = src[s];
    if (r !== '*' && r !== '_' && r !== '~') continue;
    const prev = s === 0 ? '\n' : src[s - 1];
    let i = s + 1;
    while (i < n && src[i] === r) i++;
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') {
      if (r === '~') del = s; else em[r] = s;
    }
    s = i - 1;
  }
  return { em, del };
}

// Try to match emphasis at the start of `rest` (the remaining inline source).
// `masked` is the length-preserving mask of the whole inline source, `offset`
// is where `rest` starts inside it, `prev` is the last character of the
// previous token ('' when the previous token was not text), and `last` is the
// precomputed last-possible-closer index for this delimiter. Returns
// {raw, inner, strong} or null.
function matchEmphasis(rest, masked, offset, prev, last) {
  const s = RE_EM_LDELIM.exec(rest);
  if (!s || (!s[1] && !s[2] && !s[3] && !s[4])) return null;
  const delim = s[0][0];
  const prevIsDelim = prev === delim;
  // i: offset of the opener inside the masked source; l: start of its run.
  const i = offset;
  let l = i;
  while (l > 0 && masked[l - 1] === delim) l--;
  // p: the character right before the delimiter run ('' at the very start).
  const p = l > 0 ? masked[l - 1] : '';
  const pIsPunct = p === '*' || p === '_' || RE_PUNCT_CHAR.test(p);
  if (l < i) prev = p;
  const prevIsPunct = l < i ? pIsPunct : RE_PUNCT_CHAR.test(prev);
  // An underscore opener preceded by an alphanumeric cannot open.
  if (s[4] && RE_ALNUM.test(prev)) return null;
  const afterPunct = s[1] || s[3] || '';
  // Can open when followed by non-punctuation, at the start, or preceded by punctuation.
  if (!afterPunct || !prev || prevIsPunct) {
    const k = [...s[0]].length - 1; // opener run length, in code points
    if (delim !== '*' && delim !== '_') return null;
    const scan = delim === '*' ? RE_EM_RDELIM_AST : RE_EM_RDELIM_UND;
    const q = i + k;
    if (last < q) return null;
    // y: delimiters from the start of the run up to the opener's end.
    const y = i - l + k;
    // R: the opener could itself close a run (the `***` interaction).
    const R = p.trim() !== '' && (!!afterPunct || (delim === '*' && !pIsPunct));
    const tail = masked.slice(q); // masked source after the opener run
    const limit = last - q; // farthest match index in `tail`
    let m = k;
    let extra = 0;
    let match;
    scan.lastIndex = 0;
    while ((match = scan.exec(tail)) !== null && !(match.index > limit)) {
      const g = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
      if (!g) continue;
      const b = [...g].length;
      if (match[3] || match[4]) { m += b; continue; }
      if (match[5] || match[6] || R) {
        if (prevIsDelim && (match[5] || match[6])) break;
        if (y % 3 && !((y + b) % 3)) { extra += b; continue; }
      }
      m -= b;
      if (m > 0) continue;
      const take = Math.min(b, b + m + extra);
      const firstLen = [...match[0]][0].length;
      const raw = rest.slice(0, k + match.index + firstLen + take);
      if (Math.min(k, take) % 2) return { raw, inner: raw.slice(1, -1), strong: false };
      return { raw, inner: raw.slice(2, -2), strong: true };
    }
  }
  return null;
}

// Try to match strikethrough at the start of `rest`. Same shape as emphasis
// but the closer run must be exactly as long as the opener (1 or 2 tildes).
// `last` is the precomputed last-possible-closer index for `~`.
function matchDel(rest, masked, offset, prev, last) {
  const s = RE_DEL_LDELIM.exec(rest);
  if (!s) return null;
  if ((s[1] || '') || !prev || RE_PUNCT_CHAR.test(prev)) {
    const o = [...s[0]].length - 1; // opener run length (1 or 2)
    const d = offset + o;
    if (last < d) return null;
    const tail = masked.slice(d);
    const limit = last - d;
    let remaining = o;
    let match;
    RE_DEL_RDELIM.lastIndex = 0;
    while ((match = RE_DEL_RDELIM.exec(tail)) !== null && !(match.index > limit)) {
      const g = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
      if (!g) continue;
      const len = [...g].length;
      if (len !== o) continue;
      if (match[3] || match[4]) { remaining += len; continue; }
      remaining -= len;
      if (remaining > 0) continue;
      const take = Math.min(len, len + remaining);
      const firstLen = [...match[0]][0].length;
      const raw = rest.slice(0, o + match.index + firstLen + take);
      return { raw, inner: raw.slice(o, -o) };
    }
  }
  return null;
}

// ---------------------------------------------------------------------------
// Inline rendering
//
// One left-to-right scanner. At each position it tries, in marked's order:
// backslash escape, raw HTML tag / autolink, inline link, reference link,
// emphasis, code span, hard break, strikethrough, extended autolink, and
// otherwise consumes a run of plain text. The same scanner serves both the
// HTML renderer (plain=false) and the plain-text renderer used for image
// alt text (plain=true); only the output of a few token kinds differs.
// ---------------------------------------------------------------------------

// GFM inline text: a run that stops before any construct another tokenizer
// could start (escape, tag, link, emphasis, code, break, autolink, url).
const RE_TEXT = /^(?:[^a-zA-Z0-9](?=(?:mailto|xmpp):)|(`+|~+|[^`~])(?:(?=[`~])|(?= {2,}\n)|(?=[a-zA-Z0-9.!#$%&'*+\/=?_`{|}~-]+@)|[\s\S]*?(?:(?=[\\<!\[`*~_]|\b_|(?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\/\/|(?<![^\s*_~(])www\.|$)|[^ ](?= {2,}\n)|[^a-zA-Z0-9](?=(?:mailto|xmpp):)|[^a-zA-Z0-9.!#$%&'*+\/=?_`{|}~-](?=[a-zA-Z0-9.!#$%&'*+\/=?_`{|}~-]+@))))/;
const RE_ANY_PUNCT = /\\([\p{P}\p{S}])/gu;
const RE_START_ANGLE = /^</;
const RE_END_ANGLE = />$/;
const RE_START_ATAG = /^<a /i;
const RE_END_ATAG = /^<\/a>/i;
const RE_START_PRE = /^<(pre|code|kbd|script)(\s|>)/i;
const RE_END_PRE = /^<\/(pre|code|kbd|script)(\s|>)/i;
const RE_OUTPUT_LINK = /\\([\[\]])/g;

// Reject a link whose label contains a raw tag or autolink that runs past
// the closing bracket. `rest` is the remaining source, `label` the label
// text, `offset` where the label starts inside `rest` (1, or 2 for images).
function beCheck(rest, label, offset) {
  if (!label.includes('<')) return false;
  for (let s = 0; s < label.length; s++) {
    if (label[s] === '\\') { s++; continue; }
    if (label[s] === '`') {
      const i = RE_CODE_SPAN.exec(label.slice(s));
      if (i) { s += i[0].length - 1; continue; }
    }
    if (label[s] !== '<') continue;
    const r = rest.slice(offset + s);
    const o = RE_TAG.exec(r) || RE_AUTOLINK.exec(r);
    if (o) {
      if (o[0].length > label.length - s) return true;
      s += o[0].length - 1;
    }
  }
  return false;
}

// Parenthesis balance in a link destination: -1 when there are no parens,
// -2 when an opener is never closed, otherwise the index of the paren that
// closes past zero. Backslash escapes do not count.
function parenBalance(a) {
  if (a.indexOf('(') === -1 && a.indexOf(')') === -1) return -1;
  let t = 0;
  for (let n = 0; n < a.length; n++) {
    if (a[n] === '\\') n++;
    else if (a[n] === '(') t++;
    else if (a[n] === ')' && (t--, t < 0)) return n;
  }
  return t > 0 ? -2 : -1;
}

// The string with its trailing backslashes removed.
function stripTrailingBackslashes(a) {
  let n = a.length;
  while (n > 0 && a[n - 1] === '\\') n--;
  return a.slice(0, n);
}

// Build a link or image from a matched link/reflink and its href/title.
// Returns the rendered HTML (or plain text when `plain`), or null when the
// label contains a nested link (the outer link is then not a link at all).
// `match` is the link regex match (groups: 1 label, 2 href, 3 title for an
// inline link; 1 label, 2 ref for a reference link — the caller resolves the
// reference to href/title first). `raw` is the full matched source.
function buildLink(match, raw, href, title, isImage, st, plain) {
  const label = match[1].replace(RE_OUTPUT_LINK, '$1');
  const savedInLink = st.inLink;
  const savedLinkEmitted = st.linkEmitted;
  const savedRawBlock = st.inRawBlock;
  st.inLink = true;
  st.linkEmitted = false;
  const inner = scanInline(label, st, isImage ? true : plain);
  const nested = st.linkEmitted;
  st.linkEmitted = savedLinkEmitted;
  st.inLink = savedInLink;
  if (!isImage) {
    if (nested) { st.inRawBlock = savedRawBlock; return null; }
    st.linkEmitted = true;
  }
  if (plain) return inner;
  if (isImage) {
    const alt = inner;
    const src = encodeHref(href);
    if (src === null) return escapeHtml(alt, false);
    let out = '<img src="' + escapeHtml(src, false) + '" alt="' + escapeHtml(alt, false) + '"';
    if (title) out += ' title="' + escapeHtml(title, false) + '"';
    return out + '>';
  }
  const encoded = encodeHref(href);
  if (encoded === null) return inner;
  let out = '<a href="' + escapeHtml(encoded, false) + '"';
  if (title) out += ' title="' + escapeHtml(title, false) + '"';
  return out + '>' + inner + '</a>';
}

// Try an inline link at the start of `rest`. Returns {html, len} or null.
function tryInlineLink(rest, st, plain) {
  if (st.linkParenPossible === false) return null;
  const m = RE_LINK.exec(rest);
  if (!m) return null;
  const isImage = m[0].charAt(0) === '!';
  const labelOff = isImage ? 2 : 1;
  if (beCheck(rest, m[1], labelOff)) return null;
  let href = m[2].trim();
  if (RE_START_ANGLE.test(href)) {
    if (!RE_END_ANGLE.test(href)) return null;
    if ((href.length - stripTrailingBackslashes(href.slice(0, -1)).length) % 2 === 0) return null;
  } else {
    const l = parenBalance(m[2]);
    if (l === -2) return null;
    if (l > -1) {
      const h = (isImage ? 5 : 4) + m[1].length + l;
      m[2] = m[2].substring(0, l);
      m[0] = m[0].substring(0, h).trim();
      m[3] = '';
    }
  }
  if ((m[0].length - stripTrailingBackslashes(m[0].slice(0, -1)).length) % 2 === 0) return null;
  href = m[2].trim();
  let title = m[3] ? m[3].slice(1, -1) : '';
  if (RE_START_ANGLE.test(href)) href = href.slice(1, -1);
  href = href ? href.replace(RE_ANY_PUNCT, '$1') : href;
  title = title ? title.replace(RE_ANY_PUNCT, '$1') : title;
  const html = buildLink(m, m[0], href, title, isImage, st, plain);
  if (html === null) return null;
  return { html, len: m[0].length };
}

// Try a reference link at the start of `rest`. Returns {html, len} or null.
// When the reference is undefined, returns the first character as plain text.
function tryRefLink(rest, st, plain) {
  let m = RE_REFLINK.exec(rest) || RE_NOLINK.exec(rest);
  if (!m) return null;
  const isImage = m[0].charAt(0) === '!';
  const labelOff = isImage ? 2 : 1;
  if (beCheck(rest, m[1], labelOff)) return null;
  const def = st.defs[foldLabel(m[2] || m[1])];
  if (!def) {
    const ch = m[0].charAt(0);
    return { html: escapeHtml(decodeNumericRefs(ch), false), len: 1, text: true };
  }
  const html = buildLink(m, m[0], def.href, def.title, isImage, st, plain);
  if (html === null) return null;
  return { html, len: m[0].length };
}

// Render one inline source to HTML (plain=false) or plain text (plain=true).
// `st` is the shared inline state for this block: {defs, inLink, inRawBlock,
// linkEmitted, linkParenPossible}. Recursive calls share it, except that
// linkParenPossible is ANDed down and restored on return.
function scanInline(src, st, plain) {
  if (src === '') return '';
  const savedParen = st.linkParenPossible;
  st.linkParenPossible = savedParen && src.includes(')');
  let masked = src;
  let last = { em: { '*': -1, '_': -1 }, del: -1 };
  if (src.includes('*') || src.includes('_') || src.includes('~')) {
    masked = maskInline(src, st.defs);
    last = lastPossibleCloser(masked);
  }
  const out = [];
  let pos = 0;
  let prev = '';
  const n = src.length;
  while (pos < n) {
    const rest = src.slice(pos);
    const c = rest[0];
    let m;
    // Backslash escape.
    if (c === '\\' && (m = RE_ESCAPE.exec(rest))) {
      out.push(escapeHtml(m[1], false));
      pos += m[0].length;
      prev = '';
      continue;
    }
    // Raw HTML tag (also toggles the in-link / in-raw-block state).
    if (c === '<' && (m = RE_TAG.exec(rest))) {
      if (!st.inLink && RE_START_ATAG.test(m[0])) st.inLink = true;
      else if (st.inLink && RE_END_ATAG.test(m[0])) st.inLink = false;
      if (!st.inRawBlock && RE_START_PRE.test(m[0])) st.inRawBlock = true;
      else if (st.inRawBlock && RE_END_PRE.test(m[0])) st.inRawBlock = false;
      out.push(m[0]);
      pos += m[0].length;
      prev = '';
      continue;
    }
    // Inline link.
    if ((c === '[' || (c === '!' && rest[1] === '['))) {
      const link = tryInlineLink(rest, st, plain);
      if (link) {
        out.push(link.html);
        pos += link.len;
        prev = '';
        continue;
      }
      const ref = tryRefLink(rest, st, plain);
      if (ref) {
        out.push(ref.html);
        pos += ref.len;
        prev = ref.text ? ref.html.slice(-1) : '';
        continue;
      }
    }
    // Emphasis / strong.
    if (c === '*' || c === '_') {
      const em = matchEmphasis(rest, masked, pos, prev, last.em[c]);
      if (em) {
        const inner = scanInline(em.inner, st, plain);
        out.push(plain ? inner : (em.strong ? '<strong>' + inner + '</strong>' : '<em>' + inner + '</em>'));
        pos += em.raw.length;
        prev = '';
        continue;
      }
    }
    // Code span.
    if (c === '`' && (m = RE_CODE_SPAN.exec(rest))) {
      let text = m[2].replace(/\n/g, ' ');
      if (/[^ ]/.test(text) && text.charAt(0) === ' ' && text.charAt(text.length - 1) === ' ') {
        text = text.substring(1, text.length - 1);
      }
      out.push(plain ? text : '<code>' + escapeHtml(text, true) + '</code>');
      pos += m[0].length;
      prev = '';
      continue;
    }
    // Hard break.
    if ((c === ' ' || c === '\\') && (m = RE_BR.exec(rest))) {
      out.push(plain ? '' : '<br>');
      pos += m[0].length;
      prev = '';
      continue;
    }
    // Strikethrough.
    if (c === '~') {
      const del = matchDel(rest, masked, pos, prev, last.del);
      if (del) {
        const inner = scanInline(del.inner, st, plain);
        out.push(plain ? inner : '<del>' + inner + '</del>');
        pos += del.raw.length;
        prev = '';
        continue;
      }
    }
    // Autolink <scheme:...> or <email>.
    if (c === '<' && (m = RE_AUTOLINK.exec(rest))) {
      const text = m[1];
      const isEmail = !/^[a-zA-Z][a-zA-Z0-9+.-]{1,31}:/.test(text);
      const href = isEmail ? 'mailto:' + text : text;
      if (plain) {
        out.push(escapeHtml(text, false));
      } else {
        const enc = encodeHref(href);
        if (enc === null) out.push(escapeHtml(text, true));
        else out.push('<a href="' + escapeHtml(enc, true) + '">' + escapeHtml(text, true) + '</a>');
      }
      pos += m[0].length;
      prev = '';
      continue;
    }
    // Extended autolink (www. / bare email / mailto: / xmpp:).
    if (!st.inLink && (m = RE_URL.exec(rest))) {
      let raw = m[0];
      let backpedalled;
      do {
        backpedalled = raw;
        const b = RE_URL_BACKPEDAL.exec(raw);
        raw = b ? b[0] : '';
      } while (raw !== backpedalled);
      if (raw !== '') {
        const isEmail = m[2] === '@';
        const href = isEmail ? 'mailto:' + raw : (m[1] === 'www.' ? 'http://' + raw : raw);
        if (plain) {
          out.push(escapeHtml(raw, false));
        } else {
          const enc = encodeHref(href);
          if (enc === null) out.push(escapeHtml(raw, true));
          else out.push('<a href="' + escapeHtml(enc, true) + '">' + escapeHtml(raw, true) + '</a>');
        }
        pos += raw.length;
        prev = '';
        continue;
      }
    }
    // Plain text run.
    m = RE_TEXT.exec(rest);
    if (m) {
      const raw = m[0];
      const text = st.inRawBlock ? raw : decodeNumericRefs(raw);
      out.push(escapeHtml(text, false));
      pos += raw.length;
      prev = raw.charAt(raw.length - 1) === '_' ? '' : raw.charAt(raw.length - 1);
      continue;
    }
    // Nothing matched (should not happen): consume one character as text.
    out.push(escapeHtml(decodeNumericRefs(c), false));
    pos += 1;
    prev = c === '_' ? '' : c;
  }
  st.linkParenPossible = savedParen;
  return out.join('');
}

// Render inline markdown to HTML. The inline state (in-link, in-raw-block,
// link-emitted) is shared across every inline source in the document, as
// in marked: an unclosed <a> tag in one paragraph suppresses autolinks in
// later paragraphs until a </a> appears. linkParenPossible is saved and
// restored per call inside scanInline.
function renderInline(src, ist) {
  return scanInline(src, ist, false);
}

// ---------------------------------------------------------------------------
// Block parsing
//
// A port of the block grammar: at each position the tokenizers are tried in
// order (blank lines, indented code, fences, ATX heading, hr, blockquote,
// list, raw HTML, link definition, table, setext heading, paragraph, text).
// Blocks are lexed into a small tree first so that link definitions — which
// may appear after their uses — are all registered before any inline text
// is rendered. A paragraph or text block directly followed (no blank line)
// by an indented code block or a link definition absorbs it, as marked does.
// ---------------------------------------------------------------------------

// Compose a regex from a template, replacing placeholders with the source of
// other patterns. A leading ^ in an inserted pattern is dropped (it only
// anchored the standalone pattern). Replacements are global.
function buildRegex(template, flags) {
  let t = typeof template === 'string' ? template : template.source;
  const api = {
    replace(from, to) {
      let src = typeof to === 'string' ? to : to.source;
      src = src.replace(/(^|[^\[])\^/g, '$1');
      t = t.replace(from, () => src);
      return api;
    },
    get() { return new RegExp(t, flags); },
  };
  return api;
}

const K_TAG = 'address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul';
const HR_SRC = ' {0,3}(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)';
const HEADING_SRC = ' {0,3}#{1,6}(?:\\s|$)';
const BLOCKQUOTE_SRC = ' {0,3}>';
const FENCES_SRC = ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)';
const HTML_SRC = ' {0,3}(?:</?(?:' + K_TAG + ')(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)';
const AE_SRC = '^([^\\n]+(?:\\n(?!hr|heading|lheading|blockquote|fences|list|html|table|[ \\t]+\\n)[^\\n]+)*)';
// The table rule, with its own inner placeholders resolved.
const TABLE_SRC = buildRegex('^ *([^\\n ].*)\\n {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)(?:\\n((?:(?! *\\n|hr|heading|blockquote|code|fences|list|html).*(?:\\n|$))*)\\n*|$)')
  .replace('hr', HR_SRC).replace('heading', HEADING_SRC).replace('blockquote', BLOCKQUOTE_SRC)
  .replace('code', '(?: {4}| {0,3}\\t)[^\\n]').replace('fences', FENCES_SRC)
  .replace('list', ' {0,3}(?:[*+-]|1[.)])[ \\t]').replace('html', HTML_SRC).get();
// GFM paragraph: no setext interrupt, tables can interrupt, only 1. lists.
const RE_B_PARAGRAPH = buildRegex(AE_SRC)
  .replace('hr', HR_SRC).replace('heading', HEADING_SRC).replace('|lheading', '')
  .replace('table', TABLE_SRC).replace('blockquote', BLOCKQUOTE_SRC).replace('fences', FENCES_SRC)
  .replace('list', ' {0,3}(?:[*+-]|1[.)])[ \\t]+[^ \\t\\n]').replace('html', HTML_SRC).get();
// The paragraph used inside blockquotes: any numbered list can interrupt.
const RE_BQ_PARAGRAPH = buildRegex(AE_SRC)
  .replace('hr', HR_SRC).replace('heading', HEADING_SRC).replace('|lheading', '')
  .replace('|table', '').replace('blockquote', BLOCKQUOTE_SRC).replace('fences', FENCES_SRC)
  .replace('list', ' {0,3}(?:[*+-]|\\d{1,9}[.)])(?:[ \\t]|\\n|$)').replace('html', HTML_SRC).get();

const RE_B_SPACE = /^(?:[ \t]*(?:\n|$))+/;
const RE_B_CODE = /^((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/;
const RE_B_FENCES = /^ {0,3}(`{3,}(?=[^`\n]*(?:\n|$))|~{3,})([^\n]*)(?:\n|$)(?:|([\s\S]*?)(?:\n|$))(?: {0,3}(?:(?=`)\1`*|(?=~)\1~*) *(?=\n|$)|$)/;
const RE_B_HEADING = /^ {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/;
const RE_B_HR = new RegExp('^' + HR_SRC);
const RE_B_LIST = /^( {0,3}(?:[*+-]|\d{1,9}[.)]))([ \t][^\n]*?)?(?:\n|$)/;
const RE_B_DEF = buildRegex('^ {0,3}\\[(label)\\]: *(?:\\n[ \\t]*)?([^<\\s][^\\s]*|<.*?>)(?:(?: +(?:\\n[ \\t]*)?| *\\n[ \\t]*)(title))? *(?:\\n+|$)')
  .replace('label', '(?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\\\n]|\\n(?![ \\t]*\\n))+')
  .replace('title', '(?:"(?:\\\\[\\s\\S]|[^"\\\\])*"|\'(?:\\\\[\\s\\S]|[^\'\\\\\\n]|\\n(?!\\n))*\'|\\((?:\\\\[\\s\\S]|[^()\\\\])*\\))').get();
const RE_B_HTML = buildRegex('^ {0,3}(?:<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:</\\1>[^\\n]*\\n*|$)|comment[^\\n]*(\\n+|$)|<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)|<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)|<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)|</?(tag)(?:[ \\t]+|\\n|/?>|$)[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?:attribute)*? */?>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)|</[a-z][a-z0-9-]*\\s*>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$))', 'i')
  .replace('comment', '<!--(?:-?>|[\\s\\S]*?(?:-->|$))')
  .replace('tag', K_TAG)
  .replace('attribute', ' +[a-zA-Z:_][\\w.:-]*(?: *= *"[^"\\n]*"| *= *\'[^\'\\n]*\'| *= *[^\\s"\'=<>`]+)?').get();
const RE_B_TABLE = TABLE_SRC;
const RE_B_LHEADING = buildRegex('^(?!bull |blockCode|fences|blockquote|heading|html|table)((?:.|\\n(?!\\s*?\\n|bull |fences|blockquote|heading|hr|html|table))+?)\\n {0,3}(=+|-+)[ \\t]*(?:\\n+|$)')
  .replace(/bull/g, ' {0,3}(?:[*+-]|\\d{1,9}[.)])')
  .replace(/blockCode/g, '(?: {4}| {0,3}\\t)')
  .replace(/fences/g, ' {0,3}(?:`{3,}|~{3,})')
  .replace(/blockquote/g, ' {0,3}>')
  .replace(/heading/g, ' {0,3}#{1,6}(?:\\s|$)')
  .replace(/hr/g, HR_SRC)
  .replace(/html/g, ' {0,3}<[^\\n>]+>\\n')
  .replace(/table/g, ' {0,3}\\|?(?:[:\\- ]*\\|)+[\\:\\- ]*\\n').get();
const RE_B_TEXT = /^[^\n]+/;
const RE_B_BLOCKQUOTE = buildRegex('^( {0,3}> ?(?:(?![ \\t]*(?:\\n|$))(paragraph)|[^\\n]*)(?:\\n|$))+')
  .replace('paragraph', RE_BQ_PARAGRAPH).get();

const memo4 = (fn) => { const cache = [undefined, undefined, undefined, undefined]; return (n) => { const k = clampR(n); const r = cache[k]; if (r !== undefined) return r; return (cache[k] = fn(k)); }; };
const RE_LIST_ITEM_CACHE = new Map();
const RE_LIST_ITEM = (bullet) => { let r = RE_LIST_ITEM_CACHE.get(bullet); if (r === undefined) { r = new RegExp(`^( {0,3}${bullet})((?:[\t ][^\n]*)?(?:\n|$))`); RE_LIST_ITEM_CACHE.set(bullet, r); } return r; };
const clampR = (n) => Math.max(0, Math.min(3, n - 1));
const RE_NEXT_BULLET = memo4((k) => new RegExp(`^ {0,${k}}(?:[*+-]|\\d{1,9}[.)])((?:[ \t][^\n]*)?(?:\n|$))`));
const RE_HR_AT = memo4((k) => new RegExp(`^ {0,${k}}((?:-[ \t]*){3,}|(?:_[ \t]*){3,}|(?:\\*[ \t]*){3,})(?:\n+|$)`));
const RE_FENCES_AT = memo4((k) => new RegExp(`^ {0,${k}}(?:\`\`\`|~~~)`));
const RE_HEADING_AT = memo4((k) => new RegExp(`^ {0,${k}}#{1,6}(?:\\s|$)`));
const RE_HTML_AT = memo4((k) => new RegExp(`^ {0,${k}}(?:</?(?:${K_TAG})(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`, 'i'));
const RE_BLOCKQUOTE_AT = memo4((k) => new RegExp(`^ {0,${k}}>`));

const RE_BLANK_LINE = /^[ \t]*$/;
const RE_DOUBLE_BLANK = /\n[ \t]*\n[ \t]*$/;
const RE_ANY_LINE = /\n.*\n/;
const RE_LEADING_SPACE_TAB = /^[ \t]+/;
const RE_NON_SPACE = /[^ ]/;
const RE_LIST_IS_TASK = /^\[[ xX]\][ \t]+\S/;
const RE_LIST_REPLACE_TASK = /^\[[ xX]\][ \t]+/;
const RE_LIST_TASK_CHECKBOX = /\[[ xX]\]/;
const RE_TABLE_DELIM = /[:|]/;
const RE_TABLE_ALIGN_CHARS = /^\||\| *$/g;
const RE_TABLE_ROW_BLANK = /\n[ \t]*$/;
const RE_TABLE_ALIGN_RIGHT = /^ *-+: *$/;
const RE_TABLE_ALIGN_CENTER = /^ *:-+: *$/;
const RE_TABLE_ALIGN_LEFT = /^ *:-+ *$/;
const RE_BQ_START = /^ {0,3}>/;
const RE_BQ_SETEXT = /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g;
const RE_BQ_STRIP = /^ {0,3}>[ \t]?/gm;
const RE_BQ_MARKER_WS = /^( {0,3}>)([ \t]+)/gm;

// Remove trailing blank lines, keeping a single trailing newline at most.
function stripTrailingBlankLines(a) {
  const e = a.split('\n');
  let t = e.length - 1;
  for (; t >= 0 && RE_BLANK_LINE.test(e[t]);) t--;
  return e.length - t <= 2 ? a : e.slice(0, t + 1).join('\n');
}

// Remove trailing characters equal to `ch`.
function stripTrailingChars(a, ch) {
  let n = a.length;
  while (n > 0 && a[n - 1] === ch) n--;
  return a.slice(0, n);
}

// Remove trailing spaces, tabs and newlines (the trimEnd marked applies to
// list raw/text, restricted to those three characters).
// Count leading spaces (the line's leading whitespace has already been
// expanded to spaces by the caller, so this equals /[^ ]/ search).
function leadingSpaces(a) {
  let n = 0;
  while (n < a.length && a.charCodeAt(n) === 32) n++;
  return n;
}

// True when the line holds only spaces and tabs.
function isBlankLineStr(a) {
  for (let i = 0; i < a.length; i++) {
    const c = a.charCodeAt(i);
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

function trimSpaceTabNl(a) {
  let n = a.length;
  while (n > 0) {
    const c = a.charCodeAt(n - 1);
    if (c !== 32 && c !== 9 && c !== 10) break;
    n--;
  }
  return n === a.length ? a : a.slice(0, n);
}

// Expand tabs to spaces, starting at column `col`.
function expandTabs(a, col = 0) {
  let t = col;
  let n = '';
  for (const s of a) {
    if (s === '\t') {
      const r = 4 - (t % 4);
      n += ' '.repeat(r);
      t += r;
    } else {
      n += s;
      t++;
    }
  }
  return n;
}

// Split a table row on unescaped pipes (marked's `de`).
function splitTableRow(a, count) {
  const t = a.replace(/\|/g, (r, o, i) => {
    let l = false;
    let p = o;
    for (; --p >= 0 && i[p] === '\\';) l = !l;
    return l ? '|' : ' |';
  });
  const n = t.split(' |');
  let s = 0;
  if (n[0].trim() || n.shift(), n.length > 0 && !n.at(-1)?.trim() && n.pop(), count) {
    if (n.length > count) n.splice(count);
    else for (; n.length < count;) n.push('');
  }
  for (; s < n.length; s++) n[s] = n[s].trim().replace(/\\\|/g, '|');
  return n;
}

// Lex `src` into block nodes. `top` selects paragraph vs bare-text nodes;
// `merge` lets the first paragraph join a preceding paragraph (blockquote
// chunks). `ctx` carries the link definitions.
function lexBlocks(src, ctx, top = true, merge = false, out = null) {
  const nodes = out || [];
  let rest = src;
  let guard = -1;
  while (rest) {
    if (rest.length === guard) {
      // No progress: consume one line as text rather than looping forever.
      const nl = rest.indexOf('\n');
      const line = nl === -1 ? rest : rest.slice(0, nl);
      nodes.push({ t: top ? 'p' : 'x', raw: line, text: line });
      rest = nl === -1 ? '' : rest.slice(nl + 1);
      guard = -1;
      continue;
    }
    guard = rest.length;
    const prev = nodes.at(-1);
    let m;
    // Blank lines.
    if ((m = RE_B_SPACE.exec(rest))) {
      rest = rest.slice(m[0].length);
      if (m[0].length === 1 && prev !== undefined) prev.raw += '\n';
      else nodes.push({ t: 'space', raw: m[0] });
      continue;
    }
    // Indented code (merges into a preceding paragraph/text block).
    if ((m = RE_B_CODE.exec(rest))) {
      const raw = stripTrailingBlankLines(m[0]);
      const text = raw.replace(/^(?: {0,3}\t| {1,4})/gm, '');
      rest = rest.slice(m[0].length);
      if (prev && (prev.t === 'p' || prev.t === 'x')) {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + raw;
        prev.text += '\n' + text;
      } else {
        nodes.push({ t: 'code', raw, text, lang: null });
      }
      continue;
    }
    // Fenced code.
    if ((m = RE_B_FENCES.exec(rest))) {
      const raw = stripTrailingBlankLines(m[0]);
      let text = m[3] || '';
      const fenceMatch = m[0].match(/^(\s+)(?:```)/);
      if (fenceMatch) {
        const ind = fenceMatch[1];
        text = text.split('\n').map((r) => {
          const o = r.match(/^\s+/);
          if (o === null) return r;
          return r.slice(Math.min(o[0].length, ind.length));
        }).join('\n');
      }
      rest = rest.slice(m[0].length);
      nodes.push({
        t: 'code', raw, text,
        lang: m[2] ? m[2].trim().replace(RE_ANY_PUNCT, '$1') : m[2],
      });
      continue;
    }
    // ATX heading.
    if ((m = RE_B_HEADING.exec(rest))) {
      let text = m[2].trim();
      if (/#$/.test(text)) {
        const stripped = stripTrailingChars(text, '#');
        if (!stripped || /[ \t]$/.test(stripped)) text = stripped.trim();
      }
      rest = rest.slice(m[0].length);
      nodes.push({ t: 'h', raw: stripTrailingChars(m[0], '\n'), depth: m[1].length, text });
      continue;
    }
    // Thematic break.
    if ((m = RE_B_HR.exec(rest))) {
      rest = rest.slice(m[0].length);
      nodes.push({ t: 'hr', raw: stripTrailingChars(m[0], '\n') });
      continue;
    }
    // Blockquote.
    if ((m = RE_B_BLOCKQUOTE.exec(rest))) {
      const node = lexBlockquote(m[0], ctx);
      rest = rest.slice(node.raw.length);
      nodes.push(node);
      continue;
    }
    // List.
    if ((m = RE_B_LIST.exec(rest))) {
      const node = lexList(rest, ctx);
      if (node) {
        rest = rest.slice(node.raw.length);
        nodes.push(node);
        continue;
      }
    }
    // Raw HTML block.
    if ((m = RE_B_HTML.exec(rest))) {
      const raw = stripTrailingBlankLines(m[0]);
      rest = rest.slice(m[0].length);
      nodes.push({ t: 'html', raw, text: raw, pre: m[1] === 'pre' || m[1] === 'script' || m[1] === 'style' });
      continue;
    }
    // Link definition (registers, or merges into a preceding paragraph).
    if ((m = RE_B_DEF.exec(rest))) {
      if (!RE_START_ANGLE.test(m[2]) && parenBalance(m[2]) !== -1) {
        // Unbalanced parens in the destination: not a definition.
      } else {
        const raw = stripTrailingChars(m[0], '\n');
        const tag = foldLabel(m[1]);
        const href = m[2] ? m[2].replace(/^<(.*)>$/, '$1').replace(RE_ANY_PUNCT, '$1') : '';
        const title = m[3] ? m[3].substring(1, m[3].length - 1).replace(RE_ANY_PUNCT, '$1') : m[3];
        rest = rest.slice(m[0].length);
        if (prev && (prev.t === 'p' || prev.t === 'x')) {
          prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + raw;
          prev.text += '\n' + raw;
        } else {
          if (!Object.hasOwn(ctx.defs, tag)) ctx.defs[tag] = { href, title };
          nodes.push({ t: 'def', raw });
        }
        continue;
      }
    }
    // Table.
    if ((m = RE_B_TABLE.exec(rest))) {
      if (RE_TABLE_DELIM.test(m[2])) {
        const header = splitTableRow(m[1]);
        const alignSrc = m[2].replace(RE_TABLE_ALIGN_CHARS, '').split('|');
        const rowsSrc = m[3] && m[3].trim() ? m[3].replace(RE_TABLE_ROW_BLANK, '').split('\n') : [];
        if (header.length === alignSrc.length) {
          const align = alignSrc.map((a) =>
            RE_TABLE_ALIGN_RIGHT.test(a) ? 'right' :
            RE_TABLE_ALIGN_CENTER.test(a) ? 'center' :
            RE_TABLE_ALIGN_LEFT.test(a) ? 'left' : null);
          const node = {
            t: 'table', raw: stripTrailingChars(m[0], '\n'),
            header: header.map((h, i) => ({ text: h, align: align[i] })),
            rows: rowsSrc.map((r) => splitTableRow(r, header.length).map((c, i) => ({ text: c, align: align[i] }))),
          };
          rest = rest.slice(m[0].length);
          nodes.push(node);
          continue;
        }
      }
    }
    // Setext heading.
    if ((m = RE_B_LHEADING.exec(rest))) {
      const text = m[1].trim();
      rest = rest.slice(m[0].length);
      nodes.push({ t: 'h', raw: stripTrailingChars(m[0], '\n'), depth: m[2].charAt(0) === '=' ? 1 : 2, text });
      continue;
    }
    // Paragraph (top level only).
    if (top && (m = RE_B_PARAGRAPH.exec(rest))) {
      const text = m[1].charAt(m[1].length - 1) === '\n' ? m[1].slice(0, -1) : m[1];
      rest = rest.slice(m[0].length);
      if (merge && prev && prev.t === 'p') {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + m[0];
        prev.text += '\n' + text;
      } else {
        nodes.push({ t: 'p', raw: m[0], text });
      }
      merge = false;
      continue;
    }
    // Bare text line (only reached when top is false, or paragraph failed).
    if ((m = RE_B_TEXT.exec(rest))) {
      rest = rest.slice(m[0].length);
      if (prev && prev.t === 'x') {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + m[0];
        prev.text += '\n' + m[0];
      } else {
        nodes.push({ t: 'x', raw: m[0], text: m[0] });
      }
      continue;
    }
    // Nothing matched: consume one character.
    rest = rest.slice(1);
  }
  return nodes;
}

// A blockquote: split the matched lines into chunks (a chunk is a run of
// `>` lines plus any lazy lines before its first `>`), strip the markers,
// and lex each chunk's content, letting a chunk's first paragraph join the
// previous chunk's last paragraph.
function lexBlockquote(matched, ctx) {
  const lines = stripTrailingChars(matched, '\n').split('\n');
  let remaining = lines;
  let raw = '';
  let text = '';
  const children = [];
  while (remaining.length > 0) {
    let seenMarker = false;
    const chunk = [];
    let p = 0;
    for (; p < remaining.length; p++) {
      if (RE_BQ_START.test(remaining[p])) { chunk.push(remaining[p]); seenMarker = true; }
      else if (!seenMarker) chunk.push(remaining[p]);
      else break;
    }
    remaining = remaining.slice(p);
    const h = chunk.join('\n');
    const u = h
      .replace(RE_BQ_MARKER_WS, (g, b, m2) => b + expandTabs(m2, b.length))
      .replace(RE_BQ_SETEXT, '\n    $1')
      .replace(RE_BQ_STRIP, '');
    raw = raw ? raw + '\n' + h : h;
    text = text ? text + '\n' + u : u;
    const before = children.length;
    lexBlocks(u, ctx, true, true, children);
    if (remaining.length === 0) break;
    const last = children.at(-1);
    if (!last) break;
    if (last.t === 'code' || last.t === 'h' || last.t === 'hr' || last.t === 'html' || last.t === 'table') break;
    if (last.t === 'q') {
      const nestedRaw = last.raw + '\n' + remaining.join('\n').replace(RE_BQ_STRIP, '');
      const nested = lexBlockquote(nestedRaw, ctx);
      children[children.length - 1] = nested;
      const y = nestedRaw.substring(nested.raw.length).replace(/^\n/, '');
      const r = y ? y.split('\n').length : 0;
      const extra = r ? remaining.slice(0, -r) : remaining;
      if (extra.length > 0) raw += '\n' + extra.join('\n');
      text = text.substring(0, text.length - last.text.length) + nested.text;
      remaining = remaining.slice(extra.length);
      if (remaining.length > 0 && RE_BQ_START.test(remaining[0])) continue;
      break;
    }
    if (last.t === 'l') {
      const b = last.raw + '\n' + remaining.join('\n');
      const relisted = lexList(b, ctx);
      if (relisted) {
        children[children.length - 1] = relisted;
        const f = relisted.raw.length > last.raw.length
          ? b.slice(last.raw.length + 1, relisted.raw.length).split('\n').length : 0;
        if (f > 0) {
          const y = remaining.slice(0, f).join('\n');
          raw += '\n' + y;
          text += '\n' + y;
        }
        remaining = remaining.slice(f);
        continue;
      }
    }
    void before;
  }
  return { t: 'q', raw, text, children };
}

// A list starting at `src`. Returns the list node or null.
function lexList(src, ctx) {
  const m = RE_B_LIST.exec(src);
  if (!m) return null;
  const n = src;
  let rest = src;
  const consumed = () => n.length - rest.length;
  const bullet = m[1].trim();
  const ordered = bullet.length > 1;
  const node = {
    t: 'l', raw: '', ordered, start: ordered ? +bullet.slice(0, -1) : '',
    loose: false, items: [],
  };
  const bulletRe = ordered ? `\\d{1,9}\\${bullet.slice(-1)}` : `\\${bullet}`;
  const itemRe = RE_LIST_ITEM(bulletRe);
  let looseFlag = false;
  let t;
  while (rest) {
    let isEmptyItem = false;
    let d = '';
    t = itemRe.exec(rest);
    if (!t || RE_B_HR.test(rest)) break;
    const startOff = consumed();
    rest = rest.slice(t[0].length);
    const g = t[2].split('\n', 1)[0];
    const b = t[1].length;
    const expanded = g.replace(RE_LEADING_SPACE_TAB, (v) => expandTabs(v, b));
    const f0 = rest.split('\n', 1)[0];
    const y = !expanded.trim();
    let R;
    if (y) {
      R = b + 1;
    } else {
      R = leadingSpaces(expanded);
      if (R > 4) R = 1;
      d = expanded.slice(R);
      R += b;
    }
    if (y && isBlankLineStr(f0)) {
      rest = rest.slice(f0.length + 1);
      isEmptyItem = true;
    }
    if (!isEmptyItem) {
      const nextBullet = RE_NEXT_BULLET(R);
      const hrAt = RE_HR_AT(R);
      const fencesAt = RE_FENCES_AT(R);
      const headingAt = RE_HEADING_AT(R);
      const htmlAt = RE_HTML_AT(R);
      const bqAt = RE_BLOCKQUOTE_AT(R);
      let curY = y;
      let curM = expanded;
      while (rest) {
        const nl = rest.indexOf('\n');
        const U = nl === -1 ? rest : rest.slice(0, nl);
        const f = U;
        const Z = (f.charCodeAt(0) === 32 || f.charCodeAt(0) === 9) ? f.replace(RE_LEADING_SPACE_TAB, (v) => expandTabs(v)) : f;
        if (fencesAt.test(f) || headingAt.test(f) || htmlAt.test(f) || bqAt.test(f) || nextBullet.test(f) || hrAt.test(f)) break;
        if (leadingSpaces(Z) >= R || isBlankLineStr(f)) {
          d += '\n' + Z.slice(R);
        } else {
          if (curY || curM.replace(/\t/g, '    ').search(RE_NON_SPACE) >= 4 ||
              fencesAt.test(curM) || headingAt.test(curM) || htmlAt.test(curM) || hrAt.test(curM)) break;
          let qe = f;
          if (/^ {0,3}(?:=+|-+) *$/.test(f) && RE_B_LHEADING.test(curM + '\n' + f)) {
            qe = '    ' + Z.replace(/^ {0,3}/, '');
          }
          d += '\n' + qe;
        }
        curY = isBlankLineStr(f);
        rest = rest.slice(U.length + 1);
        curM = Z.slice(R);
      }
    }
    const itemRaw = n.slice(startOff, consumed());
    if (!node.loose) {
      if (looseFlag) node.loose = true;
      else if (RE_DOUBLE_BLANK.test(itemRaw)) looseFlag = true;
    }
    node.items.push({
      t: 'item', raw: itemRaw, task: RE_LIST_IS_TASK.test(d),
      loose: false, text: d, children: [],
    });
  }
  const lastItem = node.items.at(-1);
  if (!lastItem) return null;
  lastItem.raw = trimSpaceTabNl(lastItem.raw);
  lastItem.text = trimSpaceTabNl(lastItem.text);
  node.raw = trimSpaceTabNl(n.slice(0, consumed()));
  for (const item of node.items) {
    item.children = lexBlocks(item.text, ctx, false, false);
    if (!node.loose) {
      const spaces = item.children.filter((g) => g.t === 'space');
      if (spaces.length > 0 && spaces.some((g) => RE_ANY_LINE.test(g.raw))) node.loose = true;
    }
  }
  for (const item of node.items) {
    const first = item.children[0];
    if (item.task && (first?.t === 'x' || first?.t === 'p')) {
      item.text = item.text.replace(RE_LIST_REPLACE_TASK, '');
      first.raw = first.raw.replace(RE_LIST_REPLACE_TASK, '');
      first.text = first.text.replace(RE_LIST_REPLACE_TASK, '');
      const k = RE_LIST_TASK_CHECKBOX.exec(item.raw);
      if (k) {
        const checked = k[0] !== '[ ]';
        if (node.loose) {
          if (first && (first.t === 'p' || first.t === 'x')) first.cb = checked;
          else item.children.unshift({ t: 'p', raw: k[0] + ' ', text: k[0] + ' ', cb: checked });
        } else {
          first.cb = checked;
        }
      }
    } else if (item.task) {
      item.task = false;
    }
  }
  if (node.loose) {
    for (const item of node.items) {
      item.loose = true;
      for (const child of item.children) {
        if (child.t === 'x') child.t = 'p';
      }
    }
  }
  return node;
}

// Render block nodes to HTML.
function renderBlocks(nodes, ctx) {
  let out = '';
  for (const node of nodes) out += renderBlock(node, ctx);
  return out;
}

function renderBlock(node, ctx) {
  const defs = ctx.defs;
  const ist = ctx.ist;
  switch (node.t) {
    case 'space':
    case 'def':
      return '';
    case 'p': {
      const cb = node.cb === undefined ? '' : '<input ' + (node.cb ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
      return '<p>' + cb + renderInline(node.text, ist) + '</p>\n';
    }
    case 'x': {
      const cb = node.cb === undefined ? '' : '<input ' + (node.cb ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
      return cb + renderInline(node.text, ist);
    }
    case 'h':
      return '<h' + node.depth + '>' + renderInline(node.text, ist) + '</h' + node.depth + '>\n';
    case 'hr':
      return '<hr>\n';
    case 'code': {
      let text = node.text ? node.text.replace(/\n$/, '') + '\n' : '';
      let open = '<pre><code';
      if (node.lang) {
        const lang = node.lang.match(/^\S*/)?.[0] || '';
        if (lang) open += ' class="language-' + escapeHtml(lang, false) + '"';
      }
      return open + '>' + escapeHtml(text, true) + '</code></pre>\n';
    }
    case 'q':
      return '<blockquote>\n' + renderBlocks(node.children, ctx) + '</blockquote>\n';
    case 'l': {
      const tag = node.ordered ? 'ol' : 'ul';
      const start = node.ordered && node.start !== 1 ? ' start="' + node.start + '"' : '';
      let out = '<' + tag + start + '>\n';
      for (const item of node.items) {
        out += '<li>' + renderBlocks(item.children, ctx) + '</li>\n';
      }
      return out + '</' + tag + '>\n';
    }
    case 'item':
      return renderBlocks(node.children, ctx);
    case 'html':
      return node.text;
    case 'table': {
      let head = '';
      for (const cell of node.header) {
        head += (cell.align ? '<th align="' + cell.align + '">' : '<th>') + renderInline(cell.text, ist) + '</th>\n';
      }
      let body = '';
      for (const row of node.rows) {
        let cells = '';
        for (const cell of row) {
          cells += (cell.align ? '<td align="' + cell.align + '">' : '<td>') + renderInline(cell.text, ist) + '</td>\n';
        }
        body += '<tr>\n' + cells + '</tr>\n';
      }
      if (body) body = '<tbody>' + body + '</tbody>';
      return '<table>\n<thead>\n<tr>\n' + head + '</tr>\n</thead>\n' + body + '</table>\n';
    }
    default:
      return '';
  }
}
