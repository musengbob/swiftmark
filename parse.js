// Swiftmark — a fast, dependency-free Markdown renderer.
//
// parse(markdown) returns exactly the HTML that marked 18.1.3 renders with its
// default options (GFM on, breaks off, pedantic off, async off). The parser is
// written from scratch here: a block lexer, an inline lexer and a renderer,
// tuned for speed with first-character dispatch (most blocks and inline tokens
// are decided by looking at one or two characters before any pattern runs) and
// with a fast path that skips the emphasis-masking pass when a span holds no
// link, code span, tag or escape.
//
// The implementation is deliberately single-purpose: no options, no extensions,
// no async. Every helper below is local to this module; parse() keeps no state
// between calls, so two runs over the same input are byte-identical.

// ---------------------------------------------------------------------------
// Small string helpers
// ---------------------------------------------------------------------------

const ESCAPE_MAP = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };
const ESC_ANY = /[&<>"']/;
const ESC_ANY_ALL = /[&<>"']/g;
const ESC_LOOSE = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/;
const ESC_LOOSE_ALL = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
const NUM_REF = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const NUM_REF_OR_AMP = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

/** Escape text for HTML. With `encodeAll`, every & becomes &amp;; otherwise an &
 *  that already starts an entity or numeric reference is left alone. */
function escapeHtml(text, encodeAll) {
  if (encodeAll) {
    if (ESC_ANY.test(text)) return text.replace(ESC_ANY_ALL, (ch) => ESCAPE_MAP[ch]);
  } else if (ESC_LOOSE.test(text)) {
    return text.replace(ESC_LOOSE_ALL, (ch) => ESCAPE_MAP[ch]);
  }
  return text;
}

/** Decode numeric character references (&#169; &#xA9;) in text. A reference to 0,
 *  to a surrogate, or above the Unicode range becomes U+FFFD; a reference to 38
 *  becomes the literal string &amp;. A bare & that starts no reference becomes
 *  &amp;. Named entities are untouched — they pass through verbatim. */
function decodeNumericRefs(text) {
  if (!NUM_REF.test(text)) return text;
  return text.replace(NUM_REF_OR_AMP,
    (whole, dec, hex) => {
      if (dec === undefined && hex === undefined) return '&amp;';
      const code = dec === undefined ? parseInt(hex, 16) : parseInt(dec, 10);
      if (code === 0 || code > 0x10FFFF || (code >= 0xD800 && code <= 0xDFFF)) return '\uFFFD';
      if (code === 38) return '&amp;';
      return String.fromCodePoint(code);
    });
}

/** encodeURI with %25 folded back to %, as marked does for link destinations.
 *  Returns null when encodeURI throws (a lone surrogate, for instance). */
function encodeHref(href) {
  try {
    return encodeURI(href).replace(/%25/g, '%');
  } catch {
    return null;
  }
}

/** Split one table row on unescaped pipes. A leading empty cell (from a leading
 *  pipe) and a trailing empty cell (from a trailing pipe) are dropped; when a
 *  width is given the row is cut or padded to it. Cells are trimmed and \| is
 *  folded to |. */
function splitTableRow(line, width) {
  const marked = line.replace(/\|/g, (ch, at, whole) => {
    let escaped = false;
    let p = at;
    while (--p >= 0 && whole[p] === '\\') escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = marked.split(/ \|/);
  let i = 0;
  if (cells[0].trim() || cells.shift(), cells.length > 0 && !cells.at(-1)?.trim() && cells.pop(), width) {
    if (cells.length > width) cells.splice(width);
    else while (cells.length < width) cells.push('');
  }
  for (; i < cells.length; i++) cells[i] = cells[i].trim().replace(/\\\|/g, '|');
  return cells;
}

/** Strip trailing runs of one character from a string. */
function trimEndChar(text, ch) {
  let n = text.length;
  while (n > 0 && text.charAt(n - 1) === ch) n--;
  return text.slice(0, n);
}

/** Drop trailing blank lines from a block, keeping at most one of them: a block
 *  ending in two or more blank lines is cut back to its last non-blank line. */
function trimBlankTail(text) {
  const lines = text.split('\n');
  let last = lines.length - 1;
  while (last >= 0 && /^[ \t]*$/.test(lines[last])) last--;
  return lines.length - last <= 2 ? text : lines.slice(0, last + 1).join('\n');
}

/** Normalize a link reference label: trim, collapse inner whitespace to one
 *  space, and fold case (lower, then upper, then lower again, as the spec's
 *  Unicode case folding approximates). */
function normalizeLabel(label) {
  return label.trim().replace(/\s+/g, ' ').toLowerCase().toUpperCase().toLowerCase();
}

/** Find an unbalanced close parenthesis in a link destination: the index of the
 *  first ) that closes more than was opened, -2 when opens are left unclosed,
 *  -1 when the parens balance. A backslash skips the next character. */
function findUnbalancedParen(text) {
  if (text.indexOf('(') === -1 && text.indexOf(')') === -1) return -1;
  let depth = 0;
  for (let i = 0; i < text.length; i++) {
    if (text[i] === '\\') i++;
    else if (text[i] === '(') depth++;
    else if (text[i] === ')' && (depth--, depth < 0)) return i;
  }
  return depth > 0 ? -2 : -1;
}

/** Expand tabs to spaces, counting columns from `startCol` (tab stops every 4). */
function expandTabs(text, startCol = 0) {
  let col = startCol;
  let out = '';
  for (const ch of text) {
    if (ch === '\t') {
      const width = 4 - (col % 4);
      out += ' '.repeat(width);
      col += width;
    } else {
      out += ch;
      col++;
    }
  }
  return out;
}

/** Scan a span for the last delimiter run of each kind (*, _, ~) whose run is
 *  not preceded by a blank — a run that could close emphasis. Records the run's
 *  start index, or -1 when there is none. */
function scanCloserRuns(src) {
  const found = { '*': -1, _: -1, '~': -1 };
  const n = src.length;
  for (let s = 0; s < n; s++) {
    const r = src[s];
    if (r !== '*' && r !== '_' && r !== '~') continue;
    const before = s === 0 ? '\n' : src[s - 1];
    let i = s + 1;
    while (i < n && src[i] === r) i++;
    if (before !== ' ' && before !== '\t' && before !== '\n' && before !== '\r' && before !== '\f') found[r] = s;
    s = i - 1;
  }
  return found;
}

// ---------------------------------------------------------------------------
// Small patterns shared by the lexers
// ---------------------------------------------------------------------------

const INDENT_STRIP = /^(?: {0,3}\t| {1,4})/gm;          // one level of indented-code indent, per line
const LINK_BRACKET_ESCAPES = /\\([\[\]])/g;             // \[ and \] inside link text
const FENCE_INDENT = /^(\s+)(?:```)/;                   // leading whitespace of a ``` fence opener
const ENDS_WITH_HASH = /#$/;
const LEADS_WITH_SPACE = /^ /;
const ENDS_WITH_SPACE = / $/;
const ENDS_WITH_SPACE_TAB = /[ \t]$/;
const NON_SPACE = /[^ ]/;
const NEWLINE_EACH = /\n/g;
const TAB_EACH = /\t/g;
const LEADING_BLANKS = /^[ \t]+/;
const BLANK_LINE = /^[ \t]*$/;
const DOUBLE_BLANK = /\n[ \t]*\n[ \t]*$/;
const QUOTE_START = /^ {0,3}>/;
const QUOTE_SETEXT = /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g;
const QUOTE_MARKER = /^ {0,3}>[ \t]?/gm;
const QUOTE_MARKER_SPACE = /^( {0,3}>)([ \t]+)/gm;
const TASK_ITEM = /^\[[ xX]\][ \t]+\S/;
const TASK_STRIP = /^\[[ xX]\][ \t]+/;
const TASK_BOX = /\[[ xX]\]/;
const HAS_LINE = /\n.*\n/;
const ANGLE_HREF = /^<(.*)>$/;
const TABLE_DELIM = /[:|]/;
const TABLE_EDGES = /^\||\| *$/g;
const TABLE_ROW_END = /\n[ \t]*$/;
const ALIGN_RIGHT = /^ *-+: *$/;
const ALIGN_CENTER = /^ *:-+: *$/;
const ALIGN_LEFT = /^ *:-+ *$/;
const OPEN_A_TAG = /^<a /i;
const CLOSE_A_TAG = /^<\/a>/i;
const OPEN_RAW_TAG = /^<(pre|code|kbd|script)(\s|>)/i;
const CLOSE_RAW_TAG = /^<\/(pre|code|kbd|script)(\s|>)/i;
const LEADS_WITH_LT = /^</;
const ENDS_WITH_GT = />$/;
const ALPHA_NUMERIC = /[\p{L}\p{N}]/u;
const NON_SPACE_START = /^\S*/;
const END_NEWLINE = /\n$/;
const SETEXT_LINE = /^ {0,3}(?:=+|-+) *$/;
const CARRIAGE_RETURN = /\r\n|\r/g;

// ---------------------------------------------------------------------------
// Block patterns
// ---------------------------------------------------------------------------

// The HTML block tag names (CommonMark's list for HTML blocks of type 6).
const BLOCK_TAGS =
  'address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|' +
  'details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|' +
  'h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|' +
  'noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|' +
  'thead|title|tr|track|ul';

// Fragments reused across several block patterns. Each is a piece of pattern
// source (a plain string), joined into full patterns below.
const F = {
  bullet: ' {0,3}(?:[*+-]|\\d{1,9}[.)])',                       // a list marker
  indented: '(?: {4}| {0,3}\\t)',                               // indented-code indent
  fenceBare: ' {0,3}(?:`{3,}|~{3,})',                           // a fence line, bare
  fenceStart: ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)',
  quote: ' {0,3}>',                                             // a quote marker
  atx: ' {0,3}#{1,6}(?:\\s|$)',                                 // an ATX heading line
  hr: ' {0,3}(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)',
  hrCap: ' {0,3}((?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)',
  htmlLine: ' {0,3}<[^\\n>]+>\\n',                              // a one-line tag
  htmlStart:
    ' {0,3}(?:</?(?:' + BLOCK_TAGS + ')(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)' +
    '(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)',
  tableDelimLine: ' {0,3}\\|?(?:[:\\- ]*\\|)+[\\:\\- ]*\\n',    // a table delimiter row
  listTight: ' {0,3}(?:[*+-]|1[.)])[ \\t]+[^ \\t\\n]',          // a list start that breaks a paragraph
  listAny: ' {0,3}(?:[*+-]|\\d{1,9}[.)])(?:[ \\t]|\\n|$)',      // any list start
  listRow: ' {0,3}(?:[*+-]|1[.)])[ \\t]',                       // a list start that ends a table
  codeLine: '(?: {4}| {0,3}\\t)[^\\n]',                         // an indented-code line
};

const BLANK_RUN = /^(?:[ \t]*(?:\n|$))+/;
const INDENTED_CODE = /^((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/;
// A fenced block: opener (backtick run with no backtick on its line, or tilde
// run), info string, body, and a closing fence of the same character at least
// as long as the opener — or the end of the input when unclosed.
const FENCES = /^ {0,3}(`{3,}(?=[^`\n]*(?:\n|$))|~{3,})([^\n]*)(?:\n|$)(?:|([\s\S]*?)(?:\n|$))(?: {0,3}(?:(?=`)\1`*|(?=~)\1~*) *(?=\n|$)|$)/;
const HR = /^ {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/;
const ATX = /^ {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/;
const LIST_START = /^( {0,3}(?:[*+-]|\d{1,9}[.)]))([ \t][^\n]*?)?(?:\n|$)/;

// A GFM table: a header line, a delimiter row, and body rows that stop at a
// blank line or at a line that starts another block.
const TABLE_RE = new RegExp(
  '^ *([^\\n ].*)\\n {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)' +
  '(?:\\n((?:(?! *\\n|' + F.hrCap + '|' + F.atx + '|' + F.quote + '|' + F.codeLine + '|' +
  F.fenceStart + '|' + F.listRow + '|' + F.htmlStart + ').*(?:\\n|$))*)\\n*|$)');

// A paragraph: lines that keep coming while none of them starts a block that
// interrupts a paragraph. The `listFrag` decides which list markers interrupt
// (a top-level paragraph only breaks for a bullet or a "1." item; a paragraph
// inside a quote breaks for any marker). With `withTable`, a table start also
// interrupts.
function paragraphPattern(listFrag, withTable) {
  const breaks = [F.hrCap, F.atx, F.quote, F.fenceStart, listFrag, F.htmlStart];
  if (withTable) breaks.push(TABLE_RE.source.slice(1));
  breaks.push('[ \\t]+\\n');
  return new RegExp('^([^\\n]+(?:\\n(?!' + breaks.join('|') + ')[^\\n]+)*)');
}
const PARAGRAPH_RE = paragraphPattern(F.listTight, true);
const QUOTE_PARAGRAPH_RE = paragraphPattern(F.listAny, false);

// A setext heading: text that is not itself a block start, then an underline
// of = or -.
const LHEADING_RE = new RegExp(
  '^(?!' + F.bullet + ' |' + F.indented + '|' + F.fenceBare + '|' + F.quote + '|' + F.atx +
  '|' + F.htmlLine + '|' + F.tableDelimLine + ')' +
  '((?:.|\\n(?!\\s*?\\n|' + F.bullet + ' |' + F.fenceBare + '|' + F.quote + '|' + F.atx +
  '|' + F.hr + '|' + F.htmlLine + '|' + F.tableDelimLine + '))+?)' +
  '\\n {0,3}(=+|-+)[ \\t]*(?:\\n+|$)');

// A link reference definition: [label]: destination ("title" | 'title' | (title)).
const REF_LABEL = '(?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\\\n]|\\n(?![ \\t]*\\n))+';
const DEF_TITLE = '"(?:\\\\[\\s\\S]|[^"\\\\])*"|\'(?:\\\\[\\s\\S]|[^\'\\\\\\n]|\\n(?!\\n))*\'|\\((?:\\\\[\\s\\S]|[^()\\\\])*\\)';
const DEF_RE = new RegExp(
  '^ {0,3}\\[(' + REF_LABEL + ')\\]: *(?:\\n[ \\t]*)?([^<\\s][^\\s]*|<.*?>)' +
  '(?:(?: +(?:\\n[ \\t]*)?| *\\n[ \\t]*)(' + DEF_TITLE + '))? *(?:\\n+|$)');

// An HTML block, types 1–7: script/pre/style/textarea, comment, processing
// instruction, declaration, CDATA, a block tag up to a blank line, or a single
// open or close tag up to a blank line.
const HTML_COMMENT = '<!--(?:-?>|[\\s\\S]*?(?:-->|$))';
const HTML_ATTR = ' +[a-zA-Z:_][\\w.:-]*(?: *= *"[^"\\n]*"| *= *\'[^\'\\n]*\'| *= *[^\\s"\'=<>`]+)?';
const HTML_BLOCK_RE = new RegExp(
  '^ {0,3}(?:<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:</\\1>[^\\n]*\\n*|$)|' +
  HTML_COMMENT + '[^\\n]*(\\n+|$)|' +
  '<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)|' +
  '<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)|' +
  '<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)|' +
  '</?(' + BLOCK_TAGS + ')(?:[ \\t]+|\\n|/?>|$)[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)|' +
  '<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?:' + HTML_ATTR + ')*? */?>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)|' +
  '</[a-z][a-z0-9-]*\\s*>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$))', 'i');

// A block quote: quote lines, where the text after a marker may be a paragraph
// that keeps going over lazy continuation lines.
const BLOCKQUOTE_RE = new RegExp(
  '^( {0,3}> ?(?:(?![ \\t]*(?:\\n|$))(' + QUOTE_PARAGRAPH_RE.source.slice(1) + ')|[^\\n]*)(?:\\n|$))+');

// The patterns a list item's continuation lines are tested against. Their
// allowed indent follows the item's content indent, clamped to 0..3 after
// subtracting one, and is cached per indent.
const indentPatternCache = [];
function indentPatterns(indent) {
  const n = Math.max(0, Math.min(3, indent - 1));
  let found = indentPatternCache[n];
  if (!found) {
    found = {
      bullet: new RegExp('^ {0,' + n + '}(?:[*+-]|\\d{1,9}[.)])((?:[ \\t][^\\n]*)?(?:\\n|$))'),
      hr: new RegExp('^ {0,' + n + '}((?:-[ \\t]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)'),
      fence: new RegExp('^ {0,' + n + '}(?:```|~~~)'),
      heading: new RegExp('^ {0,' + n + '}#{1,6}(?:\\s|$)'),
      html: new RegExp('^ {0,' + n + '}(?:</?(?:' + BLOCK_TAGS + ')(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)', 'i'),
      quote: new RegExp('^ {0,' + n + '}>'),
    };
    indentPatternCache[n] = found;
  }
  return found;
}

// The pattern for a list item's later lines, given the bullet shape.
function listItemPattern(bullet) {
  return new RegExp('^( {0,3}' + bullet + ')((?:[\\t ][^\\n]*)?(?:\\n|$))');
}

// ---------------------------------------------------------------------------
// Inline patterns
// ---------------------------------------------------------------------------

// Unicode classes for the emphasis rules: punctuation, punctuation-or-space,
// and neither (an alphanumeric or symbol run).
const PUNCT = '[\\p{P}\\p{S}]';
const PUNCT_SPACE = '[\\s\\p{P}\\p{S}]';
const NOT_PUNCT_SPACE = '[^\\s\\p{P}\\p{S}]';
// The same classes with ~ taken out (GFM's emphasis rules treat the
// strikethrough delimiter as neither punctuation nor a word character), and
// the word-character class with ~ put back in.
const PUNCT_NO_TILDE = '(?!~)[\\p{P}\\p{S}]';
const PUNCT_SPACE_NO_TILDE = '(?!~)[\\s\\p{P}\\p{S}]';
const NOT_PUNCT_SPACE_TILDE = '(?:[^\\s\\p{P}\\p{S}]|~)';

const ESCAPE_RE = /^\\([!"#$%&'()*+,\-./:;<=>?@\[\]\\^_`{|}~])/;
const CODESPAN_RE = /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/;
const BR_RE = /^( {2,}|\\)\n(?!\s*$)[ \t]*/;
// Tests one character: is it punctuation or space, but not * or _?
const PUNCT_TEST = new RegExp('^((?![*_])' + PUNCT_SPACE + ')', 'u');
// An escaped punctuation mark, anywhere (used to fold \X to X).
const ESCAPED_PUNCT = new RegExp('\\\\(' + PUNCT + ')', 'gu');

// Plain text: a run that stops where another inline construct could start —
// before a backtick, tilde, backslash, <, !, [, * or a word-boundary _, before
// a URL or email start, and before a hard break. The first character may also
// be a lone non-alphanumeric ahead of a mailto:/xmpp: scheme.
const EMAIL_LOCAL = "[a-zA-Z0-9.!#$%&'*+\\/=?_`{|}~-]+";
const PROTOCOL = '[hH][tT][tT][pP][sS]?|[fF][tT][pP]';
const EMAIL_PROTO = '(?:mailto|xmpp):';
const WWW_START = '(?<![^\\s*_~(])www\\.';
const TEXT_RE = new RegExp(
  '^(?:[^a-zA-Z0-9](?=' + EMAIL_PROTO + ')|(`+|~+|[^`~])(?:(?=[`~])|(?= {2,}\\n)|(?=' + EMAIL_LOCAL + '@)' +
  '|[\\s\\S]*?(?:(?=[\\\\<!\\[`*~_]|\\b_|' + PROTOCOL + ':\\/\\/|' + WWW_START + '|$)|[^ ](?= {2,}\\n)' +
  '|[^a-zA-Z0-9](?=' + EMAIL_PROTO + ')|[^a-zA-Z0-9.!#$%&\'*+\\/=?_`{|}~-](?=' + EMAIL_LOCAL + '@))))');

// An emphasis opener: a run of * or _ followed by punctuation (but not ~)
// or by a non-space character. Groups 1/3 hold the punctuation after a
// *-run/_-run; groups 2/4 the plain character after one.
const EM_OPEN = new RegExp(
  '^(?:\\*+(?:((?!\\*)' + PUNCT_NO_TILDE + ')|([^\\s*]))?)' +
  '|^_+(?:((?!_)' + PUNCT_NO_TILDE + ')|([^\\s_]))?', 'u');

// An emphasis closer run, by flanking: groups 1–2 close only, groups 3–4 open
// only, groups 5–6 do both. The first two alternatives skip text that holds no
// closer. The * version's classes treat ~ as a word character; the _ version
// has no final alternative — a _ run after punctuation cannot close onto a word.
const EM_CLOSE_AST = new RegExp(
  '^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)|[^*]+(?=[^*])' +
  '|(?!\\*)' + PUNCT_NO_TILDE + '(\\*+)(?=[\\s]|$)' +
  '|' + NOT_PUNCT_SPACE_TILDE + '(\\*+)(?!\\*)(?=' + PUNCT_SPACE_NO_TILDE + '|$)' +
  '|(?!\\*)' + PUNCT_SPACE_NO_TILDE + '(\\*+)(?=' + NOT_PUNCT_SPACE_TILDE + ')' +
  '|[\\s](\\*+)(?!\\*)(?=' + PUNCT_NO_TILDE + ')' +
  '|(?!\\*)' + PUNCT_NO_TILDE + '(\\*+)(?!\\*)(?=' + PUNCT_NO_TILDE + ')' +
  '|' + NOT_PUNCT_SPACE_TILDE + '(\\*+)(?=' + NOT_PUNCT_SPACE_TILDE + ')', 'gu');
const EM_CLOSE_UND = new RegExp(
  '^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)|[^_]+(?=[^_])' +
  '|(?!_)' + PUNCT + '(_+)(?=[\\s]|$)' +
  '|' + NOT_PUNCT_SPACE + '(_+)(?!_)(?=' + PUNCT_SPACE + '|$)' +
  '|(?!_)' + PUNCT_SPACE + '(_+)(?=' + NOT_PUNCT_SPACE + ')' +
  '|[\\s](_+)(?!_)(?=' + PUNCT + ')' +
  '|(?!_)' + PUNCT + '(_+)(?!_)(?=' + PUNCT + ')', 'gu');

// A strikethrough opener: ~ or ~~ followed by punctuation or a non-space,
// non-tilde character. Its closers mirror the emphasis ones, with ~~? runs.
const DEL_OPEN = new RegExp('^~~?(?:((?!~)' + PUNCT + ')|[^\\s~])', 'u');
const DEL_CLOSE = new RegExp(
  '^[^~]+(?=[^~])' +
  '|(?!~)' + PUNCT + '(~~?)(?=[\\s]|$)' +
  '|' + NOT_PUNCT_SPACE + '(~~?)(?!~)(?=' + PUNCT_SPACE + '|$)' +
  '|(?!~)' + PUNCT_SPACE + '(~~?)(?=' + NOT_PUNCT_SPACE + ')' +
  '|[\\s](~~?)(?!~)(?=' + PUNCT + ')' +
  '|(?!~)' + PUNCT + '(~~?)(?!~)(?=' + PUNCT + ')' +
  '|' + NOT_PUNCT_SPACE + '(~~?)(?=' + NOT_PUNCT_SPACE + ')', 'gu');

// An autolink: <scheme:...> or <user@host>. Group 2 is the @ of an email.
const SCHEME = '[a-zA-Z][a-zA-Z0-9+.-]{1,31}';
const EMAIL_ADDR = "[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_])";
const AUTOLINK_RE = new RegExp('^<(' + SCHEME + ':[^\\s\\x00-\\x1f<>]*|' + EMAIL_ADDR + ')>');

// An inline tag: comment, closing tag, open tag, processing instruction,
// declaration or CDATA section.
const TAG_COMMENT = '<!--(?:-?>|[\\s\\S]*?-->)';
const TAG_ATTR = "\\s+[a-zA-Z:_][\\w.:-]*(?:\\s*=\\s*\"[^\"]*\"|\\s*=\\s*'[^']*'|\\s*=\\s*[^\\s\"'=<>`]+)?";
const TAG_RE = new RegExp(
  '^' + TAG_COMMENT +
  '|^</[a-zA-Z][a-zA-Z0-9-]*\\s*>' +
  '|^<[a-zA-Z][a-zA-Z0-9-]*(?:' + TAG_ATTR + ')*?\\s*/?>' +
  '|^<\\?[\\s\\S]*?\\?>' +
  '|^<![a-zA-Z]+\\s[\\s\\S]*?>' +
  '|^<!\\[CDATA\\[[\\s\\S]*?\\]\\]>');

// Link text: balanced brackets (one level), escapes, code spans, or plain
// characters that are not brackets, backslashes or backticks.
const BRACKETS = '\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]';
const LINK_LABEL =
  '(?:\\[(?:' + BRACKETS + '|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]' +
  '|`+(?!`)[^`]*?`+(?!`)|``+(?=\\])|[^\\[\\]\\\\`])*?';
const LINK_HREF = '<(?:\\\\.|[^\\n<>\\\\])+>|[^ \\t\\n\\x00-\\x1f]+|(?=\\))';
const LINK_TITLE = '"(?:\\\\[\\s\\S]|[^"\\\\])*"|\'(?:\\\\[\\s\\S]|[^\'\\\\])*\'|\\((?:\\\\[\\s\\S]|[^)\\\\])*\\)';
const LINK_RE = new RegExp(
  '^!?\\[(' + LINK_LABEL + ')\\]\\([ \\t\\n]*(' + LINK_HREF + ')' +
  '(?:(?:[ \\t]+(?:\\n[ \\t]*)?|\\n[ \\t]*)(' + LINK_TITLE + '))?[ \\t\\n]*\\)');
const REFLINK_RE = new RegExp('^!?\\[(' + LINK_LABEL + ')\\]\\[(' + REF_LABEL + ')\\]');
const NOLINK_RE = new RegExp('^!?\\[(' + REF_LABEL + ')\\](?:\\[\\])?');

// The looser label shapes used when masking link text for emphasis: a label
// of up to 999 bracketed or plain runs, and a reference of up to 999
// characters that may span lines.
const REF_LABEL_LOOSE = '(?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\]){1,999}';
const SEARCH_LABEL =
  '(?:[^\\[\\]\\\\`]*(?:\\[(?:' + BRACKETS + '|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]' +
  '|`+(?!`)[^`]*?`+(?!`)|``+(?=\\]))){0,999}?[^\\[\\]\\\\`]*?';
const REFLINK_SEARCH = new RegExp(
  '!?\\[(' + SEARCH_LABEL + ')\\]\\[(' + REF_LABEL_LOOSE + ')\\]' +
  '|!?\\[(' + REF_LABEL_LOOSE + ')\\](?:\\[\\])?(?!\\()', 'g');

// A GFM extended autolink: mailto:/xmpp: plus an address, a scheme:// URL or a
// www. host, or a bare email address. Group 1 is the www. or scheme:// prefix,
// group 2 the @ of a bare email.
const EMAIL_PLAIN = "[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])";
const MAILTO = '(?:mailto:' + EMAIL_PLAIN + '|xmpp:' + EMAIL_PLAIN + '(?:\\/[A-Za-z0-9@.]+)?)';
const EMAIL_BARE = "[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])";
const URL_RE = new RegExp(
  '^' + MAILTO + '|^((?:' + PROTOCOL + '):\\/\\/|www\\.)(?:[a-zA-Z0-9\\-]+\\.?)+[^\\s<]*|^' + EMAIL_BARE);
// Trims a URL's trailing punctuation: balanced parens and &entities stay, a
// trailing run of punctuation goes.
const URL_TRIM = /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/;

// The spans the emphasis masker hides: inline links, code spans and tags.
const SKIP_LINK =
  '\\[(?:[^\\[\\]`]|(?<a>`+)[^`]+\\k<a>(?!`))*?\\]' +
  '\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)]|\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)])*\\))*\\)';
const BLOCK_SKIP = new RegExp(
  SKIP_LINK + '|(?<!`)()(?<b>`+)[^`]+\\k<b>(?!`)|<(?! )[^<>]*?>', 'g');
// Code spans and escaped punctuation, for the same masker.
const PUNCT_OUTSIDE_CODE = new RegExp(
  '(`+)(?:[^`]|[^`][\\s\\S]*?[^`])\\1(?!`)|`+|\\\\(' + PUNCT + ')', 'gu');

// ---------------------------------------------------------------------------
// The engine
// ---------------------------------------------------------------------------

const LEADING_WS = /^\s+/;
const TEXT_LINE = /^[^\n]+/;
const LEADING_3SPACES = /^ {0,3}/;
const LEADING_NEWLINE = /^\n/;

/** Remove up to the fence opener's indent from every content line of a fenced
 *  block (backtick fences only — the indent compensation pattern says ```). */
function dedentFence(raw, content) {
  const m = raw.match(FENCE_INDENT);
  if (m === null) return content;
  const pad = m[1];
  return content.split('\n').map((line) => {
    const lead = line.match(LEADING_WS);
    if (lead === null) return line;
    return line.slice(Math.min(lead[0].length, pad.length));
  }).join('\n');
}

class Engine {
  constructor() {
    this.links = Object.create(null); // normalized label -> {href, title}
    this.queue = [];                  // deferred inline jobs {src, tokens}
    this.inLink = false;              // inside link text or an <a> tag
    this.inRaw = false;               // inside <pre>/<code>/<kbd>/<script>
    this.linkEmitted = false;         // a link was emitted in this span
    this.parenPossible = true;        // the current span holds a )
    this.top = true;                  // block lexer at top level
  }

  // Queue an inline job: `src` is lexed into `tokens` once every block is
  // known, so definitions later in the document apply to earlier text.
  deferInline(src, tokens) {
    this.queue.push({ src, tokens });
    return tokens;
  }

  // -- Block tokenizers: each takes the remaining source, returns a token or null.

  trySpace(src) {
    const m = BLANK_RUN.exec(src);
    if (m && m[0].length > 0) return { type: 'space', raw: m[0] };
    return null;
  }

  tryCode(src) {
    const m = INDENTED_CODE.exec(src);
    if (!m) return null;
    const raw = trimBlankTail(m[0]);
    return { type: 'code', raw, codeBlockStyle: 'indented', text: raw.replace(INDENT_STRIP, '') };
  }

  tryFences(src) {
    const m = FENCES.exec(src);
    if (!m) return null;
    return {
      type: 'code',
      raw: m[0],
      lang: m[2] ? m[2].trim().replace(ESCAPED_PUNCT, '$1') : m[2],
      text: dedentFence(m[0], m[3] || ''),
    };
  }

  tryHeading(src) {
    const m = ATX.exec(src);
    if (!m) return null;
    let text = m[2].trim();
    if (ENDS_WITH_HASH.test(text)) {
      const stripped = trimEndChar(text, '#');
      if (!stripped || ENDS_WITH_SPACE_TAB.test(stripped)) text = stripped.trim();
    }
    return { type: 'heading', raw: trimEndChar(m[0], '\n'), depth: m[1].length, text, tokens: this.deferInline(text, []) };
  }

  tryHr(src) {
    const m = HR.exec(src);
    if (!m) return null;
    return { type: 'hr', raw: trimEndChar(m[0], '\n') };
  }

  tryHtml(src) {
    const m = HTML_BLOCK_RE.exec(src);
    if (!m) return null;
    const raw = trimBlankTail(m[0]);
    return { type: 'html', block: true, raw, pre: m[1] === 'pre' || m[1] === 'script' || m[1] === 'style', text: raw };
  }

  tryDef(src) {
    const m = DEF_RE.exec(src);
    if (!m) return null;
    if (!LEADS_WITH_LT.test(m[2]) && findUnbalancedParen(m[2]) !== -1) return null;
    return {
      type: 'def',
      tag: normalizeLabel(m[1]),
      raw: trimEndChar(m[0], '\n'),
      href: m[2] ? m[2].replace(ANGLE_HREF, '$1').replace(ESCAPED_PUNCT, '$1') : '',
      title: m[3] ? m[3].substring(1, m[3].length - 1).replace(ESCAPED_PUNCT, '$1') : m[3],
    };
  }

  tryTable(src) {
    const m = TABLE_RE.exec(src);
    if (!m || !TABLE_DELIM.test(m[2])) return null;
    const headerCells = splitTableRow(m[1]);
    const delimCells = m[2].replace(TABLE_EDGES, '').split('|');
    const bodyLines = m[3]?.trim() ? m[3].replace(TABLE_ROW_END, '').split('\n') : [];
    const table = { type: 'table', raw: trimEndChar(m[0], '\n'), header: [], align: [], rows: [] };
    if (headerCells.length !== delimCells.length) return null;
    for (const cell of delimCells) {
      if (ALIGN_RIGHT.test(cell)) table.align.push('right');
      else if (ALIGN_CENTER.test(cell)) table.align.push('center');
      else if (ALIGN_LEFT.test(cell)) table.align.push('left');
      else table.align.push(null);
    }
    for (let i = 0; i < headerCells.length; i++) {
      table.header.push({ text: headerCells[i], tokens: this.deferInline(headerCells[i], []), header: true, align: table.align[i] });
    }
    for (const line of bodyLines) {
      table.rows.push(splitTableRow(line, table.header.length).map((cell, j) => ({
        text: cell, tokens: this.deferInline(cell, []), header: false, align: table.align[j],
      })));
    }
    return table;
  }

  tryLheading(src) {
    const m = LHEADING_RE.exec(src);
    if (!m) return null;
    const text = m[1].trim();
    return { type: 'heading', raw: trimEndChar(m[0], '\n'), depth: m[2].charAt(0) === '=' ? 1 : 2, text, tokens: this.deferInline(text, []) };
  }

  tryParagraph(src) {
    const m = PARAGRAPH_RE.exec(src);
    if (!m) return null;
    const text = m[1].charAt(m[1].length - 1) === '\n' ? m[1].slice(0, -1) : m[1];
    return { type: 'paragraph', raw: m[0], text, tokens: this.deferInline(text, []) };
  }

  tryText(src) {
    const m = TEXT_LINE.exec(src);
    if (!m) return null;
    return { type: 'text', raw: m[0], text: m[0], tokens: this.deferInline(m[0], []) };
  }

  // -- Block quotes and lists: the two recursive block tokenizers.

  tryBlockquote(src) {
    const m = BLOCKQUOTE_RE.exec(src);
    if (!m) return null;
    let lines = trimEndChar(m[0], '\n').split('\n');
    let raw = '';
    let text = '';
    const tokens = [];
    while (lines.length > 0) {
      // One chunk: leading lazy lines, then quote lines, up to the next lazy
      // line after a quote line.
      let seenMarker = false;
      const chunk = [];
      let p = 0;
      for (; p < lines.length; p++) {
        if (QUOTE_START.test(lines[p])) { chunk.push(lines[p]); seenMarker = true; }
        else if (!seenMarker) chunk.push(lines[p]);
        else break;
      }
      lines = lines.slice(p);
      const chunkText = chunk.join('\n');
      const stripped = chunkText
        .replace(QUOTE_MARKER_SPACE, (whole, marker, ws) => marker + expandTabs(ws, marker.length))
        .replace(QUOTE_SETEXT, '\n    $1')
        .replace(QUOTE_MARKER, '');
      raw = raw ? raw + '\n' + chunkText : chunkText;
      text = text ? text + '\n' + stripped : stripped;
      const savedTop = this.top;
      this.top = true;
      this.lexBlocks(stripped, tokens, true);
      this.top = savedTop;
      if (lines.length === 0) break;
      const last = tokens.at(-1);
      if (last?.type === 'code' || last?.type === 'heading' || last?.type === 'hr' || last?.type === 'html' || last?.type === 'table') break;
      if (last?.type === 'blockquote') {
        // A nested quote may absorb the lines that follow it.
        const inner = last;
        const combined = inner.raw + '\n' + lines.join('\n').replace(QUOTE_MARKER, '');
        const relexed = this.tryBlockquote(combined);
        tokens[tokens.length - 1] = relexed;
        const leftover = combined.substring(relexed.raw.length).replace(LEADING_NEWLINE, '');
        const leftoverLines = leftover ? leftover.split('\n').length : 0;
        const consumedLines = leftoverLines ? lines.slice(0, -leftoverLines) : lines;
        if (consumedLines.length > 0) raw += '\n' + consumedLines.join('\n');
        text = text.substring(0, text.length - inner.text.length) + relexed.text;
        lines = lines.slice(consumedLines.length);
        if (lines.length > 0 && QUOTE_START.test(lines[0])) continue;
        break;
      }
      if (last?.type === 'list') {
        // A list at the end may absorb lazy continuation lines.
        const inner = last;
        const combined = inner.raw + '\n' + lines.join('\n');
        const relexed = this.tryList(combined);
        tokens[tokens.length - 1] = relexed;
        const taken = relexed.raw.length > inner.raw.length
          ? combined.slice(inner.raw.length + 1, relexed.raw.length).split('\n').length : 0;
        if (taken > 0) {
          const extra = lines.slice(0, taken).join('\n');
          raw += '\n' + extra;
          text += '\n' + extra;
        }
        lines = lines.slice(taken);
      }
    }
    return { type: 'blockquote', raw, tokens, text };
  }

  tryList(src) {
    const m = LIST_START.exec(src);
    if (!m) return null;
    const full = src;
    let rest = src;
    const consumed = () => full.length - rest.length;
    const bulletText = m[1].trim();
    const ordered = bulletText.length > 1;
    const list = {
      type: 'list', raw: '', ordered,
      start: ordered ? +bulletText.slice(0, -1) : '',
      loose: false, items: [],
    };
    const bulletPat = ordered ? '\\d{1,9}\\'.concat(bulletText.slice(-1)) : '\\'.concat(bulletText);
    const itemRe = listItemPattern(bulletPat);
    let sawDoubleBlank = false;
    let item;
    while (rest) {
      let blankFollow = false;
      let content = '';
      if (!(item = itemRe.exec(rest)) || HR.test(rest)) break;
      const itemStart = consumed();
      rest = rest.substring(item[0].length);
      const firstLine = item[2].split('\n', 1)[0];
      const bulletWidth = item[1].length;
      const expanded = firstLine.replace(LEADING_BLANKS, (ws) => expandTabs(ws, bulletWidth));
      let nextLine = rest.split('\n', 1)[0];
      let prevBlank = !expanded.trim();
      let contentIndent = 0;
      if (prevBlank) {
        contentIndent = bulletWidth + 1;
      } else {
        contentIndent = expanded.search(NON_SPACE);
        if (contentIndent > 4) contentIndent = 1;
        content = expanded.slice(contentIndent);
        contentIndent += bulletWidth;
      }
      if (prevBlank && BLANK_LINE.test(nextLine)) {
        rest = rest.substring(nextLine.length + 1);
        blankFollow = true;
      }
      if (!blankFollow) {
        const pats = indentPatterns(contentIndent);
        let prevContent = expanded;
        while (rest) {
          const line = rest.split('\n', 1)[0];
          nextLine = line;
          const expandedLine = line.replace(LEADING_BLANKS, (ws) => expandTabs(ws));
          if (pats.fence.test(line) || pats.heading.test(line) || pats.html.test(line) ||
              pats.quote.test(line) || pats.bullet.test(line) || pats.hr.test(line)) break;
          if (expandedLine.search(NON_SPACE) >= contentIndent || !line.trim()) {
            content += '\n' + expandedLine.slice(contentIndent);
          } else {
            if (prevBlank || prevContent.replace(TAB_EACH, '    ').search(NON_SPACE) >= 4 ||
                pats.fence.test(prevContent) || pats.heading.test(prevContent) ||
                pats.html.test(prevContent) || pats.hr.test(prevContent)) break;
            // A setext-looking lazy line is pushed in by four spaces so it
            // does not turn the item's paragraph into a heading.
            const lazy = SETEXT_LINE.test(line) && LHEADING_RE.test(prevContent + '\n' + line)
              ? '    ' + expandedLine.replace(LEADING_3SPACES, '') : line;
            content += '\n' + lazy;
          }
          prevBlank = !line.trim();
          rest = rest.substring(line.length + 1);
          prevContent = expandedLine.slice(contentIndent);
        }
      }
      const itemRaw = full.slice(itemStart, consumed());
      if (!list.loose) {
        if (sawDoubleBlank) list.loose = true;
        else if (DOUBLE_BLANK.test(itemRaw)) sawDoubleBlank = true;
      }
      list.items.push({
        type: 'list_item', raw: itemRaw, task: TASK_ITEM.test(content),
        loose: false, text: content, tokens: [],
      });
    }
    const lastItem = list.items.at(-1);
    if (!lastItem) return null;
    lastItem.raw = lastItem.raw.trimEnd();
    lastItem.text = lastItem.text.trimEnd();
    list.raw = full.slice(0, consumed()).trimEnd();
    for (const itemTok of list.items) {
      this.top = false;
      itemTok.tokens = this.lexBlocks(itemTok.text, []);
      if (!list.loose) {
        const spaces = itemTok.tokens.filter((t) => t.type === 'space');
        if (spaces.length > 0 && spaces.some((t) => HAS_LINE.test(t.raw))) list.loose = true;
      }
    }
    for (const itemTok of list.items) {
      const first = itemTok.tokens[0];
      if (itemTok.task && (first?.type === 'text' || first?.type === 'paragraph')) {
        itemTok.text = itemTok.text.replace(TASK_STRIP, '');
        first.raw = first.raw.replace(TASK_STRIP, '');
        first.text = first.text.replace(TASK_STRIP, '');
        for (let q = this.queue.length - 1; q >= 0; q--) {
          if (TASK_ITEM.test(this.queue[q].src)) {
            this.queue[q].src = this.queue[q].src.replace(TASK_STRIP, '');
            break;
          }
        }
        const box = TASK_BOX.exec(itemTok.raw);
        if (box) {
          const check = { type: 'checkbox', raw: box[0] + ' ', checked: box[0] !== '[ ]' };
          itemTok.checked = check.checked;
          if (list.loose) {
            const head = itemTok.tokens[0];
            if (head && (head.type === 'paragraph' || head.type === 'text') && 'tokens' in head && head.tokens) {
              head.raw = check.raw + head.raw;
              head.text = check.raw + head.text;
              head.tokens.unshift(check);
            } else {
              itemTok.tokens.unshift({ type: 'paragraph', raw: check.raw, text: check.raw, tokens: [check] });
            }
          } else {
            itemTok.tokens.unshift(check);
          }
        }
      } else if (itemTok.task) {
        itemTok.task = false;
      }
    }
    if (list.loose) {
      for (const itemTok of list.items) {
        itemTok.loose = true;
        for (const t of itemTok.tokens) if (t.type === 'text') t.type = 'paragraph';
      }
    }
    return list;
  }

  // The generic fall-through: table, setext heading, paragraph (top level
  // only), then a single line of text.
  genericBlock(rest) {
    return this.tryTable(rest) || this.tryLheading(rest) ||
      (this.top ? this.tryParagraph(rest) : null) || this.tryText(rest);
  }

  // Decide the next block by its first characters, so most blocks run one
  // pattern instead of twelve.
  nextBlock(rest) {
    const c0 = rest.charCodeAt(0);
    if (c0 === 10) return this.trySpace(rest);
    let spaces = 0;
    while (rest.charCodeAt(spaces) === 32) spaces++;
    const after = rest.charCodeAt(spaces);
    if (after === 10 || Number.isNaN(after)) return this.trySpace(rest);
    if (after === 9) {
      // A tab after the spaces: a blank line, or indented code.
      let j = spaces + 1;
      while (rest.charCodeAt(j) === 32 || rest.charCodeAt(j) === 9) j++;
      const c = rest.charCodeAt(j);
      if (c === 10 || Number.isNaN(c)) return this.trySpace(rest);
      return this.tryCode(rest);
    }
    if (spaces >= 4) return this.tryCode(rest);
    switch (after) {
      case 96: // `
      case 126: // ~
        return this.tryFences(rest) || this.genericBlock(rest);
      case 35: // #
        return this.tryHeading(rest) || this.genericBlock(rest);
      case 45: // -
      case 42: // *
        return this.tryHr(rest) || this.tryList(rest) || this.genericBlock(rest);
      case 43: // +
        return this.tryList(rest) || this.genericBlock(rest);
      case 95: // _
        return this.tryHr(rest) || this.genericBlock(rest);
      case 62: // >
        return this.tryBlockquote(rest) || this.genericBlock(rest);
      case 60: // <
        return this.tryHtml(rest) || this.genericBlock(rest);
      case 91: // [
        return this.tryDef(rest) || this.genericBlock(rest);
      default:
        if (after >= 48 && after <= 57) return this.tryList(rest) || this.genericBlock(rest);
        return this.genericBlock(rest);
    }
  }

  // Lex blocks from `src` into `out`. With `nested`, the first paragraph
  // merges into a paragraph token already in `out` (a quote's lazy lines).
  lexBlocks(src, out, nested = false) {
    let rest = src;
    let guard = Infinity;
    while (rest) {
      if (rest.length < guard) guard = rest.length;
      else throw new Error('Infinite loop on byte: ' + rest.charCodeAt(0));
      const tok = this.nextBlock(rest);
      if (!tok) throw new Error('Infinite loop on byte: ' + rest.charCodeAt(0));
      rest = rest.substring(tok.raw.length);
      if (tok.type === 'space') {
        const prev = out.at(-1);
        if (tok.raw.length === 1 && prev !== undefined) prev.raw += '\n';
        else out.push(tok);
        continue;
      }
      if ((tok.type === 'code' && tok.codeBlockStyle === 'indented') || tok.type === 'def') {
        // Indented code and definitions cannot interrupt a paragraph: they
        // are absorbed into it as text instead. (Fenced code never merges.)
        const prev = out.at(-1);
        if (prev?.type === 'paragraph' || prev?.type === 'text') {
          prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + tok.raw;
          prev.text += '\n' + (tok.type === 'code' ? tok.text : tok.raw);
          this.queue.at(-1).src = prev.text;
          continue;
        }
        if (tok.type === 'def' && !this.links[tok.tag]) {
          this.links[tok.tag] = { href: tok.href, title: tok.title };
        }
        out.push(tok);
        continue;
      }
      if (tok.type === 'paragraph') {
        if (nested) {
          const prev = out.at(-1);
          if (prev?.type === 'paragraph') {
            prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + tok.raw;
            prev.text += '\n' + tok.text;
            this.queue.pop();
            this.queue.at(-1).src = prev.text;
            nested = false;
            continue;
          }
        }
        nested = false;
        out.push(tok);
        continue;
      }
      if (tok.type === 'text') {
        const prev = out.at(-1);
        if (prev?.type === 'text') {
          prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + tok.raw;
          prev.text += '\n' + tok.text;
          this.queue.pop();
          this.queue.at(-1).src = prev.text;
          continue;
        }
      }
      out.push(tok);
    }
    this.top = true;
    return out;
  }

  // -- Inline lexing ---------------------------------------------------------

  // Does this span hold a link — an inline link, or a reference link whose
  // definition exists? Used while masking link text for emphasis.
  linkInText(src) {
    if (!src.includes('[')) return false;
    for (const m of src.matchAll(BLOCK_SKIP)) {
      if (LINK_RE.test(m[0]) && src.charAt(m.index - 1) !== '!') return true;
    }
    for (const m of src.matchAll(REFLINK_SEARCH)) {
      const label = m[0];
      const open = label.lastIndexOf('[');
      if (!(label.charAt(0) === '!' || !Object.hasOwn(this.links, normalizeLabel(label.slice(open + 1, -1)))) &&
          !(open > 1 && this.linkInText(label.slice(1, open - 1)))) return true;
    }
    return false;
  }

  // Hide link text, code spans, tags and escaped punctuation from the emphasis
  // scanner, keeping every character's place — the mask is exactly as long as
  // the source, so positions line up.
  maskEmphasis(src) {
    let masked = src;
    if (src.includes('[')) {
      const hide = (match) => {
        const open = match.lastIndexOf('[');
        if (!Object.hasOwn(this.links, normalizeLabel(match.slice(open + 1, -1)))) return match;
        if (open > 1 && match.charAt(0) !== '!') {
          const label = match.slice(1, open - 1);
          if (this.linkInText(label)) {
            return '[' + label.replace(REFLINK_SEARCH, hide) + '][' + 'a'.repeat(match.length - open - 2) + ']';
          }
        }
        return '[' + 'a'.repeat(match.length - 2) + ']';
      };
      masked = masked.replace(REFLINK_SEARCH, hide);
    }
    masked = masked
      .replace(PUNCT_OUTSIDE_CODE, (whole, ticks, punct) =>
        punct ? '+'.repeat(whole.length)
          : ticks ? ticks + whole.slice(ticks.length, -ticks.length).replace(/`/g, '+') + ticks
          : whole)
      .replace(BLOCK_SKIP, (whole) => '[' + 'a'.repeat(whole.length - 2) + ']');
    return masked;
  }

  // Lex the inline tokens of `src` into `tokens`. The emphasis mask is built
  // only when the span holds an emphasis delimiter, and the masking pass
  // itself only when it also holds a link, code span, tag or escape.
  lexInline(src, tokens) {
    const savedParen = this.parenPossible;
    this.parenPossible = savedParen && src.includes(')');
    try {
      const hasDelim = src.includes('*') || src.includes('_') || src.includes('~');
      const masked = hasDelim &&
        (src.includes('[') || src.includes('`') || src.includes('<') || src.includes('\\'))
        ? this.maskEmphasis(src) : src;
      const closers = hasDelim ? scanCloserRuns(masked) : null;
      return this.lexInlineLoop(src, masked, closers, tokens);
    } finally {
      this.parenPossible = savedParen;
    }
  }

  lexInlineLoop(src, masked, closers, tokens) {
    let rest = src;
    let afterText = false;
    let prevChar = '';
    let guard = Infinity;
    while (rest) {
      if (rest.length < guard) guard = rest.length;
      else throw new Error('Infinite loop on byte: ' + rest.charCodeAt(0));
      if (!afterText) prevChar = '';
      afterText = false;
      const c = rest.charCodeAt(0);
      let tok = null;
      let isText = false;
      if (c === 92) tok = this.tryEscape(rest) || this.tryBr(rest); // backslash
      else if (c === 60) tok = this.tryTag(rest) || this.tryAutolink(rest); // <
      else if (c === 91 || c === 33) tok = this.tryLink(rest) || this.tryReflink(rest); // [ !
      else if (c === 42 || c === 95) tok = this.tryEmStrong(rest, masked, src.length - rest.length, prevChar, closers); // * _
      else if (c === 96) tok = this.tryCodespan(rest); // `
      else if (c === 126) tok = this.tryDel(rest, masked, src.length - rest.length, prevChar, closers); // ~
      else if (c === 32) tok = this.tryBr(rest); // space
      if (!tok && !this.inLink && isUrlStartChar(c)) tok = this.tryUrl(rest);
      if (!tok) { tok = this.tryInlineText(rest); isText = true; }
      if (!tok) throw new Error('Infinite loop on byte: ' + rest.charCodeAt(0));
      rest = rest.substring(tok.raw.length);
      if (isText) {
        if (tok.raw.slice(-1) !== '_') prevChar = tok.raw.slice(-1);
        afterText = true;
        const prev = tokens.at(-1);
        if (prev?.type === 'text') { prev.raw += tok.raw; prev.text += tok.text; }
        else tokens.push(tok);
      } else if (tok.type === 'text') {
        // A reference link with no definition yields one literal character.
        const prev = tokens.at(-1);
        if (prev?.type === 'text') { prev.raw += tok.raw; prev.text += tok.text; }
        else tokens.push(tok);
      } else {
        tokens.push(tok);
      }
    }
    return tokens;
  }

  // -- Inline tokenizers -----------------------------------------------------

  tryEscape(rest) {
    const m = ESCAPE_RE.exec(rest);
    if (!m) return null;
    return { type: 'escape', raw: m[0], text: m[1] };
  }

  tryTag(rest) {
    const m = TAG_RE.exec(rest);
    if (!m) return null;
    if (!this.inLink && OPEN_A_TAG.test(m[0])) this.inLink = true;
    else if (this.inLink && CLOSE_A_TAG.test(m[0])) this.inLink = false;
    if (!this.inRaw && OPEN_RAW_TAG.test(m[0])) this.inRaw = true;
    else if (this.inRaw && CLOSE_RAW_TAG.test(m[0])) this.inRaw = false;
    return { type: 'html', raw: m[0], inLink: this.inLink, inRawBlock: this.inRaw, block: false, text: m[0] };
  }

  tryCodespan(rest) {
    const m = CODESPAN_RE.exec(rest);
    if (!m) return null;
    let text = m[2].replace(NEWLINE_EACH, ' ');
    if (NON_SPACE.test(text) && LEADS_WITH_SPACE.test(text) && ENDS_WITH_SPACE.test(text)) {
      text = text.substring(1, text.length - 1);
    }
    return { type: 'codespan', raw: m[0], text };
  }

  tryBr(rest) {
    const m = BR_RE.exec(rest);
    if (!m) return null;
    return { type: 'br', raw: m[0] };
  }

  tryAutolink(rest) {
    const m = AUTOLINK_RE.exec(rest);
    if (!m) return null;
    const text = m[1];
    return {
      type: 'link', raw: m[0], text,
      href: m[2] === '@' ? 'mailto:' + text : text,
      autolink: true, tokens: [{ type: 'text', raw: text, text }],
    };
  }

  tryUrl(rest) {
    // Cheap gates: a URL here must start with www., a scheme://, mailto: or
    // xmpp:, or an email local part that reaches an @.
    let possible = rest.startsWith('www.') || rest.startsWith('mailto:') || rest.startsWith('xmpp:');
    if (!possible && URL_SCHEME.test(rest)) possible = true;
    if (!possible) {
      let i = 0;
      const n = rest.length;
      while (i < n) {
        const ch = rest.charCodeAt(i);
        if ((ch >= 65 && ch <= 90) || (ch >= 97 && ch <= 122) || (ch >= 48 && ch <= 57) ||
            ch === 46 || ch === 95 || ch === 43 || ch === 45) i++;
        else break;
      }
      possible = i > 0 && rest.charCodeAt(i) === 64;
    }
    if (!possible) return null;
    const m = URL_RE.exec(rest);
    if (!m) return null;
    let text;
    let href;
    if (m[2] === '@') {
      text = m[0];
      href = 'mailto:' + text;
    } else {
      let cur = m[0];
      let prev;
      do {
        prev = cur;
        cur = URL_TRIM.exec(cur)?.[0] ?? '';
      } while (cur !== prev);
      text = cur;
      href = m[1] === 'www.' ? 'http://' + cur : cur;
    }
    return { type: 'link', raw: text, text, href, autolink: true, tokens: [{ type: 'text', raw: text, text }] };
  }

  tryInlineText(rest) {
    const m = TEXT_RE.exec(rest);
    if (!m) return null;
    const raw = m[0];
    return { type: 'text', raw, text: this.inRaw ? raw : decodeNumericRefs(raw), escaped: this.inRaw };
  }

  // Does the link text hide a tag that runs past the text's end? A tag or
  // autolink starting inside the label must end inside it too.
  linkTextHidesTag(full, label, offset) {
    if (!label.includes('<')) return false;
    for (let s = 0; s < label.length; s++) {
      if (label[s] === '\\') { s++; continue; }
      if (label[s] === '`') {
        const code = CODESPAN_RE.exec(label.slice(s));
        if (code) { s += code[0].length - 1; continue; }
      }
      if (label[s] !== '<') continue;
      const tag = TAG_RE.exec(full.slice(offset + s)) || AUTOLINK_RE.exec(full.slice(offset + s));
      if (tag) {
        if (tag[0].length > label.length - s) return true;
        s += tag[0].length - 1;
      }
    }
    return false;
  }

  // Build a link or image token from a match, lexing its text inline. A link
  // whose text already holds a link is refused — links do not nest.
  buildLink(match, href, title, raw) {
    const text = match[1].replace(LINK_BRACKET_ESCAPES, '$1');
    const image = match[0].charAt(0) === '!';
    const savedInLink = this.inLink;
    const savedEmitted = this.linkEmitted;
    const savedRaw = this.inRaw;
    this.inLink = true;
    this.linkEmitted = false;
    const inner = this.lexInline(text, []);
    const nestedLink = this.linkEmitted;
    this.linkEmitted = savedEmitted;
    this.inLink = savedInLink;
    if (!image) {
      if (nestedLink) {
        this.inRaw = savedRaw;
        return null;
      }
      this.linkEmitted = true;
    }
    return { type: image ? 'image' : 'link', raw, href, title: title || null, text, tokens: inner };
  }

  tryLink(rest) {
    if (this.parenPossible === false) return null;
    const m = LINK_RE.exec(rest);
    if (!m) return null;
    const offset = m[0].charAt(0) === '!' ? 2 : 1;
    if (this.linkTextHidesTag(rest, m[1], offset)) return null;
    const dest = m[2].trim();
    if (LEADS_WITH_LT.test(dest)) {
      if (!ENDS_WITH_GT.test(dest)) return null;
      const unslashed = trimEndChar(dest.slice(0, -1), '\\');
      if ((dest.length - unslashed.length) % 2 === 0) return null;
    } else {
      const unbalanced = findUnbalancedParen(m[2]);
      if (unbalanced === -2) return null;
      if (unbalanced > -1) {
        const cut = (m[0].indexOf('!') === 0 ? 5 : 4) + m[1].length + unbalanced;
        m[2] = m[2].substring(0, unbalanced);
        m[0] = m[0].substring(0, cut).trim();
        m[3] = '';
      }
    }
    const unslashedRaw = trimEndChar(m[0].slice(0, -1), '\\');
    if ((m[0].length - unslashedRaw.length) % 2 === 0) return null;
    let href = m[2].trim();
    if (LEADS_WITH_LT.test(href)) href = href.slice(1, -1);
    const title = m[3] ? m[3].slice(1, -1) : '';
    return this.buildLink(m, href && href.replace(ESCAPED_PUNCT, '$1'), title && title.replace(ESCAPED_PUNCT, '$1'), m[0]);
  }

  tryReflink(rest) {
    const m = REFLINK_RE.exec(rest) || NOLINK_RE.exec(rest);
    if (!m) return null;
    const offset = m[0].charAt(0) === '!' ? 2 : 1;
    if (this.linkTextHidesTag(rest, m[1], offset)) return null;
    const def = this.links[normalizeLabel(m[2] || m[1])];
    if (!def) {
      const first = m[0].charAt(0);
      return { type: 'text', raw: first, text: first };
    }
    return this.buildLink(m, def.href, def.title, m[0]);
  }

  // Emphasis and strong emphasis, by the CommonMark flanking rules: an opener
  // run pairs with closer runs until its delimiters are used up, opener-only
  // runs in between add to the debt, and the rule of three refuses a pairing
  // when the opener's run length and the sum of both runs are multiples of 3
  // in the wrong way. One delimiter each side makes em, two make strong.
  tryEmStrong(rest, masked, pos, prevChar, closers) {
    const m = EM_OPEN.exec(rest);
    if (!m || (!m[1] && !m[2] && !m[3] && !m[4])) return null;
    const delim = m[0][0];
    const prevIsDelim = prevChar === delim;
    let runStart = pos;
    while (runStart > 0 && masked[runStart - 1] === delim) runStart--;
    const beforeRun = [...masked.slice(Math.max(0, runStart - 2), runStart)].at(-1) ?? '';
    const beforeRunIsPunct = beforeRun === '*' || beforeRun === '_' || !!PUNCT_TEST.exec(beforeRun);
    let before = prevChar;
    if (runStart < pos) before = beforeRun;
    const beforeIsPunct = runStart < pos ? beforeRunIsPunct : !!PUNCT_TEST.exec(before);
    if (m[4] && before.match(ALPHA_NUMERIC)) return null;
    const afterIsPunct = m[1] || m[3] || '';
    if (!afterIsPunct || !before || beforeIsPunct) {
      const openLen = [...m[0]].length - 1;
      let remaining = openLen;
      let skipped = 0;
      const runLen = pos - runStart + openLen;
      const canClose = !!beforeRun.trim() && (!!afterIsPunct || (delim === '*' && !beforeRunIsPunct));
      if (delim !== '*' && delim !== '_') return null;
      const closerRe = delim === '*' ? EM_CLOSE_AST : EM_CLOSE_UND;
      const lastCloser = closers[delim];
      const searchFrom = pos + openLen;
      if (lastCloser < searchFrom) return null;
      const tail = masked.slice(searchFrom);
      const limit = lastCloser - searchFrom;
      let closer;
      let run;
      let runLen2;
      closerRe.lastIndex = 0;
      while ((closer = closerRe.exec(tail)) !== null && !(closer.index > limit)) {
        run = closer[1] || closer[2] || closer[3] || closer[4] || closer[5] || closer[6];
        if (!run) continue;
        runLen2 = [...run].length;
        if (closer[3] || closer[4]) { remaining += runLen2; continue; }
        if (closer[5] || closer[6] || canClose) {
          if (prevIsDelim && (closer[5] || closer[6])) break;
          if (runLen % 3 && !((runLen + runLen2) % 3)) { skipped += runLen2; continue; }
        }
        remaining -= runLen2;
        if (remaining > 0) continue;
        runLen2 = Math.min(runLen2, runLen2 + remaining + skipped);
        const leadLen = [...closer[0]][0].length;
        const raw = rest.slice(0, openLen + closer.index + leadLen + runLen2);
        if (Math.min(openLen, runLen2) % 2) {
          const inner = raw.slice(1, -1);
          return { type: 'em', raw, text: inner, tokens: this.lexInline(inner, []) };
        }
        const inner = raw.slice(2, -2);
        return { type: 'strong', raw, text: inner, tokens: this.lexInline(inner, []) };
      }
    }
    return null;
  }

  // Strikethrough: like emphasis, but the closer run must be exactly as long
  // as the opener run, and there is no rule of three.
  tryDel(rest, masked, pos, prevChar, closers) {
    const m = DEL_OPEN.exec(rest);
    if (!m) return null;
    if (!(m[1] || '') || !prevChar || PUNCT_TEST.exec(prevChar)) {
      const openLen = [...m[0]].length - 1;
      let remaining = openLen;
      const lastCloser = closers['~'];
      const searchFrom = pos + openLen;
      if (lastCloser < searchFrom) return null;
      const tail = masked.slice(searchFrom);
      const limit = lastCloser - searchFrom;
      let closer;
      let run;
      let runLen2;
      DEL_CLOSE.lastIndex = 0;
      while ((closer = DEL_CLOSE.exec(tail)) !== null && !(closer.index > limit)) {
        run = closer[1] || closer[2] || closer[3] || closer[4] || closer[5] || closer[6];
        if (!run || (runLen2 = [...run].length, runLen2 !== openLen)) continue;
        if (closer[3] || closer[4]) { remaining += runLen2; continue; }
        remaining -= runLen2;
        if (remaining > 0) continue;
        runLen2 = Math.min(runLen2, runLen2 + remaining);
        const leadLen = [...closer[0]][0].length;
        const raw = rest.slice(0, openLen + closer.index + leadLen + runLen2);
        const inner = raw.slice(openLen, -openLen);
        return { type: 'del', raw, text: inner, tokens: this.lexInline(inner, []) };
      }
    }
    return null;
  }

  // -- Rendering -------------------------------------------------------------

  renderBlocks(tokens) {
    let out = '';
    for (const tok of tokens) {
      switch (tok.type) {
        case 'space': break;
        case 'hr': out += '<hr>\n'; break;
        case 'heading': out += '<h' + tok.depth + '>' + this.renderInline(tok.tokens, false) + '</h' + tok.depth + '>\n'; break;
        case 'code': out += this.renderCode(tok); break;
        case 'table': out += this.renderTable(tok); break;
        case 'blockquote': out += '<blockquote>\n' + this.renderBlocks(tok.tokens) + '</blockquote>\n'; break;
        case 'list': out += this.renderList(tok); break;
        case 'checkbox': out += this.renderCheckbox(tok); break;
        case 'html': out += tok.text; break;
        case 'def': break;
        case 'paragraph': out += '<p>' + this.renderInline(tok.tokens, false) + '</p>\n'; break;
        case 'text': out += this.renderText(tok, false); break;
        default: throw new Error('Token with "' + tok.type + '" type was not found.');
      }
    }
    return out;
  }

  renderCode(tok) {
    const lang = (tok.lang || '').match(NON_SPACE_START)?.[0];
    const body = tok.text ? tok.text.replace(END_NEWLINE, '') + '\n' : '';
    const inner = tok.escaped ? body : escapeHtml(body, true);
    if (lang) return '<pre><code class="language-' + escapeHtml(lang) + '">' + inner + '</code></pre>\n';
    return '<pre><code>' + inner + '</code></pre>\n';
  }

  renderList(tok) {
    let items = '';
    for (const item of tok.items) items += '<li>' + this.renderBlocks(item.tokens) + '</li>\n';
    const tag = tok.ordered ? 'ol' : 'ul';
    const start = tok.ordered && tok.start !== 1 ? ' start="' + tok.start + '"' : '';
    return '<' + tag + start + '>\n' + items + '</' + tag + '>\n';
  }

  renderCheckbox(tok) {
    return '<input ' + (tok.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
  }

  renderTable(tok) {
    let head = '';
    for (const cell of tok.header) head += this.renderTableCell(cell);
    let body = '';
    for (const row of tok.rows) {
      let cells = '';
      for (const cell of row) cells += this.renderTableCell(cell);
      body += '<tr>\n' + cells + '</tr>\n';
    }
    if (body) body = '<tbody>' + body + '</tbody>';
    return '<table>\n<thead>\n<tr>\n' + head + '</tr>\n</thead>\n' + body + '</table>\n';
  }

  renderTableCell(cell) {
    const tag = cell.header ? 'th' : 'td';
    const align = cell.align ? ' align="' + cell.align + '"' : '';
    return '<' + tag + align + '>' + this.renderInline(cell.tokens, false) + '</' + tag + '>\n';
  }

  renderText(tok, plain) {
    if (plain) return tok.text;
    if ('tokens' in tok && tok.tokens) return this.renderInline(tok.tokens, false);
    if ('escaped' in tok && tok.escaped) return tok.text;
    return escapeHtml(tok.text);
  }

  // Plain rendering (for image alt text): tags drop out, only the words stay.
  renderPlain(tok) {
    return tok.tokens ? this.renderInline(tok.tokens, true) : tok.text;
  }

  renderLink(tok) {
    const inner = tok.autolink ? escapeHtml(tok.text, true) : this.renderInline(tok.tokens, false);
    const href = encodeHref(tok.href);
    if (href === null) return inner;
    let out = '<a href="' + escapeHtml(href, tok.autolink) + '"';
    if (tok.title) out += ' title="' + escapeHtml(tok.title) + '"';
    return out + '>' + inner + '</a>';
  }

  renderImage(tok) {
    let alt = tok.text;
    if (tok.tokens) alt = this.renderInline(tok.tokens, true);
    const src = encodeHref(tok.href);
    if (src === null) return escapeHtml(alt);
    let out = '<img src="' + escapeHtml(src) + '" alt="' + escapeHtml(alt) + '"';
    if (tok.title) out += ' title="' + escapeHtml(tok.title) + '"';
    return out + '>';
  }

  renderInline(tokens, plain) {
    let out = '';
    for (const tok of tokens) {
      switch (tok.type) {
        case 'escape': out += plain ? tok.text : escapeHtml(tok.text); break;
        case 'html': out += tok.text; break;
        case 'link': out += plain ? this.renderPlain(tok) : this.renderLink(tok); break;
        case 'image': out += plain ? this.renderPlain(tok) : this.renderImage(tok); break;
        case 'checkbox': out += plain ? tok.raw : this.renderCheckbox(tok); break;
        case 'strong': out += plain ? this.renderPlain(tok) : '<strong>' + this.renderInline(tok.tokens, false) + '</strong>'; break;
        case 'em': out += plain ? this.renderPlain(tok) : '<em>' + this.renderInline(tok.tokens, false) + '</em>'; break;
        case 'codespan': out += plain ? tok.text : '<code>' + escapeHtml(tok.text, true) + '</code>'; break;
        case 'br': out += plain ? '' : '<br>'; break;
        case 'del': out += plain ? this.renderPlain(tok) : '<del>' + this.renderInline(tok.tokens, false) + '</del>'; break;
        case 'text': out += this.renderText(tok, plain); break;
        default: throw new Error('Token with "' + tok.type + '" type was not found.');
      }
    }
    return out;
  }
}

// A URL can start at a letter, a digit, or one of . _ + - (an email's local
// part, a www. host, or a scheme name).
function isUrlStartChar(c) {
  return (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || (c >= 48 && c <= 57) ||
    c === 46 || c === 95 || c === 43 || c === 45;
}
const URL_SCHEME = /^[a-zA-Z][a-zA-Z0-9+.-]{1,31}:\/\//;

// ---------------------------------------------------------------------------
// The entry point
// ---------------------------------------------------------------------------

/** The HTML marked 18.1.3 renders for `markdown`, with marked's defaults. */
export function parse(markdown) {
  const engine = new Engine();
  const src = markdown.replace(CARRIAGE_RETURN, '\n');
  const tokens = engine.lexBlocks(src, []);
  for (let i = 0; i < engine.queue.length; i++) {
    const job = engine.queue[i];
    engine.inRaw = false;
    engine.lexInline(job.src, job.tokens);
  }
  return engine.renderBlocks(tokens);
}