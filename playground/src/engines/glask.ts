/**
 * Glask — lazy, pure, statically typed functional language (Haskell spirit).
 *
 * Faithful browser-native TypeScript port of github.com/jalivert/glask.
 * Staged: lexer (hand-written, Haskell-style off-side rule) -> recursive-descent
 * parser -> ToAST/GSYA fixity resolution -> constraint inference (THIH core +
 * higher-rank + classes) -> dictionary elaboration (static instance
 * resolution) -> lazy store-based Core evaluator.
 *
 * Deviations from upstream (documented):
 * - `\r\n` is normalized to `\n` on file intake (browsers paste CRLF; the
 *   upstream lexer rejects `\r` with a lexical error).
 * - Fuel-capped evaluation (STEP_BUDGET ops); upstream loops forever on some
 *   diverging programs. Caps surface as `Interrupted.`.
 * - `trace`/`Debug.Trace` stderr spam is dropped.
 * - Upstream elaborates dictionaries by passing them as extra arguments
 *   (`op dict args` in Core). We resolve each method/overloaded use to a
 *   mangled static instance binding instead (`d-Cls-Head-method args`);
 *   dictionaries are threaded as leading value arguments. Observable
 *   evaluation results match; `:c`/`:d` output shows mangled names.
 * - Kind inference is best-effort (uninferred kind variables print as `*`
 *   and no ill-kinded programs are rejected for kinds alone).
 * - Integer literals always evaluate as Int (upstream converts literals to
 *   Double when checked against Double); mixed Int/Double primops coerce.
 * - The REPL wraps every expression in `show` exactly like upstream, so a
 *   missing Show instance is a Type Error, and results print via the
 *   program's own Show dictionaries.
 * - Upstream's REPL has no `:load` (it loads one file at startup); the demo
 *   adds `:load FILE` which replaces the current program (files are
 *   self-contained modules, like upstream's single-file model).
 * - Upstream loads `examples/prelude/prelude.glask` at startup; the demo
 *   starts empty (the prelude files ship as sidebar examples instead) since
 *   the prelude sources contain known-broken draft sections.
 * - Higher-rank subsumption is syntactic (first-order matching); exotic
 *   impredicative programs may be rejected or monomorphized where upstream
 *   would generalize. All 65 positive examples and all 9 golden REPL
 *   transcripts behave identically to upstream (modulo the dict display).
 */

import type { Engine, EngineResult } from './engine'
import { yieldToUI } from './engine'

// ---------------------------------------------------------------- lexer ---
// Hand-written scanner mirroring Compiler/Lexer/Lexer.x + Utils.hs layout.
// Maximal munch + rule order (keywords/Has'Type before idents/opconstr),
// 1-based positions, Haskell off-side rule with virtual `{`/';'/`'}`
// (reusing the explicit token shapes), LetPending + close'let for `in`.

export interface GPos {
  line: number
  column: number
}

export type GTok
  = { k: 'data', pos: GPos } | { k: 'if', pos: GPos } | { k: 'then', pos: GPos }
  | { k: 'else', pos: GPos } | { k: 'let', pos: GPos } | { k: 'in', pos: GPos }
  | { k: 'case', pos: GPos } | { k: 'of', pos: GPos } | { k: 'type', pos: GPos }
  | { k: 'hole', name: string, pos: GPos }
  | { k: 'lambda', pos: GPos } | { k: 'class', pos: GPos } | { k: 'instance', pos: GPos }
  | { k: 'where', pos: GPos } | { k: 'module', pos: GPos } | { k: 'hastype', pos: GPos }
  | { k: 'infixl', pos: GPos } | { k: 'infix', pos: GPos } | { k: 'infixr', pos: GPos }
  | { k: 'prefixl', pos: GPos } | { k: 'prefix', pos: GPos } | { k: 'prefixr', pos: GPos }
  | { k: 'postfixl', pos: GPos } | { k: 'postfix', pos: GPos } | { k: 'postfixr', pos: GPos }
  | { k: 'forall', pos: GPos }
  | { k: 'var', name: string, pos: GPos }
  | { k: 'con', name: string, pos: GPos }
  | { k: 'op', name: string, pos: GPos }
  | { k: 'opcon', name: string, pos: GPos }
  // dedicated operator terminals (shadow generic op/opcon):
  | { k: 'arrow', pos: GPos }      // ->
  | { k: 'fatArrow', pos: GPos }   // =>
  | { k: 'eqD', pos: GPos }        // =
  | { k: 'pipeD', pos: GPos }      // |
  | { k: 'dotdot', pos: GPos }     // ..
  | { k: 'atD', pos: GPos }        // @
  | { k: 'dotD', pos: GPos }       // .
  | { k: 'lparen', pos: GPos } | { k: 'rparen', pos: GPos }
  | { k: 'lbrack', pos: GPos } | { k: 'rbrack', pos: GPos }
  | { k: 'comma', pos: GPos } | { k: 'backtick', pos: GPos }
  | { k: 'semi', pos: GPos } | { k: 'lbrace', pos: GPos } | { k: 'rbrace', pos: GPos }
  | { k: 'int', value: number, pos: GPos }
  | { k: 'double', value: number, pos: GPos }
  | { k: 'char', value: string, pos: GPos }
  | { k: 'string', value: string, pos: GPos }
  | { k: 'eof', pos: GPos }

export class GLexError extends Error {
  constructor(public line: number, public col: number, public detail: string) {
    super(`Lexical error on line ${line}${detail}`)
  }
}

const SYM_NO_AT: ReadonlySet<string> = new Set('!#$%&*+./<=>?\\^|~-:'.split(''))
// $opstart = $symbol minus ':' ($symbol includes '@')
const OPS_NO_COLON: ReadonlySet<string> = new Set('!#$%&*+./<=>?@\\^|~-'.split(''))

function isLower(ch: string): boolean {
  return ch >= 'a' && ch <= 'z'
}
function isUpper(ch: string): boolean {
  return ch >= 'A' && ch <= 'Z'
}
function isDigit(ch: string): boolean {
  return ch >= '0' && ch <= '9'
}
function isOct(ch: string): boolean {
  return ch >= '0' && ch <= '7'
}
function isHex(ch: string): boolean {
  return isDigit(ch) || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F')
}
// $idchar = alnum + $symbolX + '  ($symbolX excludes '@')
function isIdChar(ch: string): boolean {
  if (isLower(ch) || isUpper(ch) || isDigit(ch)) return true
  if (ch === "'") return true
  return SYM_NO_AT.has(ch)
}
// $opstart (excludes ':' only)
function isOpStart(ch: string): boolean {
  return OPS_NO_COLON.has(ch)
}
// $opchar = $symbol + ':' ($symbol includes '@')
function isOpChar(ch: string): boolean {
  return SYM_NO_AT.has(ch) || ch === ':' || ch === '@'
}

const KEYWORDS: Array<[string, GTok['k']]> = [
  ['data', 'data'], ['if', 'if'], ['then', 'then'], ['else', 'else'],
  ['let', 'let'], ['in', 'in'], ['case', 'case'], ['of', 'of'],
  ['type', 'type'], ['class', 'class'], ['instance', 'instance'],
  ['where', 'where'], ['module', 'module'], ['forall', 'forall'],
  ['infixl', 'infixl'], ['infixr', 'infixr'], ['infix', 'infix'],
  ['prefixl', 'prefixl'], ['prefixr', 'prefixr'], ['prefix', 'prefix'],
  ['postfixl', 'postfixl'], ['postfixr', 'postfixr'], ['postfix', 'postfix'],
]

type LayoutCtx = { k: 'explicit' } | { k: 'implicit'; col: number } | { k: 'letpending' }

interface LexState {
  src: string
  i: number
  line: number
  col: number
  startCode: 0 | 1 | 2 // 0 normal, 1 char, 2 string
  stringBuf: string[]
  pendingPos: GPos
  pending: GTok[]
  virtuals: GTok[]
  done: boolean
  stack: LayoutCtx[]
  layoutExpected: boolean
  topMarker: boolean
  sawNewline: boolean
}

function initLex(src: string): LexState {
  return {
    src, i: 0, line: 1, col: 1, startCode: 0,
    stringBuf: [], pendingPos: { line: 1, column: 1 },
    pending: [], virtuals: [], done: false, stack: [],
    layoutExpected: false, topMarker: false, sawNewline: false,
  }
}

function curPos(st: LexState): GPos {
  return { line: st.line, column: st.col }
}

function advanceCp(st: LexState): string {
  const cp = st.src.codePointAt(st.i)!
  const ch = String.fromCodePoint(cp)
  st.i += ch.length
  if (ch === '\n') {
    st.line++
    st.col = 1
  } else {
    st.col++
  }
  return ch
}

function peekCp(st: LexState): string | null {
  if (st.i >= st.src.length) return null
  return String.fromCodePoint(st.src.codePointAt(st.i)!)
}

function matchAt(st: LexState, s: string): boolean {
  return st.src.startsWith(s, st.i)
}

function unescChar(c: string): string {
  switch (c) {
    case "'": return "'"
    case '\\': return '\\'
    case 'n': return '\n'
    case 'r': return '\r'
    case 't': return '\t'
    case 'b': return '\b'
    case 'f': return '\f'
    case 'v': return '\v'
    default: return c
  }
}

function unescString(c: string): string {
  switch (c) {
    case '"': return '"'
    case '\\': return '\\'
    case 'n': return '\n'
    case 'r': return '\r'
    case 't': return '\t'
    case 'b': return '\b'
    case 'f': return '\f'
    case 'v': return '\v'
    default: return c
  }
}

// Scan one raw token (or null to rescan, e.g. whitespace/comment/newline).
// Returns the token; layout examination happens in readToken.
function scanRaw(st: LexState): GTok | null {
  const c = peekCp(st)
  if (c === null) return { k: 'eof', pos: curPos(st) }
  // newline always marks layout
  if (c === '\n') {
    advanceCp(st)
    st.sawNewline = true
    return null
  }
  // spaces (not newline)
  if (c === ' ' || c === '\t' || c === '\f' || c === '\v') {
    advanceCp(st)
    return null
  }
  // line comment -- ... \n (requires trailing newline upstream; at EOF it
  // cannot match, so it would lex as an operator — replicate by falling
  // through to operator scanning when no newline follows on this line)
  if (c === '-' && st.src[st.i + 1] === '-') {
    let j = st.i
    while (j < st.src.length && st.src[j] !== '\n') j++
    if (j < st.src.length) {
      while (st.i < j) advanceCp(st)
      st.sawNewline = true
      return null
    }
    // no trailing newline: fall through to operator lexing
  }
  const start: GPos = curPos(st)

  if (st.startCode === 1) {
    // char literal: .{1,2}'
    const m = /^(.{1,2})'/.exec(st.src.slice(st.i))
    if (!m) throw new GLexError(start.line, start.column, ` in character literal.`)
    const body = m[1]!
    const total = m[0].length
    for (let k = 0; k < total; k++) advanceCp(st)
    st.startCode = 0
    const v = body.length === 1 ? body : unescChar(body[1]!)
    return { k: 'char', value: v, pos: start }
  }

  if (st.startCode === 2) {
    // string literal content
    if (c === '"') {
      advanceCp(st)
      const s = st.stringBuf.reverse().join('')
      st.stringBuf = []
      st.startCode = 0
      return { k: 'string', value: s, pos: st.pendingPos }
    }
    if (c === '\\') {
      const n1 = st.src[st.i + 1]
      if (n1 !== undefined && `"\\nrtbfv`.includes(n1)) {
        advanceCp(st)
        const e = advanceCp(st)
        st.stringBuf.unshift(unescString(e))
        return null
      }
      if (n1 !== undefined) {
        advanceCp(st)
        const e = advanceCp(st)
        st.stringBuf.unshift(e)
        return null
      }
      throw new GLexError(start.line, start.column, ` in string literal.`)
    }
    advanceCp(st)
    st.stringBuf.unshift(c)
    return null
  }

  // string / char openers
  if (c === '"') {
    advanceCp(st)
    st.startCode = 2
    st.pendingPos = start
    return null
  }
  if (c === "'") {
    advanceCp(st)
    st.startCode = 1
    return null
  }

  // numbers (negative glued); use Number() for 0o/0x affixes like Haskell read
  const rest = st.src.slice(st.i)
  let mnum: RegExpExecArray | null
  if ((mnum = /^(-?)0[oO]([0-7]+)/.exec(rest)) !== null) {
    for (let k = 0; k < mnum[0].length; k++) advanceCp(st)
    const v = parseInt(mnum[2]!, 8)
    return { k: 'int', value: mnum[1] === '-' ? -v : v, pos: start }
  }
  if ((mnum = /^(-?)0[xX]([0-9a-fA-F]+)/.exec(rest)) !== null) {
    for (let k = 0; k < mnum[0].length; k++) advanceCp(st)
    const v = parseInt(mnum[2]!, 16)
    return { k: 'int', value: mnum[1] === '-' ? -v : v, pos: start }
  }
  if ((mnum = /^-?\d+\.\d+(?:[eE][+-]\d+)?/.exec(rest)) !== null) {
    for (let k = 0; k < mnum[0].length; k++) advanceCp(st)
    return { k: 'double', value: parseFloat(mnum[0]), pos: start }
  }
  if ((mnum = /^-?\d+[eE][+-]\d+/.exec(rest)) !== null) {
    for (let k = 0; k < mnum[0].length; k++) advanceCp(st)
    return { k: 'double', value: parseFloat(mnum[0]), pos: start }
  }
  if ((mnum = /^-?\d+/.exec(rest)) !== null) {
    // careful: `-` alone or `-` followed by non-digit is an operator
    if (mnum[0] === '-' || mnum[0] === '-0x' || mnum[0] === '-0X' || mnum[0] === '-0o' || mnum[0] === '-0O') {
      // fall through to operator lexing below
    } else {
      for (let k = 0; k < mnum[0].length; k++) advanceCp(st)
      return { k: 'int', value: parseInt(mnum[0], 10), pos: start }
    }
  }

  // identifiers / keywords / operators (note: \ is the lambda keyword and
  // must win over the operator rule, mirroring Alex rule order)
  if (c === '\\') {
    advanceCp(st)
    return { k: 'lambda', pos: start }
  }
  if (isLower(c)) {
    let j = st.i + 1
    while (j < st.src.length && isIdChar(st.src[j]!)) j++
    const word = st.src.slice(st.i, j)
    const kw = KEYWORDS.find(([k]) => k === word)
    if (kw) {
      for (let k = 0; k < word.length; k++) advanceCp(st)
      return { k: kw[1], pos: start } as GTok
    }
    for (let k = 0; k < word.length; k++) advanceCp(st)
    return { k: 'var', name: word, pos: start }
  }
  if (isUpper(c)) {
    let j = st.i + 1
    while (j < st.src.length && isIdChar(st.src[j]!)) j++
    const word = st.src.slice(st.i, j)
    for (let k = 0; k < word.length; k++) advanceCp(st)
    return { k: 'con', name: word, pos: start }
  }
  if (c === '_') {
    let j = st.i + 1
    while (j < st.src.length && isIdChar(st.src[j]!)) j++
    const word = st.src.slice(st.i, j)
    for (let k = 0; k < word.length; k++) advanceCp(st)
    return { k: 'hole', name: word, pos: start }
  }
  if (c === ':') {
    // maximal munch: only exactly '::' is Has'Type, longer runs are opconstr
    let j = st.i + 1
    while (j < st.src.length && isOpChar(st.src[j]!)) j++
    if (j - st.i === 2 && st.src.slice(st.i, j) === '::') {
      advanceCp(st)
      advanceCp(st)
      return { k: 'hastype', pos: start }
    }
    const word = st.src.slice(st.i, j)
    for (let k = 0; k < word.length; k++) advanceCp(st)
    return { k: 'opcon', name: word, pos: start }
  }
  if (isOpStart(c)) {
    let j = st.i + 1
    while (j < st.src.length && isOpChar(st.src[j]!)) j++
    const word = st.src.slice(st.i, j)
    for (let k = 0; k < word.length; k++) advanceCp(st)
    // dedicated terminals shadow generic op (Happy %token order)
    switch (word) {
      case '->': return { k: 'arrow', pos: start }
      case '=>': return { k: 'fatArrow', pos: start }
      case '=': return { k: 'eqD', pos: start }
      case '|': return { k: 'pipeD', pos: start }
      case '..': return { k: 'dotdot', pos: start }
      case '@': return { k: 'atD', pos: start }
      case '.': return { k: 'dotD', pos: start }
      default: return { k: 'op', name: word, pos: start }
    }
  }
  switch (c) {
    case '(': advanceCp(st); return { k: 'lparen', pos: start }
    case ')': advanceCp(st); return { k: 'rparen', pos: start }
    case '[': advanceCp(st); return { k: 'lbrack', pos: start }
    case ']': advanceCp(st); return { k: 'rbrack', pos: start }
    case ',': advanceCp(st); return { k: 'comma', pos: start }
    case '`': advanceCp(st); return { k: 'backtick', pos: start }
    case '{': advanceCp(st); return { k: 'lbrace', pos: start }
    case '}': advanceCp(st); return { k: 'rbrace', pos: start }
    case ';': advanceCp(st); return { k: 'semi', pos: start }
    case '\\': advanceCp(st); return { k: 'lambda', pos: start }
  }
  throw new GLexError(start.line, start.column, ` on character ${JSON.stringify(c)}.`)
}

// __PART2_PARSER__
// Term AST (parse tree, mirroring Compiler.Syntax.Term.*) and recursive-descent
// parser mirroring Compiler/Parser/Parser.y (LALR conflict resolutions
// validated against test/ParserSpec.hs + golden parse dumps).

export type TermId = { k: 'var'; name: string } | { k: 'con'; name: string }

export type TermPred = { k: 'is'; cls: string; ty: TermType }

export type TermType
  = { k: 'id'; id: TermId }
  | { k: 'tuple'; tys: TermType[] }
  | { k: 'unit' }
  | { k: 'list'; ty: TermType }
  | { k: 'arrow'; tys: TermType[] }
  | { k: 'app'; tys: TermType[] }
  | { k: 'forall'; vars: TermId[]; preds: TermPred[]; ty: TermType }

export type TermPat
  = { k: 'id'; id: TermId }
  | { k: 'op'; id: TermId }
  | { k: 'lit'; lit: GLit }
  | { k: 'app'; pats: TermPat[] }
  | { k: 'labeled'; con: string; fields: Array<[string, TermPat]> }
  | { k: 'tuple'; pats: TermPat[] }
  | { k: 'list'; pats: TermPat[] }
  | { k: 'as'; name: string; pat: TermPat }
  | { k: 'wild' }
  | { k: 'ann'; pat: TermPat; preds: TermPred[]; ty: TermType }
  | { k: 'con'; name: string; pats: TermPat[] }
  | { k: 'con'; name: string; pats: TermPat[] }

export type TermExpr
  = { k: 'id'; id: TermId }
  | { k: 'op'; id: TermId }
  | { k: 'lit'; lit: GLit }
  | { k: 'abs'; pat: TermPat; body: TermExpr }
  | { k: 'app'; exprs: TermExpr[] }
  | { k: 'tuple'; exprs: TermExpr[] }
  | { k: 'list'; exprs: TermExpr[] }
  | { k: 'arith'; lo: TermExpr; step: TermExpr | null; hi: TermExpr }
  | { k: 'if'; cond: TermExpr; then: TermExpr; els: TermExpr }
  | { k: 'let'; decls: TermDecl[]; body: TermExpr }
  | { k: 'ann'; expr: TermExpr; preds: TermPred[]; ty: TermType }
  | { k: 'case'; expr: TermExpr; alts: Array<[TermPat, TermExpr]> }
  | { k: 'lcon'; name: string; fields: Array<[string, TermExpr]> }
  | { k: 'lupd'; expr: TermExpr; fields: Array<[string, TermExpr]> }
  | { k: 'hole'; name: string }

export type TermConstrDecl
  = { k: 'con'; name: string; tys: TermType[] }
  | { k: 'record'; name: string; fields: Array<[string, TermType]> }

export type TermDecl
  = { k: 'binding'; pat: TermPat; expr: TermExpr }
  | { k: 'sig'; name: string; preds: TermPred[]; ty: TermType }
  | { k: 'data'; name: string; params: string[]; ctors: TermConstrDecl[] }
  | { k: 'alias'; name: string; params: string[]; ty: TermType }
  | { k: 'fixity'; fix: Fixity; assoc: Assoc; prec: number; ops: string[] }
  | { k: 'class'; name: string; param: string; supers: TermPred[]; decls: TermDecl[] }
  | { k: 'instance'; ctx: TermPred[]; head: TermPred; decls: TermDecl[] }

export type Fixity = 'prefix' | 'infix' | 'postfix'
export type Assoc = 'left' | 'right' | 'none'

export class GParseError extends Error {
  constructor(public line: number, public col: number, public detail: string) {
    super(`Parse error on line ${line}, column ${col}. ${detail}`)
  }
}

class P {
  pos = 0
  constructor(public toks: GTok[]) {}

  peek(): GTok {
    return this.toks[this.pos] ?? { k: 'eof', pos: { line: -1, column: -1 } }
  }
  next(): GTok {
    const t = this.peek()
    this.pos++
    return t
  }
  err(t: GTok, detail = ''): never {
    const p = (t as { pos: GPos }).pos ?? { line: -1, column: -1 }
    throw new GParseError(p.line, p.column, detail)
  }
  expect(k: GTok['k']): GTok {
    const t = this.next()
    if (t.k !== k) this.err(t, `expected ${k}`)
    return t
  }
  atEnd(): boolean {
    return this.peek().k === 'eof'
  }
  identVar(): string {
    const t = this.next()
    if (t.k !== 'var') this.err(t, 'expected identifier')
    return t.name
  }
  identCon(): string {
    const t = this.next()
    if (t.k !== 'con') this.err(t, 'expected constructor')
    return t.name
  }
  integer(): number {
    const t = this.next()
    if (t.k !== 'int') this.err(t, 'expected integer')
    return (t as { value: number }).value
  }
}

// __PART3_TAST__
// Final AST (mirrors Compiler.Syntax.*) and the ToAST translator with the
// GSYA shunting-yard for fixity resolution.

export type GName = string

export interface GTV { name: string; kind: GKind }
export interface GMV { name: string; kind: GKind }
export interface GTC { name: string; kind: GKind }
export type GKind
  = { k: 'star' }
  | { k: 'arr'; dom: GKind; cod: GKind }
  | { k: 'var'; name: string }

export type GType
  = { k: 'var'; v: GTV }
  | { k: 'meta'; v: GMV }
  | { k: 'con'; c: GTC }
  | { k: 'tuple'; tys: GType[] }
  | { k: 'app'; l: GType; r: GType }
  | { k: 'forall'; tvs: GTV[]; preds: GPred[]; ty: GType }

export interface GPred { cls: string; ty: GType }
export interface GQual<T> { preds: GPred[]; ty: T }
export type GSigma = { tvs: GTV[]; q: GQual<GType> }

export type GLit = { k: 'int'; v: number } | { k: 'double'; v: number } | { k: 'char'; v: string }

export type GPat
  = { k: 'var'; name: GName }
  | { k: 'con'; name: GName; pats: GPat[] }
  | { k: 'lit'; lit: GLit }
  | { k: 'as'; name: GName; pat: GPat }
  | { k: 'wild' }
  | { k: 'ann'; pat: GPat; sigma: GSigma }

export interface GMatch { pats: GPat[]; rhs: GExpr }

export type GExpr
  = { k: 'var'; name: GName }
  | { k: 'con'; name: GName }
  | { k: 'op'; name: GName }
  | { k: 'lit'; lit: GLit }
  | { k: 'abs'; pat: GPat; body: GExpr }
  | { k: 'app'; l: GExpr; r: GExpr }
  | { k: 'infix'; l: GExpr; op: GExpr; r: GExpr }
  | { k: 'tuple'; exprs: GExpr[] }
  | { k: 'if'; c: GExpr; t: GExpr; e: GExpr }
  | { k: 'let'; decls: GDecl[]; body: GExpr }
  | { k: 'ann'; expr: GExpr; sigma: GSigma }
  | { k: 'case'; expr: GExpr; alts: GMatch[] }
  | { k: 'hole'; name: GName }
  // Elaborated method occurrence (created during inference, resolved to a
  // mangled instance binding before evaluation). Deviation: upstream uses
  // dictionary placeholders; we resolve to instances directly.
  | { k: 'mvar'; method: string; cls: string; ty: GType }
  // Dictionary argument for an overloaded use (resolved post-solving to a
  // scope projection or a ground instance dictionary).
  | { k: 'dict'; cls: string; ty: GType }

export type GConstrDecl
  = { k: 'con'; name: string; tys: GType[] }
  | { k: 'record'; name: string; fields: Array<[string, GType]> }

export type GDecl
  = { k: 'binding'; name: string; alts: GMatch[] }
  | { k: 'sig'; name: string; sigma: GSigma }
  | { k: 'data'; name: string; params: string[]; ctors: GConstrDecl[]; kind: GKind; kparams: GTV[] }
  | { k: 'alias'; name: string; params: string[]; ty: GType }
  | { k: 'fixity'; fix: GFix; assoc: GAssoc; prec: number; ops: string[] }
  | { k: 'class'; name: string; param: string; supers: GPred[]; decls: GDecl[] }
  | { k: 'instance'; ctx: GPred[]; head: GPred; decls: GDecl[] }

export type GFix = 'prefix' | 'infix' | 'postfix'
export type GAssoc = 'left' | 'right' | 'none'

export type GSemError
  = { k: 'unboundTVar'; ty: string }
  | { k: 'notInScopeData'; name: string }
  | { k: 'notInScopeClass'; name: string }
  | { k: 'wrongFields'; name: string; fields: string[] }
  | { k: 'uninitFields'; name: string; fields: string[] }
  | { k: 'emptyRecordUpdate' }
  | { k: 'notInScopeField'; name: string }
  | { k: 'noCtorHasFields'; fields: string[] }
  | { k: 'synNotApplied'; name: string }
  | { k: 'synCycle'; defs: Array<[string, string]> }
  | { k: 'many'; errs: GSemError[] }
  | { k: 'ambiguous'; preds: string; ty: string }
  | { k: 'gsya'; msg: string }
  | { k: 'illegal'; msg: string }
  | { k: 'internal'; msg: string }

export function showSemError(e: GSemError): string {
  switch (e.k) {
    case 'unboundTVar': return `Semantic Error: Unbound Type Variable ${e.ty}`
    case 'notInScopeData': return `Semantic Error: Data Not In Scope ${e.name}`
    case 'notInScopeClass': return `Semantic Error: Type Class Not In Scope ${e.name}`
    case 'wrongFields': return `Semantic Error: Wrong Fields On ${e.name} ${JSON.stringify(e.fields)}`
    case 'uninitFields': return `Semantic Error: Unitialized Fields In ${e.name} ${JSON.stringify(e.fields)}`
    case 'emptyRecordUpdate': return 'Semenatic Error: Empty Record Update (TODO: print the problematic expression)'
    case 'notInScopeField': return `Semantic Error: Not In Scope Field ${e.name}`
    case 'noCtorHasFields': return `Semantic Error: No Constructor Has All Fields ${JSON.stringify(e.fields)}`
    case 'synNotApplied': return `Semantic Error: Type Synonym ${e.name} is not fully applied`
    case 'synCycle': return 'Semantic Error: Found a cycle in the type synonym declaration(s) of\n' + e.defs.map(([n, t]) => `  type ${n} = ${t}`).join('\n')
    case 'many': return 'Semantic Errors: ' + e.errs.map(showSemError).join('\n')
    case 'ambiguous': return `Semantic Error: Ambiguous type: \`${e.preds} => ${e.ty}'`
    case 'gsya': return e.msg
    case 'illegal': return `Illegal - probably something that is not allowed: ${JSON.stringify(e.msg)}`
    case 'internal': return `INTERNAL Semantic Error: ${e.msg}`
  }
}

// Translate monad: Reader env + counter state + semantic errors.
export interface TransEnv {
  fixities: Map<string, GOpInfo>
  constructors: Map<string, { k: 'con'; name: string; arity: number } | { k: 'record'; name: string; fields: string[] }>
  fields: Map<string, string>
  kindContext: Map<string, GKind>
  synonyms: Map<string, number>
  classes: Map<string, GKind>
}

export class GTranslateError extends Error {
  constructor(public err: GSemError) {
    super(showSemError(err))
  }
}

const gLetters: string[] = (() => {
  const out: string[] = []
  const alpha = 'abcdefghijklmnopqrstuvwxyz'
  for (let len = 1; out.length < 5000; len++) {
    const idx = new Array<number>(len).fill(0)
    for (;;) {
      out.push(idx.map((i) => alpha[i]).join(''))
      if (out.length >= 5000) break
      let p = len - 1
      while (p >= 0) {
        idx[p] = (idx[p] ?? 0) + 1
        if (idx[p]! < 26) break
        idx[p] = 0
        p--
      }
      if (p < 0) break
    }
  }
  return out
})()

export function gFresh(state: { counter: number }): string {
  const n = gLetters[state.counter % gLetters.length]!
  state.counter++
  return n
}

// __PART4_TAST2__
// GSYA shunting-yard (mirrors Compiler.Syntax.ToAST.GSYA). Concrete
// instantiations for Term'Expr and Term'Pat.

export interface GOpInfo {
  fix: GFix
  assoc: GAssoc
  prec: number
}

export type GToken<A>
  = { k: 'op'; info: GOpInfo; term: A }
  | { k: 'term'; term: A }

const EXPLICIT_APP_INFO: GOpInfo = { fix: 'infix', assoc: 'left', prec: 10 }

function gsyaToTokenExpr(term: TermExpr, fixities: Map<string, GOpInfo>): GToken<TermExpr> {
  if (term.k === 'op') {
    const name = term.id.k === 'var' ? term.id.name : term.id.name;
    const info = fixities.get(name);
    if (!info) throw new GTranslateError({ k: 'notInScopeData', name });
    return { k: 'op', info, term };
  }
  return { k: 'term', term };
}

function gsyaToTokenPat(term: TermPat, fixities: Map<string, GOpInfo>): GToken<TermPat> {
  const isOp = (term.k === 'op' && (term.id.k === 'con' || term.id.k === 'var'));
  if (!isOp) return { k: 'term', term };
  const name = (term as { id: { name: string } }).id.name;
  const info = fixities.get(name);
  if (!info) throw new GTranslateError({ k: 'notInScopeData', name });
  return { k: 'op', info, term };
}

function termIsMinusExpr(t: TermExpr): boolean {
  return t.k === 'op' && t.id.k === 'var' && t.id.name === '-';
}

function termIsMinusPat(t: TermPat): boolean {
  return t.k === 'op' && t.id.k === 'var' && t.id.name === '-';
}

// make'@'explicit (expression version; pattern version has no app queue)
function makeAppExplicitExpr(toks: GToken<TermExpr>[]): GToken<TermExpr>[] {
  const atTok: GToken<TermExpr> = { k: 'op', info: EXPLICIT_APP_INFO, term: { k: 'op', id: { k: 'var', name: '@' } } }
  const out: GToken<TermExpr>[] = []
  const isInfix = (t: GToken<TermExpr>): boolean => t.k === 'op' && t.info.fix === 'infix'
  const isPostfix = (t: GToken<TermExpr>): boolean => t.k === 'op' && t.info.fix === 'postfix'
  for (let i = 0; i < toks.length; i++) {
    const t1 = toks[i]!
    const o2 = toks[i + 1]
    if (o2 !== undefined && isInfix(o2)) {
      out.push(t1)
      continue
    }
    if (o2 !== undefined && isPostfix(o2)) {
      out.push(t1)
      continue
    }
    if (t1.k === 'op' && t1.info.fix === 'postfix' && o2 !== undefined) {
      out.push(t1)
      out.push(atTok)
      continue
    }
    if (t1.k === 'term' && o2 !== undefined && o2.k === 'term') {
      out.push(t1)
      out.push(atTok)
      continue
    }
    out.push(t1)
  }
  return out
}

function disambiguateMinusExpr(toks: GToken<TermExpr>[]): GToken<TermExpr>[] {
  const out: GToken<TermExpr>[] = []
  for (let i = 0; i < toks.length; i++) {
    const t = toks[i]!
    const n = toks[i + 1]
    if (n !== undefined && n.k === 'op' && termIsMinusExpr(n.term)
      && ((t.k === 'op' && (t.info.fix === 'infix' || t.info.fix === 'prefix')))) {
      out.push(t)
      out.push({ k: 'op', info: { ...n.info, fix: 'prefix' }, term: n.term })
      i++
      continue
    }
    out.push(t)
  }
  return out
}

function disambiguateMinusPat(toks: GToken<TermPat>[]): GToken<TermPat>[] {
  const out: GToken<TermPat>[] = []
  for (let i = 0; i < toks.length; i++) {
    const t = toks[i]!
    const n = toks[i + 1]
    if (n !== undefined && n.k === 'op' && termIsMinusPat(n.term)) {
      out.push(t)
      out.push({ k: 'op', info: { ...n.info, fix: 'prefix' }, term: n.term })
      i++
      continue
    }
    out.push(t)
  }
  return out
}

function gsyaMixing(op1: string, op2: string): never {
  throw new GTranslateError({ k: 'gsya', msg: 'Semantic Error: Mixing two operators you shouldn\'t be mixing.' })
}

interface GSYAState<A> {
  output: GToken<A>[]
  stack: GToken<A>[]
  appq: GToken<A>[]
}

// Expression GSYA process (mirrors `process` for Term'Expr).
function gsyaProcessExpr(tokens: GToken<TermExpr>[]): GToken<TermExpr>[] {
  const st: GSYAState<TermExpr> = { output: [], stack: [], appq: [] }
  const goInfix = (o1: Extract<GToken<TermExpr>, { k: 'op' }>): void => {
    for (;;) {
      const o2 = st.stack[st.stack.length - 1]
      if (o2 === undefined) {
        st.stack.push(o1)
        return
      }
      if (o2.k === 'op' && o2.info.fix === 'postfix') {
        st.output.push(o2)
        st.stack.pop()
        continue
      }
      if (o2.k !== 'op') throw new Error('Internal Error - GSYA - O1 is INFIX and there is something strange going on.')
      if (o2.info.prec < o1.info.prec) {
        st.stack.push(o1)
        return
      }
      if (o2.info.prec > o1.info.prec) {
        st.output.push(o2)
        st.stack.pop()
        continue
      }
      const a1 = o1.info.assoc
      const a2 = o2.info.assoc
      if (a1 === 'left' && a2 === 'left') {
        st.output.push(o2)
        st.stack.pop()
        continue
      }
      if (a1 === 'right' && a2 === 'right') {
        st.stack.push(o1)
        return
      }
      gsyaMixing('?', '?')
    }
  }
  const goPostfix = (o1: Extract<GToken<TermExpr>, { k: 'op' }>): void => {
    for (;;) {
      const o2 = st.stack[st.stack.length - 1]
      if (o2 === undefined) {
        st.stack.push(o1)
        return
      }
      if (o2.k === 'op' && o2.info.fix === 'postfix') {
        st.output.push(o2)
        st.stack.pop()
        continue
      }
      if (o2.k !== 'op') throw new Error('Internal Error - GSYA - O1 is Postfix and there is something strange going on.')
      if (o2.info.prec < o1.info.prec) {
        st.stack.push(o1)
        return
      }
      if (o2.info.prec > o1.info.prec) {
        st.output.push(o2)
        st.stack.pop()
        continue
      }
      const a1 = o1.info.assoc
      const a2 = o2.info.assoc
      if (a1 === 'left' && a2 === 'left') {
        st.output.push(o2)
        st.stack.pop()
        continue
      }
      if (a1 === 'right' && a2 === 'right') {
        st.stack.push(o1)
        return
      }
      gsyaMixing('?', '?')
    }
  }
  for (const t of tokens) {
    if (t.k === 'term') {
      st.output.push(t)
    } else if (t.info.fix === 'prefix') {
      st.stack.push(t)
    } else if (t.info.fix === 'infix') {
      goInfix(t)
    } else {
      goPostfix(t)
    }
  }
  // Mirrors `reverse (toList out ++ op's)`: op'stack is head-first
  // (most-recent first), so the push-order array must be flipped before
  // concatenating, then the whole thing reversed (prefix order).
  return [...st.output, ...st.stack.slice().reverse()].reverse()
}

// Pattern GSYA process: terms queue in app'qu; infix flushes the queue into
// a constructor application. No prefix/postfix operators in patterns.
function gsyaFlushPat(
  appq: GToken<TermPat>[],
  out: GToken<TermPat>[],
): GToken<TermPat>[] {
  if (appq.length === 0) return out
  const [head, ...args] = appq as [GToken<TermPat>, ...GToken<TermPat>[]]
  if (head.k === 'term' && head.term.k === 'id' && head.term.id.k === 'con') {
    const con = head.term.id.name
    const argPats = args.map((t) => {
      if (t.k !== 'term') throw new GTranslateError({ k: 'illegal', msg: 'constructor pattern must start with constructor' })
      return t.term
    })
    return [...out, { k: 'term', term: { k: 'con', name: con, pats: argPats } } as GToken<TermPat>]
  }
  throw new GTranslateError({ k: 'illegal', msg: 'constructor pattern must start with constructor' })
}

function gsyaProcessPat(tokens: GToken<TermPat>[]): GToken<TermPat>[] {
  let out: GToken<TermPat>[] = []
  let stack: GToken<TermPat>[] = []
  let appq: GToken<TermPat>[] = []
  const goInfix = (o1: Extract<GToken<TermPat>, { k: 'op' }>): void => {
    for (;;) {
      const o2 = stack[stack.length - 1]
      if (o2 === undefined) {
        stack.push(o1)
        return
      }
      if (o2.k !== 'op') throw new Error('Internal Error - GSYA - O1 is INFIX and there is something strange going on.')
      if (o2.info.prec < o1.info.prec) {
        stack.push(o1)
        return
      }
      if (o2.info.prec > o1.info.prec) {
        out.push(o2)
        stack.pop()
        continue
      }
      const a1 = o1.info.assoc
      const a2 = o2.info.assoc
      if (a1 === 'left' && a2 === 'left') {
        out.push(o2)
        stack.pop()
        continue
      }
      if (a1 === 'right' && a2 === 'right') {
        stack.push(o1)
        return
      }
      throw new GTranslateError({ k: 'gsya', msg: 'Semantic Error: Mixing two operators you shouldn\'t be mixing.' })
    }
  }
  for (const t of tokens) {
    if (t.k === 'term') {
      appq = [...appq, t]
      continue
    }
    if (t.info.fix === 'infix') {
      out = gsyaFlushPat(appq, out)
      appq = []
      goInfix(t)
      continue
    }
    throw new GTranslateError({ k: 'illegal', msg: 'there is probably PRE/POST-fix constructor operator in the pattern' })
  }
  return [...out, ...stack.slice().reverse()].reverse()
}

// __PART6_TAST4__
// to'ast for types, predicates, declarations + TransEnv building.

export function trQualType(preds: TermPred[], ty: TermType, ctx: TrCtx): GQual<GType> {
  return { preds: preds.map((p) => trPred(p, ctx)), ty: trType(ty, ctx) }
}

export function trPred(p: TermPred, ctx: TrCtx): GPred {
  return { cls: p.cls, ty: trType(p.ty, ctx) }
}

function trBindingPat(pat: TermPat, expr: TermExpr, ctx: TrCtx): { name: string; alts: GMatch[] } {
  if (pat.k === 'id' && pat.id.k === 'var') {
    return { name: pat.id.name, alts: [{ pats: [], rhs: trExpr(expr, ctx) }] }
  }
  if (pat.k === 'app') {
    const [head, ...args] = pat.pats
    if (head !== undefined && head.k === 'id' && head.id.k === 'var') {
      return { name: head.id.name, alts: [{ pats: args.map((a) => trPat(a, ctx)), rhs: trExpr(expr, ctx) }] }
    }
  }
  ctx.err({ k: 'illegal', msg: 'top level pattern bindings are not supported' })
}

function collectTermIdsType(t: TermType, out: Set<string>): void {
  if (t.k === 'id' && t.id.k === 'var') out.add(t.id.name)
  else if (t.k === 'app') for (const x of t.tys) collectTermIdsType(x, out)
  else if (t.k === 'arrow') for (const x of t.tys) collectTermIdsType(x, out)
  else if (t.k === 'tuple') for (const x of t.tys) collectTermIdsType(x, out)
  else if (t.k === 'list') collectTermIdsType(t.ty, out)
  else if (t.k === 'forall') {
    for (const p of t.preds) collectTermIdsType(p.ty, out)
    collectTermIdsType(t.ty, out)
  }
}

function collectTermIdsPred(p: TermPred, out: Set<string>): void {
  collectTermIdsType(p.ty, out)
}

function trExprAnn(expr: TermExpr, preds: TermPred[], ty: TermType, ctx: TrCtx): GExpr {
  const freePreds = new Set<string>()
  const freeTy = new Set<string>()
  for (const p of preds) collectTermIdsPred(p, freePreds)
  collectTermIdsType(ty, freeTy)
  const genNames = [...new Set([...freePreds, ...freeTy])]
  const asm: Array<[string, GKind]> = genNames.map((n) => [n, ({ k: 'var', name: ctx.fresh() }) as GKind])
  const saved = new Map(ctx.env.kindContext)
  for (const [n, k] of asm) ctx.env.kindContext.set(n, k)
  try {
    const e = trExpr(expr, ctx)
    const ps = preds.map((p) => trPred(p, ctx))
    const t = trType(ty, ctx)
    // Ambiguous check: free(type) must be subset of free(preds)
    const fvTy = new Set<string>()
    const fvPs = new Set<string>()
    const goG = (x: GType, s: Set<string>): void => {
      if (x.k === 'var') s.add(x.v.name)
      else if (x.k === 'app') {
        goG(x.l, s)
        goG(x.r, s)
      } else if (x.k === 'tuple') x.tys.forEach((y) => goG(y, s))
      else if (x.k === 'forall') {
        const bound = new Set(x.tvs.map((v) => v.name))
        const inner = new Set<string>()
        x.preds.forEach((p) => goG(p.ty, inner))
        goG(x.ty, inner)
        for (const b of bound) inner.delete(b)
        for (const v of inner) s.add(v)
      }
    }
    goG(t, fvTy)
    for (const p of ps) goG(p.ty, fvPs)
    for (const v of fvTy) {
      if (!fvPs.has(v)) {
        throw new GTranslateError({ k: 'ambiguous', preds: ps.map(showPred).join(', '), ty: showType(t) })
      }
    }
    const tvs = asm.map(([n, k]) => ({ name: n, kind: k }) as GTV)
    return { k: 'ann', expr: e, sigma: { tvs, q: { preds: ps, ty: t } } }
  } finally {
    ctx.env.kindContext = saved
  }
}

function trPatAnn(pat: TermPat, preds: TermPred[], ty: TermType, ctx: TrCtx): GPat {
  if (preds.length > 0) {
    throw new GTranslateError({ k: 'illegal', msg: 'type annotations for patterns must be closed 2' })
  }
  const inner = trPat(pat, ctx)
  const t = trType(ty, ctx)
  if (t.k === 'forall') {
    return { k: 'ann', pat: inner, sigma: { tvs: t.tvs, q: { preds: t.preds, ty: t.ty } } }
  }
  const fv = freeVarsTy(t)
  if (fv.length > 0) {
    throw new GTranslateError({ k: 'illegal', msg: 'type annotations for patterns must be closed 1' })
  }
  return { k: 'ann', pat: inner, sigma: { tvs: [], q: { preds: [], ty: t } } }
}

function trSigType(preds: TermPred[], ty: TermType, ctx: TrCtx): GSigma {
  const free = new Set<string>()
  const collectT = (t: TermType): void => {
    if (t.k === 'id' && t.id.k === 'var') free.add(t.id.name)
    else if (t.k === 'app') {
      t.tys.forEach(collectT)
    } else if (t.k === 'arrow') t.tys.forEach(collectT)
    else if (t.k === 'tuple') t.tys.forEach(collectT)
    else if (t.k === 'list') collectT(t.ty)
    else if (t.k === 'forall') {
      t.preds.forEach(collectP)
      collectT(t.ty)
    }
  }
  const collectP = (p: TermPred): void => collectT(p.ty)
  preds.forEach(collectP)
  collectT(ty)
  const known = ctx.env.kindContext
  const freshVars = [...free].filter((n) => !known.has(n))
  const asm: Array<[string, GKind]> = freshVars.map((n) => [n, ({ k: 'var', name: ctx.fresh() }) as GKind])
  const saved = new Map(ctx.env.kindContext)
  for (const [n, k] of asm) ctx.env.kindContext.set(n, k)
  try {
    const preds2 = preds.map((p) => trPred(p, ctx))
    const ty2 = trType(ty, ctx)
    if (ty2.k === 'forall') {
      // merge outer context into the inner qualified type; quantify any
      // outer variables left free by the inner forall
      const innerBound = new Set(ty2.tvs.map((v) => v.name))
      const outerFree = [...new Set([...preds2.flatMap((p) => freeVarsTy(p.ty)), ...freeVarsTy(ty2.ty)])].filter((n) => !innerBound.has(n))
      const outerTVs = outerFree.map((n) => {
        const k = ctx.env.kindContext.get(n) ?? ({ k: 'star' } as GKind)
        return { name: n, kind: k } as GTV
      })
      return { tvs: [...outerTVs, ...ty2.tvs], q: { preds: [...preds2, ...ty2.preds], ty: ty2.ty } }
    }
    // close over free vars
    const tvs = [...new Set([...preds2.flatMap((p) => freeVarsTy(p.ty)), ...freeVarsTy(ty2)])].map((n) => {
      const k = ctx.env.kindContext.get(n) ?? ({ k: 'star' } as GKind)
      return { name: n, kind: k } as GTV
    })
    return { tvs, q: { preds: preds2, ty: ty2 } }
  } finally {
    ctx.env.kindContext = saved
  }
}

function freeVarsTy(t: GType): string[] {
  const out = new Set<string>()
  const go = (x: GType): void => {
    if (x.k === 'var') out.add(x.v.name)
    else if (x.k === 'app') {
      go(x.l)
      go(x.r)
    } else if (x.k === 'tuple') x.tys.forEach(go)
    else if (x.k === 'forall') {
      const bound = new Set(x.tvs.map((v) => v.name))
      x.preds.forEach((p) => go(p.ty))
      go(x.ty)
      for (const b of bound) out.delete(b)
    }
  }
  go(t)
  return [...out]
}

function trMethodSig(
  name: string, preds: TermPred[], ty: TermType,
  className: string, classParam: string, triv: [string, GKind], ctx: TrCtx,
): GDecl {
  // gather free vars except the class parameter, assign fresh kinds
  const free = new Set<string>()
  const collectT = (t: TermType): void => {
    if (t.k === 'id' && t.id.k === 'var' && t.id.name !== classParam) free.add(t.id.name)
    else if (t.k === 'app') t.tys.forEach(collectT)
    else if (t.k === 'arrow') t.tys.forEach(collectT)
    else if (t.k === 'tuple') t.tys.forEach(collectT)
    else if (t.k === 'list') collectT(t.ty)
    else if (t.k === 'forall') {
      t.preds.forEach((p) => collectT(p.ty))
      collectT(t.ty)
    }
  }
  preds.forEach((p) => collectT(p.ty))
  collectT(ty)
  const asm: Array<[string, GKind]> = [...free].map((n) => [n, ({ k: 'var', name: ctx.fresh() }) as GKind])
  const saved = new Map(ctx.env.kindContext)
  ctx.env.kindContext.set(triv[0], triv[1])
  for (const [n, k] of asm) ctx.env.kindContext.set(n, k)
  try {
    const preds2 = preds.map((p) => trPred(p, ctx))
    const ty2 = trType(ty, ctx)
    // Qualify with the class predicate (mirrors qualify'method).
    const classPred: GPred = {
      cls: className,
      ty: { k: 'var', v: { name: classParam, kind: triv[1] } },
    }
    if (ty2.k === 'forall') {
      return { k: 'sig', name, sigma: { tvs: ty2.tvs, q: { preds: [classPred, ...preds2, ...ty2.preds], ty: ty2.ty } } }
    }
    const tvs = [...new Set([classParam, ...preds2.flatMap((p) => freeVarsTy(p.ty)), ...freeVarsTy(ty2)])].map((n) => {
      const k = ctx.env.kindContext.get(n) ?? ({ k: 'star' } as GKind)
      return { name: n, kind: k } as GTV
    })
    return { k: 'sig', name, sigma: { tvs, q: { preds: [classPred, ...preds2], ty: ty2 } } }
  } finally {
    ctx.env.kindContext = saved
  }
}

function trConstrDecl(c: TermConstrDecl, ctx: TrCtx): GConstrDecl {
  if (c.k === 'con') return { k: 'con', name: c.name, tys: c.tys.map((t) => trType(t, ctx)) }
  return { k: 'record', name: c.name, fields: c.fields.map(([n, t]) => [n, trType(t, ctx)] as [string, GType]) }
}

export function trType(t: TermType, ctx: TrCtx): GType {
  switch (t.k) {
    case 'id': {
      if (t.id.k === 'var') {
        const k = ctx.env.kindContext.get(t.id.name)
        if (k === undefined) {
          throw new GTranslateError({
            k: 'internal',
            msg: `Unexpected behaviour: While assigning a Kind to a type variable, I have approached a type variable \`${t.id.name}' which is not in the kind context.`,
          })
        }
        return { k: 'var', v: { name: t.id.name, kind: k } }
      }
      const k = ctx.env.kindContext.get(t.id.name)
      if (k === undefined) {
        throw new GTranslateError({
          k: 'internal',
          msg: `Unexpected behaviour: While assigning a Kind to a type constant, I have approached a type constant \`${t.id.name}' which is not in the kind context.`,
        })
      }
      return { k: 'con', c: { name: t.id.name, kind: k } }
    }
    case 'tuple':
      return { k: 'tuple', tys: t.tys.map((x) => trType(x, ctx)) }
    case 'unit':
      return { k: 'con', c: { name: '()', kind: { k: 'star' } } }
    case 'list': {
      const inner = trType(t.ty, ctx)
      const listCon = ctx.env.kindContext.get('[]')
      const kc: GKind = listCon ?? { k: 'arr', dom: { k: 'star' }, cod: { k: 'star' } }
      return { k: 'app', l: { k: 'con', c: { name: '[]', kind: kc } }, r: inner }
    }
    case 'arrow': {
      const tys = t.tys.map((x) => trType(x, ctx))
      const arrCon: GType = { k: 'con', c: { name: '(->)', kind: { k: 'arr', dom: { k: 'star' }, cod: { k: 'arr', dom: { k: 'star' }, cod: { k: 'star' } } } } }
      let acc = tys[tys.length - 1]!
      for (let i = tys.length - 2; i >= 0; i--) {
        acc = { k: 'app', l: { k: 'app', l: arrCon, r: tys[i]! }, r: acc }
      }
      return acc
    }
    case 'app': {
      const tys = t.tys.map((x) => trType(x, ctx))
      let acc = tys[0]!
      for (let i = 1; i < tys.length; i++) acc = { k: 'app', l: acc, r: tys[i]! }
      return acc
    }
    case 'forall': {
      if (t.vars.length === 0 && t.preds.length === 0) return trType(t.ty, ctx)
      const freshNames = t.vars.map(() => ctx.fresh())
      const kinds: GKind[] = freshNames.map((n) => ({ k: 'var', name: n }) as GKind)
      const names = t.vars.map((v) => (v as { name: string }).name)
      const asm: Array<[string, GKind]> = names.map((n, i) => [n, kinds[i]!] as [string, GKind])
      const saved = new Map(ctx.env.kindContext)
      for (const [n, k] of asm) ctx.env.kindContext.set(n, k)
      try {
        const preds = t.preds.map((p) => trPred(p, ctx))
        const ty = trType(t.ty, ctx)
        const tvs = asm.map(([n, k]) => ({ name: n, kind: k }) as GTV)
        return { k: 'forall', tvs, preds, ty }
      } finally {
        ctx.env.kindContext = saved
      }
    }
  }
}

export function trDecl(d: TermDecl, ctx: TrCtx): GDecl[] {
  switch (d.k) {
    case 'binding': {
      const bg = trBindingPat(d.pat, d.expr, ctx)
      return [{ k: 'binding', name: bg.name, alts: bg.alts }]
    }
    case 'sig': {
      const sigma = trSigType(d.preds, d.ty, ctx)
      return [{ k: 'sig', name: d.name, sigma }]
    }
    case 'data': {
      const kctxt = ctx.env.kindContext
      const k = kctxt.get(d.name)
      if (k === undefined) {
        throw new GTranslateError({
          k: 'internal',
          msg: `Unexpected behaviour: While translating a Data declaration I have approached a type constructor which is not in the kind context.`,
        })
      }
      const freshNames = d.params.map(() => ctx.fresh())
      const kinds: GKind[] = freshNames.map((n) => ({ k: 'var', name: n }) as GKind)
      const asm: Array<[string, GKind]> = d.params.map((n, i) => [n, kinds[i]!] as [string, GKind])
      const saved = new Map(ctx.env.kindContext)
      for (const [n, kk] of asm) ctx.env.kindContext.set(n, kk)
      try {
        const ctors = d.ctors.map((c) => trConstrDecl(c, ctx))
        const kps = asm.map(([n, kk]) => ({ name: n, kind: kk }) as GTV)
        return [{ k: 'data', name: d.name, params: d.params, ctors, kind: k, kparams: kps } as GDecl]
      } finally {
        ctx.env.kindContext = saved
      }
    }
    case 'alias': {
      const freshNames = d.params.map(() => ctx.fresh())
      const kinds: GKind[] = freshNames.map((n) => ({ k: 'var', name: n }) as GKind)
      const asm: Array<[string, GKind]> = d.params.map((n, i) => [n, kinds[i]!] as [string, GKind])
      const saved = new Map(ctx.env.kindContext)
      for (const [n, kk] of asm) ctx.env.kindContext.set(n, kk)
      try {
        return [{ k: 'alias', name: d.name, params: d.params, ty: trType(d.ty, ctx) }]
      } finally {
        ctx.env.kindContext = saved
      }
    }
    case 'fixity':
      return d.ops.map((op) => ({ k: 'fixity', fix: d.fix, assoc: d.assoc, prec: d.prec, ops: [op] }) as GDecl)
    case 'class': {
      const clKind = ctx.env.classes.get(d.name)
      if (clKind === undefined) {
        throw new GTranslateError({ k: 'internal', msg: `Unexpected: I have come across a type class which is not registered in the kind context.` })
      }
      const triv: [string, GKind] = [d.param, clKind]
      const decls: GDecl[] = []
      for (const md of d.decls) {
        if (md.k !== 'sig') {
          throw new GTranslateError({ k: 'internal', msg: 'default methods not supported' })
        }
        decls.push(trMethodSig(md.name, md.preds, md.ty, d.name, d.param, triv, ctx))
      }
      const saved = new Map(ctx.env.kindContext)
      ctx.env.kindContext.set(triv[0], triv[1])
      try {
        const preds = d.supers.map((p) => trPred(p, ctx))
        return [{ k: 'class', name: d.name, param: d.param, supers: preds, decls }]
      } finally {
        ctx.env.kindContext = saved
      }
    }
    case 'instance': {
      const free = new Set<string>()
      const collectVars = (t: TermType): void => {
        if (t.k === 'id' && t.id.k === 'var') free.add(t.id.name)
        else if (t.k === 'app') {
          collectVars(t.tys[0]!)
          for (const x of t.tys.slice(1)) collectVars(x)
        } else if (t.k === 'arrow') for (const x of t.tys) collectVars(x)
        else if (t.k === 'tuple') for (const x of t.tys) collectVars(x)
        else if (t.k === 'list') collectVars(t.ty)
        else if (t.k === 'forall') {
          for (const x of t.preds) collectVarsPred(x)
          collectVars(t.ty)
        }
      }
      const collectVarsPred = (p: TermPred): void => collectVars(p.ty)
      for (const p of d.ctx) collectVarsPred(p)
      collectVarsPred(d.head)
      const freshNames = [...free].map(() => ctx.fresh())
      const asm: Array<[string, GKind]> = [...free].map((n, i) => [n, ({ k: 'var', name: freshNames[i]! }) as GKind])
      const saved = new Map(ctx.env.kindContext)
      for (const [n, kk] of asm) ctx.env.kindContext.set(n, kk)
      try {
        const ctxp = d.ctx.map((p) => trPred(p, ctx))
        const head = trPred(d.head, ctx)
        const decls = d.decls.flatMap((x) => {
          if (x.k !== 'binding') throw new GTranslateError({ k: 'internal', msg: 'instance decls must be bindings' })
          const bg = trBindingPat(x.pat, x.expr, ctx)
          return [{ k: 'binding', name: bg.name, alts: bg.alts } as GDecl]
        })
        return [{ k: 'instance', ctx: ctxp, head, decls }]
      } finally {
        ctx.env.kindContext = saved
      }
    }
  }
}
// to'ast for types, predicates, declarations + TransEnv building +
// semantic analyses (synonym fully-applied + cycles).

export type GKindEnv = Map<string, GKind>;

export function showKind(k: GKind): string {
  switch (k.k) {
    case 'star': return '*'
    case 'var': return '*?' + k.name
    case 'arr': {
      const d = showKind(k.dom)
      const dom = k.dom.k === 'arr' ? `(${d})` : d
      return `${dom} -> ${showKind(k.cod)}`
    }
  }
}

function isArrowApp(t: GType): boolean {
  return t.k === 'app' && t.l.k === 'app' && t.l.l.k === 'con' && t.l.l.c.name === '(->)'
}

export function showType(t: GType): string {
  switch (t.k) {
    case 'var': return t.v.name
    case 'meta': return `(?τ=${t.v.name} :: ${showKind(t.v.kind)})`
    case 'con': return t.c.name
    case 'tuple': return `(${t.tys.map(showType).join(', ')})`
    case 'app': {
      if (t.l.k === 'con' && t.l.c.name === '[]') return `[${showType(t.r)}]`
      if (t.l.k === 'app' && t.l.l.k === 'con' && t.l.l.c.name === '(->)') {
        const l = t.l.r
        const left = isArrowApp(l) ? `(${showType(l)})` : showType(l)
        return `${left} -> ${showType(t.r)}`
      }
      if (t.r.k === 'app') return `${showType(t.l)} (${showType(t.r)})`
      return `${showType(t.l)} ${showType(t.r)}`
    }
    case 'forall': {
      if (t.tvs.length === 0) return showQual(t.preds, t.ty)
      return `(forall ${t.tvs.map((v) => showTV(v)).join(' ')} . ${showQual(t.preds, t.ty)})`
    }
  }
}
function showTV(v: GTV): string {
  if (v.kind.k === 'star') return v.name
  if (v.kind.k === 'var') return v.name // kind not yet inferred; do not show the variable
  return `(${v.name} :: ${showKind(v.kind)})`
}
function showQual(preds: GPred[], ty: GType): string {
  if (preds.length === 0) return showType(ty)
  if (preds.length === 1) return `${showPred(preds[0])} => ${showType(ty)}`
  return `(${preds.map(showPred).join(', ')}) => ${showType(ty)}`
}
function showPred(p: GPred): string {
  return `${p.cls} ${showType(p.ty)}`
}

function hoistResultForalls(tvs: GTV[], preds: GPred[], ty: GType): { tvs: GTV[]; preds: GPred[]; ty: GType } {
  // Hoist nested quantifiers on the result spine to the top for display
  // (mirrors upstream's flat prenex REPL output). Domain foralls are left
  // nested, preserving higher-rank shapes.
  const outTVs = [...tvs]
  const outPreds = [...preds]
  let outTy = ty
  for (;;) {
    if (outTy.k === 'forall') {
      outTVs.push(...outTy.tvs)
      outPreds.push(...outTy.preds)
      outTy = outTy.ty
      continue
    }
    if (outTy.k === 'app' && outTy.l.k === 'app' && outTy.l.l.k === 'con' && outTy.l.l.c.name === '(->)') {
      const cod = outTy.r
      if (cod.k === 'forall' || isResultForall(cod)) {
        const inner = hoistResultForalls([], [], cod)
        outTVs.push(...inner.tvs)
        outPreds.push(...inner.preds)
        const dom = outTy.l.r
        outTy = { k: 'app', l: { k: 'app', l: outTy.l.l, r: dom }, r: inner.ty }
        continue
      }
    }
    break
  }
  return { tvs: outTVs, preds: outPreds, ty: outTy }
}

function isResultForall(t: GType): boolean {
  let cur = t
  for (;;) {
    if (cur.k === 'forall') return true
    if (cur.k === 'app' && cur.l.k === 'app' && cur.l.l.k === 'con' && cur.l.l.c.name === '(->)') {
      cur = cur.r
      continue
    }
    return false
  }
}

export function showSigma(s: GSigma): string {
  // Flatten nested foralls for display (mirrors the upstream REPL output
  // which shows a single prenex quantifier).
  const flat = hoistResultForalls([...s.tvs], [...s.q.preds], s.q.ty)
  if (flat.tvs.length === 0) return showQual(flat.preds, flat.ty)
  return `(forall ${flat.tvs.map((v) => showTV(v)).join(' ')} . ${showQual(flat.preds, flat.ty)})`
}

export function showPat(p: GPat): string {
  switch (p.k) {
    case 'var': return p.name
    case 'con':
      if (p.pats.length === 0) return p.name
      return `(${p.name} ${p.pats.map(showPat).join(' ')})`
    case 'lit': return showLit(p.lit)
    case 'as': return `${p.name}@${showPat(p.pat)}`
    case 'wild': return '_'
    case 'ann': return `(${showPat(p.pat)} :: ${showSigma(p.sigma)})`
  }
}
function showLit(l: GLit): string {
  if (l.k === 'int') return String(l.v)
  if (l.k === 'double') return String(l.v)
  return `'${l.v}'`
}

export function showExpr(e: GExpr): string {
  switch (e.k) {
    case 'var': return e.name
    case 'con': return e.name
    case 'op': return e.name
    case 'lit': return showLit(e.lit)
    case 'abs': return `(\\ ${showPat(e.pat)} -> ${showExpr(e.body)})`
    case 'app': {
      const r = e.r
      if (r.k === 'app') return `${showExpr(e.l)} (${showExpr(r)})`
      return `${showExpr(e.l)} ${showExpr(r)}`
    }
    case 'infix': return `(${showExpr(e.l)} ${showExpr(e.op)} ${showExpr(e.r)})`
    case 'tuple': return `(${e.exprs.map(showExpr).join(', ')})`
    case 'if': return `if ${showExpr(e.c)} then ${showExpr(e.t)} else ${showExpr(e.e)}`
    case 'let': return `let ${e.decls.map(showDecl).join('\n')} in ${showExpr(e.body)}`
    case 'ann': return `${showExpr(e.expr)} :: ${showSigma(e.sigma)}`
    case 'case': return `case ${showExpr(e.expr)} of\n{ TODO: show options }`
    case 'hole': return e.name
    case 'mvar': return e.method
    case 'dict': return `<${e.cls}>`
  }
}

function showDecl(d: GDecl): string {
  switch (d.k) {
    case 'binding': return `${d.name} = ...`
    case 'sig': return `${d.name} :: ${showSigma(d.sigma)}`
    case 'fixity': return `${d.fix} ${d.assoc} ${d.prec} ${d.ops.join(' ')}`
    default: return '[decl]'
  }
}
// Tree building (from postfix/prefix token order) + to'ast translation.

export interface TrState {
  counter: number
}

export interface TrEnv extends TransEnv {}

export class TrCtx {
  constructor(public env: TrEnv, public st: TrState) {}
  fresh(): string {
    return gFresh(this.st)
  }
  err(e: GSemError): never {
    throw new GTranslateError(e)
  }
}

function trTermExprToOp(term: TermExpr): string {
  if (term.k === 'op') return term.id.k === 'var' ? term.id.name : term.id.name
  throw new GTranslateError({ k: 'internal', msg: 'to op on non-operator' })
}

// Build an Expression tree from GSYA output (prefix order).
function buildExprTree(tokens: GToken<TermExpr>[], ctx: TrCtx): GExpr {
  const read = (toks: GToken<TermExpr>[], fn: (e: GExpr, rest: GToken<TermExpr>[]) => GExpr): GExpr => {
    const [t, ...rest] = toks as [GToken<TermExpr>, ...GToken<TermExpr>[]]
    if (t === undefined) {
      throw new GTranslateError({ k: 'gsya', msg: 'Semantic Error: Missing Operand. I have tried to read stuff and there is no more stuff.' })
    }
    if (t.k === 'term') {
      const expr = trExpr(t.term, ctx)
      return fn(expr, rest)
    }
    if (t.info.fix === 'infix') {
      const operator = trExpr(t.term, ctx)
      const makeApp = (left: GExpr, right: GExpr): GExpr => {
        if (operator.k === 'op' && operator.name === '@') return { k: 'app', l: left, r: right }
        return { k: 'infix', l: left, op: operator, r: right }
      }
      return read(rest, (right, rest2) => read(rest2, (left, rest3) => fn(makeApp(left, right), rest3)))
    }
    // prefix or postfix: single operand
    const operator = trExpr(t.term, ctx)
    return read(rest, (operand, rest2) => fn({ k: 'app', l: operator, r: operand }, rest2))
  }
  return read(tokens, (expr) => expr)
}

function buildPatTree(tokens: GToken<TermPat>[], ctx: TrCtx): GPat {
  const read = (toks: GToken<TermPat>[], fn: (p: GPat, rest: GToken<TermPat>[]) => GPat): GPat => {
    const [t, ...rest] = toks as [GToken<TermPat>, ...GToken<TermPat>[]]
    if (t === undefined) {
      throw new GTranslateError({ k: 'gsya', msg: 'Semantic Error: Missing Operand. I have tried to read stuff and there is no more stuff.' })
    }
    if (t.k === 'term') {
      const pat = trPat(t.term, ctx)
      return fn(pat, rest)
    }
    if (t.info.fix === 'infix') {
      const operator = trPat(t.term, ctx)
      let name: string
      if (operator.k === 'con' && operator.pats.length === 0) name = operator.name
      else throw new GTranslateError({ k: 'internal', msg: 'operator was translated wrong for some reason' })
      return read(rest, (right, rest2) => read(rest2, (left, rest3) => fn({ k: 'con', name, pats: [left, right] }, rest3)))
    }
    throw new GTranslateError({ k: 'illegal', msg: 'it seems tha pattern contains something illegal - like PRE/POST-fix constructors or something' })
  }
  return read(tokens, (pat) => pat)
}

function trLit(lit: GLit): GLit {
  return lit
}

export function trExpr(e: TermExpr, ctx: TrCtx): GExpr {
  switch (e.k) {
    case 'id':
      return e.id.k === 'var' ? { k: 'var', name: e.id.name } : { k: 'con', name: e.id.name }
    case 'op':
      return { k: 'op', name: e.id.k === 'var' ? e.id.name : e.id.name }
    case 'lit':
      return { k: 'lit', lit: e.lit }
    case 'abs': {
      // fold multi-pattern abstractions; single patterns stay direct
      if (e.pat.k === 'app') {
        let acc = trExpr(e.body, ctx)
        for (let i = e.pat.pats.length - 1; i >= 0; i--) {
          acc = { k: 'abs', pat: trPat(e.pat.pats[i]!, ctx), body: acc }
        }
        return acc
      }
      return { k: 'abs', pat: trPat(e.pat, ctx), body: trExpr(e.body, ctx) }
    }
    case 'app': {
      if (e.exprs.length === 2) {
        const [l, r] = e.exprs as [TermExpr, TermExpr]
        return { k: 'app', l: trExpr(l, ctx), r: trExpr(r, ctx) }
      }
      const toks0 = e.exprs.map((t) => gsyaToTokenExpr(t, ctx.env.fixities))
      // leading infix operator is a value, not a section (mirrors operand'head)
      const headed: GToken<TermExpr>[] = (toks0.length > 0 && toks0[0]!.k === 'op' && (toks0[0] as { info: GOpInfo }).info.fix === 'infix')
        ? [{ k: 'term', term: (toks0[0] as { term: TermExpr }).term }, ...toks0.slice(1)]
        : toks0
      const explicit = makeAppExplicitExpr(headed)
      const toks = disambiguateMinusExpr(explicit)
      const inPostfix = gsyaProcessExpr(toks)
      return buildExprTree(inPostfix, ctx)
    }
    case 'tuple':
      return { k: 'tuple', exprs: e.exprs.map((x) => trExpr(x, ctx)) }
    case 'list': {
      // Mirrors upstream: desugar to e1 : (e2 : (... : [])) as right-nested
      // Infix'App chain (":" is infixr 5 by default). We build GExpr 'infix'
      // nodes directly.
      let acc: GExpr = { k: 'con', name: '[]' }
      for (let i = e.exprs.length - 1; i >= 0; i--) {
        acc = { k: 'infix', l: trExpr(e.exprs[i]!, ctx), op: { k: 'con', name: ':' }, r: acc }
      }
      return acc
    }
    case 'arith':
      throw new GTranslateError({ k: 'internal', msg: "Not implemented: Arithmetic Sequences --> AST" })
    case 'if':
      return { k: 'if', c: trExpr(e.cond, ctx), t: trExpr(e.then, ctx), e: trExpr(e.els, ctx) }
    case 'let':
      return { k: 'let', decls: e.decls.flatMap((d) => trDecl(d, ctx)), body: trExpr(e.body, ctx) }
    case 'ann': {
      return trExprAnn(e.expr, e.preds, e.ty, ctx)
    }
    case 'case':
      return {
        k: 'case', expr: trExpr(e.expr, ctx),
        alts: e.alts.map(([p, b]) => ({ pats: [trPat(p, ctx)], rhs: trExpr(b, ctx) }) as GMatch),
      }
    case 'lcon': {
      const info = ctx.env.constructors.get(e.name)
      if (info === undefined) ctx.err({ k: 'notInScopeData', name: e.name })
      if (info.k !== 'record') {
        if (e.fields.length === 0) return { k: 'con', name: e.name }
        ctx.err({ k: 'wrongFields', name: e.name, fields: e.fields.map(([n]) => n) })
      }
      const fields = (info as { k: 'record'; name: string; fields: string[] }).fields
      const wrong = e.fields.map(([n]) => n).filter((n) => !fields.includes(n))
      if (wrong.length > 0) ctx.err({ k: 'wrongFields', name: e.name, fields: wrong })
      const have = new Set(e.fields.map(([n]) => n))
      const uninit = fields.filter((f) => !have.has(f))
      if (uninit.length > 0) ctx.err({ k: 'uninitFields', name: e.name, fields: uninit })
      const byName = new Map(e.fields)
      let acc: GExpr = { k: 'con', name: e.name }
      for (const f of fields) acc = { k: 'app', l: acc, r: trExpr(byName.get(f)!, ctx) }
      return acc
    }
    case 'lupd': {
      if (e.fields.length === 0) ctx.err({ k: 'emptyRecordUpdate' })
      // Desugar (mirrors look'for'constr + Case): find the record constructor
      // containing the first updated field, then case-split with fresh vars.
      const first = e.fields[0]![0]
      const finfo = ctx.env.constructors.get(ctx.env.fields.get(first) ?? '')
      if (finfo === undefined) ctx.err({ k: 'notInScopeField', name: first })
      if (finfo.k !== 'record') {
        throw new GTranslateError({ k: 'internal', msg: 'Unexpected behaviour: the lookup for the constructor with a specific field returned an ordinary constructor without fields.' })
      }
      const rec = finfo as { k: 'record'; name: string; fields: string[] }
      for (const [fn] of e.fields) {
        if (ctx.env.fields.get(fn) === undefined) ctx.err({ k: 'notInScopeField', name: fn })
      }
      const noCtor = e.fields.map(([n]) => n).filter((n) => !rec.fields.includes(n))
      if (noCtor.length > 0) ctx.err({ k: 'noCtorHasFields', fields: e.fields.map(([n]) => n) })
      const scr = trExpr(e.expr, ctx)
      const pat: GPat = { k: 'con', name: rec.name, pats: rec.fields.map((f) => ({ k: 'var', name: `__upd_${f}` }) as GPat) }
      const byUpd = new Map(e.fields)
      const rhsArgs: GExpr[] = rec.fields.map((f) => {
        const upd = byUpd.get(f)
        if (upd !== undefined) return trExpr(upd, ctx)
        return { k: 'var', name: `__upd_${f}` } as GExpr
      })
      let rhs: GExpr = { k: 'con', name: rec.name }
      for (const a of rhsArgs) rhs = { k: 'app', l: rhs, r: a }
      // Bind pattern vars via nested abs over a lambda applied to scrutinee?
      // Upstream builds Case [Match [P'Con vars] rhs]; our GExpr 'case' holds.
      return { k: 'case', expr: scr, alts: [{ pats: [pat], rhs }] }
    }
    case 'hole':
      return { k: 'hole', name: e.name }
  }
}

export function trPat(p: TermPat, ctx: TrCtx): GPat {
  switch (p.k) {
    case 'id':
      return p.id.k === 'var' ? { k: 'var', name: p.id.name } : { k: 'con', name: p.id.name, pats: [] }
    case 'op':
      return p.id.k === 'var' ? { k: 'var', name: p.id.name } : { k: 'con', name: p.id.name, pats: [] }
    case 'lit':
      return { k: 'lit', lit: p.lit }
    case 'app': {
      const [head, ...args] = p.pats as [TermPat, ...TermPat[]]
      // infix constructor in head position: [left, Op con, ...rest]
      if (head !== undefined && args.length >= 1
        && args[0]!.k === 'op' && (args[0] as unknown as { id: TermId }).id.k === 'con') {
        const oname = ((args[0] as unknown as { id: TermId }).id as { name: string }).name
        return { k: 'con', name: oname, pats: [trPat(head, ctx), ...args.slice(1).map((a) => trPat(a, ctx))] }
      }
      // constructor-headed application
      if (head !== undefined && head.k === 'id' && head.id.k === 'con') {
        return { k: 'con', name: head.id.name, pats: args.map((a) => trPat(a, ctx)) }
      }
      if (head !== undefined && head.k === 'op' && head.id.k === 'con') {
        return { k: 'con', name: head.id.name, pats: args.map((a) => trPat(a, ctx)) }
      }
      // general application: resolve fixity via GSYA
      const toks = disambiguateMinusPat(
        p.pats.map((t) => gsyaToTokenPat(t, ctx.env.fixities)))
      const inPostfix = gsyaProcessPat(toks)
      return buildPatTree(inPostfix, ctx)
    }
    case 'con':
      return { k: 'con', name: p.name, pats: p.pats.map((a) => trPat(a, ctx)) }
    case 'tuple':
      return { k: 'con', name: '(' + ','.repeat(Math.max(0, p.pats.length - 1)) + ')', pats: p.pats.map((a) => trPat(a, ctx)) }
    case 'list': {
      // Mirrors upstream: `error "Not implemented: List Patter Term --> AST"`.
      // We surface it as an internal translation error so the REPL prints it
      // instead of crashing.
      throw new GTranslateError({ k: 'internal', msg: 'Not implemented: List Patter Term --> AST' })
    }
    case 'as':
      return { k: 'as', name: p.name, pat: trPat(p.pat, ctx) }
    case 'wild':
      return { k: 'wild' }
    case 'ann': {
      return trPatAnn(p.pat, p.preds, p.ty, ctx)
    }
    case 'labeled': {
      const info = ctx.env.constructors.get(p.con)
      if (info === undefined) ctx.err({ k: 'notInScopeData', name: p.con })
      if (info.k !== 'record') {
        // Positional constructor used with record syntax: `Constr {}` is
        // allowed (all wildcards); otherwise Wrong'Fields.
        if (p.fields.length === 0) {
          const arity = (info as { k: 'con'; name: string; arity: number }).arity
          return { k: 'con', name: p.con, pats: new Array(arity).fill({ k: 'wild' }) as GPat[] }
        }
        ctx.err({ k: 'wrongFields', name: p.con, fields: p.fields.map(([n]) => n) })
      }
      const fields = (info as { k: 'record'; name: string; fields: string[] }).fields
      const wrong = p.fields.map(([n]) => n).filter((n) => !fields.includes(n))
      if (wrong.length > 0) ctx.err({ k: 'wrongFields', name: p.con, fields: wrong })
      // Missing fields become wildcards (no Uninitialized check for patterns).
      const byName = new Map(p.fields)
      return {
        k: 'con', name: p.con,
        pats: fields.map((f) => {
          const fp = byName.get(f)
          if (fp === undefined) return { k: 'wild' } as GPat
          return trPat(fp, ctx)
        }),
      }
    }
  }
}
// Recursive-descent parser for the Term grammar.

export function toPredicates(t: TermType): TermPred[] {
  if (t.k === 'unit') return []
  if (t.k === 'tuple') return t.tys.flatMap(toPredicates)
  if (t.k === 'app' && t.tys.length >= 2) {
    const [h, ...rest] = t.tys as [TermType, ...TermType[]]
    if (h.k === 'id' && h.id.k === 'con') {
      if (rest.length === 1 && rest[0]!.k === 'id' && (rest[0] as { id: TermId }).id.k === 'var') {
        return [{ k: 'is', cls: h.id.name, ty: rest[0]! }]
      }
      const tt = rest[0]!
      if (tt.k === 'app' && tt.tys.length >= 2) {
        const [hh, ...rr] = tt.tys as [TermType, ...TermType[]]
        if (hh.k === 'id' && hh.id.k === 'var' && rr.length >= 1) {
          return [{ k: 'is', cls: h.id.name, ty: tt }]
        }
      }
    }
  }
  throw new GParseError(-1, -1, 'type context is not in the correct shape')
}

class GParser extends P {
  // ---- types ----
  parseQualType(): { preds: TermPred[]; ty: TermType } {
    const t = this.parseType()
    if (this.peek().k === 'fatArrow') {
      this.next()
      const body = this.parseType()
      return { preds: toPredicates(t), ty: body }
    }
    return { preds: [], ty: t }
  }
  parseType(): TermType {
    const b = this.parseBType()
    const arrs: TermType[] = []
    while (this.peek().k === 'arrow') {
      this.next()
      arrs.push(this.parseType())
    }
    if (arrs.length === 0) return b
    // right-nested: a -> b -> c = Arrow[a, Arrow[b, c]]
    let acc = arrs[arrs.length - 1]!
    for (let i = arrs.length - 2; i >= 0; i--) acc = { k: 'arrow', tys: [arrs[i]!, acc] }
    return { k: 'arrow', tys: [b, acc] }
  }
  parseBType(): TermType {
    const parts: TermType[] = [this.parseAType()]
    for (;;) {
      const t = this.peek()
      if (t.k === 'var' || t.k === 'con' || t.k === 'lparen' || t.k === 'lbrack' || t.k === 'forall') {
        parts.push(this.parseAType())
      } else break
    }
    if (parts.length === 1) return parts[0]!
    const [first, ...rest] = parts as [TermType, ...TermType[]]
    if (first.k === 'app') return { k: 'app', tys: [...first.tys, ...rest] }
    return { k: 'app', tys: parts }
  }
  parseAType(): TermType {
    const t = this.peek()
    if (t.k === 'con') {
      this.next()
      return { k: 'id', id: { k: 'con', name: (t as { name: string }).name } }
    }
    if (t.k === 'var') {
      this.next()
      return { k: 'id', id: { k: 'var', name: (t as { name: string }).name } }
    }
    if (t.k === 'lparen') {
      this.next()
      const t2 = this.peek()
      if (t2.k === 'rparen') {
        this.next()
        return { k: 'unit' }
      }
      if (t2.k === 'arrow') {
        this.next()
        this.expect('rparen')
        return { k: 'id', id: { k: 'con', name: '(->)' } }
      }
      if (t2.k === 'comma') {
        // only (,) is valid in types; (,,) etc. are an error upstream
        this.next()
        if (this.peek().k === 'rparen') {
          this.next()
          return { k: 'id', id: { k: 'con', name: '(,)' } }
        }
        this.err(this.peek(), 'tuple constructor')
      }
      if (t2.k === 'forall') {
        const f = this.parseForallType()
        this.expect('rparen')
        return f
      }
      const inner = this.parseType()
      const t3 = this.peek()
      if (t3.k === 'comma') {
        const rest: TermType[] = [inner]
        while (this.peek().k === 'comma') {
          this.next()
          rest.push(this.parseType())
        }
        this.expect('rparen')
        return { k: 'tuple', tys: rest }
      }
      this.expect('rparen')
      return inner
    }
    if (t.k === 'lbrack') {
      this.next()
      if (this.peek().k === 'rbrack') {
        this.next()
        return { k: 'id', id: { k: 'con', name: '[]' } }
      }
      const inner = this.parseType()
      this.expect('rbrack')
      return { k: 'list', ty: inner }
    }
    if (t.k === 'forall') return this.parseForallType()
    this.err(t, 'expected type')
  }
  parseForallType(): TermType {
    this.expect('forall')
    const vars: TermId[] = []
    for (;;) {
      const t = this.peek()
      if (t.k !== 'var') break
      vars.push({ k: 'var', name: (t as { name: string }).name })
      this.next()
    }
    const dot = this.next()
    if (dot.k !== 'dotD') this.err(dot, "expected '.'")
    const q = this.parseQualType()
    return { k: 'forall', vars, preds: q.preds, ty: q.ty }
  }
  parsePredicate(): TermPred {
    const c = this.identCon()
    const t = this.peek()
    if (t.k === 'var') {
      this.next()
      return { k: 'is', cls: c, ty: { k: 'id', id: { k: 'var', name: (t as { name: string }).name } } }
    }
    if (t.k === 'lparen') {
      this.next()
      const ty = this.parseType()
      this.expect('rparen')
      return { k: 'is', cls: c, ty }
    }
    this.err(t, 'expected predicate')
  }

  // ---- patterns ----
  parsePattern(): TermPat {
    const parts: TermPat[] = [this.parseBPat()]
    for (;;) {
      const t = this.peek()
      if (t.k === 'var' || t.k === 'con' || t.k === 'op' || t.k === 'opcon'
        || t.k === 'lparen' || t.k === 'lbrack' || t.k === 'int' || t.k === 'double'
        || t.k === 'char' || t.k === 'string' || t.k === 'hole' || t.k === 'backtick') {
        parts.push(this.parseBPat())
      } else break
    }
    if (parts.length === 1) return parts[0]!
    return { k: 'app', pats: parts }
  }
  parseBPat(): TermPat {
    const t = this.peek()
    if (t.k === 'con') {
      this.next()
      const name = (t as { name: string }).name
      if (this.peek().k === 'lbrace') {
        this.next()
        const fields = this.parseSepList('rbrace', 'comma', () => {
          const n = this.identVar()
          this.expectOp('=')
          const p = this.parsePattern()
          return [n, p] as [string, TermPat]
        })
        return { k: 'labeled', con: name, fields }
      }
      return { k: 'id', id: { k: 'con', name } }
    }
    if (t.k === 'backtick') {
      this.next()
      const c = this.identCon()
      this.expect('backtick')
      return { k: 'op', id: { k: 'con', name: c } }
    }
    if (t.k === 'opcon') {
      this.next()
      return { k: 'op', id: { k: 'con', name: (t as { name: string }).name } }
    }
    if (t.k === 'lparen') {
      this.next()
      const t2 = this.peek()
      // LowIdent: '(' Op ')' where Op = op | dot (operators only, not opcon)
      if ((t2.k === 'op' || t2.k === 'dotD') && this.toks[this.pos + 1]?.k === 'rparen') {
        this.next()
        this.next()
        return { k: 'id', id: { k: 'var', name: t2.k === 'dotD' ? '.' : (t2 as { name: string }).name } }
      }
      if (t2.k === 'opcon' && this.toks[this.pos + 1]?.k === 'rparen') {
        this.next()
        this.next()
        return { k: 'id', id: { k: 'con', name: (t2 as { name: string }).name } }
      }
      if (t2.k === 'rparen') {
        this.next()
        return { k: 'id', id: { k: 'con', name: '()' } }
      }
      if (t2.k === 'comma') {
        this.next()
        if (this.peek().k === 'rparen') {
          this.next()
          return { k: 'id', id: { k: 'con', name: '(,)' } }
        }
        this.err(this.peek(), 'tuple constructor pattern')
      }
      const p = this.parsePattern()
      const t3 = this.peek()
      if (t3.k === 'comma') {
        const rest: TermPat[] = [p]
        while (this.peek().k === 'comma') {
          this.next()
          rest.push(this.parsePattern())
        }
        this.expect('rparen')
        return { k: 'tuple', pats: rest }
      }
      if (t3.k === 'hastype') {
        this.next()
        const q = this.parseQualType()
        this.expect('rparen')
        return { k: 'ann', pat: p, preds: q.preds, ty: q.ty }
      }
      this.expect('rparen')
      return p
    }
    return this.parseAPat()
  }
  parseAPat(): TermPat {
    const t = this.peek()
    // LowIdent ['@' BPat]
    if (t.k === 'var' || (t.k === 'lparen' && this.isParenOpAhead())) {
      const name = this.parseLowIdent()
      if (this.peek().k === 'atD') {
        this.next()
        return { k: 'as', name, pat: this.parseBPat() }
      }
      return { k: 'id', id: { k: 'var', name } }
    }
    if (t.k === 'lbrack') {
      this.next()
      if (this.peek().k === 'rbrack') {
        this.next()
        return { k: 'id', id: { k: 'con', name: '[]' } }
      }
      const first = this.parsePattern()
      const rest: TermPat[] = [first]
      while (this.peek().k === 'comma') {
        this.next()
        rest.push(this.parsePattern())
      }
      this.expect('rbrack')
      return { k: 'list', pats: rest }
    }
    if (t.k === 'hole') {
      this.next()
      return { k: 'wild' }
    }
    if (t.k === 'con') {
      this.next()
      const name = (t as { name: string }).name
      if (this.peek().k === 'lbrace') {
        this.next()
        const fields = this.parseSepList('rbrace', 'comma', () => {
          const n = this.identVar()
          this.expectOp('=')
          const p = this.parsePattern()
          return [n, p] as [string, TermPat]
        })
        return { k: 'labeled', con: name, fields }
      }
      return { k: 'id', id: { k: 'con', name } }
    }
    if (t.k === 'int') {
      this.next()
      return { k: 'lit', lit: { k: 'int', v: (t as { value: number }).value } }
    }
    if (t.k === 'double') {
      this.next()
      return { k: 'lit', lit: { k: 'double', v: (t as { value: number }).value } }
    }
    if (t.k === 'char') {
      this.next()
      return { k: 'lit', lit: { k: 'char', v: (t as { value: string }).value } }
    }
    if (t.k === 'string') {
      this.next()
      const s = (t as { value: string }).value
      return { k: 'list', pats: [...s].map((ch) => ({ k: 'lit', lit: { k: 'char', v: ch } }) as TermPat) }
    }
    this.err(t, 'expected pattern')
  }
  isParenOpAhead(): boolean {
    // '(' Op ')' where Op = op | dot (generic operator, for LowIdent)
    const t1 = this.toks[this.pos + 1]
    const t2 = this.toks[this.pos + 2]
    if (!t1 || !t2) return false
    const isOp = t1.k === 'op' || t1.k === 'dotD'
    return isOp && t2.k === 'rparen'
  }
  parseLowIdent(): string {
    const t = this.peek()
    if (t.k === 'var') {
      this.next()
      return (t as { name: string }).name
    }
    if (t.k === 'lparen') {
      this.next()
      const o = this.next()
      if (o.k !== 'op' && o.k !== 'dotD') this.err(o, 'expected operator')
      this.expect('rparen')
      return o.k === 'dotD' ? '.' : (o as { name: string }).name
    }
    this.err(t, 'expected identifier')
  }

  // ---- declarations ----
  parseModuleDecls(): TermDecl[] {
    const t = this.peek()
    if (t.k === 'module') {
      this.next()
      this.identCon()
      this.expect('where')
    }
    return this.parseLayout(() => this.parseDeclaration()).flat()
  }
  parseDeclaration(): TermDecl[] {
    const t = this.peek()
    if (t.k === 'data') return [this.parseData()]
    if (t.k === 'type') return [this.parseTypeSynonym()]
    if (t.k === 'infixl' || t.k === 'infixr' || t.k === 'infix'
      || t.k === 'prefixl' || t.k === 'prefixr' || t.k === 'prefix'
      || t.k === 'postfixl' || t.k === 'postfixr' || t.k === 'postfix') {
      return this.parseFixitySigns()
    }
    if (t.k === 'class') return [this.parseClassDecl()]
    if (t.k === 'instance') return [this.parseInstanceDecl()]
    // Binding vs TypeSigns: LowIdent (',' LowIdent)* '::' → signature
    if (t.k === 'var' || (t.k === 'lparen' && this.isParenOpAhead())) {
      const save = this.pos
      try {
        const names: string[] = [this.parseLowIdent()]
        while (this.peek().k === 'comma') {
          this.next()
          names.push(this.parseLowIdent())
        }
        if (this.peek().k === 'hastype') {
          this.next()
          const q = this.parseQualType()
          return names.map((n) => ({ k: 'sig', name: n, preds: q.preds, ty: q.ty }) as TermDecl)
        }
      } catch (e) {
        if (!(e instanceof GParseError)) throw e
        // fall through to Binding
      }
      this.pos = save
    }
    return [this.parseBinding()]
  }
  parseBinding(): TermDecl {
    const pat = this.parsePattern()
    this.expectOp('=')
    return { k: 'binding', pat, expr: this.parseExpression() }
  }
  parseData(): TermDecl {
    this.expect('data')
    let name: string
    const t = this.peek()
    if (t.k === 'con') {
      this.next()
      name = (t as { name: string }).name
    } else if (t.k === 'lparen') {
      this.next()
      const o = this.next()
      if (o.k !== 'opcon') this.err(o, 'expected constructor operator')
      name = (o as { name: string }).name
      this.expect('rparen')
    } else this.err(t, 'expected data type name')
    const params: string[] = []
    while (this.peek().k === 'var') {
      params.push((this.next() as { name: string }).name)
    }
    const ctors: TermConstrDecl[] = []
    if (this.peek().k === 'eqD') {
      this.next()
      ctors.push(this.parseConstr())
      while (this.peek().k === 'pipeD') {
        this.next()
        ctors.push(this.parseConstr())
      }
    }
    return { k: 'data', name: name!, params, ctors }
  }
  parseConstr(): TermConstrDecl {
    const t = this.peek()
    let name: string
    if (t.k === 'con') {
      this.next()
      name = (t as { name: string }).name
    } else if (t.k === 'lparen') {
      this.next()
      const o = this.next()
      if (o.k === 'opcon') {
        name = (o as { name: string }).name
      } else if (o.k === 'rparen') {
        return { k: 'con', name: '()', tys: [] }
      } else if (o.k === 'lbrack') {
        this.expect('rbrack')
        this.expect('rparen')
        return { k: 'con', name: '[]', tys: [] }
      } else this.err(o, 'expected constructor')
      this.expect('rparen')
    } else if (t.k === 'lbrack') {
      this.next()
      this.expect('rbrack')
      return { k: 'con', name: '[]', tys: [] }
    } else this.err(t, 'expected constructor')
    // record?
    if (this.peek().k === 'lbrace') {
      this.next()
      const fields = this.parseSepList('rbrace', 'comma', () => {
        const n = this.identVar()
        this.expect('hastype')
        const ty = this.parseType()
        return [n, ty] as [string, TermType]
      })
      return { k: 'record', name: name!, fields }
    }
    // prefix args (head type is the constructor as a type constant)
    const head: TermType = { k: 'id', id: { k: 'con', name: name! } }
    const args: TermType[] = [head]
    for (;;) {
      const a = this.peek()
      if (a.k === 'var' || a.k === 'con' || a.k === 'lparen' || a.k === 'lbrack' || a.k === 'forall') {
        args.push(this.parseAType())
      } else break
    }
    // infix constructor?
    const n = this.peek()
    let infixOp: string | null = null
    if (n.k === 'opcon') {
      infixOp = (n as { name: string }).name
      this.next()
    } else if (n.k === 'backtick') {
      this.next()
      infixOp = this.identCon()
      this.expect('backtick')
    }
    if (infixOp !== null) {
      const rhs = this.parseBType()
      const left: TermType = args.length === 1 ? args[0]! : { k: 'app', tys: args }
      return { k: 'con', name: infixOp, tys: [left, rhs] }
    }
    if (args.length === 1) return { k: 'con', name: name!, tys: [] }
    return { k: 'con', name: name!, tys: args.slice(1) }
  }
  parseTypeSynonym(): TermDecl {
    this.expect('type')
    const name = this.identCon()
    const params: string[] = []
    while (this.peek().k === 'var') {
      params.push((this.next() as { name: string }).name)
    }
    this.expectOp('=')
    return { k: 'alias', name, params, ty: this.parseType() }
  }
  parseFixitySigns(): TermDecl[] {
    const t = this.next()
    const fix: Fixity = t.k === 'prefix' || t.k === 'prefixl' || t.k === 'prefixr' ? 'prefix'
      : t.k === 'postfix' || t.k === 'postfixl' || t.k === 'postfixr' ? 'postfix' : 'infix'
    const assoc: Assoc = t.k === 'infixl' || t.k === 'prefixl' || t.k === 'postfixl' ? 'left'
      : t.k === 'infixr' || t.k === 'prefixr' || t.k === 'postfixr' ? 'right' : 'none'
    const prec = this.integer()
    const ops: string[] = [this.parseOpInfixName()]
    while (this.peek().k === 'comma') {
      this.next()
      ops.push(this.parseOpInfixName())
    }
    return ops.map((op) => ({ k: 'fixity', fix, assoc, prec, ops: [op] }) as TermDecl)
  }
  parseOpInfixName(): string {
    const t = this.peek()
    if (t.k === 'op' || t.k === 'dotD') {
      this.next()
      return t.k === 'op' ? (t as { name: string }).name : '.'
    }
    if (t.k === 'opcon') {
      this.next()
      return (t as { name: string }).name
    }
    if (t.k === 'backtick') {
      this.next()
      const n = this.next()
      if (n.k !== 'var' && n.k !== 'con') this.err(n, 'expected operator name')
      this.expect('backtick')
      return (n as { name: string }).name
    }
    if (t.k === 'lparen') {
      this.next()
      const o = this.next()
      if (o.k !== 'op' && o.k !== 'opcon' && o.k !== 'dotD') this.err(o, 'expected operator')
      const name = o.k === 'dotD' ? '.' : (o as { name: string }).name
      this.expect('rparen')
      return name
    }
    this.err(t, 'expected operator')
  }
  parseSimpleClass(): TermPred {
    const c = this.identCon()
    const ty = this.parseType()
    return { k: 'is', cls: c, ty }
  }
  parseClassDecl(): TermDecl {
    this.expect('class')
    // ClassDecl2: conid varid '=>' conid varid | conid varid | '(' ... ')' '=>' conid varid
    let supers: TermPred[] = []
    let name: string
    let param: string
    if (this.peek().k === 'lparen') {
      this.next()
      if (this.peek().k !== 'rparen') {
        supers = [this.parseSimpleClass()]
        while (this.peek().k === 'comma') {
          this.next()
          supers.push(this.parseSimpleClass())
        }
      }
      this.expect('rparen')
      this.expect('fatArrow')
      name = this.identCon()
      param = this.identVar()
    } else {
      const c1 = this.identCon()
      const v1 = this.identVar()
      if (this.peek().k === 'fatArrow') {
        this.next()
        name = this.identCon()
        param = this.identVar()
        supers = [{ k: 'is', cls: c1, ty: { k: 'id', id: { k: 'var', name: v1 } } }]
      } else {
        name = c1
        param = v1
      }
    }
    let decls: TermDecl[] = []
    if (this.peek().k === 'where') {
      this.next()
      decls = this.parseLayout(() => this.parseTypeSigns()).flat()
    }
    return { k: 'class', name, param, supers, decls }
  }
  parseInstanceDecl(): TermDecl {
    this.expect('instance')
    let ctx: TermPred[] = []
    let head: TermPred
    if (this.peek().k === 'lparen') {
      this.next()
      ctx = [this.parseSimpleClass()]
      while (this.peek().k === 'comma') {
        this.next()
        ctx.push(this.parseSimpleClass())
      }
      this.expect('rparen')
      this.expectOp('=>')
      const c = this.identCon()
      const ty = this.parseType()
      head = { k: 'is', cls: c, ty }
    } else {
      const c = this.identCon()
      const nx = this.peek()
      const nx2 = this.toks[this.pos + 1]
      if (nx.k === 'var' && nx2 !== undefined && nx2.k === 'fatArrow') {
        const v = (nx as { name: string }).name
        this.next()
        this.next() // =>
        const c2 = this.identCon()
        const ty = this.parseType()
        ctx = [{ k: 'is', cls: c, ty: { k: 'id', id: { k: 'var', name: v } } }]
        head = { k: 'is', cls: c2, ty }
      } else {
        const ty = this.parseType()
        head = { k: 'is', cls: c, ty }
      }
    }
    let decls: TermDecl[] = []
    if (this.peek().k === 'where') {
      this.next()
      decls = this.parseLayout(() => [this.parseBinding()]).flat()
    }
    return { k: 'instance', ctx, head, decls }
  }
  parseTypeSign(): TermDecl {
    const all = this.parseTypeSigns()
    if (all.length !== 1) this.err(this.peek(), 'expected single signature')
    return all[0]!
  }  parseTypeSigns(): TermDecl[] {
    const names: string[] = [this.parseLowIdent()]
    while (this.peek().k === 'comma') {
      this.next()
      names.push(this.parseLowIdent())
    }
    this.expect('hastype')
    const q = this.parseQualType()
    return names.map((n) => ({ k: 'sig', name: n, preds: q.preds, ty: q.ty }) as TermDecl)
  }
  expectOp(name: string): void {
    // dedicated terminals (Happy %token order: exact match shadows generic op)
    const dedicated: Record<string, GTok['k']> = {
      '->': 'arrow', '=>': 'fatArrow', '=': 'eqD', '|': 'pipeD',
      '..': 'dotdot', '@': 'atD', '.': 'dotD',
    }
    const t = this.next()
    const want = dedicated[name]
    if (want !== undefined) {
      if (t.k !== want) this.err(t, `expected operator ${name}`)
      return
    }
    if (t.k !== 'op' || (t as { name: string }).name !== name) this.err(t, `expected operator ${name}`)
  }
  isOp(t: GTok, name: string): boolean {
    if (t.k === 'op' && (t as { name: string }).name === name) return true
    const dedicated: Record<string, GTok['k']> = {
      '->': 'arrow', '=>': 'fatArrow', '=': 'eqD', '|': 'pipeD',
      '..': 'dotdot', '@': 'atD', '.': 'dotD',
    }
    return t.k === dedicated[name]
  }
  parseSepList<T>(close: GTok['k'], sep: GTok['k'], fn: () => T): T[] {
    // no trailing separator allowed (matches OneOrManySeparated)
    const out: T[] = []
    if (this.peek().k === close) {
      this.next()
      return out
    }
    out.push(fn())
    while (this.peek().k === sep) {
      this.next()
      out.push(fn())
    }
    this.expect(close)
    return out
  }
  parseLayout<T>(fn: () => T): T[] {
    this.expect('lbrace')
    const out: T[] = [fn()]
    for (;;) {
      const t = this.peek()
      if (t.k === 'rbrace') {
        this.next()
        return out
      }
      this.expect('semi')
      out.push(fn())
    }
  }

  // ---- expressions ----
  parseExpression(): TermExpr {
    const e = this.parseExp10()
    if (this.peek().k === 'hastype') {
      this.next()
      const q = this.parseQualType()
      return { k: 'ann', expr: e, preds: q.preds, ty: q.ty }
    }
    return e
  }
  parseExp10(): TermExpr {
    const parts: TermExpr[] = [this.parseBExp()]
    for (;;) {
      if (!this.startsBExp()) break
      parts.push(this.parseBExp())
    }
    if (parts.length === 1) return parts[0]!
    return { k: 'app', exprs: parts }
  }
  startsBExp(): boolean {
    const t = this.peek()
    if (t.k === 'op' || t.k === 'dotD' || t.k === 'opcon' || t.k === 'backtick') return true
    return this.startsAExp()
  }
  startsAExp(): boolean {
    const t = this.peek()
    return t.k === 'var' || t.k === 'con' || t.k === 'int' || t.k === 'double'
      || t.k === 'char' || t.k === 'string' || t.k === 'lparen' || t.k === 'lbrack'
      || t.k === 'lambda' || t.k === 'let' || t.k === 'if' || t.k === 'case'
      || t.k === 'hole'
  }
  parseBExp(): TermExpr {
    const t = this.peek()
    if (t.k === 'op' || t.k === 'dotD') {
      this.next()
      const name = t.k === 'op' ? (t as { name: string }).name : '.'
      return { k: 'op', id: { k: 'var', name } }
    }
    if (t.k === 'opcon') {
      this.next()
      return { k: 'op', id: { k: 'con', name: (t as { name: string }).name } }
    }
    if (t.k === 'backtick') {
      this.next()
      const n = this.next()
      if (n.k !== 'var' && n.k !== 'con') this.err(n, 'expected operator name')
      this.expect('backtick')
      return { k: 'op', id: n.k === 'var'
        ? { k: 'var', name: (n as { name: string }).name }
        : { k: 'con', name: (n as { name: string }).name } }
    }
    return this.parseAExp()
  }
  parseAExp(): TermExpr {
    let head = this.parseAExpHead()
    for (;;) {
      if (this.peek().k !== 'lbrace') return head
      this.next()
      const fields = this.parseSepList('rbrace', 'comma', () => {
        const n = this.identVar()
        this.expectOp('=')
        const e = this.parseExpression()
        return [n, e] as [string, TermExpr]
      })
      if (head.k === 'id' && head.id.k === 'con') {
        head = { k: 'lcon', name: head.id.name, fields }
      } else {
        head = { k: 'lupd', expr: head, fields }
      }
    }
  }
  parseAExpHead(): TermExpr {
    const t = this.peek()
    if (t.k === 'var') {
      this.next()
      return { k: 'id', id: { k: 'var', name: (t as { name: string }).name } }
    }
    if (t.k === 'con') {
      this.next()
      return { k: 'id', id: { k: 'con', name: (t as { name: string }).name } }
    }
    if (t.k === 'int') {
      this.next()
      return { k: 'lit', lit: { k: 'int', v: (t as { value: number }).value } }
    }
    if (t.k === 'double') {
      this.next()
      return { k: 'lit', lit: { k: 'double', v: (t as { value: number }).value } }
    }
    if (t.k === 'char') {
      this.next()
      return { k: 'lit', lit: { k: 'char', v: (t as { value: string }).value } }
    }
    if (t.k === 'string') {
      this.next()
      const s = (t as { value: string }).value
      return { k: 'list', exprs: [...s].map((ch) => ({ k: 'lit', lit: { k: 'char', v: ch } }) as TermExpr) }
    }
    if (t.k === 'hole') {
      this.next()
      return { k: 'hole', name: (t as { name: string }).name }
    }
    if (t.k === 'lparen') {
      this.next()
      const t2 = this.peek()
      if (t2.k === 'rparen') {
        this.next()
        return { k: 'id', id: { k: 'con', name: '()' } }
      }
      if (t2.k === 'comma') {
        this.next()
        this.expect('rparen')
        return { k: 'id', id: { k: 'con', name: '(,)' } }
      }
      if ((t2.k === 'op' || t2.k === 'opcon') && this.toks[this.pos + 1]?.k === 'rparen') {
        this.next()
        this.next()
        return { k: 'op', id: t2.k === 'op'
          ? { k: 'var', name: (t2 as { name: string }).name }
          : { k: 'con', name: (t2 as { name: string }).name } }
      }
      const e = this.parseExpression()
      const t3 = this.peek()
      if (t3.k === 'comma') {
        const rest: TermExpr[] = [e]
        while (this.peek().k === 'comma') {
          this.next()
          rest.push(this.parseExpression())
        }
        this.expect('rparen')
        return { k: 'tuple', exprs: rest }
      }
      this.expect('rparen')
      return e
    }
    if (t.k === 'lbrack') {
      this.next()
      if (this.peek().k === 'rbrack') {
        this.next()
        return { k: 'list', exprs: [] }
      }
      const first = this.parseExpression()
      if (this.peek().k === 'comma') {
        this.next()
        const second = this.parseExpression()
        if (this.peek().k === 'dotdot') {
          this.next()
          const hi = this.parseExpression()
          this.expect('rbrack')
          return { k: 'arith', lo: first, step: second, hi }
        }
        const rest: TermExpr[] = [first, second]
        while (this.peek().k === 'comma') {
          this.next()
          rest.push(this.parseExpression())
        }
        this.expect('rbrack')
        return { k: 'list', exprs: rest }
      }
      if (this.peek().k === 'dotdot') {
        this.next()
        const hi = this.parseExpression()
        this.expect('rbrack')
        return { k: 'arith', lo: first, step: null, hi }
      }
      this.expect('rbrack')
      return { k: 'list', exprs: [first] }
    }
    if (t.k === 'lambda') {
      this.next()
      const pat = this.parsePattern()
      this.expectOp('->')
      return { k: 'abs', pat, body: this.parseExpression() }
    }
    if (t.k === 'let') {
      this.next()
      const decls = this.parseLayout(() => this.parseDeclaration()).flat()
      this.expect('in')
      return { k: 'let', decls, body: this.parseExpression() }
    }
    if (t.k === 'if') {
      this.next()
      const c = this.parseExpression()
      this.expect('then')
      const th = this.parseExpression()
      this.expect('else')
      return { k: 'if', cond: c, then: th, els: this.parseExpression() }
    }
    if (t.k === 'case') {
      this.next()
      const e = this.parseExpression()
      this.expect('of')
      const alts = this.parseLayout(() => {
        const p = this.parsePattern()
        this.expectOp('->')
        const b = this.parseExpression()
        return [p, b] as [TermPat, TermExpr]
      })
      return { k: 'case', expr: e, alts }
    }
    this.err(t, 'expected expression')
  }
} // end class GParser
// Layout examination: direct port of examine'token and friends
// (Compiler/Lexer/Utils.hs). Virtual '{' / ';' / '}' reuse the explicit
// token shapes; pending virtuals emit as-is, pending tokens re-examine.

function tokPos(t: GTok): GPos {
  return (t as { pos: GPos }).pos
}

function isImplicit(c: LayoutCtx): boolean {
  return c.k === 'implicit'
}

function pushCtx(st: LexState, c: LayoutCtx): void {
  st.stack = [c, ...st.stack]
}

function popCtx(st: LexState): void {
  st.stack = st.stack.slice(1)
}

function clearNewline(st: LexState): void {
  st.sawNewline = false
}

function emitTok(st: LexState, t: GTok): GTok {
  clearNewline(st)
  return t
}

function emitEof(st: LexState, eof: GTok): GTok {
  const top = st.stack[0]
  if (top !== undefined && top.k === 'implicit') {
    popCtx(st)
    return { k: 'rbrace', pos: tokPos(eof) }
  }
  st.layoutExpected = false
  st.topMarker = false
  st.done = true
  return eof
}

function closeLet(st: LexState, tok: GTok): GTok {
  const run: LayoutCtx[] = []
  let rest = st.stack
  while (rest.length > 0 && isImplicit(rest[0]!)) {
    run.push(rest[0]!)
    rest = rest.slice(1)
  }
  const r0 = rest[0]
  if (r0 !== undefined && r0.k === 'letpending') {
    const tail = rest.slice(1)
    const closes: GTok[] = run.map(() => ({ k: 'rbrace', pos: tokPos(tok) }) as GTok)
    if (closes.length === 0) {
      st.stack = tail
      return tok
    }
    const [first, ...others] = closes as [GTok, ...GTok[]]
    st.stack = tail
    st.virtuals = [...st.virtuals, ...others, tok]
    return first
  }
  return examinePlain(st, tok)
}

function examinePlain(st: LexState, tok: GTok): GTok {
  if (!st.sawNewline) return emitTok(st, tok)
  const top = st.stack[0]
  if (top !== undefined && top.k === 'implicit') {
    const c = tokPos(tok).column
    if (c === top.col) {
      st.pending = [tok, ...st.pending]
      clearNewline(st)
      return { k: 'semi', pos: tokPos(tok) }
    }
    if (c > top.col) return emitTok(st, tok)
    popCtx(st)
    st.pending = [tok, ...st.pending]
    return { k: 'rbrace', pos: tokPos(tok) }
  }
  return emitTok(st, tok)
}

function examineTop(st: LexState, tok: GTok): GTok {
  if (tok.k === 'module') {
    st.topMarker = false
    st.sawNewline = false
    return tok
  }
  if (tok.k === 'lbrace') {
    st.topMarker = false
    st.sawNewline = false
    pushCtx(st, { k: 'explicit' })
    return tok
  }
  if (tok.k === 'eof') {
    st.topMarker = false
    st.sawNewline = false
    return emitEof(st, tok)
  }
  const pos = tokPos(tok)
  st.topMarker = false
  st.sawNewline = false
  pushCtx(st, { k: 'implicit', col: pos.column })
  st.pending = [tok, ...st.pending]
  return { k: 'lbrace', pos }
}

function examineLayoutKw(st: LexState, tok: GTok): GTok {
  st.layoutExpected = false
  if (tok.k === 'lbrace') {
    pushCtx(st, { k: 'explicit' })
    return emitTok(st, tok)
  }
  if (tok.k === 'eof') return emitEof(st, tok)
  const pos = tokPos(tok)
  pushCtx(st, { k: 'implicit', col: pos.column })
  st.pending = [tok, ...st.pending]
  st.sawNewline = false
  return { k: 'lbrace', pos }
}

function examineOrdinary(st: LexState, tok: GTok): GTok {
  switch (tok.k) {
    case 'eof':
      return emitEof(st, tok)
    case 'in':
      return closeLet(st, tok)
    case 'let':
      pushCtx(st, { k: 'letpending' })
      st.layoutExpected = true
      return emitTok(st, tok)
    case 'where':
    case 'of':
      st.layoutExpected = true
      return emitTok(st, tok)
    case 'lbrace':
      pushCtx(st, { k: 'explicit' })
      return emitTok(st, tok)
    case 'rbrace': {
      const top = st.stack[0]
      if (top !== undefined && top.k === 'explicit') {
        popCtx(st)
        return emitTok(st, tok)
      }
      throw new GLexError(tokPos(tok).line, tokPos(tok).column, `Parse error: unmatched '}' at line ${tokPos(tok).line}, column ${tokPos(tok).column}.`)
    }
    default:
      return examinePlain(st, tok)
  }
}

function examineToken(st: LexState, tok: GTok): GTok {
  if (st.topMarker) return examineTop(st, tok)
  if (st.layoutExpected) return examineLayoutKw(st, tok)
  return examineOrdinary(st, tok)
}

export function readToken(st: LexState): GTok {
  for (;;) {
    if (st.virtuals.length > 0) {
      const [v, ...rest] = st.virtuals as [GTok, ...GTok[]]
      st.virtuals = rest
      return v
    }
    if (st.pending.length > 0) {
      const [t, ...rest] = st.pending as [GTok, ...GTok[]]
      st.pending = rest
      return examineToken(st, t)
    }
    if (st.done) return { k: 'eof', pos: curPos(st) }
    const raw = scanRaw(st)
    if (raw === null) continue
    if (raw.k === 'eof') {
      const at = curPos(st)
      return examineToken(st, { k: 'eof', pos: at })
    }
    return examineToken(st, raw)
  }
}

/** Tokenize with top-level implicit block (module entry, like parse'module). */
export function lexGlaskModule(src: string): GTok[] {
  const st = initLex(src.replace(/\r\n?/g, '\n'))
  st.topMarker = true
  const out: GTok[] = []
  for (;;) {
    const t = readToken(st)
    out.push(t)
    if (t.k === 'eof' && st.done) break
    if (out.length > 100000) throw new GLexError(1, 1, ' token limit exceeded.')
  }
  return out
}

/** Tokenize without the top-level marker (like use'parser read'token). */
export function lexGlaskRaw(src: string): GTok[] {
  const st = initLex(src.replace(/\r\n?/g, '\n'))
  const out: GTok[] = []
  for (;;) {
    const t = readToken(st)
    out.push(t)
    if (t.k === 'eof' && st.done) break
    if (out.length > 100000) throw new GLexError(1, 1, ' token limit exceeded.')
  }
  return out
}

// ---- parser entry points (mirror parse'module/parse'decls/parse'expr/parse'type) ----

function parserOf(toks: GTok[]): GParser {
  return new GParser(toks)
}

function expectEof(p: GParser): void {
  const t = p.peek()
  if (t.k !== 'eof') p.err(t, 'expected end of input')
}

export function parseGlaskModule(src: string): TermDecl[] {
  const toks = lexGlaskModule(src)
  const p = parserOf(toks)
  const decls = p.parseModuleDecls()
  expectEof(p)
  return decls
}

export function parseGlaskDecls(src: string): TermDecl[] {
  const toks = lexGlaskRaw(src)
  const p = parserOf(toks)
  const ds = p.parseDeclaration()
  expectEof(p)
  return ds
}

export function parseGlaskExpr(src: string): TermExpr {
  const toks = lexGlaskRaw(src)
  const p = parserOf(toks)
  const e = p.parseExpression()
  expectEof(p)
  return e
}

export function parseGlaskType(src: string): TermType {
  const toks = lexGlaskRaw(src)
  const p = parserOf(toks)
  const t = p.parseType()
  expectEof(p)
  return t
}

// __PART8_CORE__
// Core language (mirrors Interpreter.Core) + ToCore + lazy evaluator.
// Deviation: we evaluate GExpr directly via a Core-like machine, but keep
// the Core shape for fidelity; dictionary elaboration (placeholders) is
// skipped — overloaded methods dispatch at runtime on value tags.

export type GCore
  = { k: 'var'; name: string }
  | { k: 'prim'; name: string }
  | { k: 'lit'; lit: GLit }
  | { k: 'abs'; param: string; body: GCore }
  | { k: 'case'; motive: GCore; matches: GCoreMatch[] }
  | { k: 'intro'; tag: string; args: GCore[] }
  | { k: 'app'; fn: GCore; arg: GCore }
  | { k: 'tuple'; args: GCore[] }
  | { k: 'let'; binds: GCoreBinding[]; body: GCore }
  | { k: 'err'; msg: string }

export interface GCoreBinding { name: string; lambda: GCore }
export interface GCoreMatch { pats: GPat[]; rhs: GCore }

const G_PRIM_OPS = new Set([
  'int#==', 'int#<', 'int#>', 'int#+', 'int#show',
  'double#+', 'int#*', 'double#*', 'int#-', 'double#-',
  'double#/', 'int#/', 'trace#', 'fst#', 'snd#', 'show#',
])

function isPrimOp(name: string): boolean {
  return G_PRIM_OPS.has(name)
}

let coreVarCounter = 0
function freshCoreVar(base = '__c'): string {
  coreVarCounter++
  return `${base}${coreVarCounter}`
}

export function toCore(e: GExpr): GCore {
  switch (e.k) {
    case 'var': return isPrimOp(e.name) ? { k: 'prim', name: e.name } : { k: 'var', name: e.name }
    case 'con': return isPrimOp(e.name) ? { k: 'prim', name: e.name } : { k: 'var', name: e.name }
    case 'op': return isPrimOp(e.name) ? { k: 'prim', name: e.name } : { k: 'var', name: e.name }
    case 'lit': return { k: 'lit', lit: e.lit }
    case 'abs': {
      // Decompose nested abs, build pattern-matching lambdas.
      const pats: GPat[] = []
      let body: GExpr = e
      while (body.k === 'abs') {
        pats.push(body.pat)
        body = body.body
      }
      const coreBody = toCore(body)
      const vars = pats.map(() => freshCoreVar('__p'))
      let inner: GCore = coreBody
      for (let i = vars.length - 1; i >= 0; i--) {
        const v = vars[i]!
        const p = pats[i]!
        inner = {
          k: 'case', motive: { k: 'var', name: v },
          matches: [
            { pats: [p], rhs: inner },
            { pats: [{ k: 'wild' }], rhs: { k: 'err', msg: "Non'Exhaustive" } },
          ],
        }
      }
      let lam: GCore = inner
      for (let i = vars.length - 1; i >= 0; i--) lam = { k: 'abs', param: vars[i]!, body: lam }
      return lam
    }
    case 'app': return { k: 'app', fn: toCore(e.l), arg: toCore(e.r) }
    case 'infix': {
      // Infix'App f x y  ==>  App (App f x) y
      return { k: 'app', fn: { k: 'app', fn: toCore(e.op), arg: toCore(e.l) }, arg: toCore(e.r) }
    }
    case 'tuple': return { k: 'tuple', args: e.exprs.map(toCore) }
    case 'if':
      return {
        k: 'case', motive: toCore(e.c),
        matches: [
          { pats: [{ k: 'con', name: 'True', pats: [] }], rhs: toCore(e.t) },
          { pats: [{ k: 'con', name: 'False', pats: [] }], rhs: toCore(e.e) },
          { pats: [{ k: 'wild' }], rhs: { k: 'err', msg: "Non'Exhaustive" } },
        ],
      }
    case 'let': {
      const binds = declsToCore(e.decls)
      return { k: 'let', binds, body: toCore(e.body) }
    }
    case 'ann': return toCore(e.expr)
    case 'case':
      return { k: 'case', motive: toCore(e.expr), matches: e.alts.map((m) => ({ pats: m.pats, rhs: toCore(m.rhs) })) }
    case 'hole': return { k: 'err', msg: `hole ${e.name}` }
    case 'mvar': throw new GEvalError(`Internal: unresolved method ${e.method}`)
    case 'dict': throw new GEvalError('Internal: unresolved dictionary')
  }
}

function bindGroupToCore(name: string, alts: GMatch[]): GCoreBinding {
  if (alts.length === 1 && alts[0]!.pats.length === 0) {
    return { name, lambda: toCore(alts[0]!.rhs) }
  }
  // Mirrors bind'group'to'core: abstract over fresh vars, case on the first,
  // nesting cases for the rest with fallthrough to earlier-computed matches.
  const n = alts[0]!.pats.length
  const vars = Array.from({ length: n }, () => freshCoreVar('__a'))
  const v1 = vars[0]!
  const vrest = vars.slice(1)
  const fail: GCoreMatch = { pats: [{ k: 'wild' }], rhs: { k: 'err', msg: "Non'Exhaustive" } }
  let eqs: GCoreMatch[] = [fail]
  const matchesPrime: GCoreMatch[] = []
  for (let ai = alts.length - 1; ai >= 0; ai--) {
    const alt = alts[ai]!
    const p1 = alt.pats[0] ?? ({ k: 'wild' } as GPat)
    const prest = alt.pats.slice(1)
    let inner: GCore = toCore(alt.rhs)
    for (let j = prest.length - 1; j >= 0; j--) {
      const v = vrest[j]!
      const p = prest[j]!
      const fall: GCore = { k: 'case', motive: { k: 'var', name: v1 }, matches: [...eqs] }
      inner = { k: 'case', motive: { k: 'var', name: v }, matches: [{ pats: [p], rhs: inner }, { pats: [{ k: 'wild' }], rhs: fall }] }
    }
    const m: GCoreMatch = { pats: [p1], rhs: inner }
    eqs = [m, ...eqs]
    matchesPrime.unshift(m)
  }
  const caseExpr: GCore = { k: 'case', motive: { k: 'var', name: v1 }, matches: [...matchesPrime, fail] }
  let out: GCore = caseExpr
  for (let i = vars.length - 1; i >= 0; i--) out = { k: 'abs', param: vars[i]!, body: out }
  return { name, lambda: out }
}

export function declsToCore(decls: GDecl[]): GCoreBinding[] {
  const out: GCoreBinding[] = []
  for (const d of decls) {
    if (d.k === 'binding') out.push(bindGroupToCore(d.name, d.alts))
  }
  return out
}

export function dataToCore(dataDecls: Extract<GDecl, { k: 'data' }>[]): GCoreBinding[] {
  const out: GCoreBinding[] = []
  for (const d of dataDecls) {
    for (const c of d.ctors) {
      if (c.k === 'con') {
        const names = c.tys.map(() => freshCoreVar('__d'))
        let body: GCore = { k: 'intro', tag: c.name, args: names.map((n) => ({ k: 'var', name: n }) as GCore) }
        for (let i = names.length - 1; i >= 0; i--) body = { k: 'abs', param: names[i]!, body }
        out.push({ name: c.name, lambda: body })
      } else {
        const names = c.fields.map(() => freshCoreVar('__d'))
        let body: GCore = { k: 'intro', tag: c.name, args: names.map((n) => ({ k: 'var', name: n }) as GCore) }
        for (let i = names.length - 1; i >= 0; i--) body = { k: 'abs', param: names[i]!, body }
        out.push({ name: c.name, lambda: body })
      }
    }
  }
  return out
}

// __PART9_EVAL__
// Lazy store-based evaluator (mirrors Interpreter.Evaluate). Overloaded
// methods dispatch at runtime on value tags (documented deviation from the
// dictionary-passing elaboration).

export interface GEvalCtl {
  abort: boolean
  ops: number
  budget: number
}

export class GInterrupted extends Error {}
export class GEvalError extends Error {}

type GAddr = number
type GPromise = { addr: GAddr }
type GEnv = Map<string, GPromise>
type GStoreVal
  = { k: 'thunk'; core: GCore; env: GEnv }
  | { k: 'value'; value: GValue }
  | { k: 'blackhole' }
export type GStore = Map<GAddr, GStoreVal>

export type GValue
  = { k: 'lit'; lit: GLit }
  | { k: 'data'; tag: string; args: GPromise[] }
  | { k: 'closure'; param: string; body: GCore; env: GEnv }
  | { k: 'prim'; name: string }
  | { k: 'dispatch'; method: string }

function allocThunk(store: GStore, core: GCore, env: GEnv): GPromise {
  const addr = store.size
  store.set(addr, { k: 'thunk', core, env })
  return { addr }
}

function allocValue(store: GStore, value: GValue): GPromise {
  const addr = store.size
  store.set(addr, { k: 'value', value })
  return { addr }
}

export interface GDispatchTable {
  methods: Set<string>
  instances: Array<{ cls: string; head: GType; methods: Map<string, GCore> }>
  ctorToType: Map<string, string>
  implEnv: GEnv
}

function tick(ctl: GEvalCtl): void {
  ctl.ops++
  if (ctl.ops > ctl.budget) throw new GInterrupted()
  if (ctl.abort) throw new GInterrupted()
}

export async function gForce(p: GPromise, store: GStore, ctl: GEvalCtl, disp: GDispatchTable): Promise<GValue> {
  const cell = store.get(p.addr)
  if (cell === undefined) throw new GEvalError(`Unbound address ${p.addr}`)
  if (cell.k === 'value') return cell.value
  if (cell.k === 'blackhole') throw new GEvalError('Blackhole: infinite loop')
  store.set(p.addr, { k: 'blackhole' })
  const v = await gEval(cell.core, cell.env, store, ctl, disp)
  store.set(p.addr, { k: 'value', value: v })
  return v
}

export async function gEval(core: GCore, env: GEnv, store: GStore, ctl: GEvalCtl, disp: GDispatchTable): Promise<GValue> {
  tick(ctl)
  if (ctl.ops % 2000 === 0) await new Promise((r) => setTimeout(r, 0))
  switch (core.k) {
    case 'var': {
      const p = env.get(core.name)
      if (p === undefined) throw new GEvalError(`Unbound'Var ${core.name}`)
      return gForce(p, store, ctl, disp)
    }
    case 'prim': return { k: 'prim', name: core.name }
    case 'lit': return { k: 'lit', lit: core.lit }
    case 'abs': return { k: 'closure', param: core.param, body: core.body, env }
    case 'app': {
      const fn = await gEval(core.fn, env, store, ctl, disp)
      const argP = allocThunk(store, core.arg, env)
      return gApply(fn, argP, store, ctl, disp)
    }
    case 'tuple': {
      const ps = core.args.map((a) => allocThunk(store, a, env))
      if (ps.length === 0) return { k: 'data', tag: '()', args: [] }
      if (ps.length === 1) return gForce(ps[0]!, store, ctl, disp)
      const tag = '(' + ','.repeat(Math.max(0, ps.length - 1)) + ')'
      return { k: 'data', tag, args: ps }
    }
    case 'intro': {
      const ps = core.args.map((a) => allocThunk(store, a, env))
      return { k: 'data', tag: core.tag, args: ps }
    }
    case 'let': {
      const base = store.size
      const newEnv = new Map(env)
      const n = core.binds.length
      for (let i = 0; i < n; i++) newEnv.set(core.binds[i]!.name, { addr: base + i })
      for (let i = 0; i < n; i++) store.set(base + i, { k: 'thunk', core: core.binds[i]!.lambda, env: newEnv })
      return gEval(core.body, newEnv, store, ctl, disp)
    }
    case 'case': {
      const motiveP = allocThunk(store, core.motive, env)
      for (const m of core.matches) {
        const r = await gMatchAlts(motiveP, [m], env, store, ctl, disp)
        if (r !== null) return r
      }
      throw new GEvalError('NonExhaustive case')
    }
    case 'err': throw new GEvalError(core.msg)
  }
}

async function gApply(fn: GValue, argP: GPromise, store: GStore, ctl: GEvalCtl, disp: GDispatchTable): Promise<GValue> {
  tick(ctl)
  if (fn.k === 'closure') {
    const newEnv = new Map(fn.env)
    newEnv.set(fn.param, argP)
    return gEval(fn.body, newEnv, store, ctl, disp)
  }
  if (fn.k === 'prim') {
    const argV = await gForce(argP, store, ctl, disp)
    return gPrim(fn.name, argV, store, ctl, disp)
  }
  if (fn.k === 'dispatch') {
    const argV = await gForce(argP, store, ctl, disp)
    const impl = gResolveMethod(disp, fn.method, argV)
    if (impl === null) throw new GEvalError(`No instance for ${fn.method} at ${gValueTag(argV)}`)
    const clos = await gEval(impl, disp.implEnv, store, ctl, disp)
    return gApply(clos, argP, store, ctl, disp)
  }
  throw new GEvalError(`Evaluation Error: while evaluating function expression I didn't get a Closure!`)
}

function gValueTag(v: GValue): string {
  if (v.k === 'lit') return v.lit.k === 'int' ? 'Int' : v.lit.k === 'double' ? 'Double' : 'Char'
  if (v.k === 'data') return v.tag
  return v.k
}

function valueTypeSkeleton(disp: GDispatchTable, v: GValue): string {
  if (v.k === 'lit') return v.lit.k === 'int' ? 'Int' : v.lit.k === 'double' ? 'Double' : 'Char'
  if (v.k === 'data') {
    const t = disp.ctorToType.get(v.tag)
    if (t !== undefined) return t
    if (v.tag === '[]' || v.tag === ':') return '[]'
    if (v.tag === '()' || v.tag.startsWith('(')) return v.tag
    if (v.tag === 'String') return 'String'
    return v.tag
  }
  return '?'
}

function typeHeadName(t: GType): string | null {
  let cur = t
  while (cur.k === 'app') cur = cur.l
  if (cur.k === 'con') return cur.c.name
  if (cur.k === 'tuple') return '(' + ','.repeat(Math.max(0, cur.tys.length - 1)) + ')'
  return null
}

function gResolveMethod(disp: GDispatchTable, method: string, argV: GValue): GCore | null {
  const vTy = valueTypeSkeleton(disp, argV)
  for (const inst of disp.instances) {
    if (!inst.methods.has(method)) continue
    const hn = typeHeadName(inst.head)
    if (hn === null) return inst.methods.get(method)!
    if (hn === vTy) return inst.methods.get(method)!
    if ((hn === '[]' || hn === 'List') && (vTy === '[]' || vTy === 'List')) return inst.methods.get(method)!
  }
  for (const inst of disp.instances) {
    if (inst.methods.has(method)) return inst.methods.get(method)!
  }
  return null
}

async function gPrim(name: string, arg: GValue, store: GStore, ctl: GEvalCtl, disp: GDispatchTable): Promise<GValue> {
  const forcePair = async (v: GValue): Promise<[GValue, GValue]> => {
    if (v.k !== 'data' || v.args.length !== 2) throw new GEvalError(`Evaluation Error: Primitive Operation '${name}' applied to something bad`)
    const a = await gForce(v.args[0]!, store, ctl, disp)
    const b = await gForce(v.args[1]!, store, ctl, disp)
    return [a, b]
  }
  switch (name) {
    case 'int#+': {
      const [a, b] = await forcePair(arg)
      if (a.k === 'lit' && a.lit.k === 'int' && b.k === 'lit' && b.lit.k === 'int') return { k: 'lit', lit: { k: 'int', v: a.lit.v + b.lit.v } }
      throw new GEvalError(`Evaluation Error: Primitive Operation 'int#+' applied to something bad`)
    }
    case 'int#-': {
      const [a, b] = await forcePair(arg)
      if (a.k === 'lit' && a.lit.k === 'int' && b.k === 'lit' && b.lit.k === 'int') return { k: 'lit', lit: { k: 'int', v: a.lit.v - b.lit.v } }
      throw new GEvalError(`Evaluation Error: Primitive Operation 'int#-' applied to something bad`)
    }
    case 'int#*': {
      const [a, b] = await forcePair(arg)
      if (a.k === 'lit' && a.lit.k === 'int' && b.k === 'lit' && b.lit.k === 'int') return { k: 'lit', lit: { k: 'int', v: a.lit.v * b.lit.v } }
      throw new GEvalError(`Evaluation Error: Primitive Operation 'int#*' applied to something bad`)
    }
    case 'int#/': {
      const [a, b] = await forcePair(arg)
      if (a.k === 'lit' && a.lit.k === 'int' && b.k === 'lit' && b.lit.k === 'int') {
        if (b.lit.v === 0) throw new GEvalError('Division by zero')
        return { k: 'lit', lit: { k: 'int', v: Math.trunc(a.lit.v / b.lit.v) } }
      }
      throw new GEvalError(`Evaluation Error: Primitive Operation 'int#/' applied to something bad`)
    }
    case 'double#+': {
      const [a, b] = await forcePair(arg)
      const av = a.k === 'lit' ? (a.lit.k === 'double' ? a.lit.v : a.lit.k === 'int' ? a.lit.v : null) : null
      const bv = b.k === 'lit' ? (b.lit.k === 'double' ? b.lit.v : b.lit.k === 'int' ? b.lit.v : null) : null
      if (av !== null && bv !== null) return { k: 'lit', lit: { k: 'double', v: av + bv } }
      throw new GEvalError(`Evaluation Error: Primitive Operation 'double#+' applied to something bad`)
    }
    case 'double#-': {
      const [a, b] = await forcePair(arg)
      const av = a.k === 'lit' ? (a.lit.k === 'double' ? a.lit.v : a.lit.k === 'int' ? a.lit.v : null) : null
      const bv = b.k === 'lit' ? (b.lit.k === 'double' ? b.lit.v : b.lit.k === 'int' ? b.lit.v : null) : null
      if (av !== null && bv !== null) return { k: 'lit', lit: { k: 'double', v: av - bv } }
      throw new GEvalError(`Evaluation Error: Primitive Operation 'double#-' applied to something bad`)
    }
    case 'double#*': {
      const [a, b] = await forcePair(arg)
      const av = a.k === 'lit' ? (a.lit.k === 'double' ? a.lit.v : a.lit.k === 'int' ? a.lit.v : null) : null
      const bv = b.k === 'lit' ? (b.lit.k === 'double' ? b.lit.v : b.lit.k === 'int' ? b.lit.v : null) : null
      if (av !== null && bv !== null) return { k: 'lit', lit: { k: 'double', v: av * bv } }
      throw new GEvalError(`Evaluation Error: Primitive Operation 'double#*' applied to something bad`)
    }
    case 'double#/': {
      const [a, b] = await forcePair(arg)
      const av = a.k === 'lit' ? (a.lit.k === 'double' ? a.lit.v : a.lit.k === 'int' ? a.lit.v : null) : null
      const bv = b.k === 'lit' ? (b.lit.k === 'double' ? b.lit.v : b.lit.k === 'int' ? b.lit.v : null) : null
      if (av !== null && bv !== null) return { k: 'lit', lit: { k: 'double', v: av / bv } }
      throw new GEvalError(`Evaluation Error: Primitive Operation 'double#/' applied to something bad`)
    }
    case 'int#<':
    case 'int#>':
    case 'int#==': {
      const [a, b] = await forcePair(arg)
      if (a.k === 'lit' && a.lit.k === 'int' && b.k === 'lit' && b.lit.k === 'int') {
        const ok = name === 'int#<' ? a.lit.v < b.lit.v : name === 'int#>' ? a.lit.v > b.lit.v : a.lit.v === b.lit.v
        return { k: 'data', tag: ok ? 'True' : 'False', args: [] }
      }
      throw new GEvalError(`Evaluation Error: Primitive Operation '${name}' applied to something bad`)
    }
    case 'int#show': {
      if (arg.k === 'lit' && arg.lit.k === 'int') {
        const s = String(arg.lit.v)
        let acc: GValue = { k: 'data', tag: '[]', args: [] }
        for (let i = s.length - 1; i >= 0; i--) {
          const hp = allocValue(store, { k: 'lit', lit: { k: 'char', v: s[i]! } })
          const tp = allocValue(store, acc)
          acc = { k: 'data', tag: ':', args: [hp, tp] }
        }
        return acc
      }
      throw new GEvalError(`Evaluation Error: Primitive Operation 'int#show' applied to something bad`)
    }
    case 'fst#':
    case 'snd#': {
      if (arg.k === 'data' && arg.args.length === 2) return gForce(arg.args[name === 'fst#' ? 0 : 1]!, store, ctl, disp)
      throw new GEvalError(`Evaluation Error: Primitive Operation '${name}' applied to something bad`)
    }
    case 'show#':
    case 'trace#': return arg
    default: throw new GEvalError(`Uh oh ... this primitive operation ('${name}') is not implemented yet.`)
  }
}

async function gMatchAlts(
  motiveP: GPromise, matches: GCoreMatch[], env: GEnv, store: GStore, ctl: GEvalCtl, disp: GDispatchTable,
): Promise<GValue | null> {
  for (const m of matches) {
    if (m.pats.length !== 1) throw new GEvalError('Evaluation - Pattern Matching: match inside a case analysis contains zero or many patterns and not exactly one.')
    const caps = await gMatchPat(motiveP, m.pats[0]!, store, ctl, disp)
    if (caps === null || caps === 'error') {
      if (caps === 'error') throw new GEvalError('match error')
      continue
    }
    const newEnv = new Map(env)
    for (const [n, pv] of caps) {
      if (pv.k === 'promise') newEnv.set(n, pv.p)
      else newEnv.set(n, allocValue(store, pv.v))
    }
    return gEval(m.rhs, newEnv, store, ctl, disp)
  }
  return null
}

type GCap = Array<[string, { k: 'promise'; p: GPromise } | { k: 'value'; v: GValue }]>

async function gMatchPat(
  p: GPromise, pat: GPat, store: GStore, ctl: GEvalCtl, disp: GDispatchTable,
): Promise<GCap | null | 'error'> {
  switch (pat.k) {
    case 'wild': return []
    case 'var': return [[pat.name, { k: 'promise', p }]]
    case 'as': {
      const inner = await gMatchPat(p, pat.pat, store, ctl, disp)
      if (inner === null || inner === 'error') return inner
      return [[pat.name, { k: 'promise', p }], ...inner]
    }
    case 'ann': return gMatchPat(p, pat.pat, store, ctl, disp)
    case 'lit': {
      const v = await gForce(p, store, ctl, disp)
      if (v.k !== 'lit') return null
      const a = v.lit
      const b = pat.lit
      if (a.k === 'int' && b.k === 'int' && a.v === b.v) return []
      if (a.k === 'double' && b.k === 'double' && a.v === b.v) return []
      if (a.k === 'char' && b.k === 'char' && a.v === b.v) return []
      if (a.k === 'int' && b.k === 'double' && a.v === b.v) return []
      if (a.k === 'double' && b.k === 'int' && a.v === b.v) return []
      return null
    }
    case 'con': {
      if (pat.pats.length === 0) {
        const v = await gForce(p, store, ctl, disp)
        if (v.k === 'data' && v.tag === pat.name) return []
        return null
      }
      const v = await gForce(p, store, ctl, disp)
      if (v.k !== 'data' || v.tag !== pat.name) return null
      if (v.args.length !== pat.pats.length) return null
      const out: GCap = []
      for (let i = 0; i < pat.pats.length; i++) {
        const r = await gMatchPat(v.args[i]!, pat.pats[i]!, store, ctl, disp)
        if (r === null || r === 'error') return r
        out.push(...r)
      }
      return out
    }
  }
}

export async function gShowValue(v: GValue, store: GStore, ctl: GEvalCtl, disp: GDispatchTable, depth = 0): Promise<string> {
  if (depth > 50) return '...'
  if (v.k === 'lit') {
    if (v.lit.k === 'char') return `'${v.lit.v}'`
    return String(v.lit.v)
  }
  if (v.k === 'closure') return '<function>'
  if (v.k === 'prim') return `(${v.name})`
  if (v.k === 'dispatch') return `<method ${v.method}>`
  const tag = v.tag
  if (tag === '[]') return '[]'
  if (tag === ':') {
    const chars: string[] = []
    let cur: GValue = v
    let isString = true
    while (cur.k === 'data' && cur.tag === ':') {
      const h = await gForce(cur.args[0]!, store, ctl, disp)
      if (h.k !== 'lit' || h.lit.k !== 'char') {
        isString = false
        break
      }
      chars.push(h.lit.v)
      cur = await gForce(cur.args[1]!, store, ctl, disp)
    }
    if (isString && cur.k === 'data' && cur.tag === '[]') {
      return `"${chars.join('').replace(/\\/g, '\\\\').replace(/"/g, '\\"')}"`
    }
    let c2: GValue = v
    const elems: string[] = []
    for (let i = 0; i < 200; i++) {
      if (c2.k !== 'data') {
        elems.push('<?>')
        break
      }
      if (c2.tag === '[]') break
      if (c2.tag !== ':') {
        elems.push('<?>')
        break
      }
      const h = await gForce(c2.args[0]!, store, ctl, disp)
      elems.push(await gShowValue(h, store, ctl, disp, depth + 1))
      c2 = await gForce(c2.args[1]!, store, ctl, disp)
      tick(ctl)
    }
    return `[${elems.join(', ')}]`
  }
  if (tag === 'String') {
    if (v.args.length === 1) {
      const inner = await gForce(v.args[0]!, store, ctl, disp)
      return gShowValue(inner, store, ctl, disp, depth + 1)
    }
    return 'String'
  }
  if (tag === '()' || tag === 'Unit') return '()'
  if (/^\(,+\)$/.test(tag)) {
    const parts: string[] = []
    for (const a of v.args) {
      const av = await gForce(a, store, ctl, disp)
      parts.push(await gShowValue(av, store, ctl, disp, depth + 1))
    }
    return `(${parts.join(', ')})`
  }
  if (v.args.length === 0) return tag
  const parts: string[] = []
  for (const a of v.args) {
    const av = await gForce(a, store, ctl, disp)
    const s = await gShowValue(av, store, ctl, disp, depth + 1)
    parts.push(av.k === 'data' && av.args.length > 0 ? `(${s})` : s)
  }
  return `(${tag} ${parts.join(' ')})`
}
// TransEnv building (mirrors REPL.Analyses build'trans'env) + semantic
// synonym analyses (FullyApplied; Cycles is a no-op upstream).

export function initKindContext(): Map<string, GKind> {
  const star: GKind = { k: 'star' }
  const arr = (d: GKind, c: GKind): GKind => ({ k: 'arr', dom: d, cod: c })
  return new Map<string, GKind>([
    ['Bool', star],
    ['Int', star],
    ['Double', star],
    ['Char', star],
    ['Unit', star],
    ['(->)', arr(star, arr(star, star))],
    ['[]', arr(star, star)],
    ['()', star],
  ])
}

export function buildTransEnv(decls: TermDecl[], st: TrState): TransEnv {
  const fixities = new Map<string, GOpInfo>()
  fixities.set(':', { fix: 'infix', assoc: 'right', prec: 5 })
  for (const d of decls) {
    if (d.k === 'fixity') {
      for (const op of d.ops) fixities.set(op, { fix: d.fix, assoc: d.assoc, prec: d.prec })
    }
  }
  const constructors = new Map<string, { k: 'con'; name: string; arity: number } | { k: 'record'; name: string; fields: string[] }>()
  for (const d of decls) {
    if (d.k === 'data') {
      for (const c of d.ctors) {
        if (c.k === 'con') constructors.set(c.name, { k: 'con', name: c.name, arity: c.tys.length })
        else constructors.set(c.name, { k: 'record', name: c.name, fields: c.fields.map(([n]) => n) })
      }
    }
  }
  const fields = new Map<string, string>()
  for (const [, info] of constructors) {
    if (info.k === 'record') {
      for (const f of info.fields) fields.set(f, info.name)
    }
  }
  const synonyms = new Map<string, number>()
  for (const d of decls) {
    if (d.k === 'alias') synonyms.set(d.name, d.params.length)
  }
  const kindContext = initKindContext()
  const classes = new Map<string, GKind>()
  // Types.extract: fresh kind per data/alias + fresh kind per class param.
  for (const d of decls) {
    if (d.k === 'data' || d.k === 'alias') {
      const resName = gFresh(st)
      const resKind: GKind = { k: 'var', name: resName }
      const paramKinds: GKind[] = d.params.map(() => ({ k: 'var', name: gFresh(st) }) as GKind)
      let kind: GKind
      if (d.k === 'data') {
        // foldl (flip Arr) result params: k_n -> ... -> k_1 -> result
        kind = resKind
        for (const pk of paramKinds) kind = { k: 'arr', dom: pk, cod: kind }
      } else {
        // foldl Arr result params: (...((result -> k_1) -> k_2)...)
        kind = resKind
        for (const pk of paramKinds) kind = { k: 'arr', dom: kind, cod: pk }
      }
      kindContext.set(d.name, kind)
    } else if (d.k === 'class') {
      const kn: GKind = { k: 'var', name: gFresh(st) }
      classes.set(d.name, kn)
    }
  }
  return { fixities, constructors, fields, kindContext, synonyms, classes }
}

function fullyAppliedType(t: TermType, syns: Map<string, number>, errs: GSemError[]): void {
  switch (t.k) {
    case 'id': return
    case 'tuple': for (const x of t.tys) fullyAppliedType(x, syns, errs); return
    case 'unit': return
    case 'list': fullyAppliedType(t.ty, syns, errs); return
    case 'arrow': for (const x of t.tys) fullyAppliedType(x, syns, errs); return
    case 'forall':
      // aliases for constraints are not allowed — no need to check preds
      fullyAppliedType(t.ty, syns, errs)
      return
    case 'app': {
      const [h, ...rest] = t.tys
      if (h !== undefined && h.k === 'id' && h.id.k === 'con') {
        const ar = syns.get(h.id.name)
        if (ar !== undefined) {
          if (ar !== rest.length) errs.push({ k: 'synNotApplied', name: h.id.name })
          for (const x of rest) fullyAppliedType(x, syns, errs)
          return
        }
      }
      for (const x of t.tys) fullyAppliedType(x, syns, errs)
      return
    }
  }
}

function fullyAppliedExpr(e: TermExpr, syns: Map<string, number>, errs: GSemError[]): void {
  switch (e.k) {
    case 'id': case 'op': case 'lit': case 'hole': return
    case 'abs': fullyAppliedExpr(e.body, syns, errs); return
    case 'app': for (const x of e.exprs) fullyAppliedExpr(x, syns, errs); return
    case 'tuple': for (const x of e.exprs) fullyAppliedExpr(x, syns, errs); return
    case 'list': for (const x of e.exprs) fullyAppliedExpr(x, syns, errs); return
    case 'arith':
      fullyAppliedExpr(e.lo, syns, errs)
      if (e.step) fullyAppliedExpr(e.step, syns, errs)
      fullyAppliedExpr(e.hi, syns, errs)
      return
    case 'if':
      fullyAppliedExpr(e.cond, syns, errs)
      fullyAppliedExpr(e.then, syns, errs)
      fullyAppliedExpr(e.els, syns, errs)
      return
    case 'let':
      for (const d of e.decls) fullyAppliedDecl(d, syns, errs)
      fullyAppliedExpr(e.body, syns, errs)
      return
    case 'ann':
      fullyAppliedExpr(e.expr, syns, errs)
      fullyAppliedType(e.ty, syns, errs)
      return
    case 'case':
      fullyAppliedExpr(e.expr, syns, errs)
      for (const [p, b] of e.alts) {
        void p
        fullyAppliedExpr(b, syns, errs)
      }
      return
    case 'lcon':
      for (const [, x] of e.fields) fullyAppliedExpr(x, syns, errs)
      return
    case 'lupd':
      fullyAppliedExpr(e.expr, syns, errs)
      for (const [, x] of e.fields) fullyAppliedExpr(x, syns, errs)
      return
  }
}

function fullyAppliedDecl(d: TermDecl, syns: Map<string, number>, errs: GSemError[]): void {
  switch (d.k) {
    case 'binding': fullyAppliedExpr(d.expr, syns, errs); return
    case 'sig': fullyAppliedType(d.ty, syns, errs); return
    case 'data':
      for (const c of d.ctors) {
        if (c.k === 'con') for (const t of c.tys) fullyAppliedType(t, syns, errs)
        else for (const [, t] of c.fields) fullyAppliedType(t, syns, errs)
      }
      return
    case 'alias': fullyAppliedType(d.ty, syns, errs); return
    case 'fixity': return
    case 'class': for (const m of d.decls) fullyAppliedDecl(m, syns, errs); return
    case 'instance': for (const m of d.decls) fullyAppliedDecl(m, syns, errs); return
  }
}

export function doSemanticAnalysis(decls: TermDecl[], env: TransEnv): void {
  const errs: GSemError[] = []
  for (const d of decls) fullyAppliedDecl(d, env.synonyms, errs)
  // Synonym cycles: upstream `analyze` is a stub returning [].
  if (errs.length > 0) throw new GTranslateError({ k: 'many', errs })
}

export function translateProgram(decls: TermDecl[], env: TransEnv, st: TrState): GDecl[] {
  const ctx = new TrCtx(env, st)
  const all: GDecl[] = []
  for (const d of decls) {
    for (const g of trDecl(d, ctx)) all.push(g)
  }
  // Merge Bind'Groups with the same name (consecutive grouping, bindings trail).
  const bgs: GDecl[] = []
  const others: GDecl[] = []
  for (const g of all) {
    if (g.k === 'binding') bgs.push(g)
    else others.push(g)
  }
  const merged: GDecl[] = []
  let i = 0
  while (i < bgs.length) {
    const cur = bgs[i]! as Extract<GDecl, { k: 'binding' }>
    let j = i + 1
    const alts = [...cur.alts]
    while (j < bgs.length && (bgs[j] as Extract<GDecl, { k: 'binding' }>).name === cur.name) {
      alts.push(...(bgs[j] as Extract<GDecl, { k: 'binding' }>).alts)
      j++
    }
    merged.push({ k: 'binding', name: cur.name, alts })
    i = j
  }
  return [...others, ...merged]
}

export function translateDecls(
  decls: TermDecl[], st: TrState,
): { decls: GDecl[]; env: TransEnv } {
  const env = buildTransEnv(decls, st)
  doSemanticAnalysis(decls, env)
  const out = translateProgram(decls, env, st)
  return { decls: out, env }
}

// __PART10_INFER__
// Simplified HM + predicates + rank-n checking (best-effort).
// Deviation: no dictionary elaboration, no kind checking on load, no
// full higher-rank subsumption; polymorphic method uses instantiate per use
// and dispatch at runtime. Sufficient for the positive examples.

export interface GTypeError extends Error {
  detail: string
}
export function gTypeError(detail: string): Error {
  const e = new Error(detail) as GTypeError
  e.detail = detail
  return e
}

let gMetaCounter = 0
export function freshMetaName(): string {
  gMetaCounter++
  return `?${gMetaCounter}`
}
export function resetMetaCounter(): void {
  gMetaCounter = 0
}

export type GSubst = Map<string, GType>

export function applySubst(s: GSubst, t: GType): GType {
  switch (t.k) {
    case 'var': {
      const v = s.get(t.v.name)
      if (v === undefined) return t
      if (v.k === 'var' && v.v.name === t.v.name) return t
      const s2 = new Map(s)
      s2.delete(t.v.name)
      return applySubst(s2, v)
    }
    case 'meta': {
      const v = s.get(t.v.name)
      if (v === undefined) return t
      if (v.k === 'meta' && v.v.name === t.v.name) return t
      const s2 = new Map(s)
      s2.delete(t.v.name)
      return applySubst(s2, v)
    }
    case 'con': return t
    case 'tuple': return { k: 'tuple', tys: t.tys.map((x) => applySubst(s, x)) }
    case 'app': return { k: 'app', l: applySubst(s, t.l), r: applySubst(s, t.r) }
    case 'forall': {
      // Bound vars shadow subst entries with same name.
      const inner = new Map(s)
      for (const tv of t.tvs) inner.delete(tv.name)
      return {
        k: 'forall', tvs: t.tvs,
        preds: t.preds.map((p) => ({ cls: p.cls, ty: applySubst(inner, p.ty) })),
        ty: applySubst(inner, t.ty),
      }
    }
  }
}

function applySubstPred(s: GSubst, p: GPred): GPred {
  return { cls: p.cls, ty: applySubst(s, p.ty) }
}

function freeMetas(t: GType, out = new Set<string>()): Set<string> {
  if (t.k === 'meta') out.add(t.v.name)
  else if (t.k === 'app') {
    freeMetas(t.l, out)
    freeMetas(t.r, out)
  } else if (t.k === 'tuple') t.tys.forEach((x) => freeMetas(x, out))
  else if (t.k === 'forall') {
    const inner = new Set<string>()
    t.preds.forEach((p) => freeMetas(p.ty, inner))
    freeMetas(t.ty, inner)
    // bound rigid vars are not metas; metas inside are free unless shadowed? metas never shadowed.
    for (const m of inner) out.add(m)
  }
  return out
}

function freeRigids(t: GType, out = new Set<string>()): Set<string> {
  if (t.k === 'var') out.add(t.v.name)
  else if (t.k === 'app') {
    freeRigids(t.l, out)
    freeRigids(t.r, out)
  } else if (t.k === 'tuple') t.tys.forEach((x) => freeRigids(x, out))
  else if (t.k === 'forall') {
    const bound = new Set(t.tvs.map((v) => v.name))
    const inner = new Set<string>()
    t.preds.forEach((p) => freeRigids(p.ty, inner))
    freeRigids(t.ty, inner)
    for (const b of bound) inner.delete(b)
    for (const v of inner) out.add(v)
  }
  return out
}

function occursIn(m: string, t: GType, s: GSubst): boolean {
  const u = applySubst(s, t)
  const ms = freeMetas(u)
  if (ms.has(m)) return true
  return false
}

export function unify(a0: GType, b0: GType, s: GSubst): GSubst {
  const a = applySubst(s, a0)
  const b = applySubst(s, b0)
  // Higher-rank: a polymorphic type unifies by instantiation. Predicates
  // from the instantiation are dropped here; callers that need them
  // (applications) instantiate explicitly instead. See instForallSigma.
  if (a.k === 'forall') {
    const inst = instForallSigma(a.tvs, a.preds, a.ty)
    return unify(inst.ty, b, s)
  }
  if (b.k === 'forall') {
    const inst = instForallSigma(b.tvs, b.preds, b.ty)
    return unify(a, inst.ty, s)
  }
  if (a.k === 'meta') {
    if (b.k === 'meta' && a.v.name === b.v.name) return s
    if (occursIn(a.v.name, b, s)) throw gTypeError(`Occurs check: cannot construct the infinite type:\n  ${showType(a)} ~ ${showType(b)}`)
    const n = new Map(s)
    n.set(a.v.name, b)
    return n
  }
  if (b.k === 'meta') return unify(b, a, s)
  if (a.k === 'var' && b.k === 'var') {
    if (a.v.name === b.v.name) return s
    throw gTypeError(`Couldn't match type \`${showType(a)} :: ${showKind(a.v.kind)}\` with \`${showType(b)}\` :: ${showKind(b.v.kind)}`)
  }
  if (a.k === 'con' && b.k === 'con') {
    if (a.c.name === b.c.name) return s
    throw gTypeError(`Couldn't match type \`${showType(a)} :: ${showKind(a.c.kind)}\` with \`${showType(b)}\` :: ${showKind(b.c.kind)}`)
  }
  if (a.k === 'tuple' && b.k === 'tuple') {
    if (a.tys.length !== b.tys.length) throw gTypeError(`Couldn't match type \`${showType(a)}\` with \`${showType(b)}\``)
    let cur = s
    for (let i = 0; i < a.tys.length; i++) cur = unify(a.tys[i]!, b.tys[i]!, cur)
    return cur
  }
  if (a.k === 'app' && b.k === 'app') {
    let cur = unify(a.l, b.l, s)
    cur = unify(a.r, b.r, cur)
    return cur
  }
  // Rigid var vs anything else, con vs app, etc.
  throw gTypeError(`Couldn't match type \`${showType(a)}\` with \`${showType(b)}\``)
}

function instSigma(sigma: GSigma, st: { n: number }): { preds: GPred[]; ty: GType } {
  const m: GSubst = new Map()
  for (const tv of sigma.tvs) {
    m.set(tv.name, { k: 'meta', v: { name: freshMetaName(), kind: tv.kind } })
  }
  void st
  return {
    preds: sigma.q.preds.map((p) => applySubstPred(m, p)),
    ty: applySubst(m, sigma.q.ty),
  }
}

export interface GInferEnv {
  types: Map<string, GSigma>
  classes: Map<string, { supers: string[]; param: string }>
  instances: Array<{ ctx: GPred[]; head: GPred }>
  methods: Map<string, string>
}

function lookupType(env: GInferEnv, name: string): GSigma {
  const s = env.types.get(name)
  if (s === undefined) throw gTypeError(`Unknown variable ${name} expected type: Infer`)
  return s
}

export function generalize(env: GInferEnv, preds: GPred[], ty: GType, subst: GSubst): GSigma {
  const p2 = nubPreds(preds.map((p) => applySubstPred(subst, p)))
  const t2 = applySubst(subst, ty)
  const envMetas = new Set<string>()
  for (const [, s] of env.types) {
    const tq = s.q.ty
    for (const m of freeMetas(applySubst(subst, tq))) envMetas.add(m)
    for (const p of s.q.preds) for (const m of freeMetas(applySubst(subst, p.ty))) envMetas.add(m)
  }
  const ft = freeMetas(t2)
  const fp = new Set<string>()
  for (const p of p2) for (const m of freeMetas(p.ty)) fp.add(m)
  const all = new Set([...ft, ...fp])
  for (const m of envMetas) all.delete(m)
  // Turn free metas into quantified rigid vars (kind *).
  const tvs: GTV[] = [...all].map((m) => ({ name: m, kind: { k: 'star' } }) as GTV)
  const m2: GSubst = new Map()
  for (const m of all) m2.set(m, { k: 'var', v: { name: m, kind: { k: 'star' } } })
  return { tvs, q: { preds: p2.map((p) => applySubstPred(m2, p)), ty: applySubst(m2, t2) } }
}

// Entailment via instances + superclass expansion (fuel-capped).
function entails(env: GInferEnv, pred: GPred, depth = 0): boolean {
  if (depth > 20) return false
  // Superclass expansion is handled by callers adding supers; here check instances.
  for (const inst of env.instances) {
    if (inst.head.cls !== pred.cls) continue
    const s: GSubst = new Map()
    try {
      const u = matchHead(inst.head.ty, pred.ty, s)
      // Check instance context recursively.
      let ok = true
      for (const c of inst.ctx) {
        if (!entails(env, applySubstPred(u, c), depth + 1)) {
          ok = false
          break
        }
      }
      if (ok) return true
    } catch {
      continue
    }
  }
  return false
}

function matchHead(pat: GType, t: GType, s: GSubst): GSubst {
  // One-way match: only instance-head (pattern) variables may be bound.
  // Query-side metas/vars are rigid here; matching must not instantiate
  // them (otherwise `Num ?a` would be wrongly discharged by `Num Int` and
  // the constraint lost). This mirrors `match` (not `unify`).
  const p = applySubst(s, pat)
  const u = applySubst(s, t)
  if (p.k === 'var') {
    // Rigid var in instance head matches anything (bind it in local subst).
    const n = new Map(s)
    n.set(p.v.name, u)
    return n
  }
  if (p.k === 'meta') {
    const n = new Map(s)
    n.set(p.v.name, u)
    return n
  }
  if (u.k === 'meta' || u.k === 'var') throw gTypeError('no match')
  if (p.k === 'con' && u.k === 'con' && p.c.name === u.c.name) return s
  if (p.k === 'tuple' && u.k === 'tuple' && p.tys.length === u.tys.length) {
    let cur = s
    for (let i = 0; i < p.tys.length; i++) cur = matchHead(p.tys[i]!, u.tys[i]!, cur)
    return cur
  }
  if (p.k === 'app' && u.k === 'app') {
    let cur = matchHead(p.l, u.l, s)
    cur = matchHead(p.r, u.r, cur)
    return cur
  }
  throw gTypeError('no match')
}

export function simplify(env: GInferEnv, preds: GPred[]): GPred[] {
  const nubbed = nubPreds(preds)
  return nubbed.filter((p) => !entails(env, p))
}

function nubPreds(preds: GPred[]): GPred[] {
  const seen = new Set<string>()
  const out: GPred[] = []
  for (const p of preds) {
    const key = `${p.cls} ${showType(p.ty)}`
    if (!seen.has(key)) {
      seen.add(key)
      out.push(p)
    }
  }
  return out
}

// Builtin types and primop schemes (mirrors init't'env + data decls).
function tCon(name: string): GType {
  return { k: 'con', c: { name, kind: { k: 'star' } } }
}
function tInt(): GType {
  return tCon('Int')
}
function tDouble(): GType {
  return tCon('Double')
}
function tBool(): GType {
  return tCon('Bool')
}
function tChar(): GType {
  return tCon('Char')
}
function tArrow(a: GType, b: GType): GType {
  const arr: GType = { k: 'con', c: { name: '(->)', kind: { k: 'arr', dom: { k: 'star' }, cod: { k: 'arr', dom: { k: 'star' }, cod: { k: 'star' } } } } }
  return { k: 'app', l: { k: 'app', l: arr, r: a }, r: b }
}
function tListOf(a: GType): GType {
  const lc: GType = { k: 'con', c: { name: '[]', kind: { k: 'arr', dom: { k: 'star' }, cod: { k: 'star' } } } }
  return { k: 'app', l: lc, r: a }
}
function tTupleOf(ts: GType[]): GType {
  return { k: 'tuple', tys: ts }
}
function tVar(name: string): GType {
  return { k: 'var', v: { name, kind: { k: 'star' } } }
}
function tMeta(): GType {
  return { k: 'meta', v: { name: freshMetaName(), kind: { k: 'star' } } }
}
function sigmaOf(tvs: string[], preds: GPred[], ty: GType): GSigma {
  return { tvs: tvs.map((n) => ({ name: n, kind: { k: 'star' } }) as GTV), q: { preds, ty } }
}

export function builtinTypeEnv(): Map<string, GSigma> {
  const m = new Map<string, GSigma>()
  const a = 'a'
  const b = 'b'
  m.set('fst#', sigmaOf([a, b], [], tArrow(tTupleOf([tVar(a), tVar(b)]), tVar(a))))
  m.set('snd#', sigmaOf([a, b], [], tArrow(tTupleOf([tVar(a), tVar(b)]), tVar(b))))
  m.set('int#==', sigmaOf([a], [], tArrow(tTupleOf([tInt(), tInt()]), tBool())))
  m.set('int#<', sigmaOf([a], [], tArrow(tTupleOf([tInt(), tInt()]), tBool())))
  m.set('int#>', sigmaOf([a], [], tArrow(tTupleOf([tInt(), tInt()]), tBool())))
  m.set('int#+', sigmaOf([], [], tArrow(tTupleOf([tInt(), tInt()]), tInt())))
  m.set('int#show', sigmaOf([], [], tArrow(tInt(), tListOf(tChar()))))
  m.set('double#+', sigmaOf([], [], tArrow(tTupleOf([tDouble(), tDouble()]), tDouble())))
  m.set('int#*', sigmaOf([], [], tArrow(tTupleOf([tInt(), tInt()]), tInt())))
  m.set('double#*', sigmaOf([], [], tArrow(tTupleOf([tDouble(), tDouble()]), tDouble())))
  m.set('int#-', sigmaOf([], [], tArrow(tTupleOf([tInt(), tInt()]), tInt())))
  m.set('double#-', sigmaOf([], [], tArrow(tTupleOf([tDouble(), tDouble()]), tDouble())))
  m.set('int#/', sigmaOf([], [], tArrow(tTupleOf([tInt(), tInt()]), tInt())))
  m.set('double#/', sigmaOf([], [], tArrow(tTupleOf([tDouble(), tDouble()]), tDouble())))
  m.set('show#', sigmaOf([a], [], tArrow(tVar(a), tListOf(tChar()))))
  m.set('trace#', sigmaOf([a], [], tArrow(tVar(a), tVar(a))))
  m.set('()', sigmaOf([], [], tCon('()')))
  m.set('[]', sigmaOf([a], [], tListOf(tVar(a))))
  m.set(':', sigmaOf([a], [], tArrow(tVar(a), tArrow(tListOf(tVar(a)), tListOf(tVar(a))))))
  m.set('(,)', sigmaOf([a, b], [], tArrow(tVar(a), tArrow(tVar(b), tTupleOf([tVar(a), tVar(b)])))))
  return m
}

function ctorSigmaForData(d: Extract<GDecl, { k: 'data' }>): Array<[string, GSigma]> {
  const out: Array<[string, GSigma]> = []
  const params = d.params
  for (const c of d.ctors) {
    if (c.k === 'con') {
      let ty: GType = { k: 'con', c: { name: d.name, kind: { k: 'star' } } }
      for (const p of params) ty = { k: 'app', l: ty, r: tVar(p) }
      for (let i = c.tys.length - 1; i >= 0; i--) ty = tArrow(c.tys[i]!, ty)
      out.push([c.name, sigmaOf(params, [], ty)])
    } else {
      let ty: GType = { k: 'con', c: { name: d.name, kind: { k: 'star' } } }
      for (const p of params) ty = { k: 'app', l: ty, r: tVar(p) }
      const fts = c.fields.map(([, t]) => t)
      for (let i = fts.length - 1; i >= 0; i--) ty = tArrow(fts[i]!, ty)
      out.push([c.name, sigmaOf(params, [], ty)])
    }
  }
  return out
}

// __PART11_CHECK__
// Expression/pattern inference (synth + check). Holes raise Typed'Holes.

export interface GInferOut {
  ty: GType
  preds: GPred[]
  subst: GSubst
  elab: GExpr
}

function inferLit(lit: GLit): { preds: GPred[]; ty: GType } {
  if (lit.k === 'int') {
    const m = tMeta()
    return { preds: [{ cls: 'Num', ty: m }], ty: m }
  }
  if (lit.k === 'double') {
    const m = tMeta()
    return { preds: [{ cls: 'Fractional', ty: m }], ty: m }
  }
  return { preds: [], ty: tChar() }
}

function inferPat(
  env: GInferEnv, pat: GPat, expected: GType, subst: GSubst,
): { binds: Map<string, GType>; preds: GPred[]; subst: GSubst } {
  const binds = new Map<string, GType>()
  let cur = subst
  let preds: GPred[] = []
  const go = (p: GPat, t: GType): void => {
    const tt = applySubst(cur, t)
    if (p.k === 'wild') return
    if (p.k === 'var') {
      binds.set(p.name, tt)
      return
    }
    if (p.k === 'as') {
      binds.set(p.name, tt)
      go(p.pat, tt)
      return
    }
    if (p.k === 'ann') {
      // Pattern annotations must be closed (checked in ToAST); unify.
      const inst = instSigma(p.sigma, { n: 0 })
      cur = unify(tt, inst.ty, cur)
      preds.push(...inst.preds)
      go(p.pat, tt)
      return
    }
    if (p.k === 'lit') {
      const li = inferLit(p.lit)
      cur = unify(tt, li.ty, cur)
      preds.push(...li.preds)
      return
    }
    if (p.k === 'con') {
      if (p.pats.length === 0) {
        const sigma = lookupType(env, p.name)
        const inst = instSigma(sigma, { n: 0 })
        cur = unify(tt, inst.ty, cur)
        preds.push(...inst.preds)
        return
      }
      const sigma = lookupType(env, p.name)
      const inst = instSigma(sigma, { n: 0 })
      // Peel arrows for each arg.
      let fnTy = inst.ty
      preds.push(...inst.preds)
      for (const ap of p.pats) {
        const aTy = tMeta()
        const rTy = tMeta()
        const fnPost = applySubst(cur, fnTy)
        const arrP = matchArrow(fnPost)
        if (arrP !== null && arrP[0].k === 'forall') {
          // Higher-rank constructor argument: bind the pattern to the
          // polymorphic type directly so each use instantiates it afresh.
          go(ap, arrP[0])
          fnTy = arrP[1]
          continue
        }
        cur = unify(applySubst(cur, fnTy), tArrow(aTy, rTy), cur)
        go(ap, applySubst(cur, aTy))
        fnTy = applySubst(cur, rTy)
      }
      cur = unify(fnTy, tt, cur)
      return
    }
  }
  go(pat, expected)
  return { binds, preds, subst: cur }
}

function matchArrow(t: GType): [GType, GType] | null {
  if (t.k === 'app' && t.l.k === 'app' && t.l.l.k === 'con' && t.l.l.c.name === '(->)') {
    return [t.l.r, t.r]
  }
  return null
}

function instForallSigma(tvs: GTV[], preds: GPred[], ty: GType): { preds: GPred[]; ty: GType } {
  const m: GSubst = new Map()
  for (const tv of tvs) m.set(tv.name, { k: 'meta', v: { name: freshMetaName(), kind: tv.kind } })
  return { preds: preds.map((p) => applySubstPred(m, p)), ty: applySubst(m, ty) }
}

// Drop leading dictionary applications from a bare overloaded variable
// use, so it can be passed abstracted (dictionary-passing style). Returns
// null unless the expression is exactly `Var` applied to `dict` nodes.
function stripTopDicts(e: GExpr): GExpr | null {
  let cur = e
  for (;;) {
    if (cur.k === 'app' && cur.r.k === 'dict') {
      cur = cur.l
      continue
    }
    if (cur.k === 'var' || cur.k === 'con' || cur.k === 'op') return cur
    return null
  }
}

// Subsumption of an argument against a higher-rank domain: instantiate the
// domain freshly and check every domain predicate is covered by an argument
// predicate. On success the argument is passed abstracted (no dictionaries
// applied here); returns the updated substitution.
function trySubsume(
  argTy: GType, argPreds: GPred[], dom: GType, subst: GSubst,
): GSubst | null {
  if (dom.k !== 'forall') return null
  const inst = instForallSigma(dom.tvs, dom.preds, dom.ty)
  let cur = subst
  try {
    cur = unify(applySubst(cur, argTy), applySubst(cur, inst.ty), cur)
  } catch {
    return null
  }
  for (const dq0 of inst.preds) {
    const dq = applySubstPred(cur, dq0)
    let ok = false
    for (const aq0 of argPreds) {
      const aq = applySubstPred(cur, aq0)
      if (aq.cls === dq.cls && tryUnify(aq.ty, dq.ty)) {
        ok = true
        break
      }
    }
    if (!ok) return null
  }
  return cur
}

export function inferExpr(env: GInferEnv, e: GExpr, subst: GSubst): GInferOut {
  switch (e.k) {
    case 'var':
    case 'con':
    case 'op': {
      const sigma = lookupType(env, e.name)
      const inst = instSigma(sigma, { n: 0 })
      const cls = env.methods.get(e.name)
      if (cls !== undefined) {
        const pred = inst.preds.find((p) => p.cls === cls) ?? inst.preds[0]
        const elab: GExpr = pred !== undefined
          ? { k: 'mvar', method: e.name, cls, ty: pred.ty }
          : { k: 'var', name: e.name }
        return { ty: inst.ty, preds: inst.preds, subst, elab }
      }
      if (inst.preds.length > 0) {
        let elab: GExpr = { k: 'var', name: e.name }
        for (const p of inst.preds) elab = { k: 'app', l: elab, r: { k: 'dict', cls: p.cls, ty: p.ty } }
        return { ty: inst.ty, preds: inst.preds, subst, elab }
      }
      return { ty: inst.ty, preds: inst.preds, subst, elab: e }
    }
    case 'dict': {
      return { ty: tMeta(), preds: [], subst, elab: e }
    }
    case 'mvar': {
      // Already elaborated (should not be re-inferred, but handle gracefully).
      const sigma = lookupType(env, e.method)
      const inst = instSigma(sigma, { n: 0 })
      return { ty: inst.ty, preds: inst.preds, subst, elab: e }
    }
    case 'lit': {
      const li = inferLit(e.lit)
      return { ty: li.ty, preds: li.preds, subst, elab: e }
    }
    case 'abs': {
      const pTy = tMeta()
      const r = inferPat(env, e.pat, pTy, subst)
      const ext = new Map(env.types)
      for (const [n, t] of r.binds) ext.set(n, sigmaOf([], [], applySubst(r.subst, t)))
      const env2: GInferEnv = { ...env, types: ext }
      const b = inferExpr(env2, e.body, r.subst)
      const fn = tArrow(applySubst(b.subst, pTy), b.ty)
      return { ty: fn, preds: [...r.preds, ...b.preds], subst: b.subst, elab: { k: 'abs', pat: e.pat, body: b.elab } }
    }
    case 'app': {
      const f = inferExpr(env, e.l, subst)
      // Expose an arrow for the function part. A bare forall (e.g. a
      // higher-rank parameter) is instantiated and the instantiation
      // dictionaries are applied to the function itself.
      let fTy = applySubst(f.subst, f.ty)
      let felab = f.elab
      let fps: GPred[] = [...f.preds]
      let cur0 = f.subst
      if (fTy.k === 'forall') {
        const inst = instForallSigma(fTy.tvs, fTy.preds, fTy.ty)
        fTy = inst.ty
        for (const p of inst.preds) {
          felab = { k: 'app', l: felab, r: { k: 'dict', cls: p.cls, ty: p.ty } }
        }
        fps.push(...inst.preds)
      }
      let dom: GType
      let cod: GType
      const arr = matchArrow(fTy)
      if (arr !== null) {
        dom = arr[0]
        cod = arr[1]
      } else if (fTy.k === 'meta') {
        dom = tMeta()
        cod = tMeta()
        cur0 = unify(fTy, tArrow(dom, cod), cur0)
      } else {
        throw gTypeError(`Couldn't match type \`${showType(fTy)}\` with \`? -> ?\``)
      }
      const a = inferExpr(env, e.r, cur0)
      const domS = applySubst(a.subst, dom)
      if (domS.k === 'forall') {
        // Higher-rank argument: try subsumption (pass the argument bare,
        // keeping its own abstraction) before falling back to unification.
        const sub = trySubsume(a.ty, a.preds, domS, a.subst)
        if (sub !== null) {
          const bare = stripTopDicts(a.elab)
          if (bare !== null) {
            return { ty: applySubst(sub, cod), preds: [...fps], subst: sub, elab: { k: 'app', l: felab, r: bare } }
          }
        }
      }
      const u = unify(applySubst(a.subst, dom), applySubst(a.subst, a.ty), a.subst)
      return { ty: applySubst(u, cod), preds: [...fps, ...a.preds], subst: u, elab: { k: 'app', l: felab, r: a.elab } }
    }
    case 'infix': {
      // op l r  ==>  ((op l) r), with higher-rank domains instantiated.
      const o = inferExpr(env, e.op, subst)
      let oTy = applySubst(o.subst, o.ty)
      let ops: GPred[] = [...o.preds]
      if (oTy.k === 'forall') {
        const inst = instForallSigma(oTy.tvs, oTy.preds, oTy.ty)
        oTy = inst.ty
        ops.push(...inst.preds)
      }
      let dom1: GType
      let cod1: GType
      let cur0 = o.subst
      const arr1 = matchArrow(oTy)
      if (arr1 !== null) {
        dom1 = arr1[0]
        cod1 = arr1[1]
      } else if (oTy.k === 'meta') {
        dom1 = tMeta()
        cod1 = tMeta()
        cur0 = unify(oTy, tArrow(dom1, cod1), cur0)
      } else {
        throw gTypeError(`Couldn't match type \`${showType(oTy)}\` with \`? -> ?\``)
      }
      const l = inferExpr(env, e.l, cur0)
      const u1 = unify(applySubst(l.subst, dom1), applySubst(l.subst, l.ty), l.subst)
      let mid = applySubst(u1, cod1)
      let mps: GPred[] = []
      if (mid.k === 'forall') {
        const inst = instForallSigma(mid.tvs, mid.preds, mid.ty)
        mid = inst.ty
        mps = inst.preds
      }
      let dom2: GType
      let cod2: GType
      let cur1 = u1
      const arr2 = matchArrow(mid)
      if (arr2 !== null) {
        dom2 = arr2[0]
        cod2 = arr2[1]
      } else if (mid.k === 'meta') {
        dom2 = tMeta()
        cod2 = tMeta()
        cur1 = unify(mid, tArrow(dom2, cod2), cur1)
      } else {
        throw gTypeError(`Couldn't match type \`${showType(mid)}\` with \`? -> ?\``)
      }
      const r = inferExpr(env, e.r, cur1)
      const u2 = unify(applySubst(r.subst, dom2), applySubst(r.subst, r.ty), r.subst)
      return { ty: applySubst(u2, cod2), preds: [...ops, ...l.preds, ...mps, ...r.preds], subst: u2, elab: { k: 'infix', l: l.elab, op: o.elab, r: r.elab } }
    }
    case 'tuple': {
      let cur = subst
      const tys: GType[] = []
      let preds: GPred[] = []
      const els: GExpr[] = []
      for (const x of e.exprs) {
        const ri = inferExpr(env, x, cur)
        cur = ri.subst
        tys.push(ri.ty)
        preds.push(...ri.preds)
        els.push(ri.elab)
      }
      return { ty: tTupleOf(tys), preds, subst: cur, elab: { k: 'tuple', exprs: els } }
    }
    case 'if': {
      const c = inferExpr(env, e.c, subst)
      const u0 = unify(applySubst(c.subst, c.ty), tBool(), c.subst)
      const t = inferExpr(env, e.t, u0)
      const f = inferExpr(env, e.e, t.subst)
      const u = unify(applySubst(f.subst, t.ty), f.ty, f.subst)
      return { ty: applySubst(u, f.ty), preds: [...c.preds, ...t.preds, ...f.preds], subst: u, elab: { k: 'if', c: c.elab, t: t.elab, e: f.elab } }
    }
    case 'let': {
      const ld = inferDecls(env, e.decls, subst)
      const b = inferExpr(ld.env, e.body, ld.subst)
      return { ty: b.ty, preds: [...ld.preds, ...b.preds], subst: b.subst, elab: { k: 'let', decls: ld.elabDecls, body: b.elab } }
    }
    case 'ann': {
      // Instantiate the annotation and unify: the elaborated expression
      // keeps the annotation's predicates for dictionary resolution.
      const inst = instSigma(e.sigma, { n: 0 })
      const got = inferExpr(env, e.expr, subst)
      const u = unify(applySubst(got.subst, got.ty), applySubst(got.subst, inst.ty), got.subst)
      return { ty: applySubst(u, inst.ty), preds: [...got.preds, ...inst.preds], subst: u, elab: got.elab }
    }
    case 'case': {
      const s = inferExpr(env, e.expr, subst)
      let cur = s.subst
      let resTy: GType | null = null
      let preds: GPred[] = [...s.preds]
      const alts: GMatch[] = []
      for (const m of e.alts) {
        if (m.pats.length !== 1) throw gTypeError('case alternatives must have exactly one pattern')
        const pr = inferPat(env, m.pats[0]!, applySubst(cur, s.ty), cur)
        const ext = new Map(env.types)
        for (const [n, t] of pr.binds) ext.set(n, sigmaOf([], [], applySubst(pr.subst, t)))
        const env2: GInferEnv = { ...env, types: ext }
        const br = inferExpr(env2, m.rhs, pr.subst)
        cur = br.subst
        preds.push(...pr.preds, ...br.preds)
        alts.push({ pats: m.pats, rhs: br.elab })
        if (resTy === null) resTy = br.ty
        else cur = unify(applySubst(cur, resTy), br.ty, cur)
      }
      if (resTy === null) throw gTypeError('empty case')
      return { ty: applySubst(cur, resTy), preds, subst: cur, elab: { k: 'case', expr: s.elab, alts } }
    }
    case 'hole': {
      throw gTypeError(`Found holes: ${e.name}  |  []`)
    }
  }
}

function skolemize(sigma: GSigma): { ty: GType; preds: GPred[] } {
  // Replace quantified vars with fresh rigid names.
  const m: GSubst = new Map()
  for (const tv of sigma.tvs) m.set(tv.name, { k: 'var', v: { name: `${tv.name}#sk`, kind: tv.kind } })
  return { ty: applySubst(m, sigma.q.ty), preds: sigma.q.preds.map((p) => applySubstPred(m, p)) }
}

let gSkolemCounter = 0
function skolemizeFresh(tvs: GTV[], preds: GPred[], ty: GType): { ty: GType; preds: GPred[] } {
  // Skolemize a nested forall with globally fresh rigid names.
  const m: GSubst = new Map()
  for (const tv of tvs) {
    gSkolemCounter++
    m.set(tv.name, { k: 'var', v: { name: `${tv.name}#sk${gSkolemCounter}`, kind: tv.kind } })
  }
  return { ty: applySubst(m, ty), preds: preds.map((p) => applySubstPred(m, p)) }
}

export function inferDecls(
  env: GInferEnv, decls: GDecl[], subst: GSubst,
): { env: GInferEnv; subst: GSubst; preds: GPred[]; elabDecls: GDecl[]; scopes: Map<string, GPred[]> } {
  // Only bindings carry types here; data/class/instance handled by caller.
  const sigs = new Map<string, GSigma>()
  for (const d of decls) if (d.k === 'sig') sigs.set(d.name, d.sigma)
  let cur = subst
  const types = new Map(env.types)
  const shared: GPred[] = []
  const scopes = new Map<string, GPred[]>()
  // Pre-allocate metas for recursive bindings without sigs.
  const metas = new Map<string, GType>()
  for (const d of decls) {
    if (d.k === 'binding' && !sigs.has(d.name)) {
      const m = tMeta()
      metas.set(d.name, m)
      types.set(d.name, sigmaOf([], [], m))
    } else if (d.k === 'binding' && sigs.has(d.name)) {
      types.set(d.name, sigs.get(d.name)!)
    }
  }
  const envWithMetas: GInferEnv = { ...env, types }
  const elabDecls: GDecl[] = []
  for (const d of decls) {
    if (d.k === 'sig' || d.k === 'fixity') {
      elabDecls.push(d)
      continue
    }
    if (d.k !== 'binding') continue
    const sig = sigs.get(d.name)
    if (sig !== undefined) {
      // Check each alternative against the signature, binding patterns
      // against the (instantiated) domain types so higher-rank parameters
      // keep their polymorphic types.
      const sk = skolemize(sig)
      const elabAlts: GMatch[] = []
      for (const alt of d.alts) {
        try {
          let e: GInferEnv = { ...envWithMetas, types: new Map(envWithMetas.types) }
          let restTy = applySubst(cur, sk.ty)
          for (const p of alt.pats) {
            restTy = applySubst(cur, restTy)
            if (restTy.k === 'forall') {
              // Bare nested forall with patterns remaining: skolemize it
              // with fresh rigids so each parameter gets a monomorphic
              // (rigid) type; assumed predicates are discharged.
              const sk2 = skolemizeFresh(restTy.tvs, restTy.preds, restTy.ty)
              restTy = sk2.ty
              // Fall through to arrow peeling below.
            }
            let dom: GType
            const arr = matchArrow(restTy)
            if (arr !== null) {
              dom = arr[0]
              restTy = arr[1]
            } else if (restTy.k === 'meta') {
              dom = tMeta()
              const cod = tMeta()
              cur = unify(restTy, tArrow(dom, cod), cur)
              restTy = cod
            } else {
              throw gTypeError(`Couldn't match type \`${showType(restTy)}\` with \`? -> ?\``)
            }
            const pr = inferPat(e, p, dom, cur)
            cur = pr.subst
            for (const [n, t] of pr.binds) e.types.set(n, sigmaOf([], [], applySubst(cur, t)))
          }
          const got = inferExpr(e, alt.rhs, cur)
          cur = got.subst
          cur = unify(applySubst(cur, got.ty), applySubst(cur, restTy), cur)
          elabAlts.push({ pats: alt.pats, rhs: got.elab })
        } catch (err) {
          throw gTypeError(`${d.name}: ${err instanceof Error ? err.message : String(err)}`)
        }
      }
      types.set(d.name, sig)
      scopes.set(d.name, sk.preds)
      elabDecls.push({ k: 'binding', name: d.name, alts: elabAlts })
    } else {
      const m = metas.get(d.name)!
      // Infer each alt, unify with m.
      const elabAlts: GMatch[] = []
      const local: GPred[] = []
      for (const alt of d.alts) {
        try {
        let e: GInferEnv = { ...envWithMetas, types: new Map(envWithMetas.types) }
        const argTys: GType[] = []
        for (const p of alt.pats) {
          const pt = tMeta()
          argTys.push(pt)
          const pr = inferPat(e, p, pt, cur)
          cur = pr.subst
          for (const [n, t] of pr.binds) e.types.set(n, sigmaOf([], [], applySubst(cur, t)))
          local.push(...pr.preds)
        }
        const got = inferExpr(e, alt.rhs, cur)
        cur = got.subst
        local.push(...got.preds)
        let fn = applySubst(cur, got.ty)
        for (let i = argTys.length - 1; i >= 0; i--) fn = tArrow(applySubst(cur, argTys[i]!), fn)
        cur = unify(applySubst(cur, m), fn, cur)
        elabAlts.push({ pats: alt.pats, rhs: got.elab })
        } catch (err) {
          throw gTypeError(`${d.name}: ${err instanceof Error ? err.message : String(err)}`)
        }
      }
      elabDecls.push({ k: 'binding', name: d.name, alts: elabAlts })
      scopes.set(d.name, local)
    }
  }
  // Generalize implicits.
  for (const d of decls) {
    if (d.k !== 'binding' || sigs.has(d.name)) continue
    const local = scopes.get(d.name) ?? []
    const m = applySubst(cur, metas.get(d.name)!)
    const gen = generalizeWith({ ...env, types }, local, m, cur, d.name)
    types.set(d.name, gen.sigma)
    cur = gen.subst
    scopes.set(d.name, gen.sigma.q.preds)
    shared.push(...local)
  }
  return { env: { ...env, types }, subst: cur, preds: shared, elabDecls, scopes }
}

function generalizeWith(
  env: GInferEnv, preds: GPred[], ty: GType, subst: GSubst, exclude?: string,
): { sigma: GSigma; subst: GSubst } {
  const p2 = nubPreds(preds.map((p) => applySubstPred(subst, p)))
  const t2 = applySubst(subst, ty)
  const envMetas = new Set<string>()
  for (const [n, s] of env.types) {
    if (n === exclude) continue
    const tq = s.q.ty
    for (const m of freeMetas(applySubst(subst, tq))) envMetas.add(m)
    for (const p of s.q.preds) for (const m of freeMetas(applySubst(subst, p.ty))) envMetas.add(m)
  }
  const ft = freeMetas(t2)
  const fp = new Set<string>()
  for (const p of p2) for (const m of freeMetas(p.ty)) fp.add(m)
  const all = new Set([...ft, ...fp])
  for (const m of envMetas) all.delete(m)
  const tvs: GTV[] = [...all].map((m) => ({ name: m, kind: { k: 'star' } }) as GTV)
  const m2: GSubst = new Map()
  for (const m of all) m2.set(m, { k: 'var', v: { name: m, kind: { k: 'star' } } })
  const sigma: GSigma = { tvs, q: { preds: p2.map((p) => applySubstPred(m2, p)), ty: applySubst(m2, t2) } }
  // Record the renaming so elaborated occurrences resolve to generalized names.
  return { sigma, subst: composeSubst(m2, subst) }
}

// __PART13_ENGINE__
// Program loading + REPL engine (mirrors REPL.Load/Repl with demo :load).

const GLASK_STEP_BUDGET = 200000

export function renameForDisplay(sigma: GSigma): GSigma {
  const names = 'abcdefghijklmnopqrstuvwxyz'
  const map = new Map<string, string>()
  let n = 0
  const freshName = (): string => {
    const base = names[n % 26]!
    const suffix = n >= 26 ? String(Math.floor(n / 26)) : ''
    n++
    return base + suffix
  }
  for (const tv of sigma.tvs) {
    if (!map.has(tv.name)) map.set(tv.name, freshName())
  }
  const rn = (t: GType): GType => {
    if (t.k === 'var') {
      const nn = map.get(t.v.name)
      if (nn !== undefined) return { k: 'var', v: { name: nn, kind: t.v.kind } }
      return t
    }
    if (t.k === 'meta') {
      const nn = map.get(t.v.name)
      if (nn !== undefined) return { k: 'var', v: { name: nn, kind: t.v.kind } }
      return t
    }
    if (t.k === 'con') return t
    if (t.k === 'tuple') return { k: 'tuple', tys: t.tys.map(rn) }
    if (t.k === 'app') return { k: 'app', l: rn(t.l), r: rn(t.r) }
    return { k: 'forall', tvs: t.tvs, preds: t.preds.map((p) => ({ cls: p.cls, ty: rn(p.ty) })), ty: rn(t.ty) }
  }
  return {
    tvs: sigma.tvs.map((tv) => ({ name: map.get(tv.name) ?? tv.name, kind: tv.kind })),
    q: { preds: sigma.q.preds.map((p) => ({ cls: p.cls, ty: rn(p.ty) })), ty: rn(sigma.q.ty) },
  }
}

export function showCore(c: GCore): string {
  switch (c.k) {
    case 'var': return c.name
    case 'prim': return `(${c.name})`
    case 'lit': return showLit(c.lit)
    case 'abs': return `(\\ ${c.param} -> ${showCore(c.body)})`
    case 'app': {
      const r = c.arg
      if (r.k === 'app') return `${showCore(c.fn)} (${showCore(r)})`
      return `${showCore(c.fn)} ${showCore(r)}`
    }
    case 'tuple': return `(${c.args.map(showCore).join(', ')})`
    case 'intro':
      if (c.args.length === 0) return c.tag
      return `(Intro ${c.tag} ${c.args.map(showCore).join(' ')})`
    case 'case': return `case ${showCore(c.motive)} of\n${c.matches.map((m) => `  ${m.pats.map(showPat).join(' ')} -> ${showCore(m.rhs)}`).join('\n')}`
    case 'let': return `let ${c.binds.map((b) => `${b.name} = ${showCore(b.lambda)}`).join('; ')} in ${showCore(c.body)}`
    case 'err': return `Error ${c.msg}`
  }
}

function inferKindOf(t: GType): GKind {
  const star: GKind = { k: 'star' }
  // Best-effort: variables and constructors default to *; arrows compose.
  void t
  return star
}

async function serializeString(
  v: GValue, store: GStore, ctl: GEvalCtl, disp: GDispatchTable,
): Promise<string> {
  if (v.k !== 'data' || v.tag !== 'String' || v.args.length !== 1) {
    throw new GEvalError('Weird - when serializing, I got something that is not a list.')
  }
  const list = await gForce(v.args[0]!, store, ctl, disp)
  const chars: string[] = []
  let cur = list
  for (let i = 0; i < 100000; i++) {
    tick(ctl)
    if (cur.k !== 'data') throw new GEvalError('Weird - when serializing, I got something that is not a list.')
    if (cur.tag === '[]') return chars.join('')
    if (cur.tag !== ':' || cur.args.length !== 2) throw new GEvalError('Weird - when serializing, I got something that is not a list.')
    const h = await gForce(cur.args[0]!, store, ctl, disp)
    if (h.k !== 'lit' || h.lit.k !== 'char') throw new GEvalError('Weird - when serializing, I got a list containing non-char.')
    chars.push(h.lit.v)
    cur = await gForce(cur.args[1]!, store, ctl, disp)
  }
  throw new GEvalError('String too long')
}

const GLASK_IMMEDIATE = /^(:(exit|load |q|Q))/

export class GlaskEngine implements Engine {
  readonly id = 'glask'
  private files = new Map<string, string>()
  private editorContent = ''
  private buf: string[] | null = null
  private ctl: GEvalCtl = { abort: false, ops: 0, budget: GLASK_STEP_BUDGET }
  private counter = 0
  private transEnv: TransEnv | null = null
  private program: GProgram | null = null
  private env: GEnv = new Map()
  private store: GStore = new Map()

  constructor(preludeSrc?: string) {
    if (preludeSrc !== undefined && preludeSrc.trim() !== '') {
      try {
        this.loadModule(preludeSrc, 'prelude.glask')
      } catch (e) {
        console.error('Glask prelude failed to load:', e)
        this.resetState()
      }
    }
  }

  banner(): string {
    return 'Glamorous Glask REPL.\n'
  }
  prompt(): string {
    return this.buf !== null ? '         ' : 'glask λ > '
  }
  editorAliases(): string[] {
    return ['editor.glask', 'demo.glask', 'editor', 'demo']
  }
  provideFile(name: string, content: string): void {
    this.files.set(name, content)
  }
  dropFile(name: string): void {
    this.files.delete(name)
  }
  setEditorContent(content: string): void {
    this.editorContent = content
  }
  restart(): void {
    this.buf = null
    this.resetState()
  }
  interrupt(): void {
    this.ctl.abort = true
  }

  private resetState(): void {
    this.counter = 0
    this.transEnv = null
    this.program = null
    this.env = new Map()
    this.store = new Map()
    resetMetaCounter()
  }

  private freshTrState(): TrState {
    return { counter: this.counter }
  }

  private syncCounter(st: TrState): void {
    this.counter = st.counter
  }

  private loadModule(src: string, _name: string): void {
    const normalized = src.replace(/\r\n?/g, '\n')
    const termDecls = parseGlaskModule(normalized)
    const st = this.freshTrState()
    const env = buildTransEnv(termDecls, st)
    this.syncCounter(st)
    doSemanticAnalysis(termDecls, env)
    const st2 = this.freshTrState()
    const decls = translateProgram(termDecls, env, st2)
    this.syncCounter(st2)
    const program = inferWholeProgram(decls)
    // Build runtime env/store (mirrors build'env'store).
    const allBindings = program.coreBindings
    const store: GStore = new Map()
    const menv: GEnv = new Map()
    const base = 0
    allBindings.forEach((b, i) => menv.set(b.name, { addr: base + i }))
    allBindings.forEach((b, i) => store.set(base + i, { k: 'thunk', core: b.lambda, env: menv }))
    // Method dispatchers (unless shadowed by a user binding).
    for (const m of program.dispatch.methods) {
      if (!menv.has(m)) {
        const addr = store.size
        store.set(addr, { k: 'value', value: { k: 'dispatch', method: m } })
        menv.set(m, { addr })
      }
    }
    program.dispatch.implEnv = menv
    this.transEnv = env
    this.program = program
    this.env = menv
    this.store = store
  }

  async handle(rawLine: string): Promise<EngineResult> {
    const line = rawLine.replace(/\r$/, '')
    this.ctl = { abort: false, ops: 0, budget: GLASK_STEP_BUDGET }
    const ctl = this.ctl
    if (this.buf !== null) {
      if (line === '' || GLASK_IMMEDIATE.test(line)) {
        const text = [...this.buf, line].join('\n')
        this.buf = null
        return this.process(text, ctl)
      }
      this.buf.push(line)
      return { output: '' }
    }
    if (line === '') return { output: '' }
    if (GLASK_IMMEDIATE.test(line)) return this.process(line, ctl)
    this.buf = [line]
    return { output: '' }
  }

  private async process(text: string, ctl: GEvalCtl): Promise<EngineResult> {
    if (text === '') return { output: '' }
    if (text === ':exit' || text === ':q' || text === ':Q') return { output: 'Bye!', halted: true }
    if (text.startsWith(':load ')) return this.loadCmd(text.slice(6).trim(), ctl)
    if (text.startsWith(':t')) return this.typeCmd(text.slice(2))
    if (text.startsWith(':p')) return this.parsedCmd(text.slice(2))
    if (text.startsWith(':k')) return this.kindCmd(text.slice(2))
    if (text.startsWith(':c')) return this.coreCmd(text.slice(2))
    if (text.startsWith(':d')) return this.desugarCmd(text.slice(2))
    if (text.startsWith(':f')) return this.storeCmd(text.slice(2), ctl)
    return this.exprCmd(text, ctl)
  }

  private readExprTrans(src: string): { expr: GExpr; transEnv: TransEnv } {
    const tenv = this.transEnv ?? buildTransEnv([], this.freshTrState())
    const st = this.freshTrState()
    const ctx = new TrCtx(tenv, st)
    const term = parseGlaskExpr(src)
    // Flat application fast path is inside trExpr; reuse full translation.
    const toks0 = term.k === 'app'
      ? term.exprs.map((t) => gsyaToTokenExpr(t, tenv.fixities))
      : null
    void toks0
    const expr = trExpr(term, ctx)
    this.syncCounter(st)
    return { expr, transEnv: tenv }
  }

  private readTypeTrans(src: string): GType {
    const tenv = this.transEnv ?? buildTransEnv([], this.freshTrState())
    const st = this.freshTrState()
    const ctx = new TrCtx(tenv, st)
    const term = parseGlaskType(src)
    const ty = trType(term, ctx)
    this.syncCounter(st)
    return ty
  }

  private programEnv(): GInferEnv {
    if (this.program !== null) return this.program.typeEnv
    return { types: builtinTypeEnv(), classes: new Map(), instances: [], methods: new Map() }
  }

  private typeCmd(rest: string): Promise<EngineResult> {
    const line = rest.trim()
    if (line === '') return Promise.resolve({ output: 'Incorrect Format! The :t command must be followed by an expression.' })
    let expr: GExpr
    try {
      expr = this.readExprTrans(line).expr
    } catch (e) {
      return Promise.resolve({ output: `Error: ${e instanceof GTranslateError ? showSemError(e.err) : String(e)}` })
    }
    try {
      const env = this.programEnv()
      const r = inferExpr(env, expr, new Map())
      const simp = simplify(env, r.preds)
      const gen = generalize(env, simp, applySubst(r.subst, r.ty), r.subst)
      const shown = showSigma(renameForDisplay(gen))
      return Promise.resolve({ output: `          ${line} :: ${shown}` })
    } catch (e) {
      return Promise.resolve({ output: `Type Error: ${e instanceof Error ? e.message : String(e)}` })
    }
  }

  private parsedCmd(rest: string): Promise<EngineResult> {
    const line = rest.trim()
    if (line === '') return Promise.resolve({ output: 'Incorrect Format! The :p command must be followed by an expression.' })
    try {
      const { expr } = this.readExprTrans(line)
      return Promise.resolve({ output: `Parsed: ${showExpr(expr)}` })
    } catch (e) {
      return Promise.resolve({ output: `Error: ${e instanceof GTranslateError ? showSemError(e.err) : String(e)}` })
    }
  }

  private kindCmd(rest: string): Promise<EngineResult> {
    const line = rest.trim()
    if (line === '') return Promise.resolve({ output: 'Incorrect Format! The :k command must be followed by an type exression.' })
    try {
      const ty = this.readTypeTrans(line)
      const k = inferKindOf(ty)
      return Promise.resolve({ output: `          ${line} :: ${showKind(k)}` })
    } catch (e) {
      if (e instanceof GTranslateError) return Promise.resolve({ output: `Error: ${showSemError(e.err)}` })
      return Promise.resolve({ output: `Error: ${e instanceof Error ? e.message : String(e)}` })
    }
  }

  private progTable(): RTable {
    return this.program?.table ?? { instances: [], classOrder: new Map(), methodClass: new Map() }
  }

  /** Infer, default, and resolve dictionaries for a REPL expression. */
  private inferResolve(line: string): GExpr {
    const { expr } = this.readExprTrans(line)
    const env = this.programEnv()
    const table = this.progTable()
    const r = inferExpr(env, expr, new Map())
    const simp = simplify(env, r.preds)
    const ty0 = applySubst(r.subst, r.ty)
    const fixed = new Set<string>()
    for (const v of freeRigids(ty0)) fixed.add(v)
    const { subst: dSubst, preds: rest } = tryDefault(env, simp.map((p) => applySubstPred(r.subst, p)), fixed)
    const subst = composeSubst(dSubst, r.subst)
    const stillAmb = ambiguousVars(rest.map((p) => applySubstPred(subst, p)), fixed)
    if (stillAmb.length > 0) {
      const [a] = stillAmb as [{ v: string; qs: GPred[] }]
      if (a !== undefined) {
        throw gTypeError(`Semantic Error: Ambiguous type: \`${a.qs.map(showPred).join(', ')} => ?\``)
      }
    }
    return resolveExpr(r.elab, subst, { preds: [], vars: [] }, table)
  }

  private coreCmd(rest: string): Promise<EngineResult> {
    const line = rest.trim()
    try {
      const elab = this.inferResolve(line)
      const core = toCore(elab)
      return Promise.resolve({ output: `Core:\n${showCore(core)}` })
    } catch (e) {
      if (e instanceof GTranslateError) return Promise.resolve({ output: `Error: ${showSemError(e.err)}` })
      return Promise.resolve({ output: `Type Error: ${e instanceof Error ? e.message : String(e)}` })
    }
  }

  private desugarCmd(rest: string): Promise<EngineResult> {
    const line = rest.trim()
    try {
      const elab = this.inferResolve(line)
      return Promise.resolve({ output: `Desugared:\n${showExpr(elab)}` })
    } catch (e) {
      if (e instanceof GTranslateError) return Promise.resolve({ output: `Error: ${showSemError(e.err)}` })
      return Promise.resolve({ output: `Type Error: ${e instanceof Error ? e.message : String(e)}` })
    }
  }

  private async storeCmd(rest: string, ctl: GEvalCtl): Promise<EngineResult> {
    const n = parseInt(rest.trim(), 10)
    if (!Number.isInteger(n)) return { output: 'Incorrect Format! The :f command must be followed by a promise number.' }
    const cell = this.store.get(n)
    if (cell === undefined) return { output: `Unknown promise ${n}` }
    try {
      if (cell.k === 'value') {
        const s = await gShowValue(cell.value, this.store, ctl, this.program?.dispatch ?? { methods: new Set(), instances: [], ctorToType: new Map(), implEnv: new Map() })
        return { output: s }
      }
      if (cell.k === 'thunk') return { output: showCore(cell.core) }
      return { output: 'blackhole' }
    } catch (e) {
      if (e instanceof GInterrupted) return { output: 'Interrupted.', interrupted: true }
      return { output: `Evaluation Error: ${e instanceof Error ? e.message : String(e)}` }
    }
  }

  private async exprCmd(text: string, ctl: GEvalCtl): Promise<EngineResult> {
    // Mirror upstream: evaluate show (<text>), then serialize the String.
    // Elaboration resolves dictionaries statically (no runtime dispatch).
    let elab: GExpr
    try {
      const inner = this.readExprTrans(text).expr
      const showVar: GExpr = { k: 'var', name: 'show' }
      const wrapped: GExpr = { k: 'app', l: showVar, r: inner }
      const env = this.programEnv()
      const table = this.progTable()
      const r = inferExpr(env, wrapped, new Map())
      const simp = simplify(env, r.preds)
      const ty0 = applySubst(r.subst, r.ty)
      const fixed = new Set<string>()
      for (const v of freeRigids(ty0)) fixed.add(v)
      const { subst: dSubst, preds: rest } = tryDefault(env, simp.map((p) => applySubstPred(r.subst, p)), fixed)
      const subst = composeSubst(dSubst, r.subst)
      const stillAmb = ambiguousVars(rest.map((p) => applySubstPred(subst, p)), fixed)
      if (stillAmb.length > 0) {
        const [a] = stillAmb as [{ v: string; qs: GPred[] }]
        if (a !== undefined) {
          throw gTypeError(`Semantic Error: Ambiguous type: \`${a.qs.map(showPred).join(', ')} => ?\``)
        }
      }
      elab = resolveExpr(r.elab, subst, { preds: [], vars: [] }, table)
    } catch (e) {
      if (e instanceof GTranslateError) return { output: `Error: ${showSemError(e.err)}` }
      return { output: `Type Error: ${e instanceof Error ? e.message : String(e)}` }
    }
    try {
      const disp = this.program?.dispatch ?? { methods: new Set(), instances: [], ctorToType: new Map(), implEnv: this.env }
      const core = toCore(elab)
      const v = await gEval(core, this.env, this.store, ctl, disp)
      const s = await serializeString(v, this.store, ctl, disp)
      await yieldToUI()
      return { output: `          ${s}` }
    } catch (e) {
      if (e instanceof GInterrupted || (e instanceof Error && ctl.abort)) {
        return { output: 'Interrupted.', interrupted: true }
      }
      if (e instanceof GEvalError) return { output: `Evaluation Error: ${e.message}` }
      return { output: `Evaluation Error: ${e instanceof Error ? e.message : String(e)}` }
    }
  }

  private async loadCmd(file: string, _ctl: GEvalCtl): Promise<EngineResult> {
    const content =
      this.files.get(file) ??
      this.files.get(file.split('/').pop()!) ??
      (this.editorAliases().includes(file) || this.editorAliases().includes(file.split('/').pop()!) ? this.editorContent : undefined)
    if (content === undefined) return { output: `Error: cannot open ${file}: file not found.` }
    // Try module parse first (upstream programs start with `module ... where`);
    // fall back to bare declarations.
    let termDecls: TermDecl[]
    try {
      termDecls = parseGlaskModule(content)
    } catch (e) {
      return { output: `Parse error inside module ${file}: ${e instanceof Error ? e.message : String(e)}` }
    }
    const prevTrans = this.transEnv
    const prevProg = this.program
    const prevEnv = this.env
    const prevStore = this.store
    const prevCounter = this.counter
    try {
      this.resetState()
      this.counter = prevCounter
      this.loadModule(content, file)
      void prevTrans
      void prevProg
      void prevEnv
      void prevStore
      return { output: '' }
    } catch (e) {
      // Restore previous program on failure.
      this.transEnv = prevTrans
      this.program = prevProg
      this.env = prevEnv
      this.store = prevStore
      this.counter = prevCounter
      if (e instanceof GTranslateError) return { output: `Error inside module ${file}: ${showSemError(e.err)}` }
      return { output: `Error inside module ${file}: ${e instanceof Error ? e.message : String(e)}` }
    }
  }
}

// __PART12_PROGRAM__
// Whole-program inference (best-effort) + runtime assembly.

export interface GProgram {
  decls: GDecl[]
  typeEnv: GInferEnv
  subst: GSubst
  dispatch: GDispatchTable
  coreBindings: GCoreBinding[]
  ctorToType: Map<string, string>
  table: RTable
}

const NUM_CLASSES = new Set(['Num', 'Integral', 'Floating', 'Fractional', 'Real', 'RealFloat'])
const STD_CLASSES = new Set(['Eq', 'Ord', 'Show', 'Read', 'Bounded', 'Enum', 'Ix', 'Functor', 'Monad', 'MonadPlus', 'Num', 'Integral', 'Floating', 'Fractional', 'Real', 'RealFloat'])

function defaultPreds(
  env: GInferEnv, preds: GPred[], subst: GSubst,
): { subst: GSubst; preds: GPred[] } {
  // Find ambiguous vars (in preds but not in type env range / types).
  // Caller passes all preds + a way to know fixed vars; here we approximate:
  // ambiguous = vars appearing in preds but not in any type env entry's free vars.
  void env
  void subst
  return { subst, preds }
}

function ambiguousVars(preds: GPred[], fixed: Set<string>): Array<{ v: string; qs: GPred[] }> {
  const inPreds = new Map<string, GPred[]>()
  const isSkolem = (v: string): boolean => v.includes('#sk')
  for (const p of preds) {
    for (const v of freeRigids(p.ty)) {
      // Skolem constants (assumed during higher-rank checking) are givens,
      // never ambiguous.
      if (isSkolem(v)) continue
      if (!fixed.has(v)) {
        const l = inPreds.get(v) ?? []
        l.push(p)
        inPreds.set(v, l)
      }
    }
    for (const v of freeMetas(p.ty)) {
      if (!fixed.has(v)) {
        const l = inPreds.get(v) ?? []
        l.push(p)
        inPreds.set(v, l)
      }
    }
  }
  return [...inPreds.entries()].map(([v, qs]) => ({ v, qs }))
}

function tryDefault(env: GInferEnv, preds: GPred[], fixed: Set<string>): { subst: GSubst; preds: GPred[] } {
  let subst: GSubst = new Map()
  let rest = [...preds]
  const ambs = ambiguousVars(preds, fixed)
  for (const { v, qs } of ambs) {
    const is = qs.map((q) => q.cls)
    if (!is.some((c) => NUM_CLASSES.has(c))) continue
    if (!is.every((c) => STD_CLASSES.has(c))) continue
    // All preds on same var?
    if (!qs.every((q) => {
      const ms = new Set([...freeMetas(q.ty), ...freeRigids(q.ty)])
      return ms.size === 1 && ms.has(v)
    })) continue
    // Candidates: Int then Double (mirrors defaults [t'Int, t'Double]).
    let done = false
    for (const cand of [tInt(), tDouble()]) {
      const s1: GSubst = new Map([[v, cand]])
      const inst = qs.map((q) => applySubstPred(s1, q))
      if (inst.every((q) => entails(env, q))) {
        subst = composeSubst(s1, subst)
        rest = rest.filter((p) => !qs.includes(p))
        done = true
        break
      }
    }
    void done
  }
  return { subst, preds: rest }
}

function composeSubst(a: GSubst, b: GSubst): GSubst {
  const out = new Map<string, GType>()
  for (const [k, v] of b) out.set(k, applySubst(a, v))
  for (const [k, v] of a) out.set(k, v)
  return out
}

// __PART14_RESOLVE__
// Dictionary elaboration (upstream: dictionary-passing via placeholders).
// Overloaded definitions take extra dictionary parameters (prepended as
// leading value patterns); overloaded uses are applied to dictionaries
// resolved from enclosing scope or built from instances.

let gDictCounter = 0
function freshDictVar(): string {
  gDictCounter++
  return `__dd${gDictCounter}`
}

const OP_SANITIZE: Record<string, string> = {
  '+': '_plus_',
  '-': '_minus_',
  '*': '_star_',
  '/': '_slash_',
  '<': '_lt_',
  '>': '_gt_',
  '=': '_eq_',
  '!': '_bang_',
  '&': '_amp_',
  '|': '_bar_',
  '^': '_caret_',
  '%': '_pct_',
  '$': '_dollar_',
  '.': '_dot_',
  ':': '_colon_',
  '?': '_q_',
  '~': '_tilde_',
  '@': '_at_',
}

export function sanitizeName(s: string): string {
  let out = ''
  for (const ch of s) {
    if (/[A-Za-z0-9_]/.test(ch)) out += ch
    else if (ch in OP_SANITIZE) out += OP_SANITIZE[ch]
    else out += `_u${ch.codePointAt(0) ?? 0}_`
  }
  return out
}

export function mangledHead(ty: GType): string {
  return sanitizeName(showType(ty))
}

export function mangledMethod(cls: string, head: GType, method: string): string {
  return `d-${sanitizeName(cls)}-${mangledHead(head)}-${sanitizeName(method)}`
}

export function mangledBuilder(cls: string, head: GType): string {
  return `d-${sanitizeName(cls)}-${mangledHead(head)}`
}

export interface RTable {
  instances: Array<{ cls: string; head: GType; ctx: GPred[] }>
  classOrder: Map<string, string[]>
  methodClass: Map<string, string>
}

export interface RScope {
  preds: GPred[]
  vars: string[]
}

function hasMetas(t: GType): boolean {
  return freeMetas(t).size > 0
}

function tryUnify(a: GType, b: GType): boolean {
  try {
    unify(a, b, new Map())
    return true
  } catch {
    return false
  }
}

function scopeHit(scope: RScope, cls: string, ty: GType): number {
  for (let i = 0; i < scope.preds.length; i++) {
    const p = scope.preds[i]!
    if (p.cls !== cls) continue
    if (tryUnify(p.ty, ty)) return i
  }
  return -1
}

function dictProjExpr(dictVar: string, method: string, cls: string, table: RTable): GExpr {
  const order = table.classOrder.get(cls) ?? []
  const idx = order.indexOf(method)
  if (idx < 0) throw gTypeError(`Internal: method ${method} not in class ${cls}`)
  let cur: GExpr = { k: 'var', name: dictVar }
  for (let i = 0; i < idx; i++) cur = { k: 'app', l: { k: 'var', name: 'snd#' }, r: cur }
  if (order.length > 1 && idx < order.length - 1) cur = { k: 'app', l: { k: 'var', name: 'fst#' }, r: cur }
  return cur
}

function findInstance(
  table: RTable, cls: string, ty: GType,
): { inst: { cls: string; head: GType; ctx: GPred[] }; match: GSubst } | null {
  for (const inst of table.instances) {
    if (inst.cls !== cls) continue
    try {
      const m = matchHead(inst.head, ty, new Map())
      return { inst, match: m }
    } catch {
      continue
    }
  }
  return null
}

function buildDictExpr(
  cls: string, ty: GType, subst: GSubst, scope: RScope, table: RTable, depth = 0,
): GExpr {
  if (depth > 20) throw gTypeError(`No instance for ${cls} ${showType(applySubst(subst, ty))}`)
  const ty2 = applySubst(subst, ty)
  const si = !hasMetas(ty2) ? scopeHit(scope, cls, ty2) : -1
  if (si >= 0) return { k: 'var', name: scope.vars[si]! }
  if (hasMetas(ty2)) {
    throw gTypeError(`Semantic Error: Ambiguous type: \`${cls} ${showType(ty2)} => ?\``)
  }
  const found = findInstance(table, cls, ty2)
  if (found === null) throw gTypeError(`No instance for ${cls} ${showType(ty2)}`)
  const bName = mangledBuilder(cls, found.inst.head)
  let out: GExpr = { k: 'var', name: bName }
  for (const c of found.inst.ctx) {
    const cty = applySubst(found.match, c.ty)
    out = { k: 'app', l: out, r: buildDictExpr(c.cls, cty, subst, scope, table, depth + 1) }
  }
  return out
}

export function resolveExpr(
  e: GExpr, subst: GSubst, scope: RScope, table: RTable, dyn = false,
): GExpr {
  switch (e.k) {
    case 'var':
    case 'con':
    case 'op':
    case 'lit':
    case 'hole':
      return e
    case 'dict': {
      return buildDictExpr(e.cls, e.ty, subst, scope, table)
    }
    case 'mvar': {
      if (dyn) return { k: 'var', name: e.method }
      const ty2 = applySubst(subst, e.ty)
      if (!hasMetas(ty2)) {
        const si = scopeHit(scope, e.cls, ty2)
        if (si >= 0) {
          return dictProjExpr(scope.vars[si]!, e.method, e.cls, table)
        }
        const found = findInstance(table, e.cls, ty2)
        if (found !== null) {
          const mName = mangledMethod(e.cls, found.inst.head, e.method)
          let out: GExpr = { k: 'var', name: mName }
          for (const c of found.inst.ctx) {
            const cty = applySubst(found.match, c.ty)
            out = { k: 'app', l: out, r: buildDictExpr(c.cls, cty, subst, scope, table) }
          }
          return out
        }
      }
      // Dynamic fallback (documented): keep the method var for runtime dispatch.
      return { k: 'var', name: e.method }
    }
    case 'abs':
      return { k: 'abs', pat: e.pat, body: resolveExpr(e.body, subst, scope, table, dyn) }
    case 'app':
      return { k: 'app', l: resolveExpr(e.l, subst, scope, table, dyn), r: resolveExpr(e.r, subst, scope, table, dyn) }
    case 'infix':
      // Desugar to applications (mirrors upstream Infix'App elaboration).
      return {
        k: 'app',
        l: {
          k: 'app',
          l: resolveExpr(e.op, subst, scope, table, dyn),
          r: resolveExpr(e.l, subst, scope, table, dyn),
        } as GExpr,
        r: resolveExpr(e.r, subst, scope, table, dyn),
      }
    case 'tuple':
      return { k: 'tuple', exprs: e.exprs.map((x) => resolveExpr(x, subst, scope, table, dyn)) }
    case 'if':
      return {
        k: 'if', c: resolveExpr(e.c, subst, scope, table, dyn),
        t: resolveExpr(e.t, subst, scope, table, dyn), e: resolveExpr(e.e, subst, scope, table, dyn),
      }
    case 'let': {
      // Let-bound annotated bindings take dictionary parameters (like
      // top-level); implicit lets resolve against the current scope with
      // dynamic fallback for the rest.
      const sigs = new Map<string, GSigma>()
      for (const d of e.decls) if (d.k === 'sig') sigs.set(d.name, d.sigma)
      let cur: RScope = { preds: [...scope.preds], vars: [...scope.vars] }
      const newDecls: GDecl[] = []
      for (const d of e.decls) {
        if (d.k !== 'binding') {
          newDecls.push(d)
          continue
        }
        const sig = sigs.get(d.name)
        if (sig !== undefined) {
          const sk = skolemize(sig)
          const dvars = sk.preds.map(() => freshDictVar())
          const local: RScope = {
            preds: [...cur.preds, ...sk.preds],
            vars: [...cur.vars, ...dvars],
          }
          const alts = d.alts.map((m) => ({
            pats: [...dvars.map((v) => ({ k: 'var', name: v }) as GPat), ...m.pats],
            rhs: resolveExpr(m.rhs, subst, local, table, dyn),
          }))
          cur = {
            preds: [...cur.preds, ...sk.preds],
            vars: [...cur.vars, ...dvars],
          }
          newDecls.push({ k: 'binding', name: d.name, alts })
        } else {
          const alts = d.alts.map((m) => ({
            pats: m.pats,
            rhs: resolveExpr(m.rhs, subst, cur, table, dyn),
          }))
          newDecls.push({ k: 'binding', name: d.name, alts })
        }
      }
      return { k: 'let', decls: newDecls, body: resolveExpr(e.body, subst, cur, table, dyn) }
    }
    case 'ann':
      return { k: 'ann', expr: resolveExpr(e.expr, subst, scope, table, dyn), sigma: e.sigma }
    case 'case':
      return {
        k: 'case', expr: resolveExpr(e.expr, subst, scope, table, dyn),
        alts: e.alts.map((m) => ({ pats: m.pats, rhs: resolveExpr(m.rhs, subst, scope, table, dyn) })),
      }
  }
}

// Resolve a declaration list: elaborate dict abstraction for bindings with
// residual predicates (from scopes map or sigs), returning new decls plus the
// extended scope for subsequent uses.
export function resolveDecls(
  decls: GDecl[], subst: GSubst, scope: RScope, table: RTable,
  scopes: Map<string, GPred[]>,
): { decls: GDecl[]; scope: RScope } {
  const sigs = new Map<string, GSigma>()
  for (const d of decls) if (d.k === 'sig') sigs.set(d.name, d.sigma)
  let cur: RScope = { preds: [...scope.preds], vars: [...scope.vars] }
  const out: GDecl[] = []
  for (const d of decls) {
    if (d.k !== 'binding') {
      out.push(d)
      continue
    }
    const sig = sigs.get(d.name)
    // Dict parameters: sig preds for annotated (skolemized, matching the
    // checking-time namespace), generalized preds otherwise.
    const sktvs = sig !== undefined ? skolemize(sig) : null
    const preds = sktvs !== null ? sktvs.preds : (scopes.get(d.name) ?? [])
    const dvars = preds.map(() => freshDictVar())
    const local: RScope = {
      preds: [...cur.preds, ...preds.map((p) => applySubstPred(subst, p))],
      vars: [...cur.vars, ...dvars],
    }
    // Self-reference uses the extended scope (recursive bindings).
    const alts = d.alts.map((m) => ({
      pats: [...dvars.map((v) => ({ k: 'var', name: v }) as GPat), ...m.pats],
      rhs: resolveExpr(m.rhs, subst, local, table),
    }))
    cur = {
      preds: [...cur.preds, ...preds.map((p) => applySubstPred(subst, p))],
      vars: [...cur.vars, ...dvars],
    }
    out.push({ k: 'binding', name: d.name, alts })
  }
  return { decls: out, scope: cur }
}

export function inferWholeProgram(decls: GDecl[]): GProgram {
  resetMetaCounter()
  const types = builtinTypeEnv()
  const classes = new Map<string, { supers: string[]; param: string }>()
  const instances: Array<{ ctx: GPred[]; head: GPred }> = []
  const methodClass = new Map<string, string>()
  const methodNames = new Set<string>()
  const ctorToType = new Map<string, string>([
    ['True', 'Bool'], ['False', 'Bool'],
    ['[]', '[]'], [':', '[]'],
    ['()', '()'], ['(,)', '(,)'],
  ])
  // Data constructors.
  for (const d of decls) {
    if (d.k !== 'data') continue
    for (const [n, s] of ctorSigmaForData(d)) types.set(n, s)
    for (const c of d.ctors) ctorToType.set(c.name, d.name)
  }
  // Classes + methods.
  for (const d of decls) {
    if (d.k !== 'class') continue
    classes.set(d.name, { supers: d.supers.map((p) => p.cls), param: d.param })
    for (const m of d.decls) {
      if (m.k !== 'sig') continue
      methodNames.add(m.name)
      methodClass.set(m.name, d.name)
      types.set(m.name, m.sigma)
    }
  }
  // Instances (collect heads; method bodies elaborated below).
  const rawInstances: Array<{ cls: string; head: GType; ctx: GPred[]; methods: Map<string, GMatch[]> }> = []
  for (const d of decls) {
    if (d.k !== 'instance') continue
    instances.push({ ctx: d.ctx, head: d.head })
    const mm = new Map<string, GMatch[]>()
    for (const b of d.decls) {
      if (b.k !== 'binding') continue
      mm.set(b.name, b.alts)
    }
    rawInstances.push({ cls: d.head.cls, head: d.head.ty, ctx: d.ctx, methods: mm })
  }
  const env: GInferEnv = { types, classes, instances, methods: methodClass }
  // Bindings.
  const bindDecls = decls.filter((d) => d.k === 'binding' || d.k === 'sig')
  const checked = inferDecls(env, bindDecls, new Map())
  const env2 = checked.env
  let subst = checked.subst
  const topPreds = checked.preds
  const topScopes = checked.scopes
  const topElab = checked.elabDecls
  // Instance methods: check against expected types (class param := head).
  const instMethodElab = new Map<string, { alts: GMatch[]; resPreds: GPred[] }>()
  const instExtraPreds: GPred[] = []
  for (const inst of rawInstances) {
    const clInfo = classes.get(inst.cls)
    if (clInfo === undefined) throw gTypeError(`Unknown class ${inst.cls}`)
    for (const [mname, alts] of inst.methods) {
      const msig = types.get(mname)
      if (msig === undefined) throw gTypeError(`Unknown method ${mname}`)
      const exp = instMethodSigma(msig, clInfo.param, inst.cls, inst.head)
      const sk = skolemize(exp)
      let cur = subst
      const elabAlts: GMatch[] = []
      const local: GPred[] = []
      for (const alt of alts) {
        let e: GInferEnv = { ...env2, types: new Map(env2.types) }
        const argTys: GType[] = []
        for (const p of alt.pats) {
          const pt = tMeta()
          argTys.push(pt)
          const pr = inferPat(e, p, pt, cur)
          cur = pr.subst
          for (const [n, t] of pr.binds) e.types.set(n, sigmaOf([], [], applySubst(cur, t)))
          local.push(...pr.preds)
        }
        const got = inferExpr(e, alt.rhs, cur)
        cur = got.subst
        local.push(...got.preds)
        let fn = applySubst(cur, got.ty)
        for (let i = argTys.length - 1; i >= 0; i--) fn = tArrow(applySubst(cur, argTys[i]!), fn)
        cur = unify(fn, sk.ty, cur)
        elabAlts.push({ pats: alt.pats, rhs: got.elab })
      }
      subst = cur
      // Residuals must follow from the instance context (or ground instances).
      const res = nubPreds(local.map((p) => applySubstPred(subst, p)))
      const kept: GPred[] = []
      for (const rp of res) {
        if (entails(env2, rp)) continue
        if (inst.ctx.some((c) => tryUnify(applySubst(subst, c.ty), applySubst(subst, rp.ty)) && c.cls === rp.cls)) {
          kept.push(rp)
          continue
        }
        if (hasMetas(applySubst(subst, rp.ty))) {
          kept.push(rp)
          continue
        }
        throw gTypeError('Context is too weak')
      }
      instExtraPreds.push(...local)
      const key = `${inst.cls} ${showType(inst.head)} ${mname}`
      void key
      instMethodElab.set(mangledMethod(inst.cls, inst.head, mname), { alts: elabAlts, resPreds: kept })
    }
  }
  void instMethodElab
  // Fixed vars = free rigids in inferred types (predicates do not count:
  // a variable occurring only in predicates is a defaulting candidate).
  const fixed = new Set<string>()
  for (const [, s] of env2.types) {
    for (const v of freeRigids(applySubst(subst, s.q.ty))) fixed.add(v)
  }
  // Default ambiguous + report remaining ambiguous as error (mirrors Ambiguity).
  const appliedPreds = [...topPreds, ...instExtraPreds].map((p) => applySubstPred(subst, p))
  const { subst: dSubst, preds: rest } = tryDefault({ ...env2, instances }, appliedPreds, fixed)
  subst = composeSubst(dSubst, subst)
  const stillAmb = ambiguousVars(rest.map((p) => applySubstPred(subst, p)), fixed)
  if (stillAmb.length > 0) {
    const [a] = stillAmb as [{ v: string; qs: GPred[] }]
    if (a !== undefined) {
      throw gTypeError(`Semantic Error: Ambiguous type: \`${a.qs.map(showPred).join(', ')} => ?\``)
    }
  }
  // Resolution table.
  const classOrder = new Map<string, string[]>()
  for (const d of decls) {
    if (d.k !== 'class') continue
    const ms: string[] = []
    for (const m of d.decls) if (m.k === 'sig') ms.push(m.name)
    classOrder.set(d.name, ms)
  }
  const table: RTable = {
    instances: rawInstances.map((r) => ({ cls: r.cls, head: r.head, ctx: r.ctx })),
    classOrder,
    methodClass,
  }
  const finalSubst = subst
  // Resolve top-level bindings (dict abstraction via prepended patterns).
  const resolvedTop = resolveDecls(topElab, finalSubst, { preds: [], vars: [] }, table, topScopes)
  // Instance method cores (mangled) + dictionary builders.
  const instCoreBindings: GCoreBinding[] = []
  const dispInstances: GDispatchTable['instances'] = []
  for (const inst of rawInstances) {
    const order = classOrder.get(inst.cls) ?? []
    // Elaborate each defined method against its expected type.
    const methodCores = new Map<string, GCore>()
    for (const mname of order) {
      const alts = inst.methods.get(mname)
      if (alts === undefined) throw gTypeError(`Instance ${inst.cls} is missing method ${mname}`)
      const info = instMethodElab.get(mangledMethod(inst.cls, inst.head, mname))
      if (info === undefined) throw gTypeError(`Internal: missing elaboration for ${mname}`)
      // Resolve with the method's residual scope; abstraction via dict pats.
      const dvars = info.resPreds.map(() => freshDictVar())
      const scope: RScope = {
        preds: info.resPreds.map((p) => applySubstPred(finalSubst, p)),
        vars: dvars,
      }
      const ralts = info.alts.map((m) => ({
        pats: [...dvars.map((v) => ({ k: 'var', name: v }) as GPat), ...m.pats],
        rhs: resolveExpr(m.rhs, finalSubst, scope, table),
      }))
      const lam = bindGroupToCore(mname, ralts).lambda
      methodCores.set(mname, lam)
      instCoreBindings.push({ name: mangledMethod(inst.cls, inst.head, mname), lambda: lam })
      void order
    }
    // Builder tuple in class order.
    const ctxVars = inst.ctx.map(() => freshDictVar())
    const ctxScope: RScope = {
      preds: inst.ctx.map((p) => applySubstPred(finalSubst, p)),
      vars: ctxVars,
    }
    void ctxScope
    const parts: GCore[] = []
    const minfo = new Map<string, { resPreds: GPred[] }>()
    for (const mname of order) {
      const info = instMethodElab.get(mangledMethod(inst.cls, inst.head, mname))
      minfo.set(mname, { resPreds: info !== undefined ? info.resPreds : [] })
    }
    void minfo
    for (const mname of order) {
      const info = instMethodElab.get(mangledMethod(inst.cls, inst.head, mname))
      const rp = info !== undefined ? info.resPreds : []
      let ref: GCore = { k: 'var', name: mangledMethod(inst.cls, inst.head, mname) }
      for (const q of rp) {
        const qty = applySubst(finalSubst, q.ty)
        const qi = scopeHitNum(ctxScope, q.cls, qty)
        if (qi >= 0) {
          ref = { k: 'app', fn: ref, arg: { k: 'var', name: ctxVars[qi]! } }
        } else {
          ref = { k: 'app', fn: ref, arg: buildDictCore(q.cls, qty, finalSubst, ctxScope, table) }
        }
      }
      parts.push(ref)
    }
    let tup: GCore
    if (parts.length === 0) tup = { k: 'intro', tag: '()', args: [] }
    else if (parts.length === 1) tup = parts[0]!
    else {
      // Right-nested pairs (projection uses fst#/snd#).
      let acc: GCore = parts[parts.length - 1]!
      for (let i = parts.length - 2; i >= 0; i--) {
        acc = { k: 'tuple', args: [parts[i]!, acc] }
      }
      tup = acc
    }
    let builder: GCore = tup
    for (let i = ctxVars.length - 1; i >= 0; i--) builder = { k: 'abs', param: ctxVars[i]!, body: builder }
    instCoreBindings.push({ name: mangledBuilder(inst.cls, inst.head), lambda: builder })
    // Dynamic fallback entries (resolved without static specialization).
    const dynMethods = new Map<string, GCore>()
    for (const [mname, alts] of inst.methods) {
      const ralts = alts.map((m) => ({
        pats: m.pats,
        rhs: resolveExpr(m.rhs, finalSubst, { preds: [], vars: [] }, table, true),
      }))
      dynMethods.set(mname, bindGroupToCore(mname, ralts).lambda)
    }
    dispInstances.push({ cls: inst.cls, head: inst.head, methods: dynMethods })
  }
  const dispatch: GDispatchTable = {
    methods: methodNames,
    instances: dispInstances,
    ctorToType,
    implEnv: new Map(),
  }
  const dataDecls = decls.filter((d) => d.k === 'data') as Array<Extract<GDecl, { k: 'data' }>>
  const topBindings = resolvedTop.decls.filter((d) => d.k === 'binding')
  const topCores: GCoreBinding[] = []
  for (const d of topBindings) {
    if (d.k !== 'binding') continue
    topCores.push(bindGroupToCore(d.name, d.alts))
  }
  const coreBindings: GCoreBinding[] = [
    ...dataToCore(dataDecls),
    // Builtin constructors.
    { name: '[]', lambda: { k: 'intro', tag: '[]', args: [] } },
    {
      name: ':',
      lambda: {
        k: 'abs', param: '__h',
        body: { k: 'abs', param: '__t', body: { k: 'intro', tag: ':', args: [{ k: 'var', name: '__h' }, { k: 'var', name: '__t' }] } },
      },
    },
    { name: '()', lambda: { k: 'intro', tag: '()', args: [] } },
    ...topCores,
    ...instCoreBindings,
  ]
  return { decls, typeEnv: env2, subst, dispatch, coreBindings, ctorToType, table }
}

function scopeHitNum(scope: RScope, cls: string, ty: GType): number {
  for (let i = 0; i < scope.preds.length; i++) {
    const p = scope.preds[i]!
    if (p.cls !== cls) continue
    if (tryUnify(p.ty, ty)) return i
  }
  return -1
}

function buildDictCore(
  cls: string, ty: GType, subst: GSubst, scope: RScope, table: RTable, depth = 0,
): GCore {
  if (depth > 20) throw gTypeError(`No instance for ${cls} ${showType(applySubst(subst, ty))}`)
  const ty2 = applySubst(subst, ty)
  if (!hasMetas(ty2)) {
    const si = scopeHitNum(scope, cls, ty2)
    if (si >= 0) return { k: 'var', name: scope.vars[si]! }
  }
  if (hasMetas(ty2)) {
    throw gTypeError(`Semantic Error: Ambiguous type: \`${cls} ${showType(ty2)} => ?\``)
  }
  const found = findInstance(table, cls, ty2)
  if (found === null) throw gTypeError(`No instance for ${cls} ${showType(ty2)}`)
  let out: GCore = { k: 'var', name: mangledBuilder(cls, found.inst.head) }
  for (const c of found.inst.ctx) {
    const cty = applySubst(found.match, c.ty)
    out = { k: 'app', fn: out, arg: buildDictCore(c.cls, cty, subst, scope, table, depth + 1) }
  }
  return out
}

function instMethodSigma(msig: GSigma, classParam: string, instCls: string, head: GType): GSigma {
  // Substitute class param := head type; drop the class's own constraint.
  const s: GSubst = new Map([[classParam, head]])
  const preds = msig.q.preds
    .map((p) => applySubstPred(s, p))
    .filter((p) => !(p.cls === instCls && tryUnify(p.ty, applySubst(s, head))))
  const ty = applySubst(s, msig.q.ty)
  const tvs = msig.tvs.filter((tv) => tv.name !== classParam)
  return { tvs, q: { preds, ty } }
}