/**
 * Frea — browser-native engine.
 *
 * Faithful port of the Haskell implementation (vendor/frea): a small lazy
 * functional language with HM inference, kinds, ADTs eliminated via
 * `which-` eliminators, type synonyms, lazy memoized evaluation, and the
 * exact REPL (banner, `frea λ > ` prompt, 9-space continuations/results,
 * empty-line submit, `:t`/`:k`/`:load`, `Bye!`).
 *
 * Two documented deviations: (1) Happy parse failures print only the first
 * line (the dumped parser-state internals are omitted); (2) `show` of a
 * whole-number `Double` prints `1.0` (Haskell) via a `.0` suffix rule, while
 * exotic exponents keep JavaScript formatting.
 */
import type { Engine, EngineResult } from './engine'
import { yieldToUI } from './engine'
import preludeSrc from '../../vendor/frea/prelude.frea?raw'

// ----------------------------------------------------------------- tokens ---

type Tok =
  | { t: 'kw'; v: string; i: number }
  | { t: 'hole'; i: number }
  | { t: 'var'; v: string; i: number }
  | { t: 'con'; v: string; i: number }
  | { t: 'op'; v: string; i: number }
  | { t: 'opcon'; v: string; i: number }
  | { t: 'native'; v: string; i: number }
  | { t: 'lp'; i: number } | { t: 'rp'; i: number }
  | { t: 'lb'; i: number } | { t: 'rb'; i: number }
  | { t: 'comma'; i: number } | { t: 'bt'; i: number }
  | { t: 'semi'; i: number } | { t: 'lbr'; i: number } | { t: 'rbr'; i: number }
  | { t: 'hasType'; i: number }
  | { t: 'int'; v: number; i: number }
  | { t: 'dbl'; v: number; i: number }
  | { t: 'chr'; v: string; i: number }
  | { t: 'str'; v: string; i: number }
  | { t: 'eof'; i: number }

const KEYWORDS = new Set([
  'assume', 'rec', 'match', 'with', 'data', 'if', 'then', 'else', 'let', 'in',
  'type', 'the', 'claim', 'define', 'lambda', 'fix', 'module', 'where',
])
const NATIVES = new Set([
  '#=', '#<', '#>', '#+', '#+.', '#-', '#-.', '#*', '#*.', '#div', '#/',
  '#fst', '#snd', '#show', '#debug',
])
const SYM_CHARS = "!$#%&*+./<=>?@\\^|-~;";
const isSym = (c: string) => SYM_CHARS.includes(c);
const isLower = (c: string) => c >= 'a' && c <= 'z'
const isUpper = (c: string) => c >= 'A' && c <= 'Z'
const isDigit = (c: string) => c >= '0' && c <= '9'
const isWordTail = (c: string) => isLower(c) || isUpper(c) || isDigit(c) || isSym(c)
const isSpace = (c: string) => c === ' ' || c === '\t' || c === '\f' || c === '\v'

function lexFrea(src: string): Tok[] {
  const toks: Tok[] = []
  let i = 0
  const fail = (at: number): never => {
    throw { msg: `Lexical error on line 1, column ${at + 1}.`, col: at + 1 }
  }
  while (i < src.length) {
    const c = src[i]!
    if (isSpace(c)) { i++; continue }
    if (c === '\n') { i++; continue }
    if (c === '-' && src[i + 1] === '-') {
      const nl = src.indexOf('\n', i)
      if (nl === -1) { i = src.length; continue } // trailing comment: operator rule would match; match it below
      i = nl + 1
      continue
    }
    if (src.startsWith('"""', i)) {
      // multiline string
      let j = i + 3
      let buf = ''
      let closed = false
      let run = 0
      while (j < src.length) {
        const d = src[j]!
        if (d === '"') { run++; j++; continue }
        if (run >= 3) { closed = true; break }
        if (run > 0) { buf += '"'.repeat(run); run = 0 }
        if (d === '\\' && j + 1 < src.length && "'\"\\nrtbfv".includes(src[j + 1]!)) {
          buf += unescStr(src[j + 1]!); j += 2; continue
        }
        if (d === '\\' && j + 1 < src.length) { buf += src[j + 1]!; j += 2; continue }
        buf += d === '\n' ? '\n' : d
        j++
      }
      if (!closed) fail(i)
      buf += '"'.repeat(run - 3)
      toks.push({ t: 'str', v: buf, i })
      i = j
      continue
    }
    if (c === '"') {
      let j = i + 1
      let buf = ''
      let closed = false
      while (j < src.length) {
        const d = src[j]!
        if (d === '\n') fail(i)
        if (d === '"') { closed = true; j++; break }
        if (d === '\\' && j + 1 < src.length && "'\"\\nrtbfv".includes(src[j + 1]!)) {
          buf += unescStr(src[j + 1]!); j += 2; continue
        }
        if (d === '\\' && j + 1 < src.length) { buf += src[j + 1]!; j += 2; continue }
        buf += d
        j++
      }
      if (!closed) fail(i)
      toks.push({ t: 'str', v: buf, i })
      i = j
      continue
    }
    if (c === "'") {
      const rest = src.slice(i + 1)
      const m2 = rest.match(/^((?:\\.|[^'\\]))'/)
      if (!m2 || m2[1] === undefined) throw { msg: `Lexical error on line 1, column ${i + 1}.`, col: i + 1 }
      const body: string = m2[1]
      let ch: string
      if (body.length === 1) ch = body
      else if (body[0] === '\\') {
        const e = body[1]!
        ch = e === 'n' ? '\n' : e === 'r' ? '\r' : e === 't' ? '\t' : e === 'b' ? '\b' : e === 'f' ? '\f' : e === 'v' ? '\v' : e === '\\' ? '\\' : e === "'" ? "'" : e
      } else fail(i)
      toks.push({ t: 'chr', v: ch!, i })
      i += 1 + body.length + 1
      continue
    }
    if (src.startsWith('let rec', i) && !isWordTail(src[i + 7] ?? '')) {
      toks.push({ t: 'kw', v: 'letrec', i })
      i += 7
      continue
    }
    if (c === '\\') {
      // a lone backslash is the lambda keyword (inside strings/chars it is
      // consumed by those branches above)
      toks.push({ t: 'kw', v: 'lambda', i })
      i++
      continue
    }
    if (c === '(') {
      const m = src.slice(i + 1).match(/^(\s*)\)/)
      if (m) { toks.push({ t: 'con', v: '()', i }); i += 1 + m[0]!.length; continue }
      toks.push({ t: 'lp', i }); i++; continue
    }
    if (c === ')') { toks.push({ t: 'rp', i }); i++; continue }
    if (c === '[') {
      const m = src.slice(i + 1).match(/^(\s*)\]/)
      if (m) { toks.push({ t: 'con', v: '[]', i }); i += 1 + m[0]!.length; continue }
      toks.push({ t: 'lb', i }); i++; continue
    }
    if (c === ']') { toks.push({ t: 'rb', i }); i++; continue }
    if (c === ',') { toks.push({ t: 'comma', i }); i++; continue }
    if (c === '`') { toks.push({ t: 'bt', i }); i++; continue }
    if (c === '{') { toks.push({ t: 'lbr', i }); i++; continue }
    if (c === '}') { toks.push({ t: 'rbr', i }); i++; continue }
    if (c === ';') { toks.push({ t: 'semi', i }); i++; continue }
    if (c === ':' && src[i + 1] === ':') { toks.push({ t: 'hasType', i }); i += 2; continue }
    // numbers (longest match wins over following operator rule)
    const num = matchNumber(src, i)
    if (num) { toks.push(num.tok); i = num.next; continue }
    if (isLower(c)) {
      let j = i + 1
      while (j < src.length && isWordTail(src[j]!)) j++
      const w = src.slice(i, j)
      if (KEYWORDS.has(w) && w !== 'let') { toks.push({ t: 'kw', v: w, i }); i = j; continue }
      if (w === 'let') { toks.push({ t: 'kw', v: 'let', i }); i = j; continue }
      toks.push({ t: 'var', v: w, i })
      i = j
      continue
    }
    if (isUpper(c)) {
      let j = i + 1
      while (j < src.length && isWordTail(src[j]!)) j++
      toks.push({ t: 'con', v: src.slice(i, j), i })
      i = j
      continue
    }
    if (c === '_' && !isWordTail(src[i + 1] ?? '')) { toks.push({ t: 'hole', i }); i++; continue }
    if (c === '_' ) { /* falls into ident? no: ident starts lower */ fail(i) }
    if (c === ':' ) {
      let j = i + 1
      while (j < src.length && (isSym(src[j]!) || isLower(src[j]!) || isUpper(src[j]!) || src[j] === ':')) j++
      toks.push({ t: 'opcon', v: src.slice(i, j), i })
      i = j
      continue
    }
    if (c === '#') {
      // native primops are literal matches; anything else starting with '#'
      // is a regular operator (upstream: '#' is in $symbol, so e.g. `#:` and
      // `#head` lex via @operator); longest native wins, as upstream puts
      // the native rules before the generic operator rule
      let best: string | undefined
      for (const n of NATIVES) {
        if (src.startsWith(n, i) && (best === undefined || n.length > best.length)) best = n
      }
      if (best !== undefined) {
        toks.push({ t: 'native', v: best, i })
        i += best.length
        continue
      }
      let j = i + 1
      while (j < src.length && (isLower(src[j]!) || isUpper(src[j]!) || isSym(src[j]!) || src[j] === ':')) j++
      toks.push({ t: 'op', v: src.slice(i, j), i })
      i = j
      continue
    }
    if (isSym(c)) {
      let j = i + 1
      while (j < src.length && (isLower(src[j]!) || isUpper(src[j]!) || isSym(src[j]!) || src[j] === ':')) j++
      const w = src.slice(i, j)
      if (NATIVES.has(w)) toks.push({ t: 'native', v: w, i })
      else toks.push({ t: 'op', v: w, i })
      i = j
      continue
    }
    fail(i)
  }
  toks.push({ t: 'eof', i })
  return toks
}

function unescStr(c: string): string {
  switch (c) {
    case 'n': return '\n'
    case 'r': return '\r'
    case 't': return '\t'
    case 'b': return '\b'
    case 'f': return '\f'
    case 'v': return '\v'
    case '\\': return '\\'
    case '"': return '"'
    default: return c
  }
}

function matchNumber(src: string, i: number): { tok: Tok; next: number } | null {
  const rest = src.slice(i)
  let m = rest.match(/^(-?(?:0[xX][0-9a-fA-F]+|0[oO][0-7]+|\d+))(?![\d.]|e[+-]?[\d])/);
  const mExpDot = rest.match(/^(-?\d+\.\d+(?:[eE][+-]?\d+)?|-?\d+[eE][+-]?\d+)/)
  // longest match wins (int rule precedes double on ties)
  const intLen = m ? m[1]!.length : -1
  const dblLen = mExpDot ? mExpDot[1]!.length : -1
  if (intLen < 0 && dblLen < 0) return null
  if (dblLen > intLen) {
    return { tok: { t: 'dbl', v: parseFloat(mExpDot![1]!), i }, next: i + dblLen }
  }
  const s = m![1]!
  const neg = s.startsWith('-')
  const body = neg ? s.slice(1) : s
  let v: number
  if (/^0[xX]/.test(body)) v = parseInt(body.slice(2), 16)
  else if (/^0[oO]/.test(body)) v = parseInt(body.slice(2), 8)
  else v = parseInt(body, 10)
  return { tok: { t: 'int', v: neg ? -v : v, i }, next: i + intLen }
}

// -------------------------------------------------------------------- AST ---

export type Lit = { k: 'int'; v: number } | { k: 'dbl'; v: number } | { k: 'chr'; v: string }
export const showLit = (l: Lit): string => {
  if (l.k === 'int') return String(l.v)
  if (l.k === 'chr') return showChar(l.v)
  return showDouble(l.v)
}
export const showChar = (c: string): string => {
  switch (c) {
    case '\n': return "'\\n'"
    case '\r': return "'\\r'"
    case '\t': return "'\\t'"
    case '\b': return "'\\b'"
    case '\f': return "'\\f'"
    case '\v': return "'\\v'"
    case '\\': return "'\\\\'"
    case "'": return "'\\''"
    default: return `'${c}'`
  }
}
export const showDouble = (d: number): string => {
  if (Object.is(d, -0)) return '-0.0'
  if (!Number.isFinite(d)) return String(d)
  if (Number.isInteger(d)) return `${String(d)}.0`
  return String(d)
}

export type Expr =
  | { k: 'var'; n: string }
  | { k: 'op'; n: string }
  | { k: 'lit'; l: Lit }
  | { k: 'lam'; v: string; b: Expr }
  | { k: 'app'; f: Expr; a: Expr }
  | { k: 'tup'; ts: Expr[] }
  | { k: 'if'; c: Expr; t: Expr; e: Expr }
  | { k: 'let'; bs: [string, Expr][]; b: Expr }
  | { k: 'ann'; t: Ty; e: Expr }
  | { k: 'intro'; n: string; args: Expr[] }
  | { k: 'elim'; cons: ConDecl[]; v: Expr; ds: Expr[] }

export const showExpr = (e: Expr): string => {
  switch (e.k) {
    case 'var': return e.n
    case 'op': return e.n
    case 'lit': return showLit(e.l)
    case 'lam': return `(\\ ${e.v} -> ${showExpr(e.b)})`
    case 'app': return `(${showExpr(e.f)} ${showExpr(e.a)})`
    case 'tup': return `(${e.ts.map(showExpr).join(', ')})`
    case 'if': return `if ${showExpr(e.c)} then ${showExpr(e.t)} else ${showExpr(e.e)}`
    case 'let': return `let ${e.bs.map(([n, v]) => n + showExpr(v)).join('\n')} in ${showExpr(e.b)}`
    case 'ann': return `${showExpr(e.e)} :: ${showTy(e.t)}`
    case 'intro': return `(${e.n} ${e.args.map(showExpr).join(' ')})`
    case 'elim': return '<eliminator>'
  }
}

export type Ty =
  | { k: 'var'; n: string }
  | { k: 'con'; n: string }
  | { k: 'tup'; ts: Ty[] }
  | { k: 'arr'; a: Ty; b: Ty }
  | { k: 'app'; a: Ty; b: Ty }
  | { k: 'op'; v: string; t: Ty }

export const showTy = (t: Ty): string => {
  switch (t.k) {
    case 'var': return t.n
    case 'con': return t.n
    case 'tup': return `(${t.ts.map(showTy).join(', ')})`
    case 'arr': {
      const l = t.a.k === 'arr' ? `(${showTy(t.a)})` : showTy(t.a)
      return `${l} -> ${showTy(t.b)}`
    }
    case 'app': {
      const r = t.b.k === 'app' ? `(${showTy(t.b)})` : showTy(t.b)
      return `${showTy(t.a)} ${r}`
    }
    case 'op': return `(λ ${t.v} . ${showTy(t.t)})`
  }
}

export type Scheme = { vars: string[]; t: Ty }
export const showScheme = (s: Scheme): string =>
  s.vars.length === 0 ? showTy(s.t) : `forall ${s.vars.join(' ')} . ${showTy(s.t)}`;

export type Kind = { k: 'star' } | { k: 'arr'; a: Kind; b: Kind } | { k: 'kvar'; n: string }
export const showKind = (k: Kind): string => {
  if (k.k === 'star') return '*'
  if (k.k === 'kvar') return '*'
  const l = k.a.k === 'arr' ? `(${showKind(k.a)})` : showKind(k.a)
  return `${l} -> ${showKind(k.b)}`
}

export type ConDecl = { n: string; ts: Ty[] }
export type Decl =
  | { k: 'bind'; n: string; e: Expr }
  | { k: 'data'; n: string; ps: string[]; cs: ConDecl[] }
  | { k: 'alias'; n: string; t: Ty }

// ------------------------------------------------------------------ parser ---

class BT {
  constructor(readonly at: number = -1) {}
}

class P {
  pos = 0
  furthest = 0
  constructor(readonly toks: Tok[]) {}
  peek(): Tok {
    const t = this.toks[this.pos]!
    if (t.i > this.furthest) this.furthest = t.i
    return t
  }
  next(): Tok {
    const t = this.toks[this.pos++]!
    if (t.i > this.furthest) this.furthest = t.i
    return t
  }
  save(): number {
    return this.pos
  }
  restore(n: number): void {
    this.pos = n
  }
  is(t: Tok['t']): boolean {
    return this.peek().t === t
  }
}

const isVar = (t: Tok): t is { t: 'var'; v: string; i: number } => t.t === 'var'
const isCon = (t: Tok): t is { t: 'con'; v: string; i: number } => t.t === 'con'

function expectVar(p: P): string {
  const t = p.next()
  if (t.t !== 'var') throw new BT(t.i)
  return t.v
}

function parseLowIdent(p: P): string {
  const t = p.peek()
  if (t.t === 'var') { p.next(); return t.v }
  if (t.t === 'lp') {
    const save = p.save()
    p.next()
    const o = p.next()
    if (o.t === 'op' && p.is('rp')) { p.next(); return o.v }
    p.restore(save)
  }
  throw new BT(t.i)
}

function parseUpIdent(p: P): string {
  const t = p.peek()
  if (t.t === 'con') { p.next(); return t.v }
  if (t.t === 'lp') {
    const save = p.save()
    p.next()
    const o = p.next()
    if (o.t === 'opcon' && p.is('rp')) { p.next(); return o.v }
    p.restore(save)
  }
  throw new BT(t.i)
}

function parseProgram(p: P): { decls: Decl[] } | { expr: Expr } {
  if (p.is('kw') && (p.peek() as { v: string }).v === 'module') return { decls: parseModule(p) }
  return { expr: parseExp(p) }
}

function parseModule(p: P): Decl[] {
  p.next() // module
  parseUpIdent(p)
  const w = p.next()
  if (!(w.t === 'kw' && (w as { v: string }).v === 'where')) throw new BT(w.i)
  if (p.next().t !== 'lbr') throw new BT(p.toks[p.pos - 1]!.i)
  const decls = [parseDecl(p)]
  while (p.is('semi')) {
    p.next()
    decls.push(parseDecl(p))
  }
  if (p.next().t !== 'rbr') throw new BT(p.toks[p.pos - 1]!.i)
  return decls
}

function parseDecl(p: P): Decl {
  const t = p.peek()
  if (t.t === 'kw' && (t as { v: string }).v === 'data') return parseData(p)
  if (t.t === 'kw' && (t as { v: string }).v === 'type') return parseTypeSyn(p)
  const [bn, be] = parseBinding(p)
  return { k: 'bind', n: bn, e: be }
}

function parseData(p: P): Decl {
  p.next() // data
  const name = parseUpIdent(p)
  const params: string[] = []
  while (p.peek().t === 'var') params.push(((p.next() as { t: 'var'; v: string }).v))
  const cons: ConDecl[] = []
  if (p.peek().t === 'op' && (p.peek() as { t: 'op'; v: string }).v === '=') {
    p.next()
    cons.push(parseConstr(p))
    while (p.peek().t === 'op' && (p.peek() as { t: 'op'; v: string }).v === '|') {
      p.next()
      cons.push(parseConstr(p))
    }
  }
  return { k: 'data', n: name, ps: params, cs: cons }
}

function parseConName(p: P): string {
  const t = p.peek()
  if (t.t === 'opcon') { p.next(); return t.v }
  if (t.t === 'bt') {
    p.next()
    const c = p.next()
    if (c.t !== 'con') throw new BT(c.i)
    if (p.next().t !== 'bt') throw new BT(p.toks[p.pos - 1]!.i)
    return c.v
  }
  throw new BT(t.i)
}

function startsTyAppLeft(p: P): boolean {
  const t = p.peek()
  if (t.t === 'var' || t.t === 'con') return true
  if (t.t === 'lp') return true
  return false
}

function parseTyAppLeft(p: P): Ty {
  const t = p.peek()
  if (t.t === 'var') { p.next(); return { k: 'var', n: t.v } }
  if (t.t === 'con') { p.next(); return { k: 'con', n: t.v } }
  if (t.t === 'lp') {
    p.next()
    const inner = parseType(p)
    if (p.is('comma')) {
      const ts = [inner]
      while (p.is('comma')) { p.next(); ts.push(parseType(p)) }
      if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
      return { k: 'tup', ts }
    }
    if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
    return inner
  }
  throw new BT(t.i)
}

function parseType(p: P): Ty {
  // juxtaposition binds tighter than '->'
  const first = parseTySingle(p)
  const rest: Ty[] = []
  while (startsTyAppLeft(p)) rest.push(parseTySingle(p))
  const left = rest.length === 0 ? first : rest.reduce<Ty>((a, b) => ({ k: 'app', a, b }), first)
  if (p.is('op') && (p.peek() as { t: 'op'; v: string }).v === '->') {
    p.next()
    return { k: 'arr', a: left, b: parseType(p) }
  }
  return left
}

function parseTySingle(p: P): Ty {
  const t = parseTyAppLeft(p)
  if (p.is('op') && (p.peek() as { t: 'op'; v: string }).v === '->') {
    p.next()
    return { k: 'arr', a: t, b: parseType(p) }
  }
  return t
}

function parseConstr(p: P): ConDecl {
  const save = p.save()
  try {
    const first = parseTyAppLeft(p)
    const t = p.peek()
    if (t.t === 'opcon' || t.t === 'bt') {
      const name = parseConName(p)
      const rest: Ty[] = [parseTySingle(p)]
      while (startsTyAppLeft(p)) rest.push(parseTySingle(p))
      return { n: name, ts: [first, ...rest] }
    }
    throw new BT(t.i)
  } catch (e) {
    if (!(e instanceof BT)) throw e
    p.restore(save)
    const name = parseUpIdent(p)
    const args: Ty[] = []
    while (startsTyAppLeft(p)) args.push(parseTySingle(p))
    return { n: name, ts: args }
  }
}

function parseTypeSyn(p: P): Decl {
  p.next() // type
  const c = p.next()
  if (c.t !== 'con') throw new BT(c.i)
  const vars: string[] = []
  while (p.peek().t === 'var') vars.push(((p.next() as { t: 'var'; v: string }).v))
  const eq = p.next()
  if (!(eq.t === 'op' && (eq as { t: 'op'; v: string }).v === '=')) throw new BT(eq.i)
  const body = parseType(p)
  return { k: 'alias', n: c.v, t: vars.reduceRight<Ty>((acc, v) => ({ k: 'op', v, t: acc }), body) }
}

function isOpTok(t: Tok): t is { t: 'op'; v: string; i: number } | { t: 'opcon'; v: string; i: number } {
  return t.t === 'op' || t.t === 'opcon'
}

function parseBinding(p: P): [string, Expr] {
  // Var '`' Var '`' Params '=' Exp
  if (p.peek().t === 'var') {
    const save = p.save()
    const first = (p.next() as { t: 'var'; v: string }).v
    if (p.is('bt')) {
      p.next()
      const second = expectVar(p)
      if (p.next().t !== 'bt') throw new BT(p.toks[p.pos - 1]!.i)
      const params = parseVars(p)
      expectEq(p)
      const body = parseExp(p)
      return [second, foldLam([first, ...params], body)]
    }
    p.restore(save)
  }
  // Var Op Params '=' Exp   vs   LowIdent Params '=' Exp
  // NOTE: only TokOperator (not opcon) is a valid binding operator upstream.
  {
    const save = p.save()
    try {
      const head = parseLowIdentHead(p)
      const t = p.peek()
      if (t.t === 'op') {
        const op = t.v
        p.next()
        const params = parseVars(p)
        expectEq(p)
        const body = parseExp(p)
        return [op, foldLam([head, ...params], body)]
      }
      throw new BT(t.i)
    } catch (e) {
      if (!(e instanceof BT)) throw e
      p.restore(save)
    }
  }
  const head = parseLowIdent(p)
  const params = parseVars(p)
  expectEq(p)
  const body = parseExp(p)
  return [head, foldLam(params, body)]
}

function parseLowIdentHead(p: P): string {
  // Var only (the '(' Op ')' shape belongs to the LowIdent fallback)
  const t = p.peek()
  if (t.t === 'var') { p.next(); return t.v }
  throw new BT(t.i)
}

function parseVars(p: P): string[] {
  const out: string[] = []
  while (p.peek().t === 'var') out.push(((p.next() as { t: 'var'; v: string }).v))
  return out
}

function expectEq(p: P): void {
  const t = p.next()
  if (!(t.t === 'op' && (t as { t: 'op'; v: string }).v === '=')) throw new BT(t.i)
}

function foldLam(params: string[], body: Expr): Expr {
  let acc = body
  for (let k = params.length - 1; k >= 0; k--) acc = { k: 'lam', v: params[k]!, b: acc }
  return acc
}

function parseExp(p: P): Expr {
  const head = parseAppLeft(p)
  const t = p.peek()
  if (t.t === 'bt') {
    p.next()
    const n = p.next()
    const op = n.t === 'var' || n.t === 'con' ? (n as { v: string }).v : null
    if (op === null || p.next().t !== 'bt') throw new BT(p.peek().i)
    const args = parseAppRightPlus(p)
    return args.reduce<Expr>((a, b) => ({ k: 'app', f: a, a: b }), { k: 'app', f: { k: 'var', n: op }, a: head })
  }
  if (isOpTok(t)) {
    // a bare `=` is not an infix operator (matches upstream: Happy rejects
    // `x = 5` at parse time; `==` and `=>` are different tokens and unaffected)
    if (t.t === 'op' && (t as { v: string }).v === '=') throw new BT(t.i)
    p.next()
    const args = parseAppRightPlus(p)
    let node: Expr = { k: 'var', n: (t as { v: string }).v }
    for (const a of [head, ...args]) node = { k: 'app', f: node, a }
    return node
  }
  if (startsAppRight(p)) {
    const args = parseAppRightPlus(p)
    let node = head
    for (const a of args) node = { k: 'app', f: node, a }
    return node
  }
  return head
}

function parseAppRightPlus(p: P): Expr[] {
  const out = [parseAppRight(p)]
  while (startsAppRight(p)) out.push(parseAppRight(p))
  return out
}

function startsAppRight(p: P): boolean {
  const t = p.peek()
  return (
    t.t === 'var' || t.t === 'con' || t.t === 'native' || t.t === 'int' ||
    t.t === 'dbl' || t.t === 'chr' || t.t === 'str' || t.t === 'lp' ||
    t.t === 'lb'
  )
}

function parseAppLeft(p: P): Expr {
  const t = p.peek()
  if (t.t === 'var') { p.next(); return { k: 'var', n: t.v } }
  if (t.t === 'con') { p.next(); return { k: 'var', n: t.v } }
  if (t.t === 'native') { p.next(); return { k: 'op', n: t.v } }
  if (t.t === 'int') { p.next(); return { k: 'lit', l: { k: 'int', v: t.v } } }
  if (t.t === 'dbl') { p.next(); return { k: 'lit', l: { k: 'dbl', v: t.v } } }
  if (t.t === 'chr') { p.next(); return { k: 'lit', l: { k: 'chr', v: t.v } } }
  if (t.t === 'str') {
    p.next()
    return [...t.v].reduceRight<Expr>((acc, ch) => ({ k: 'app', f: { k: 'app', f: { k: 'var', n: ':' }, a: { k: 'lit', l: { k: 'chr', v: ch } } }, a: acc }), { k: 'var', n: '[]' })
  }
  if (t.t === 'kw' && (t as { v: string }).v === 'lambda') {
    p.next()
    const params = parseVars(p)
    // also allow (op) params? Params are plain vars only
    const arr = p.next()
    if (!(arr.t === 'op' && (arr as { t: 'op'; v: string }).v === '->')) throw new BT(arr.i)
    return foldLam(params, parseExp(p))
  }
  if (t.t === 'kw' && (t as { v: string }).v === 'if') {
    p.next()
    const c = parseExp(p)
    const th = p.next()
    if (!(th.t === 'kw' && (th as { v: string }).v === 'then')) throw new BT(th.i)
    const a = parseExp(p)
    const el = p.next()
    if (!(el.t === 'kw' && (el as { v: string }).v === 'else')) throw new BT(el.i)
    return { k: 'if', c, t: a, e: parseExp(p) }
  }
  if (t.t === 'kw' && (t as { v: string }).v === 'let') {
    p.next()
    if (p.next().t !== 'lbr') throw new BT(p.toks[p.pos - 1]!.i)
    const bs = [parseBinding(p)]
    while (p.is('semi')) {
      p.next()
      bs.push(parseBinding(p))
    }
    if (p.next().t !== 'rbr') throw new BT(p.toks[p.pos - 1]!.i)
    const inw = p.next()
    if (!(inw.t === 'kw' && (inw as { v: string }).v === 'in')) throw new BT(inw.i)
    return { k: 'let', bs, b: parseExp(p) }
  }
  if (t.t === 'lb') {
    p.next()
    if (p.is('rb')) {
      p.next()
      return { k: 'var', n: '[]' }
    }
    const first = parseExp(p)
    const rest: Expr[] = []
    while (p.is('comma')) {
      p.next()
      rest.push(parseExp(p))
    }
    if (p.next().t !== 'rb') throw new BT(p.toks[p.pos - 1]!.i)
    const items = [first, ...rest]
    return items.reduceRight<Expr>((acc, it) => ({ k: 'app', f: { k: 'app', f: { k: 'var', n: ':' }, a: it }, a: acc }), { k: 'var', n: '[]' })
  }
  if (t.t === 'lp') {
    p.next()
    // '(' opcon ')' and '(' op ')' are variables (LowIdent / UpIdent)
    const nt = p.peek()
    if ((nt.t === 'opcon' || nt.t === 'op') && p.toks[p.pos + 1]?.t === 'rp') {
      p.next()
      p.next()
      return { k: 'var', n: (nt as { v: string }).v }
    }
    const inner = parseExp(p)
    if (p.is('comma')) {
      const ts = [inner]
      while (p.is('comma')) {
        p.next()
        ts.push(parseExp(p))
      }
      if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
      return { k: 'tup', ts }
    }
    if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
    return inner
  }
  throw new BT(t.i)
}

function parseAppRight(p: P): Expr {
  return parseAppLeft(p)
}

// ------------------------------------------------- types and schemes ---

export type SubstT = Map<string, Ty>
export type SubstK = Map<string, Kind>

export const applyTy = (s: SubstT, t: Ty): Ty => {
  switch (t.k) {
    case 'var': return s.get(t.n) ?? t
    case 'con': return t
    case 'tup': return { k: 'tup', ts: t.ts.map((x) => applyTy(s, x)) }
    case 'arr': return { k: 'arr', a: applyTy(s, t.a), b: applyTy(s, t.b) }
    case 'app': return { k: 'app', a: applyTy(s, t.a), b: applyTy(s, t.b) }
    case 'op': {
      const s2 = new Map(s)
      s2.delete(t.v)
      return { k: 'op', v: t.v, t: applyTy(s2, t.t) }
    }
  }
}

export const applyKind = (s: SubstK, k: Kind): Kind => {
  switch (k.k) {
    case 'star': return k
    case 'kvar': return s.get(k.n) ?? k
    case 'arr': return { k: 'arr', a: applyKind(s, k.a), b: applyKind(s, k.b) }
  }
}

const applyScheme = (s: SubstT, sc: Scheme): Scheme => {
  const s2 = new Map(s)
  for (const v of sc.vars) s2.delete(v)
  return { vars: sc.vars, t: applyTy(s2, sc.t) }
}

export const freeTy = (t: Ty, acc = new Set<string>()): Set<string> => {
  switch (t.k) {
    case 'var': acc.add(t.n); break
    case 'tup': t.ts.forEach((x) => freeTy(x, acc)); break
    case 'arr': freeTy(t.a, acc); freeTy(t.b, acc); break
    case 'app': freeTy(t.a, acc); freeTy(t.b, acc); break
    case 'op': freeTy(t.t, acc); acc.delete(t.v); break
    default: break
  }
  return acc
}

export const freeKind = (k: Kind, acc = new Set<string>()): Set<string> => {
  if (k.k === 'kvar') acc.add(k.n)
  else if (k.k === 'arr') { freeKind(k.a, acc); freeKind(k.b, acc) }
  return acc
}

const freeScheme = (s: Scheme): Set<string> => {
  const f = freeTy(s.t)
  for (const v of s.vars) f.delete(v)
  return f
}

const freeTypeEnv = (env: Map<string, Scheme>): Set<string> => {
  const out = new Set<string>()
  for (const s of env.values()) for (const v of freeScheme(s)) out.add(v)
  return out
}

const freeKindEnv = (env: Map<string, Kind>): Set<string> => {
  const out = new Set<string>()
  for (const k of env.values()) for (const v of freeKind(k)) out.add(v)
  return out
}

// ---------------------------------------------------------------- errors ---

export type FError =
  | { k: 'InfiniteType'; a: Ty; b: Ty }
  | { k: 'InfiniteKind'; a: Kind; b: Kind }
  | { k: 'TypeUnifMismatch'; a: Ty; b: Ty }
  | { k: 'KindUnifMismatch'; a: Kind; b: Kind }
  | { k: 'UnboundVar'; n: string }
  | { k: 'UnboundTypeVar'; n: string }
  | { k: 'TypeShapeMismatch'; a: Ty; b: Ty }
  | { k: 'KindShapeMismatch'; a: Kind; b: Kind }
  | { k: 'TypeUnifCountMismatch'; a: Ty[]; b: Ty[] }
  | { k: 'KindUnifCountMismatch'; a: Kind[]; b: Kind[] }
  | { k: 'SynonymCycle'; ds: [string, Ty][] }
  | { k: 'Unexpected'; m: string }

export const showFError = (e: FError): string => {
  switch (e.k) {
    case 'InfiniteType': return `Occurs check: cannot construct the infinite type:\n  ${showTy(e.a)} ~ ${showTy(e.b)}`
    case 'InfiniteKind': return `Occurs check: cannot construct the infinite kind:\n  ${showKind(e.a)} ~ ${showKind(e.b)}`
    case 'TypeUnifMismatch': return `Couldn't match type \`${showTy(e.a)}\` with \`${showTy(e.b)}\``
    case 'KindUnifMismatch': return `Couldn't match kind \`${showKind(e.a)}\` with \`${showKind(e.b)}\``
    case 'UnboundVar': return `Unknown variable ${e.n}`
    case 'UnboundTypeVar': return `Unknown type variable ${e.n}`
    case 'TypeShapeMismatch': return `[Shape] Couldn't match type \`${showTy(e.a)}\` with \`${showTy(e.b)}\``
    case 'KindShapeMismatch': return `[Shape] Couldn't match kind \`${showKind(e.a)}\` with \`${showKind(e.b)}\``
    case 'TypeUnifCountMismatch': return `TypeUnifCountMismatch ${e.a.map(showTy).join(' ')} vs ${e.b.map(showTy).join(' ')}`
    case 'KindUnifCountMismatch': return `KindUnifCountMismatch`
    case 'SynonymCycle':
      return `Found a cycle in the type synonym declaration(s) of\n` + e.ds.map(([n, t]) => `  type ${n} = ${showTy(t)}`).join('\n')
    case 'Unexpected': return `Something bad happened: ${e.m}`
  }
}

function fail(e: FError): never {
  throw e
}

// ------------------------------------------------------------------ solver ---

const occursTy = (name: string, t: Ty): boolean => {
  switch (t.k) {
    case 'var': return t.n === name
    case 'con': return t.n === name
    case 'tup': return t.ts.some((x) => occursTy(name, x))
    case 'arr': return occursTy(name, t.a) || occursTy(name, t.b)
    case 'app': return occursTy(name, t.a) || occursTy(name, t.b)
    case 'op': return false
  }
}

const occursKind = (name: string, k: Kind): boolean => {
  if (k.k === 'kvar') return k.n === name
  if (k.k === 'star') return false
  return occursKind(name, k.a) || occursKind(name, k.b)
}

function bindTy(name: string, t: Ty): SubstT {
  if (t.k === 'var' && t.n === name) return new Map()
  if (occursTy(name, t)) fail({ k: 'InfiniteType', a: { k: 'var', n: name }, b: t })
  return new Map([[name, t]])
}

function bindKind(name: string, k: Kind): SubstK {
  if (k.k === 'kvar' && k.n === name) return new Map()
  if (occursKind(name, k)) fail({ k: 'InfiniteKind', a: { k: 'kvar', n: name }, b: k })
  return new Map([[name, k]])
}

function unifyTy(a: Ty, b: Ty): SubstT {
  if (eqTy(a, b)) return new Map()
  if (a.k === 'var') return bindTy(a.n, b)
  if (b.k === 'var') return bindTy(b.n, a)
  if (a.k === 'arr' && b.k === 'arr') return unifyManyTy([a.a, a.b], [b.a, b.b])
  if (a.k === 'app' && b.k === 'app') return unifyManyTy([a.a, a.b], [b.a, b.b])
  if (a.k === 'con' && b.k === 'con') {
    if (a.n === b.n) return new Map()
    fail({ k: 'TypeUnifMismatch', a, b })
  }
  if (a.k === 'tup' && b.k === 'tup') {
    if (a.ts.length !== b.ts.length) fail({ k: 'TypeShapeMismatch', a, b })
    return unifyManyTy(a.ts, b.ts)
  }
  throw { k: 'TypeShapeMismatch', a, b }
}

function unifyManyTy(as: Ty[], bs: Ty[]): SubstT {
  if (as.length === 0 && bs.length === 0) return new Map()
  if (as.length === 0 || bs.length === 0 || as.length !== bs.length) {
    fail({ k: 'TypeUnifCountMismatch', a: as, b: bs })
  }
  const [a, ...arest] = as
  const [b, ...brest] = bs
  const su1 = unifyTy(a!, b!)
  const su2 = unifyManyTy(arest.map((t) => applyTy(su1, t)), brest.map((t) => applyTy(su1, t)))
  return composeTy(su2, su1)
}

function unifyKind(a: Kind, b: Kind): SubstK {
  if (eqKind(a, b)) return new Map()
  if (a.k === 'kvar') return bindKind(a.n, b)
  if (b.k === 'kvar') return bindKind(b.n, a)
  if (a.k === 'arr' && b.k === 'arr') return unifyManyKind([a.a, a.b], [b.a, b.b])
  if (a.k === 'star' && b.k === 'star') return new Map()
  fail({ k: 'KindShapeMismatch', a, b })
}

function unifyManyKind(as: Kind[], bs: Kind[]): SubstK {
  if (as.length === 0 && bs.length === 0) return new Map()
  if (as.length !== bs.length) fail({ k: 'KindUnifCountMismatch', a: as, b: bs })
  const [a, ...arest] = as
  const [b, ...brest] = bs
  const su1 = unifyKind(a!, b!)
  const su2 = unifyManyKind(arest.map((t) => applyKind(su1, t)), brest.map((t) => applyKind(su1, t)))
  return composeKind(su2, su1)
}

function composeTy(s1: SubstT, s2: SubstT): SubstT {
  const out = new Map<string, Ty>()
  for (const [k, v] of s2) out.set(k, applyTy(s1, v))
  for (const [k, v] of s1) out.set(k, v)
  return out
}

function composeKind(s1: SubstK, s2: SubstK): SubstK {
  const out = new Map<string, Kind>()
  for (const [k, v] of s2) out.set(k, applyKind(s1, v))
  for (const [k, v] of s1) out.set(k, v)
  return out
}

const eqTy = (a: Ty, b: Ty): boolean => {
  if (a.k !== b.k) return false
  switch (a.k) {
    case 'var': return (b as { n: string }).n === a.n
    case 'con': return (b as { n: string }).n === a.n
    case 'tup': {
      const bb = b as { ts: Ty[] }
      return a.ts.length === bb.ts.length && a.ts.every((t, i) => eqTy(t, bb.ts[i]!))
    }
    case 'arr': { const bb = b as { a: Ty; b: Ty }; return eqTy(a.a, bb.a) && eqTy(a.b, bb.b) }
    case 'app': { const bb = b as { a: Ty; b: Ty }; return eqTy(a.a, bb.a) && eqTy(a.b, bb.b) }
    case 'op': { const bb = b as { v: string; t: Ty }; return a.v === bb.v && eqTy(a.t, bb.t) }
  }
}

const eqKind = (a: Kind, b: Kind): boolean => {
  if (a.k !== b.k) return false
  if (a.k === 'star' || a.k === 'kvar') return (a as { n?: string }).n === (b as { n?: string }).n
  const bb = b as { a: Kind; b: Kind }
  const aa = a as { a: Kind; b: Kind }
  return eqKind(aa.a, bb.a) && eqKind(aa.b, bb.b)
}

function runSolveTy(cs: [Ty, Ty][]): SubstT {
  let subst: SubstT = new Map()
  let constrs = cs
  while (constrs.length > 0) {
    const [[l, r], ...rest] = constrs
    const s = unifyTy(l!, r!)
    subst = composeTy(s, subst)
    constrs = rest.map(([a, b]) => [applyTy(s, a), applyTy(s, b)] as [Ty, Ty])
  }
  return subst
}

function runSolveKind(cs: [Kind, Kind][]): SubstK {
  let subst: SubstK = new Map()
  let constrs = cs
  while (constrs.length > 0) {
    const [[l, r], ...rest] = constrs
    const s = unifyKind(l, r)
    subst = composeKind(s, subst)
    constrs = rest.map(([a, b]) => [applyKind(s, a), applyKind(s, b)] as [Kind, Kind])
  }
  return subst
}

// ---------------------------------------------------------------- analyze ---

export interface AEnv {
  kenv: Map<string, Kind>
  tenv: Map<string, Scheme>
  alienv: Map<string, Ty>
}

const T_INT: Ty = { k: 'con', n: 'Int' }
const T_DOUBLE: Ty = { k: 'con', n: 'Double' }
const T_CHAR: Ty = { k: 'con', n: 'Char' }
const T_BOOL: Ty = { k: 'con', n: 'Bool' }

export function emptyAEnv(): AEnv {
  return {
    kenv: new Map([
      ['Bool', { k: 'star' }],
      ['Int', { k: 'star' }],
      ['Double', { k: 'star' }],
      ['Char', { k: 'star' }],
      ['Unit', { k: 'star' }],
    ]),
    tenv: new Map<string, Scheme>([
      ['#fst', { vars: ['a', 'b'], t: { k: 'arr', a: { k: 'tup', ts: [{ k: 'var', n: 'a' }, { k: 'var', n: 'b' }] }, b: { k: 'var', n: 'a' } } }],
      ['#snd', { vars: ['a', 'b'], t: { k: 'arr', a: { k: 'tup', ts: [{ k: 'var', n: 'a' }, { k: 'var', n: 'b' }] }, b: { k: 'var', n: 'b' } } }],
      ['#=', { vars: ['a'], t: { k: 'arr', a: { k: 'tup', ts: [{ k: 'var', n: 'a' }, { k: 'var', n: 'a' }] }, b: T_BOOL } }],
      ['#<', { vars: ['a'], t: { k: 'arr', a: { k: 'tup', ts: [{ k: 'var', n: 'a' }, { k: 'var', n: 'a' }] }, b: T_BOOL } }],
      ['#>', { vars: ['a'], t: { k: 'arr', a: { k: 'tup', ts: [{ k: 'var', n: 'a' }, { k: 'var', n: 'a' }] }, b: T_BOOL } }],
      ['#+', { vars: [], t: { k: 'arr', a: { k: 'tup', ts: [T_INT, T_INT] }, b: T_INT } }],
      ['#+.', { vars: [], t: { k: 'arr', a: { k: 'tup', ts: [T_DOUBLE, T_DOUBLE] }, b: T_DOUBLE } }],
      ['#*', { vars: [], t: { k: 'arr', a: { k: 'tup', ts: [T_INT, T_INT] }, b: T_INT } }],
      ['#*.', { vars: [], t: { k: 'arr', a: { k: 'tup', ts: [T_DOUBLE, T_DOUBLE] }, b: T_DOUBLE } }],
      ['#-', { vars: [], t: { k: 'arr', a: { k: 'tup', ts: [T_INT, T_INT] }, b: T_INT } }],
      ['#-.', { vars: [], t: { k: 'arr', a: { k: 'tup', ts: [T_DOUBLE, T_DOUBLE] }, b: T_DOUBLE } }],
      ['#div', { vars: [], t: { k: 'arr', a: { k: 'tup', ts: [T_INT, T_INT] }, b: T_INT } }],
      ['#/', { vars: [], t: { k: 'arr', a: { k: 'tup', ts: [T_DOUBLE, T_DOUBLE] }, b: T_DOUBLE } }],
      ['#show', { vars: ['a'], t: { k: 'arr', a: { k: 'var', n: 'a' }, b: { k: 'app', a: { k: 'con', n: 'List' }, b: T_CHAR } } }],
      ['#debug', { vars: ['a'], t: { k: 'arr', a: { k: 'var', n: 'a' }, b: { k: 'var', n: 'a' } } }],
    ]),
    alienv: new Map(),
  }
}

const TUP2 = (a: Ty, b: Ty): Ty => ({ k: 'tup', ts: [a, b] })

function letters(i: number): string {
  let n = i
  let len = 1
  let block = 26
  while (n >= block) {
    n -= block
    len++
    block *= 26
  }
  let s = ''
  for (let k = 0; k < len; k++) {
    s = String.fromCharCode(97 + (n % 26)) + s
    n = Math.floor(n / 26)
  }
  return s
}

class AN {
  count = 0
  constructor(public env: AEnv) {}
  fresh(): string {
    const n = letters(this.count)
    this.count++
    return n
  }
  realFresh(avoid: Set<string>): string {
    for (;;) {
      const n = letters(this.count)
      this.count++
      if (!avoid.has(n)) return n
    }
  }
  local<T>(f: (e: AEnv) => AEnv, m: () => T): T {
    const save = this.env
    this.env = f(save)
    try {
      return m()
    } finally {
      this.env = save
    }
  }
}

function lookupT(an: AN, name: string): Ty {
  const sc = an.env.tenv.get(name)
  if (!sc) fail({ k: 'UnboundVar', n: name })
  return instantiate(an, sc as Scheme)
}

function putT(an: AN, name: string, sc: Scheme, m: () => void): void {
  an.local((e) => {
    const t = new Map(e.tenv)
    t.delete(name)
    t.set(name, sc)
    return { ...e, tenv: t }
  }, m)
}

function mergeT(an: AN, binds: [string, Scheme][], m: () => void): void {
  an.local((e) => {
    const t = new Map(e.tenv)
    for (const [n, s] of binds) t.set(n, s)
    return { ...e, tenv: t }
  }, m)
}

function lookupK(an: AN, name: string): Kind {
  const k = an.env.kenv.get(name)
  if (!k) fail({ k: 'UnboundTypeVar', n: name })
  return k as Kind
}

function mergeK(an: AN, binds: [string, Kind][], m: () => void): void {
  an.local((e) => {
    const k = new Map(e.kenv)
    for (const [n, kk] of binds) k.set(n, kk)
    return { ...e, kenv: k }
  }, m)
}

function putK(an: AN, name: string, k: Kind, m: () => void): void {
  an.local((e) => {
    const kk = new Map(e.kenv)
    kk.delete(name)
    kk.set(name, k)
    return { ...e, kenv: kk }
  }, m)
}

function putA(an: AN, name: string, t: Ty, m: () => void): void {
  an.local((e) => {
    const a = new Map(e.alienv)
    a.delete(name)
    a.set(name, t)
    return { ...e, alienv: a }
  }, m)
}

function instantiate(an: AN, sc: Scheme): Ty {
  const freshs = sc.vars.map((v) => {
    const n = an.realFresh(new Set(sc.vars))
    return { v, n }
  })
  const sub = new Map(freshs.map(({ v, n }) => [v, { k: 'var', n } as Ty]))
  return applyTy(sub, sc.t)
}

function generalize(env: Map<string, Scheme>, t: Ty): Scheme {
  const fvt = freeTy(t)
  const fve = new Set<string>()
  for (const s of env.values()) for (const v of freeScheme(s)) fve.add(v)
  const vars = [...fvt].filter((v) => !fve.has(v)).sort()
  return { vars, t }
}

function closeOver(t: Ty): Scheme {
  return normalize(generalize(new Map(), t))
}

function normalize(sc: Scheme): Scheme {
  const ord = new Map<string, string>()
  ;[...freeTy(sc.t)].sort().forEach((v, i) => ord.set(v, letters(i)))
  const norm = (t: Ty): Ty => {
    switch (t.k) {
      case 'var': {
        const n = ord.get(t.n)
        if (n === undefined) fail({ k: 'Unexpected', m: `Type variable ${t.n} not in the signature.` })
        return { k: 'var', n: n as string }
      }
      case 'con': return t
      case 'tup': return { k: 'tup', ts: t.ts.map(norm) }
      case 'arr': return { k: 'arr', a: norm(t.a), b: norm(t.b) }
      case 'app': return { k: 'app', a: norm(t.a), b: norm(t.b) }
      case 'op': fail({ k: 'Unexpected', m: 'normalize met a type operator.' })
    }
  }
  return { vars: [...ord.values()], t: norm(sc.t) }
}

// ------------------------------------------------- HM inference ---

type TC = [Ty, Ty][]
type KC = [Kind, Kind][]

function infer(an: AN, e: Expr): [Ty, TC, KC] {
  switch (e.k) {
    case 'lit':
      if (e.l.k === 'int') return [T_INT, [], []]
      if (e.l.k === 'dbl') return [T_DOUBLE, [], []]
      return [T_CHAR, [], []]
    case 'var': {
      const t = lookupT(an, e.n)
      return [t, [], []]
    }
    case 'op': {
      const t = lookupT(an, e.n)
      return [t, [], []]
    }
    case 'lam': {
      const v = { k: 'var', n: an.fresh() } as Ty
      let res!: [Ty, TC, KC]
      putT(an, e.v, { vars: [], t: v }, () => { res = infer(an, e.b) })
      return [{ k: 'arr', a: v, b: res![0] }, res![1], res![2]]
    }
    case 'app': {
      const [tl, csl, kl] = infer(an, e.f)
      const [tr, csr, kr] = infer(an, e.a)
      const tv: Ty = { k: 'var', n: an.fresh() }
      return [tv, [...csl, ...csr, [tl, { k: 'arr', a: tr, b: tv }]], [...kl, ...kr]]
    }
    case 'if': {
      const [t1, c1, k1] = infer(an, e.c)
      const [t2, c2, k2] = infer(an, e.t)
      const [t3, c3, k3] = infer(an, e.e)
      return [t2, [[t1, T_BOOL], [t2, t3], ...c1, ...c2, ...c3], [...k1, ...k2, ...k3]]
    }
    case 'let': {
      const [tenv2, tcs, kcs] = inferDefinitions(an, e.bs)
      let res!: [Ty, TC, KC]
      an.local((env) => ({ ...env, tenv: tenv2 }), () => { res = infer(an, e.b) })
      return [res![0], [...tcs, ...res![1]], [...kcs, ...res![2]]]
    }
    case 'tup': {
      const types: Ty[] = []
      let cs: TC = []
      let ks: KC = []
      for (const x of e.ts) {
        const [t, c, k] = infer(an, x)
        types.unshift(t)
        cs = [...cs, ...c]
        ks = [...ks, ...k]
      }
      return [{ k: 'tup', ts: types.reverse() }, cs, ks]
    }
    case 'ann': {
      const scheme = generalize(new Map(), e.t)
      const t = instantiate(an, scheme)
      const pairs = [...freeTy(t)].map((name): [string, Kind] => [name, { k: 'kvar', n: an.fresh() }])
      let kind!: Kind
      let kcon!: KC
      mergeK(an, pairs, () => { const r = kindInfer(an, e.t); kind = r[0]; kcon = r[1] })
      const [constrs, kcs] = check(an, t, e.e)
      void kind
      return [t, constrs, [[kind!, { k: 'star' }], ...kcon!, ...kcs]]
    }
    default:
      fail({ k: 'Unexpected', m: 'infer met a generated-only expression.' })
  }
}

function check(an: AN, t: Ty, e: Expr): [TC, KC] {
  switch (e.k) {
    case 'lit':
      if (e.l.k === 'int') return [[[t, T_INT]], []]
      if (e.l.k === 'dbl') return [[[t, T_DOUBLE]], []]
      return [[[t, T_CHAR]], []]
    case 'ann': {
      const [tann, cs, kcs] = infer(an, e)
      return [[[t, tann], ...cs], kcs]
    }
    case 'var':
    case 'op': {
      const ty = lookupT(an, e.n)
      return [[[t, ty]], []]
    }
    case 'lam': {
      const from: Ty = { k: 'var', n: an.fresh() }
      const to: Ty = { k: 'var', n: an.fresh() }
      let res!: [TC, KC]
      putT(an, e.v, { vars: [], t: from }, () => { res = check(an, to, e.b) })
      return [[ [t, { k: 'arr', a: from, b: to }], ...res![0]], res![1]]
    }
    case 'app': {
      const [tl, csl, kl] = infer(an, e.f)
      const [tr, csr, kr] = infer(an, e.a)
      const tv: Ty = { k: 'var', n: an.fresh() }
      return [[[t, tv], [tl, { k: 'arr', a: tr, b: tv }], ...csl, ...csr], [...kl, ...kr]]
    }
    case 'if': {
      const [t1, c1, k1] = infer(an, e.c)
      const [c2, k2] = check(an, t, e.t)
      const [c3, k3] = check(an, t, e.e)
      return [[[t1, T_BOOL], ...c1, ...c2, ...c3], [...k1, ...k2, ...k3]]
    }
    case 'let': {
      const [tenv2, tcs, kcs] = inferDefinitions(an, e.bs)
      let res!: [TC, KC]
      an.local((env) => ({ ...env, tenv: tenv2 }), () => { res = check(an, t, e.b) })
      return [[...tcs, ...res![0]], [...kcs, ...res![1]]]
    }
    case 'tup': {
      const freshs = e.ts.map((): Ty => ({ k: 'var', n: an.fresh() }))
      let cs: TC = []
      let ks: KC = []
      const pairs = freshs.map((f, i) => [f, e.ts[i]!] as [Ty, Expr])
      for (const [ty, ex] of pairs) {
        const [c, k] = check(an, ty, ex)
        cs = [...c, ...cs]
        ks = [...ks, ...k]
      }
      return [[[t, { k: 'tup', ts: freshs }], ...cs], ks]
    }
    default:
      fail({ k: 'Unexpected', m: 'check met a generated-only expression.' })
  }
}

// ------------------------------------------------- binding groups ---

function indexBindings(bs: [string, unknown][]): Map<string, number> {
  const m = new Map<string, number>()
  bs.forEach(([n], i) => m.set(n, i))
  return m
}

function exprDeps(e: Expr, idx: Map<string, number>): Set<number> {
  switch (e.k) {
    case 'var': {
      const i = idx.get(e.n)
      return i === undefined ? new Set() : new Set([i])
    }
    case 'op':
    case 'lit':
      return new Set()
    case 'lam': {
      const d = exprDeps(e.b, idx)
      const i = idx.get(e.v)
      if (i !== undefined) d.delete(i)
      return d
    }
    case 'app':
      return new Set([...exprDeps(e.f, idx), ...exprDeps(e.a, idx)])
    case 'tup':
      return e.ts.reduce((s, x) => new Set([...s, ...exprDeps(x, idx)]), new Set<number>())
    case 'if':
      return new Set([...exprDeps(e.c, idx), ...exprDeps(e.t, idx), ...exprDeps(e.e, idx)])
    case 'let': {
      const s = new Set<number>()
      for (const [, v] of e.bs) for (const d of exprDeps(v, idx)) s.add(d)
      for (const d of exprDeps(e.b, idx)) s.add(d)
      return s
    }
    case 'intro':
      return e.args.reduce((s, x) => new Set([...s, ...exprDeps(x, idx)]), new Set<number>())
    case 'elim': {
      const s = new Set<number>()
      for (const d of exprDeps(e.v, idx)) s.add(d)
      for (const x of e.ds) for (const d of exprDeps(x, idx)) s.add(d)
      return s
    }
    case 'ann':
      return exprDeps(e.e, idx)
  }
}

function tarjan<T>(nodes: T[], keyOf: (t: T) => number, depsOf: (t: T) => number[]): T[][] {
  const index = new Map<number, number>()
  const low = new Map<number, number>()
  const onStack = new Set<number>()
  const stack: number[] = []
  const byKey = new Map<number, T>()
  for (const n of nodes) byKey.set(keyOf(n), n)
  const out: number[][] = []
  let counter = 0
  const visit = (v: number): void => {
    index.set(v, counter)
    low.set(v, counter)
    counter++
    stack.push(v)
    onStack.add(v)
    const deps = [...(depsOf(byKey.get(v)!) ?? [])].sort((a, b) => a - b)
    for (const w of deps) {
      if (!index.has(w)) {
        visit(w)
        low.set(v, Math.min(low.get(v)!, low.get(w)!))
      } else if (onStack.has(w)) {
        low.set(v, Math.min(low.get(v)!, index.get(w)!))
      }
    }
    if (low.get(v) === index.get(v)) {
      const comp: number[] = []
      let w = -1
      do {
        w = stack.pop()!
        onStack.delete(w)
        comp.push(w)
      } while (w !== v)
      out.push(comp)
    }
  }
  for (const n of nodes) {
    const k = keyOf(n)
    if (!index.has(k)) visit(k)
  }
  return out.map((c) => c.map((k) => byKey.get(k)!))
}

function inferDefinitions(an: AN, bindings: [string, Expr][]): [Map<string, Scheme>, TC, KC] {
  const indexed = indexBindings(bindings)
  const nodes = bindings.map(([n, e], i) => ({ n, e, i, deps: [...exprDeps(e, indexed)] }))
  const groups = tarjan(nodes, (x) => x.i, (x) => x.deps)
  const inferGroups = (gs: typeof groups): [Map<string, Scheme>, TC, KC] => {
    if (gs.length === 0) return [an.env.tenv, [], []]
    const [g, ...rest] = gs
    if (g!.length === 1 && !g![0]!.deps.includes(g![0]!.i)) {
      const { n, e } = g![0]!
      const freshName = an.fresh()
      let inner!: [Ty, TC, KC]
      putT(an, n, { vars: [], t: { k: 'var', n: freshName } }, () => {
        const [ty, tcs, kcs] = infer(an, e)
        const orig = lookupT(an, n)
        inner = [ty, [[orig, ty], ...tcs], kcs]
      })
      const subst = runSolveTy(inner![1])
      let out!: [Map<string, Scheme>, TC, KC]
      putT(an, n, closeOver(applyTy(subst, inner![0])), () => {
        out = inferGroups(rest)
      })
      return [out![0], [...inner![1], ...out![1]], [...inner![2], ...out![2]]]
    }
    // cyclic group
    const freshs = g!.map(({ n }) => ({ n, s: { vars: [], t: { k: 'var', n: an.fresh() } as Ty } as Scheme }))
    let collected!: [Ty, TC, KC][]
    mergeT(an, freshs.map(({ n, s }) => [n, s] as [string, Scheme]), () => {
      collected = g!.map(({ e }) => {
        const [ty, tcs, kcs] = infer(an, e)
        return [ty, tcs, kcs] as [Ty, TC, KC]
      })
      // add (orig, type) constraints
      collected = g!.map(({ n }, i) => {
        const orig = lookupT(an, n)
        const [ty, tcs, kcs] = collected![i]!
        return [ty, [[orig, ty], ...tcs], kcs] as [Ty, TC, KC]
      })
    })
    const allTcs = collected!.flatMap(([, tcs]) => tcs)
    const allKcs = collected!.flatMap(([, , kcs]) => kcs)
    const subst = runSolveTy(allTcs)
    const schemes = g!.map(({ n }, i) => [n, closeOver(applyTy(subst, collected![i]![0]))] as [string, Scheme])
    let out!: [Map<string, Scheme>, TC, KC]
    mergeT(an, schemes, () => {
      out = inferGroups(rest)
    })
    return [out![0], [...allTcs, ...out![1]], [...allKcs, ...out![2]]]
  }
  return inferGroups(groups)
}

// ----------------------------------------------------------------- kinds ---

function kindInfer(an: AN, t: Ty): [Kind, KC] {
  switch (t.k) {
    case 'var':
    case 'con': {
      const k = lookupK(an, t.n)
      return [k, []]
    }
    case 'tup': {
      const kinds: Kind[] = []
      let cs: KC = []
      for (const x of t.ts) {
        const [k, c] = kindInfer(an, x)
        kinds.unshift(k)
        cs = [...cs, ...c]
      }
      const len = t.ts.length
      return [{ k: 'star' }, [...kinds.map((k) => [{ k: 'star' } as Kind, k] as [Kind, Kind]), ...cs]]
    }
    case 'arr': {
      const [kl, csl] = kindInfer(an, t.a)
      const [kr, csr] = kindInfer(an, t.b)
      return [{ k: 'star' }, [[{ k: 'star' }, kl], [{ k: 'star' }, kr], ...csl, ...csr]]
    }
    case 'app': {
      const [kl, csl] = kindInfer(an, t.a)
      const [kr, csr] = kindInfer(an, t.b)
      const v: Kind = { k: 'kvar', n: an.fresh() }
      return [v, [[kl, { k: 'arr', a: kr, b: v }], ...csl, ...csr]]
    }
    case 'op': {
      const v: Kind = { k: 'kvar', n: an.fresh() }
      let res!: [Kind, KC]
      putK(an, t.v, v, () => { res = kindInfer(an, t.t) })
      // TyOp par (TyOp par' type') vs TyOp par type'
      if (t.t.k === 'op') return [{ k: 'arr', a: v, b: res![0] }, res![1]]
      return [{ k: 'arr', a: v, b: res![0] }, [[res![0], { k: 'star' }], ...res![1]]]
    }
  }
}

function specifyKvars(k: Kind): Kind {
  switch (k.k) {
    case 'star': return k
    case 'kvar': return { k: 'star' }
    case 'arr': return { k: 'arr', a: specifyKvars(k.a), b: specifyKvars(k.b) }
  }
}

function kindOf(env: AEnv, t: Ty): Kind {
  const an = new AN(env)
  const [k, cs] = kindInfer(an, t)
  const subst = runSolveKind(cs)
  return applyKind(subst, k)
}

function analyzeTypes(an: AN, decls: [string, Decl][]): [[string, Kind][], KC] {
  const names = decls.map(([n]) => n)
  const freshs = names.map((): Kind => ({ k: 'kvar', n: an.fresh() }))
  const pairs = names.map((n, i) => [n, freshs[i]!] as [string, Kind])
  let out!: [[string, Kind][], KC]
  mergeK(an, pairs, () => {
    out = analyzeTypesGo(an, decls)
  })
  return out!
}

function analyzeTypesGo(an: AN, decls: [string, Decl][]): [[string, Kind][], KC] {
  if (decls.length === 0) return [[], []]
  const [[name, d], ...rest] = decls as [[string, Decl], ...[string, Decl][]]
  if (d.k === 'alias') {
    const [k, cs] = kindInfer(an, d.t)
    let tail!: [[string, Kind][], KC]
    putK(an, name, k, () => {
      tail = analyzeTypesGo(an, rest)
    })
    return [[[name, k], ...tail![0]], [...cs, ...tail![1]]]
  }
  // DataDecl
  const tparams = (d as { k: 'data'; n: string; ps: string[]; cs: ConDecl[] }).ps
  const pks: Kind[] = tparams.map((): Kind => ({ k: 'kvar', n: an.fresh() }))
  const pairs = tparams.map((p, i) => [p, pks[i]!] as [string, Kind])
  let res!: [Kind, KC]
  mergeK(an, pairs, () => {
    res = analyzeDataDeclKind(an, d as { k: 'data'; n: string; ps: string[]; cs: ConDecl[] })
  })
  const orig = lookupK(an, name)
  const [tail, tcs] = analyzeTypesGo(an, rest)
  return [[[name, res![0]], ...tail], [[orig, res![0]], ...res![1], ...tcs]]
}

function analyzeDataDeclKind(an: AN, d: { k: 'data'; n: string; ps: string[]; cs: ConDecl[] }): [Kind, KC] {
  const origParams = d.ps.map((p) => lookupK(an, p))
  const main: Kind = origParams.reduceRight<Kind>((a, b) => ({ k: 'arr', a: b, b: a }), { k: 'star' })
  const orig = lookupK(an, d.n)
  const constrs: KC = []
  for (const c of d.cs) {
    for (const t of c.ts) {
      const [k, cs] = kindInfer(an, t)
      constrs.push([{ k: 'star' }, k], ...cs)
    }
  }
  return [orig, [[orig, main], ...constrs]]
}

// ------------------------------------------------------- type synonyms ---

function typeEval(an: AN, t: Ty): Ty {
  switch (t.k) {
    case 'var': {
      const hit = an.env.alienv.get(t.n)
      return hit ? typeEval(an, hit) : t
    }
    case 'con': {
      const hit = an.env.alienv.get(t.n)
      return hit ? typeEval(an, hit) : t
    }
    case 'tup':
      return { k: 'tup', ts: t.ts.map((x) => typeEval(an, x)) }
    case 'arr':
      return { k: 'arr', a: typeEval(an, t.a), b: typeEval(an, t.b) }
    case 'op': {
      const nt = typeEval(an, t.t)
      return { k: 'op', v: t.v, t: nt }
    }
    case 'app': {
      const l = typeEval(an, t.a)
      const r = typeEval(an, t.b)
      return tyApp(an, l, r)
    }
  }
}

function tyApp(an: AN, op: Ty, arg: Ty): Ty {
  if (op.k !== 'op') return { k: 'app', a: op, b: arg }
  const free = freeTy(arg)
  const bound = collectBound(op)
  const reserved = new Set([...free, ...bound])
  const renamed = renameTy(an, reserved, op)
  if (renamed.k !== 'op') return { k: 'app', a: renamed, b: arg }
  let res!: Ty
  putA(an, renamed.v, arg, () => {
    res = typeEval(an, renamed.t)
  })
  return res!
}

function collectBound(t: Ty, acc = new Set<string>()): Set<string> {
  switch (t.k) {
    case 'var': acc.add(t.n); break
    case 'tup': t.ts.forEach((x) => collectBound(x, acc)); break
    case 'arr': collectBound(t.a, acc); collectBound(t.b, acc); break
    case 'app': collectBound(t.a, acc); collectBound(t.b, acc); break
    case 'op': acc.add(t.v); collectBound(t.t, acc); break
    default: break
  }
  return acc
}

function renameTy(an: AN, avoid: Set<string>, t: Ty): Ty {
  if (t.k !== 'op') return t
  const n = an.realFresh(avoid)
  const body = renameTy(an, avoid, t.t)
  const sub = new Map([[t.v, { k: 'var', n } as Ty]])
  return { k: 'op', v: n, t: applyTy(sub, body) }
}

// ------------------------------------------------- expansion & modules ---

function expandExpr(an: AN, e: Expr): Expr {
  switch (e.k) {
    case 'ann':
      return { k: 'ann', e: expandExpr(an, e.e), t: typeEval(an, e.t) }
    case 'lam':
      return { k: 'lam', v: e.v, b: expandExpr(an, e.b) }
    case 'app':
      return { k: 'app', f: expandExpr(an, e.f), a: expandExpr(an, e.a) }
    case 'tup':
      return { k: 'tup', ts: e.ts.map((x) => expandExpr(an, x)) }
    case 'if':
      return { k: 'if', c: expandExpr(an, e.c), t: expandExpr(an, e.t), e: expandExpr(an, e.e) }
    case 'let':
      return { k: 'let', bs: e.bs.map(([n, v]) => [n, expandExpr(an, v)] as [string, Expr]), b: expandExpr(an, e.b) }
    default:
      return e
  }
}

function expandConstr(an: AN, c: ConDecl): ConDecl {
  return { n: c.n, ts: c.ts.map((t) => typeEval(an, t)) }
}

function expandDecl(an: AN, d: Decl): Decl {
  switch (d.k) {
    case 'bind':
      return { k: 'bind', n: d.n, e: expandExpr(an, d.e) }
    case 'data':
      return { k: 'data', n: d.n, ps: d.ps, cs: d.cs.map((c) => expandConstr(an, c)) }
    case 'alias':
      return { k: 'alias', n: d.n, t: typeEval(an, d.t) }
  }
}

function checkSynonymCycles(an: AN, decls: Decl[]): void {
  const pairs = decls.filter((d): d is { k: 'alias'; n: string; t: Ty } => d.k === 'alias').map((d) => [d.n, d.t] as [string, Ty])
  const indexed = indexBindings(pairs)
  const nodes = pairs.map(([n, t], i) => ({ n, t, i, deps: [...aliasDeps(t, indexed)] }))
  const groups = tarjan(nodes, (x) => x.i, (x) => x.deps)
  for (const g of groups) {
    if (g.length > 1 || (g.length === 1 && g[0]!.deps.includes(g[0]!.i))) {
      fail({ k: 'SynonymCycle', ds: g.map(({ n, t }) => [n, t] as [string, Ty]) })
    }
  }
}

function aliasDeps(t: Ty, idx: Map<string, number>): Set<number> {
  const out = new Set<number>()
  const go = (x: Ty): void => {
    if (x.k === 'con') {
      const i = idx.get(x.n)
      if (i !== undefined) out.add(i)
    } else if (x.k === 'var') {
      // TyVar: no deps (matches upstream: only TyCon counts)
    } else if (x.k === 'tup') x.ts.forEach(go)
    else if (x.k === 'arr') { go(x.a); go(x.b) }
    else if (x.k === 'app') { go(x.a); go(x.b) }
    else if (x.k === 'op') go(x.t)
  }
  go(t)
  return out
}

function analyzeTopDecls(an: AN, pairs: [string, Expr][]): [Map<string, Scheme>, KC] {
  const [tenv, , kcs] = inferDefinitions(an, pairs)
  return [tenv, kcs]
}

export interface ModResult {
  aenv: AEnv
  kindBindings: [string, Kind][]
}

function analyzeModule(an: AN, decls: Decl[]): { aenv: AEnv } {
  // process'declarations: register env addrs, build thunks, add data types
  const proc = processDecls(an, decls)
  const aliEntries = decls.filter((d): d is { k: 'alias'; n: string; t: Ty } => d.k === 'alias').map((d) => [d.n, d.t] as [string, Ty])
  const aliExt = new Map([...proc.alienv, ...aliEntries])
  return an.local(
    (e) => ({ kenv: e.kenv, tenv: proc.tenv, alienv: aliExt }),
    () => {
      const funs = decls.filter((d) => d.k === 'bind').map((d) => [d.n, (d as { k: 'bind'; n: string; e: Expr }).e] as [string, Expr])
      const aliases = decls.filter((d) => d.k === 'alias')
      const types = decls.filter((d) => d.k === 'data' || d.k === 'alias')
      checkSynonymCycles(an, aliases)
      const expandedFuns = funs.map(([n, e]) => [n, expandExpr(an, e)] as [string, Expr])
      const expandedTypes = types.map((d) => expandDecl(an, d)).map((d): [string, Decl] => {
        if (d.k === 'data') return [d.n, d]
        return [(d as { k: 'alias'; n: string; t: Ty }).n, d]
      })
      const [kindBindings, kcs] = analyzeTypes(an, expandedTypes)
      const [tenv, kcs2] = an.local((e) => {
        const k = new Map(e.kenv)
        for (const [n, kk] of kindBindings) k.set(n, kk)
        return { ...e, kenv: k }
      }, () => analyzeTopDecls(an, expandedFuns))
      const subst = runSolveKind([...kcs, ...kcs2])
      const kenv = new Map(an.env.kenv)
      for (const [n, kk] of kindBindings) kenv.set(n, kk)
      const kenv2 = new Map<string, Kind>()
      for (const [n, kk] of kenv) kenv2.set(n, specifyKvars(applyKind(subst, kk)))
      const aliOut = new Map(an.env.alienv)
      return { aenv: { kenv: kenv2, tenv, alienv: aliOut } }
    },
  )
}

function processDecls(an: AN, decls: Decl[]): { tenv: Map<string, Scheme>; alienv: Map<string, Ty> } {
  // NOTE: value env/memory are handled by the interpreter layer (see below);
  // here we only compute the data-constructor/eliminator type schemes.
  let tenv = new Map(an.env.tenv)
  for (const d of decls) {
    if (d.k !== 'data') continue
    const resultT = d.ps.reduce<Ty>((a, v) => ({ k: 'app', a, b: { k: 'var', n: v } }), { k: 'con', n: d.n })
    for (const c of d.cs) {
      const ty = c.ts.reduceRight<Ty>((acc, a) => ({ k: 'arr', a, b: acc }), resultT)
      const vars = [...freeTy(ty)].sort()
      tenv.set(c.n, { vars, t: ty })
    }
    const free = new Set<string>([...freeTy(resultT)])
    for (const c of d.cs) for (const t of c.ts) for (const v of freeTy(t)) free.add(v)
    const resName = an.realFresh(free)
    const destrs = d.cs.map((c) => c.ts.reduceRight<Ty>((acc, a) => ({ k: 'arr', a, b: acc }), { k: 'var', n: resName }))
    const whichT = destrs.reduceRight<Ty>((acc, a) => ({ k: 'arr', a, b: acc }), { k: 'var', n: resName })
    const full: Ty = { k: 'arr', a: resultT, b: whichT }
    tenv.set(`which-${d.n}`, generalize(new Map(), full))
  }
  return { tenv, alienv: new Map(an.env.alienv) }
}

export function inferExpression(an: AN, e: Expr): Scheme {
  const ex = expandExpr(an, e)
  const [t, tcs, kcs] = infer(an, ex)
  const subst = runSolveTy(tcs)
  runSolveKind(kcs)
  return closeOver(applyTy(subst, t))
}

// ------------------------------------------------------------ interpreter ---

export type VEnv = Map<string, number>
export type Mem = Map<number, Value>

export type Value =
  | { k: 'op'; n: string }
  | { k: 'lit'; l: Lit }
  | { k: 'lam'; v: string; b: Expr; env: VEnv }
  | { k: 'tup'; vs: Value[] }
  | { k: 'thunk'; f: (env: VEnv, mem: Mem, ctl: Ctl) => Promise<[ERes, Mem]>; env: VEnv; addr: number }
  | { k: 'data'; n: string; args: Value[] }

type ERes = { ok: true; v: Value } | { ok: false; e: EEval }

export type EEval =
  | { k: 'UnboundVar'; n: string }
  | { k: 'BadOp'; op: string; v: Value }
  | { k: 'IndexOut'; i: number }
  | { k: 'NilHead' }
  | { k: 'NilTail' }
  | { k: 'EmptyString' }
  | { k: 'DivByZero'; l: number }
  | { k: 'Unexpected'; m: string }

export const showEvalErr = (e: EEval): string => {
  switch (e.k) {
    case 'UnboundVar': return `Unknown variable ${e.n}`
    case 'BadOp': return `Bad use of the operator ${e.op}\n  in the expression \n    (${e.op})`
    case 'IndexOut': return `Index out of bound error. (${e.i})`
    case 'NilHead': return 'Native function #head called on an empty list.'
    case 'NilTail': return 'Native function #tail called on an empty list.'
    case 'EmptyString': return 'Operation called with an empty string.'
    case 'DivByZero': return `Division by zero error. (${e.l} / 0)`
    case 'Unexpected': return `Unexpected: ${e.m}`
  }
}

const okV = (v: Value): ERes => ({ ok: true, v })
const errV = (e: EEval): ERes => ({ ok: false, e })

// ------------------------------------------------------ async evaluator ---

export interface Ctl {
  abort: boolean
  ops: number
}

export class Interrupted {}

async function tick(ctl: Ctl): Promise<void> {
  if ((++ctl.ops & 1023) === 0) {
    await yieldToUI()
    if (ctl.abort) throw new Interrupted()
  }
}

export async function forceVal(v: Value, mem: Mem, ctl: Ctl): Promise<[ERes, Mem]> {
  let cur = v
  let m = mem
  for (;;) {
    await tick(ctl)
    if (cur.k !== 'thunk') return [okV(cur), m]
    const [r, m2] = await cur.f(cur.env, m, ctl)
    m = m2
    if (!r.ok) return [r, m]
    m = new Map(m)
    m.set(cur.addr, r.v)
    cur = r.v
  }
}

async function forceE(e: Expr, env: VEnv, mem: Mem, ctl: Ctl): Promise<[ERes, Mem]> {
  await tick(ctl)
  const [r, m1] = await evaluate(e, env, mem, ctl)
  if (!r.ok) return [r, m1]
  if (r.v.k !== 'thunk') return [r, m1]
  const [r2, m2] = await r.v.f(r.v.env, m1, ctl)
  if (!r2.ok) return [r2, m2]
  const m3 = new Map(m2)
  m3.set(r.v.addr, r2.v)
  return forceVal(r2.v, m3, ctl)
}

function mkThunk(e: Expr, env: VEnv, addr: number, ctl: Ctl): Value {
  // NOTE: like upstream, the thunk closes over its defining environment;
  // memory is supplied fresh at forcing time, never captured.
  return { k: 'thunk', f: (ee, mm, cc) => forceE(e, ee, mm, cc), env, addr }
}

export async function evaluate(e: Expr, env: VEnv, mem: Mem, ctl: Ctl): Promise<[ERes, Mem]> {
  await tick(ctl)
  switch (e.k) {
    case 'var': {
      const addr = env.get(e.n)
      if (addr === undefined) return [errV({ k: 'UnboundVar', n: e.n }), mem]
      const v = mem.get(addr)
      if (v === undefined) return [errV({ k: 'Unexpected', m: `Value of ${e.n} not found in the memory for some reason.` }), mem]
      return [okV(v), mem]
    }
    case 'op':
      return [okV({ k: 'op', n: e.n }), mem]
    case 'lit':
      return [okV({ k: 'lit', l: e.l }), mem]
    case 'tup': {
      const vs = e.ts.map((x) => mkThunk(x, env, -1, ctl))
      return [okV({ k: 'tup', vs }), mem]
    }
    case 'let': {
      const env2 = new Map(env)
      for (const [n] of e.bs) env2.set(n, env2.size)
      let m = mem
      for (const [n, ex] of e.bs) {
        const addr = env2.get(n)!
        const val = mkThunk(ex, env2, addr, ctl)
        m = new Map(m)
        m.set(addr, val)
      }
      return evaluate(e.b, env2, m, ctl)
    }
    case 'lam':
      return [okV({ k: 'lam', v: e.v, b: e.b, env }), mem]
    case 'app': {
      if (e.f.k === 'lam') {
        const addr = mem.size
        const th = mkThunk(e.a, env, addr, ctl)
        const m2 = new Map(mem)
        m2.set(addr, th)
        const env2 = new Map(env)
        env2.set(e.f.v, addr)
        return evaluate(e.f.b, env2, m2, ctl)
      }
      if (e.f.k === 'op') {
        const [r, m2] = await forceE(e.a, env, mem, ctl)
        if (!r.ok) return [r, m2]
        return applyOperator(e.f.n, r.v, m2, ctl)
      }
      const [r, m2] = await forceE(e.f, env, mem, ctl)
      if (!r.ok) return [r, m2]
      const f = r.v
      if (f.k === 'lam') {
        const addr = m2.size
        const th = mkThunk(e.a, env, addr, ctl)
        const m3 = new Map(m2)
        m3.set(addr, th)
        const env2 = new Map(f.env)
        env2.set(f.v, addr)
        return evaluate(f.b, env2, m3, ctl)
      }
      if (f.k === 'op') return evaluate({ k: 'app', f, a: e.a }, env, m2, ctl)
      return [errV({ k: 'Unexpected', m: `Cannot apply ${showValInner(f)}.` }), m2]
    }
    case 'if': {
      const [r, m2] = await forceE(e.c, env, mem, ctl)
      if (!r.ok) return [r, m2]
      if (r.v.k === 'data' && r.v.args.length === 0) {
        if (r.v.n === 'True') return evaluate(e.t, env, m2, ctl)
        return evaluate(e.e, env, m2, ctl)
      }
      return [errV({ k: 'Unexpected', m: 'If on a non-Boolean value.' }), m2]
    }
    case 'intro': {
      const vs = e.args.map((x) => mkThunk(x, env, -1, ctl))
      return [okV({ k: 'data', n: e.n, args: vs }), mem]
    }
    case 'elim': {
      const [r, m2] = await forceE(e.v, env, mem, ctl)
      if (!r.ok) return [r, m2]
      if (r.v.k !== 'data') return [errV({ k: 'Unexpected', m: 'Eliminee is not data.' }), m2]
      const sc = r.v
      const found = e.cons.map((c, i) => [c, e.ds[i]!] as const).find(([c]) => c.n === sc.n)
      if (!found) return [errV({ k: 'Unexpected', m: `No eliminator branch for ${sc.n}.` }), m2]
      const [, destr] = found
      const [rd, m3] = await forceE(destr, env, m2, ctl)
      if (!rd.ok) return [rd, m3]
      const dv = rd.v
      if (r.v.args.length === 0) return [okV(dv), m3]
      if (dv.k === 'lam') return applyClosure(r.v.args, dv, m3, ctl)
      if (dv.k === 'op' && r.v.args.length === 1) {
        const [rr, m4] = await forceVal(r.v.args[0]!, m3, ctl)
        if (!rr.ok) return [rr, m4]
        return applyOperator(dv.n, rr.v, m4, ctl)
      }
      return [errV({ k: 'Unexpected', m: 'Bad eliminator branch.' }), m3]
    }
    case 'ann':
      return evaluate(e.e, env, mem, ctl)
  }
}

async function applyClosure(args: Value[], lam: { v: string; b: Expr; env: VEnv }, mem: Mem, ctl: Ctl): Promise<[ERes, Mem]> {
  if (args.length === 0) return [okV({ k: 'lam', v: lam.v, b: lam.b, env: lam.env }), mem]
  const [v, ...rest] = args
  const addr = mem.size
  const m2 = new Map(mem)
  m2.set(addr, v!)
  const env2 = new Map(lam.env)
  env2.set(lam.v, addr)
  const [r, m3] = await forceE(lam.b, env2, m2, ctl)
  if (!r.ok) return [r, m3]
  if (r.v.k !== 'lam') {
    if (rest.length === 0) return [okV(r.v), m3]
    return [errV({ k: 'Unexpected', m: 'Over-applied eliminator branch.' }), m3]
  }
  return applyClosure(rest, { v: r.v.v, b: r.v.b, env: r.v.env }, m3, ctl)
}

function litRank(l: Lit): number {
  return l.k === 'int' ? 0 : l.k === 'dbl' ? 1 : 2
}

function litEq(a: Lit, b: Lit): boolean {
  if (a.k !== b.k) return false
  return a.v === (b as { v: unknown }).v
}

function litLt(a: Lit, b: Lit): boolean {
  const ra = litRank(a)
  const rb = litRank(b)
  if (ra !== rb) return ra < rb
  if (a.k === 'chr' && b.k === 'chr') return a.v < b.v
  return (a.v as number) < (b as { v: number }).v
}

async function applyOperator(op: string, val: Value, mem: Mem, ctl: Ctl): Promise<[ERes, Mem]> {
  const pair = (v: Value): [Value, Value] | null =>
    v.k === 'tup' && v.vs.length === 2 ? [v.vs[0]!, v.vs[1]!] : null;
  const binLit = async (f: (a: Lit, b: Lit) => ERes | null): Promise<[ERes, Mem]> => {
    const p = pair(val)
    if (!p) return [errV({ k: 'BadOp', op, v: val }), mem]
    const [ra, m2] = await forceVal(p[0], mem, ctl)
    if (!ra.ok) return [ra, m2]
    const [rb, m3] = await forceVal(p[1], m2, ctl)
    if (!rb.ok) return [rb, m3]
    if (ra.v.k !== 'lit' || rb.v.k !== 'lit') return [errV({ k: 'BadOp', op, v: val }), m3]
    const r = f(ra.v.l, rb.v.l)
    return [r ?? errV({ k: 'BadOp', op, v: val }), m3]
  }
  switch (op) {
    case '#=':
      return binLit((a, b) => okV(toBool(litEq(a, b))))
    case '#<':
      return binLit((a, b) => okV(toBool(litLt(a, b))))
    case '#>':
      return binLit((a, b) => okV(toBool(litLt(b, a))))
    case '#+':
      return binLit((a, b) => (a.k === 'int' && b.k === 'int' ? okV({ k: 'lit', l: { k: 'int', v: a.v + b.v } }) : null))
    case '#+.':
      return binLit((a, b) => (a.k === 'dbl' && b.k === 'dbl' ? okV({ k: 'lit', l: { k: 'dbl', v: a.v + b.v } }) : null))
    case '#*':
      return binLit((a, b) => (a.k === 'int' && b.k === 'int' ? okV({ k: 'lit', l: { k: 'int', v: a.v * b.v } }) : null))
    case '#*.':
      return binLit((a, b) => (a.k === 'dbl' && b.k === 'dbl' ? okV({ k: 'lit', l: { k: 'dbl', v: a.v * b.v } }) : null))
    case '#-':
      return binLit((a, b) => (a.k === 'int' && b.k === 'int' ? okV({ k: 'lit', l: { k: 'int', v: a.v - b.v } }) : null))
    case '#-.':
      return binLit((a, b) => (a.k === 'dbl' && b.k === 'dbl' ? okV({ k: 'lit', l: { k: 'dbl', v: a.v - b.v } }) : null))
    case '#div': {
      const p = pair(val)
      if (!p) return [errV({ k: 'BadOp', op, v: val }), mem]
      const [ra, m2] = await forceVal(p[0], mem, ctl)
      if (!ra.ok) return [ra, m2]
      const [rb, m3] = await forceVal(p[1], m2, ctl)
      if (!rb.ok) return [rb, m3]
      if (ra.v.k !== 'lit' || rb.v.k !== 'lit') return [errV({ k: 'BadOp', op, v: val }), m3]
      const la = ra.v.l
      const lb = rb.v.l
      if (la.k !== 'int' || lb.k !== 'int') {
        return [errV({ k: 'BadOp', op, v: val }), m3]
      }
      if (lb.v === 0) return [errV({ k: 'DivByZero', l: la.v }), m3]
      return [okV({ k: 'lit', l: { k: 'int', v: Math.floor(la.v / lb.v) } }), m3]
    }
    case '#/': {
      const p = pair(val)
      if (!p) return [errV({ k: 'BadOp', op, v: val }), mem]
      const [ra, m2] = await forceVal(p[0], mem, ctl)
      if (!ra.ok) return [ra, m2]
      const [rb, m3] = await forceVal(p[1], m2, ctl)
      if (!rb.ok) return [rb, m3]
      if (ra.v.k !== 'lit' || rb.v.k !== 'lit') return [errV({ k: 'BadOp', op, v: val }), m3]
      const la = ra.v.l
      const lb = rb.v.l
      if (la.k !== 'dbl' || lb.k !== 'dbl') {
        return [errV({ k: 'BadOp', op, v: val }), m3]
      }
      if (lb.v === 0) return [errV({ k: 'DivByZero', l: 0 }), m3]
      return [okV({ k: 'lit', l: { k: 'dbl', v: la.v / lb.v } }), m3]
    }
    case '#fst': {
      const p = pair(val)
      if (!p) return [errV({ k: 'BadOp', op, v: val }), mem]
      return [okV(p[0]), mem]
    }
    case '#snd': {
      const p = pair(val)
      if (!p) return [errV({ k: 'BadOp', op, v: val }), mem]
      return [okV(p[1]), mem]
    }
    case '#show': {
      const [r, m2] = await forceVal(val, mem, ctl)
      if (!r.ok) return [r, m2]
      return [okV(strToValue(showValInner(r.v))), m2]
    }
    case '#debug': {
      const [r, m2] = await forceVal(val, mem, ctl)
      if (!r.ok) return [r, m2]
      console.debug(`@debug:  \`${showValInner(r.v)}\``)
      return [okV(r.v), m2]
    }
    default:
      return [errV({ k: 'BadOp', op, v: val }), mem]
  }
}

const toBool = (b: boolean): Value => ({ k: 'data', n: b ? 'True' : 'False', args: [] })

function strToValue(s: string): Value {
  let out: Value = { k: 'data', n: '[]', args: [] }
  for (let i = s.length - 1; i >= 0; i--) {
    out = { k: 'data', n: ':', args: [{ k: 'lit', l: { k: 'chr', v: s[i]! } }, out] }
  }
  return out
}

export function showValInner(v: Value): string {
  switch (v.k) {
    case 'op': return v.n
    case 'lit': return showLit(v.l)
    case 'lam': return '<lambda>'
    case 'tup': return `(${v.vs.map((x) => (x.k === 'thunk' ? '<thunk>' : showValInner(x))).join(', ')})`
    case 'thunk': return '<thunk>'
    case 'data':
      if (v.args.length === 0) return v.n
      return `(${v.n} ${v.args.map((x) => (x.k === 'thunk' ? '<thunk>' : showValInner(x))).join(' ')})`
  }
}

// ----------------------------------------------------------------- printing ---

export type POut = { ok: true; s: string } | { ok: false; e: EEval }

export async function printState(expr: Expr, env: VEnv, mem: Mem, ctl: Ctl): Promise<[POut, Mem]> {
  const [r, m1] = await forceE(expr, env, mem, ctl)
  if (!r.ok) return [{ ok: false as const, e: r.e }, m1]
  return printGo(r.v, m1, ctl)
}

async function printGo(v: Value, mem: Mem, ctl: Ctl): Promise<[POut, Mem]> {
  await tick(ctl)
  switch (v.k) {
    case 'op':
      return [{ ok: true, s: v.n }, mem]
    case 'lit':
      return [{ ok: true, s: showLit(v.l) }, mem]
    case 'lam':
      return [{ ok: true, s: '<lambda>' }, mem]
    case 'tup': {
      const out: string[] = []
      let m = mem
      for (const x of v.vs) {
        const [r, m2] = await printGo(x, m, ctl)
        m = m2
        if (!r.ok) return [{ ok: false as const, e: r.e }, m]
        out.push(r.s)
      }
      return [{ ok: true, s: `(${out.join(', ')})` }, m]
    }
    case 'thunk': {
      const [r, m1] = await forceVal(v, mem, ctl)
      if (!r.ok) return [{ ok: false as const, e: r.e }, m1]
      const m2 = new Map(m1)
      m2.set(v.addr, r.v)
      return printGo(r.v, m2, ctl)
    }
    case 'data': {
      if (v.args.length === 0) return [{ ok: true, s: v.n }, mem]
      if (v.n === ':' && v.args.length === 2) {
        const [h, m1] = await forceVal(v.args[0]!, mem, ctl)
        if (!h.ok) return [{ ok: false as const, e: h.e }, m1]
        const [t, m2] = await forceVal(v.args[1]!, m1, ctl)
        if (!t.ok) return [{ ok: false as const, e: t.e }, m2]
        if (h.v.k === 'lit' && h.v.l.k === 'chr') {
          const [r, m3] = await printList(t.v, m2, ctl)
          if (!r.ok) return [{ ok: false as const, e: r.e }, m3]
          return [{ ok: true, s: `"${h.v.l.v}${r.s}"` }, m3]
        }
        const [hs, m3] = await printGo(h.v, m2, ctl)
        if (!hs.ok) return [{ ok: false as const, e: hs.e }, m3]
        if (t.v.k === 'data' && t.v.n === '[]' && t.v.args.length === 0) {
          return [{ ok: true, s: `[${hs.s}]` }, m3]
        }
        const [rest, m4] = await printList(t.v, m3, ctl)
        if (!rest.ok) return [{ ok: false as const, e: rest.e }, m4]
        return [{ ok: true, s: `[${hs.s}, ${rest.s}` }, m4]
      }
      const out: string[] = []
      let m = mem
      for (const x of v.args) {
        const [r, m2] = await printGo(x, m, ctl)
        m = m2
        if (!r.ok) return [{ ok: false as const, e: r.e }, m]
        out.push(r.s)
      }
      return [{ ok: true, s: `(${v.n} ${out.join(' ')})` }, m]
    }
  }
}

async function printList(v: Value, mem: Mem, ctl: Ctl): Promise<[POut, Mem]> {
  await tick(ctl)
  if (v.k === 'data' && v.n === '[]' && v.args.length === 0) return [{ ok: true, s: '' }, mem]
  if (v.k === 'data' && v.n === ':' && v.args.length === 2) {
    const [h, m1] = await forceVal(v.args[0]!, mem, ctl)
    if (!h.ok) return [{ ok: false as const, e: h.e }, m1]
    const [t, m2] = await forceVal(v.args[1]!, m1, ctl)
    if (!t.ok) return [{ ok: false as const, e: t.e }, m2]
    if (h.v.k === 'lit' && h.v.l.k === 'chr') {
      const [r, m3] = await printList(t.v, m2, ctl)
      if (!r.ok) return [{ ok: false as const, e: r.e }, m3]
      return [{ ok: true, s: `${h.v.l.v}${r.s}` }, m3]
    }
    const [hs, m3] = await printGo(h.v, m2, ctl)
    if (!hs.ok) return [{ ok: false as const, e: hs.e }, m3]
    if (t.v.k === 'data' && t.v.n === '[]' && t.v.args.length === 0) {
      return [{ ok: true, s: `${hs.s}]` }, m3]
    }
    const [rest, m4] = await printList(t.v, m3, ctl)
    if (!rest.ok) return [{ ok: false as const, e: rest.e }, m4]
    return [{ ok: true, s: `${hs.s}, ${rest.s}` }, m4]
  }
  return [{ ok: false, e: { k: 'Unexpected', m: `Something unexpected happened: ${showValInner(v)}` } }, mem]
}

// ----------------------------------------------------------------- engine ---

const isCmdPrefix = (line: string): boolean =>
  /^:exit/.test(line) || /^:load /.test(line) || /^:q/.test(line) || /^:Q/.test(line);

function buildValueEnv(decls: Decl[], env: VEnv): VEnv {
  const e2 = new Map(env)
  for (const d of decls) {
    if (d.k === 'bind') {
      e2.set(d.n, e2.size)
    } else if (d.k === 'data') {
      for (const c of d.cs) e2.set(c.n, e2.size)
      e2.set(`which-${d.n}`, e2.size)
    }
  }
  return e2
}

function buildMemory(decls: Decl[], env: VEnv, mem: Mem, ctl: Ctl): Mem {
  let m = new Map(mem)
  for (const d of decls) {
    if (d.k === 'bind') {
      const addr = env.get(d.n)!
      const th: Value = { k: 'thunk', f: (ee, mm, cc) => forceE(d.e, ee, mm, cc), env, addr }
      m = new Map(m)
      m.set(addr, th)
    } else if (d.k === 'data') {
      for (const c of d.cs) {
        const addr = env.get(c.n)!
        const params = c.ts.map((_, i) => `p${i + 1}`)
        const intro: Expr = { k: 'intro', n: c.n, args: params.map((v) => ({ k: 'var', n: v }) as Expr) }
        const conlam = params.reduceRight<Expr>((acc, v) => ({ k: 'lam', v, b: acc }), intro)
        const th: Value = { k: 'thunk', f: (ee, mm, cc) => forceE(conlam, ee, mm, cc), env: new Map(), addr }
        m = new Map(m)
        m.set(addr, th)
      }
      const addr = env.get(`which-${d.n}`)!
      const params = d.cs.map((_, i) => `destr${i + 1}`)
      const elim: Expr = {
        k: 'elim',
        cons: d.cs,
        v: { k: 'var', n: 'value' },
        ds: params.map((v) => ({ k: 'var', n: v }) as Expr),
      }
      const inner = params.reduceRight<Expr>((acc, v) => ({ k: 'lam', v, b: acc }), elim)
      const whichlam: Expr = { k: 'lam', v: 'value', b: inner }
      const th: Value = { k: 'thunk', f: (ee, mm, cc) => forceE(whichlam, ee, mm, cc), env, addr }
      m = new Map(m)
      m.set(addr, th)
    }
  }
  return m
}

export class FreaEngine implements Engine {
  readonly id = 'frea'
  private env: VEnv = new Map()
  private aenv: AEnv = emptyAEnv()
  private mem: Mem = new Map()
  private buf: string[] | null = null
  private files = new Map<string, string>()
  private editorContent = ''
  private ctl: Ctl = { abort: false, ops: 0 }

  constructor() {
    this.loadPrelude()
  }

  banner(): string {
    return 'Glamorous Frea REPL.\n'
  }
  prompt(): string {
    return this.buf !== null ? '         ' : 'frea λ > '
  }
  editorAliases(): string[] {
    return ['editor.frea', 'demo.frea', 'editor', 'demo']
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
    this.env = new Map()
    this.aenv = emptyAEnv()
    this.mem = new Map()
    this.buf = null
    this.loadPrelude()
  }
  interrupt(): void {
    this.ctl.abort = true
  }

  private loadPrelude(): void {
    try {
      const prog = this.parseProgram(preludeSrc)
      if (!('decls' in prog)) return
      const an = new AN(this.aenv)
      const env2 = buildValueEnv(prog.decls, this.env)
      const mem2 = buildMemory(prog.decls, env2, this.mem, this.ctl)
      const { aenv } = analyzeModule(an, prog.decls)
      this.env = env2
      this.mem = mem2
      this.aenv = aenv
    } catch (e) {
      console.error('Frea prelude failed to load:', e)
    }
  }

  private parseProgram(src: string): { decls: Decl[] } | { expr: Expr } {
    const toks = lexFrea(src)
    const p = new P(toks)
    let out: { decls: Decl[] } | { expr: Expr }
    const t = p.peek()
    if (t.t === 'kw' && (t as { v: string }).v === 'module') out = { decls: parseModule(p) }
    else out = { expr: parseExp(p) }
    if (!p.is('eof')) throw { msg: `Parse error on line 1, column ${p.peek().i + 1}.` }
    return out
  }

  async handle(rawLine: string): Promise<EngineResult> {
    const line = rawLine.replace(/\r$/, '')
    this.ctl = { abort: false, ops: 0 }
    const ctl = this.ctl
    if (this.buf !== null) {
      if (line === '' || isCmdPrefix(line)) {
        const text = [...this.buf, line].join('\n')
        this.buf = null
        return this.process(text, ctl)
      }
      this.buf.push(line)
      return { output: '' }
    }
    if (line === '') return { output: '' }
    if (isCmdPrefix(line)) return this.process(line, ctl)
    this.buf = [line]
    return { output: '' }
  }

  private async process(text: string, ctl: Ctl): Promise<EngineResult> {
    if (text === '') return { output: '' }
    if (text === ':exit') return { output: 'Bye!', halted: true }
    if (text.startsWith(':load ')) return this.loadCmd(text.slice(6).trim(), ctl)
    if (text === ':q') return { output: 'Bye!', halted: true }
    if (text === ':Q') return { output: 'Bye!', halted: true }
    if (text.startsWith(':t')) return this.typeCmd(text.slice(2))
    if (text.startsWith(':k')) return this.kindCmd(text.slice(2))
    return this.exprOrDecls(text, ctl)
  }

  private async typeCmd(rest: string): Promise<EngineResult> {
    let prog: { decls: Decl[] } | { expr: Expr }
    try {
      prog = this.parseProgram(rest)
    } catch (e: unknown) {
      return { output: `Parse Error: ${parseMsg(e)}` }
    }
    if ('decls' in prog) return { output: 'Incorrect Format! The :t command must be followed by an expression, not a declaration.' }
    try {
      const an = new AN(this.aenv)
      const scheme = inferExpression(an, prog.expr)
      return { output: `         ${rest.trim()} :: ${showScheme(scheme)}` }
    } catch (e: unknown) {
      return { output: `Type Error: ${showFError(asErr(e))}` }
    }
  }

  private async kindCmd(rest: string): Promise<EngineResult> {
    let ty: Ty
    try {
      const toks = lexFrea(rest)
      const p = new P(toks)
      ty = parseType(p)
      if (!p.is('eof')) throw { msg: `Parse error on line 1, column ${p.peek().i + 1}.` }
    } catch (e: unknown) {
      return { output: `Parse Error: ${parseMsg(e)}` }
    }
    try {
      const k = kindOf(this.aenv, ty)
      return { output: `         ${showTy(ty)} :: ${showKind(k)}` }
    } catch (e: unknown) {
      return { output: `Kind Error: ${showFError(asErr(e))}` }
    }
  }

  private async exprOrDecls(text: string, ctl: Ctl): Promise<EngineResult> {
    let prog: { decls: Decl[] } | { expr: Expr }
    try {
      prog = this.parseProgram(text)
    } catch (e: unknown) {
      return { output: `Parse Error: ${parseMsg(e)}` }
    }
    if ('decls' in prog) {
      try {
        const an = new AN(this.aenv)
        const env2 = buildValueEnv(prog.decls, this.env)
        const mem2 = buildMemory(prog.decls, env2, this.mem, ctl)
        const { aenv } = analyzeModule(an, prog.decls)
        this.env = env2
        this.mem = mem2
        this.aenv = aenv
        return { output: '' }
      } catch (e: unknown) {
        if (e instanceof Interrupted) return { output: 'Interrupted.', interrupted: true }
        return { output: `Error ${showFError(asErr(e))}` }
      }
    }
    try {
      const an = new AN(this.aenv)
      const scheme = inferExpression(an, prog.expr)
      void scheme
      const [r, mem2] = await printState(prog.expr, this.env, this.mem, ctl)
      if (!r.ok) return { output: `Evaluation Error: ${showEvalErr(r.e)}` }
      this.mem = mem2
      return { output: `         ${r.s}` }
    } catch (e: unknown) {
      if (e instanceof Interrupted) return { output: 'Interrupted.', interrupted: true }
      if (typeof e === 'object' && e !== null && 'k' in (e as Record<string, unknown>)) {
        return { output: `Type Error: ${showFError(e as FError)}` }
      }
      throw e
    }
  }

  private async loadCmd(file: string, ctl: Ctl): Promise<EngineResult> {
    const content =
      this.files.get(file) ??
      this.files.get(file.split('/').pop()!) ??
      (this.editorAliases().includes(file) || this.editorAliases().includes(file.split('/').pop()!) ? this.editorContent : undefined);
    if (content === undefined) return { output: `Error: cannot open ${file}: file not found.` }
    let prog: { decls: Decl[] } | { expr: Expr }
    try {
      prog = this.parseProgram(content)
    } catch (e: unknown) {
      return { output: `Parse error inside module ${file}: ${parseMsg(e)}` }
    }
    if (!('decls' in prog)) return { output: `Error: ${file} must only contain declarations.` }
    try {
      const an = new AN(this.aenv)
      const env2 = buildValueEnv(prog.decls, this.env)
      const mem2 = buildMemory(prog.decls, env2, this.mem, ctl)
      const { aenv } = analyzeModule(an, prog.decls)
      this.env = env2
      this.mem = mem2
      this.aenv = aenv
      return { output: '' }
    } catch (e: unknown) {
      if (e instanceof Interrupted) return { output: 'Interrupted.', interrupted: true }
      return { output: `Error inside module ${file}: ${showFError(asErr(e))}` }
    }
  }
}

function parseMsg(e: unknown): string {
  if (e !== null && typeof e === 'object' && 'msg' in e && typeof (e as { msg: unknown }).msg === 'string') {
    return (e as { msg: string }).msg
  }
  if (e instanceof BT) return `Parse error on line 1, column ${e.at + 1}.`
  return 'Parse error.'
}

function asErr(e: unknown): FError {
  if (e !== null && typeof e === 'object' && 'k' in e) return e as FError
  return { k: 'Unexpected', m: String(e) }
}
