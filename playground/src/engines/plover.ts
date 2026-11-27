/**
 * Plover — browser-native engine.
 *
 * Faithful port of the Haskell implementation (vendored under vendor/plover):
 *  - same terms, unification with strict occurs-check, same renaming
 *  - two syntaxes: Prolog (`.pl`, `:-`, commas, periods) and natural
 *    deduction (`.nad`, dash-lines, rule names, juxtaposed goals)
 *  - breadth-first-style search: a before/current/after queue with a
 *    direction flag instead of Minilog's depth-first backtracking stack,
 *    including the `Unknown predicate: name/arity.` program error
 *  - REPL: `?- ` prompt, `:load` (parser chosen by `.nad` suffix),
 *    `:next` / `:done`, `:q` / `:Q`
 *
 * Two deliberate deviations: the empty-state parser defaults to Prolog
 * (upstream reads an uninitialized field and crashes on query-before-load),
 * and the search is bounded (step + queued-path caps) plus interruptible
 * so a diverging query can not hang the browser tab.
 */
import type { Engine, EngineResult } from './engine'
import { yieldToUI } from './engine'

// ---------------------------------------------------------------- terms ---

export type Term =
  | { k: 'var'; name: string }
  | { k: 'atom'; name: string }
  | { k: 'compound'; name: string; args: Term[] }
  | { k: 'wild' }

export interface Struct {
  name: string
  args: Term[]
}

export type Goal = { k: 'call'; fn: Struct } | { k: 'unify'; l: Term; r: Term }
export type Predicate = { k: 'fact'; fn: Struct; name: string | null } | { k: 'rule'; head: Struct; body: Goal[]; name: string | null }

export const showTerm = (t: Term): string =>
  t.k === 'var' ? t.name : t.k === 'atom' ? t.name : t.k === 'wild' ? '_' : showStruct({ name: t.name, args: t.args })
// NOTE: like the Haskell Show, a nullary struct prints with parens.
export const showStruct = (s: Struct): string => `${s.name}(${s.args.map(showTerm).join(', ')})`

// ---------------------------------------------------------------- lexer ---

type Tok =
  | { t: 'atom'; v: string }
  | { t: 'var'; v: string }
  | { t: ',' }
  | { t: '.' }
  | { t: ':-' }
  | { t: '=' }
  | { t: '(' }
  | { t: ')' }
  | { t: '_' }
  | { t: 'line' }
  | { t: 'eof' }

const isLower = (c: string) => c >= 'a' && c <= 'z'
const isUpper = (c: string) => c >= 'A' && c <= 'Z'

function lexProlog(src: string): Tok[] {
  const toks: Tok[] = []
  let i = 0
  const fail = (n: number): never => {
    throw { msg: `Lexical error (column ${n + 1}).`, col: n + 1 }
  }
  while (i < src.length) {
    const c = src[i]!
    if (c === ' ' || c === '\t' || c === '\f' || c === '\v' || c === '\n' || c === '\r') { i++; continue }
    // NOTE: like upstream, a `%` comment must be terminated by a newline.
    if (c === '%') {
      const nl = src.indexOf('\n', i)
      if (nl === -1) fail(i)
      i = nl + 1
      continue
    }
    if (c === ',') { toks.push({ t: ',' }); i++; continue }
    if (c === '.') { toks.push({ t: '.' }); i++; continue }
    if (c === '(') { toks.push({ t: '(' }); i++; continue }
    if (c === ')') { toks.push({ t: ')' }); i++; continue }
    if (c === '_') { toks.push({ t: '_' }); i++; continue }
    if (c === '=') { toks.push({ t: '=' }); i++; continue }
    if (c === ':' && src[i + 1] === '-') { toks.push({ t: ':-' }); i += 2; continue }
    if (isLower(c)) {
      let j = i
      while (j < src.length && isLower(src[j]!)) j++
      toks.push({ t: 'atom', v: src.slice(i, j) })
      i = j
      continue
    }
    if (isUpper(c)) {
      let j = i
      while (j < src.length && isUpper(src[j]!)) j++
      toks.push({ t: 'var', v: src.slice(i, j) })
      i = j
      continue
    }
    fail(i)
  }
  toks.push({ t: 'eof' })
  return toks
}

function lexNatural(src: string): Tok[] {
  const toks: Tok[] = []
  let i = 0
  const fail = (n: number): never => {
    throw { msg: `Lexical error (column ${n + 1}).`, col: n + 1 }
  }
  const tailCharL = (c: string) => c === '-' || c === ' ' || isLower(c)
  const tailCharU = (c: string) => c === '-' || c === ' ' || isUpper(c)
  while (i < src.length) {
    const c = src[i]!
    if (c === ' ' || c === '\t' || c === '\f' || c === '\v' || c === '\n' || c === '\r') { i++; continue }
    if (c === '%') {
      const nl = src.indexOf('\n', i)
      if (nl === -1) fail(i)
      i = nl + 1
      continue
    }
    if (c === ',') { toks.push({ t: ',' }); i++; continue }
    if (c === '(') { toks.push({ t: '(' }); i++; continue }
    if (c === ')') { toks.push({ t: ')' }); i++; continue }
    if (c === '_') { toks.push({ t: '_' }); i++; continue }
    if (c === '=') { toks.push({ t: '=' }); i++; continue }
    if (c === ':' && src[i + 1] === '-') { toks.push({ t: ':-' }); i += 2; continue }
    if (c === '-') {
      let j = i
      while (j < src.length && src[j] === '-') j++
      toks.push({ t: 'line' })
      i = j
      continue
    }
    if (isLower(c)) {
      let j = i + 1
      while (j < src.length && tailCharL(src[j]!)) j++
      toks.push({ t: 'atom', v: src.slice(i, j) })
      i = j
      continue
    }
    if (isUpper(c)) {
      let j = i + 1
      while (j < src.length && tailCharU(src[j]!)) j++
      toks.push({ t: 'var', v: src.slice(i, j) })
      i = j
      continue
    }
    fail(i)
  }
  toks.push({ t: 'eof' })
  return toks
}

// --------------------------------------------------------------- parser ---

class P {
  pos = 0
  constructor(public toks: Tok[]) {}
  peek(): Tok { return this.toks[this.pos]! }
  next(): Tok { return this.toks[this.pos++]! }
}

function parseStruct(p: P): Struct {
  const t = p.next()
  if (t.t !== 'atom') throw { msg: 'Parse error: expected a predicate name.', col: p.pos }
  return parseStructAt(p, t.v)
}

function parseTerm(p: P): Term {
  const t = p.next()
  if (t.t === 'var') return { k: 'var', name: t.v }
  if (t.t === 'atom') {
    if (p.peek().t === '(') {
      const s = parseStructAt(p, t.v)
      return { k: 'compound', name: s.name, args: s.args }
    }
    return { k: 'atom', name: t.v }
  }
  if (t.t === '_') return { k: 'wild' }
  throw { msg: 'Parse error: expected a term.', col: p.pos }
}

function parseStructAt(p: P, name: string): Struct {
  const open = p.next()
  if (open.t !== '(') throw { msg: 'Parse error: expected `(`.', col: p.pos }
  const args = parseTerms(p)
  const close = p.next()
  if (close.t !== ')') throw { msg: 'Parse error: expected `)`.', col: p.pos }
  return { name, args }
}

function parseTerms(p: P): Term[] {
  const out = [parseTerm(p)]
  while (p.peek().t === ',') { p.next(); out.push(parseTerm(p)) }
  return out
}

function parseGoal(p: P): Goal {
  const t = p.peek()
  if (t.t === 'atom' && p.toks[p.pos + 1]?.t === '(') {
    const s = parseStruct(p)
    if (p.peek().t === '=') { p.next(); return { k: 'unify', l: { k: 'compound', name: s.name, args: s.args }, r: parseTerm(p) } }
    return { k: 'call', fn: s }
  }
  if (t.t === 'atom') {
    p.next()
    if (p.peek().t === '=') { p.next(); return { k: 'unify', l: { k: 'atom', name: t.v }, r: parseTerm(p) } }
    throw { msg: 'Parse error: expected `(` (bare atoms are not calls here).', col: p.pos }
  }
  const lhs = parseTerm(p)
  const eq = p.next()
  if (eq.t !== '=') throw { msg: 'Parse error: expected `=`.', col: p.pos }
  return { k: 'unify', l: lhs, r: parseTerm(p) }
}

function parseGoalsComma(p: P): Goal[] {
  const gs = [parseGoal(p)]
  while (p.peek().t === ',') { p.next(); gs.push(parseGoal(p)) }
  return gs
}

function parseGoalsJuxta(p: P): Goal[] {
  const gs = [parseGoal(p)]
  for (;;) {
    const t = p.peek()
    if (t.t === 'atom' || t.t === 'var' || t.t === '(' || t.t === '_') gs.push(parseGoal(p))
    else return gs
  }
}

export function parsePrologBase(src: string): Predicate[] {
  const p = new P(lexProlog(src))
  if (p.peek().t === 'eof') throw { msg: 'Parse error: empty knowledge base.', col: 1 }
  const preds: Predicate[] = []
  while (p.peek().t !== 'eof') {
    const s = parseStruct(p)
    const nx = p.next()
    if (nx.t === '.') { preds.push({ k: 'fact', fn: s, name: null }); continue }
    if (nx.t === ':-') {
      const body = parseGoalsComma(p)
      const dot = p.next()
      if (dot.t !== '.') throw { msg: 'Parse error: expected `.`.', col: p.pos }
      preds.push({ k: 'rule', head: s, body, name: null })
      continue
    }
    throw { msg: 'Parse error: expected `.` or `:-`.', col: p.pos }
  }
  return preds
}

export function parsePrologQuery(src: string): Goal[] {
  const p = new P(lexProlog(src))
  if (p.peek().t === 'eof') throw { msg: 'Empty query.', col: 1 }
  const gs = parseGoalsComma(p)
  const dot = p.next()
  if (dot.t !== '.') throw { msg: 'Parse error: expected `.` at the end of the query.', col: p.pos }
  return gs
}

export function parseNaturalBase(src: string): Predicate[] {
  const p = new P(lexNatural(src))
  if (p.peek().t === 'eof') throw { msg: 'Parse error: empty knowledge base.', col: 1 }
  const preds: Predicate[] = []
  while (p.peek().t !== 'eof') {
    // gather a rule body or go straight to the dash line
    if (p.peek().t === 'line') {
      p.next()
      const name = parseRuleName(p)
      preds.push({ k: 'fact', fn: parseStruct(p), name })
      continue
    }
    const body = parseGoalsJuxta(p)
    const dash = p.next()
    if (dash.t !== 'line') throw { msg: 'Parse error: expected a rule line (`---`).', col: p.pos }
    const name = parseRuleName(p)
    preds.push({ k: 'rule', head: parseStruct(p), body, name })
  }
  return preds
}

function parseRuleName(p: P): string | null {
  if (p.peek().t === 'atom') return (p.next() as { t: 'atom'; v: string }).v
  return null
}

export function parseNaturalQuery(src: string): Goal[] {
  const p = new P(lexNatural(src))
  if (p.peek().t === 'eof') throw { msg: 'Empty query.', col: 1 }
  const gs = parseGoalsJuxta(p)
  if (p.peek().t !== 'eof') throw { msg: 'Parse error: unexpected input after the query.', col: p.pos }
  return gs
}

// ------------------------------------------------------------- evaluate ---

type QVars = Map<string, Term>
type Path = { goals: Goal[]; qvars: QVars }
type Dir = 'fwd' | 'bwd'
type Qu = { before: Path[]; current: Path; after: Path[]; dir: Dir } | null

interface PState {
  base: Predicate[]
  pathq: Qu
  counter: number
  natural: boolean
}

type Action =
  | { k: 'searching'; state: PState }
  | { k: 'succeeded'; state: PState }
  | { k: 'failed' }
  | { k: 'unknown'; fn: Struct }
  | { k: 'redoing'; state: PState }
  | { k: 'done' }

const freeVarsTerm = (t: Term, acc: Set<string>): void => {
  if (t.k === 'var') acc.add(t.name)
  else if (t.k === 'compound') t.args.forEach((a) => freeVarsTerm(a, acc))
}
const freeVarsGoal = (g: Goal, acc: Set<string>): void => {
  if (g.k === 'call') g.fn.args.forEach((a) => freeVarsTerm(a, acc))
  else { freeVarsTerm(g.l, acc); freeVarsTerm(g.r, acc) }
}

function lookForAll(f: Struct, base: Predicate[]): Predicate[] {
  return base.filter((pr) => {
    const h = pr.k === 'fact' ? pr.fn : pr.head
    return h.name === f.name && h.args.length === f.args.length
  })
}

function renameVal(s: { c: number; m: Map<string, string> }, t: Term): Term {
  if (t.k === 'var') {
    const hit = s.m.get(t.name)
    if (hit !== undefined) return { k: 'var', name: hit }
    const fresh = `_${s.c++}`
    s.m.set(t.name, fresh)
    return { k: 'var', name: fresh }
  }
  if (t.k === 'compound') return { k: 'compound', name: t.name, args: t.args.map((a) => renameVal(s, a)) }
  return t
}
const renameGoal = (s: { c: number; m: Map<string, string> }, g: Goal): Goal =>
  g.k === 'call'
    ? { k: 'call', fn: { name: g.fn.name, args: g.fn.args.map((a) => renameVal(s, a)) } }
    : { k: 'unify', l: renameVal(s, g.l), r: renameVal(s, g.r) };

function occurs(v: string, t: Term): boolean {
  if (t.k === 'var') return t.name === v
  if (t.k === 'atom' || t.k === 'wild') return false
  return t.args.some((a) => occurs(v, a))
}
const substVal = (from: string, to: Term, t: Term): Term =>
  t.k === 'var'
    ? (t.name === from ? to : t)
    : t.k === 'compound'
      ? { k: 'compound', name: t.name, args: t.args.map((a) => substVal(from, to, a)) }
      : t;
const substGoal = (from: string, to: Term, g: Goal): Goal =>
  g.k === 'call'
    ? { k: 'call', fn: { name: g.fn.name, args: g.fn.args.map((a) => substVal(from, to, a)) } }
    : { k: 'unify', l: substVal(from, to, g.l), r: substVal(from, to, g.r) };

function unifyPair(l: Term, r: Term, rest: Goal[], qvars: QVars): { goals: Goal[]; qvars: QVars } | null {
  if (l.k === 'wild' || r.k === 'wild') return { goals: rest, qvars }
  if (l.k === 'atom' && r.k === 'atom') return l.name === r.name ? { goals: rest, qvars } : null
  if (l.k === 'compound' && r.k === 'compound') {
    if (l.name !== r.name || l.args.length !== r.args.length) return null
    const eqs: Goal[] = l.args.map((a, i) => ({ k: 'unify', l: a, r: r.args[i]! }) as Goal)
    return { goals: [...eqs, ...rest], qvars }
  }
  if (l.k === 'var') {
    if (r.k === 'var' && r.name === l.name) return { goals: rest, qvars }
    if (occurs(l.name, r)) return null
    const goals = rest.map((g) => substGoal(l.name, r, g))
    const q2: QVars = new Map()
    for (const [k, v] of qvars) q2.set(k, substVal(l.name, r, v))
    return { goals, qvars: q2 }
  }
  if (r.k === 'var') return unifyPair(r, l, rest, qvars)
  return null
}

function toPath(counter: number, pred: Predicate, args: Term[], rest: Goal[], qvars: QVars): { counter: number; path: Path } {
  const st = { c: counter, m: new Map<string, string>() }
  let pats: Term[]
  let extra: Goal[] = []
  if (pred.k === 'fact') {
    pats = pred.fn.args.map((a) => renameVal(st, a))
  } else {
    pats = pred.head.args.map((a) => renameVal(st, a))
    extra = pred.body.map((g) => renameGoal(st, g))
  }
  const eqs: Goal[] = args.map((a, i) => ({ k: 'unify', l: a, r: pats[i]! }) as Goal)
  return { counter: st.c, path: { goals: [...eqs, ...extra, ...rest], qvars } }
}

function step(st: PState): Action {
  let s = st
  for (;;) {
    const q = s.pathq
    if (q === null) return { k: 'done' }
    // A path just finished: decide what to resume.
    if (q.current.goals.length === 0) {
      if (q.before.length === 0 && q.after.length === 0) return { k: 'done' }
      if (q.dir === 'fwd') {
        if (q.after.length > 0) {
          const [p, ...ps] = q.after
          return { k: 'redoing', state: { ...s, pathq: { before: q.before, current: p!, after: ps, dir: 'fwd' } } }
        }
        s = { ...s, pathq: { ...q, dir: 'bwd' } }
        continue
      } else {
        if (q.before.length > 0) {
          const [p, ...ps] = q.before
          return { k: 'redoing', state: { ...s, pathq: { before: ps, current: p!, after: q.after, dir: 'bwd' } } }
        }
        s = { ...s, pathq: { ...q, dir: 'fwd' } }
        continue
      }
    }
    const [head, ...rest] = q.current.goals
    if (head!.k === 'unify') {
      const u = unifyPair(head!.l, head!.r, rest, q.current.qvars)
      if (!u) {
        // fail'and'backtrack
        if (q.before.length === 0 && q.after.length === 0) return { k: 'failed' }
        if (q.dir === 'fwd') {
          if (q.after.length === 0) { s = { ...s, pathq: { ...q, dir: 'bwd' } }; continue }
          const [p, ...ps] = q.after
          s = { ...s, pathq: { ...q, current: p!, after: ps } }
          continue
        } else {
          if (q.before.length === 0) { s = { ...s, pathq: { ...q, dir: 'fwd' } }; continue }
          const [p, ...ps] = q.before
          s = { ...s, pathq: { ...q, before: ps, current: p! } }
          continue
        }
      }
      const qvars = u.qvars
      if (u.goals.length === 0) return { k: 'succeeded', state: { ...s, pathq: { ...q, current: { goals: [], qvars } } } }
      // succeed: rotate the queue around the advanced path
      if (q.before.length === 0 && q.after.length === 0) {
        return { k: 'searching', state: { ...s, pathq: { ...q, current: { goals: u.goals, qvars } } } }
      }
      if (q.dir === 'fwd') {
        if (q.after.length === 0) { s = { ...s, pathq: { ...q, dir: 'bwd' } }; continue }
        const [p, ...ps] = q.after
        return {
          k: 'searching',
          state: { ...s, pathq: { before: [...q.before, { goals: u.goals, qvars }], current: p!, after: ps, dir: 'fwd' } },
        }
      } else {
        if (q.before.length === 0) { s = { ...s, pathq: { ...q, dir: 'fwd' } }; continue }
        const [p, ...ps] = q.before
        return {
          k: 'searching',
          state: { ...s, pathq: { before: ps, current: p!, after: [...q.after, { goals: u.goals, qvars }], dir: 'bwd' } },
        }
      }
    }
    // call
    const matches = lookForAll(head!.fn, s.base)
    if (matches.length === 0) return { k: 'unknown', fn: head!.fn }
    let counter = s.counter
    const paths: Path[] = []
    for (const m of matches) {
      const r = toPath(counter, m, head!.fn.args, rest, q.current.qvars)
      counter = r.counter
      paths.push(r.path)
    }
    const added: Qu =
      q.dir === 'fwd'
        ? { before: [...paths, ...q.before], current: q.current, after: q.after, dir: q.dir }
        : { before: q.before, current: q.current, after: [...paths, ...q.after], dir: q.dir };
    // pop'path (non-empty by construction)
    if (added.dir === 'fwd') {
      if (added.after.length === 0) {
        const [p, ...ps] = added.before
        return { k: 'searching', state: { ...s, counter, pathq: { before: ps, current: p!, after: [], dir: 'bwd' } } }
      }
      const [p, ...ps] = added.after
      return { k: 'searching', state: { ...s, counter, pathq: { before: added.before, current: p!, after: ps, dir: 'fwd' } } }
    } else {
      if (added.before.length === 0) {
        const [p, ...ps] = added.after
        return { k: 'searching', state: { ...s, counter, pathq: { before: [], current: p!, after: ps, dir: 'fwd' } } }
      }
      const [p, ...ps] = added.before
      return { k: 'searching', state: { ...s, counter, pathq: { before: ps, current: p!, after: added.after, dir: 'bwd' } } }
    }
  }
}

const STEP_BUDGET = 200_000
const PATH_CAP = 5_000
const SOLUTION_CAP = 500

// ---------------------------------------------------------------- engine ---

type Mode = { k: 'idle' } | { k: 'more'; state: PState; solutions: number }

export class PloverEngine implements Engine {
  readonly id = 'plover'
  private base: Predicate[] = []
  private natural = false
  private mode: Mode = { k: 'idle' }
  private files = new Map<string, string>()
  private editorContent = ''
  private abort = false

  banner(): string {
    return 'Plover — a toy automated theorem prover.'
  }
  prompt(): string {
    return '?- '
  }
  editorAliases(): string[] {
    return ['editor.pl', 'demo.pl', 'editor.nad', 'demo.nad', 'editor', 'demo']
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
    this.base = []
    this.natural = false
    this.mode = { k: 'idle' }
    this.abort = false
  }
  interrupt(): void {
    this.abort = true
  }

  private resolveLoad(path: string): { content: string; natural: boolean } | null {
    const name = path.trim()
    if (!name) return null
    const hit = this.files.get(name) ?? this.files.get(name.split('/').pop()!)
    if (hit !== undefined) return { content: hit, natural: /\.nad$/i.test(name) }
    if (this.editorAliases().includes(name) || this.editorAliases().includes(name.split('/').pop()!)) {
      return { content: this.editorContent, natural: /\.nad$/i.test(name) }
    }
    return null
  }

  private queueSize(s: PState): number {
    if (s.pathq === null) return 0
    return s.pathq.before.length + 1 + s.pathq.after.length
  }

  async handle(rawLine: string): Promise<EngineResult> {
    const line = rawLine.replace(/\r$/, '')
    this.abort = false
    if (this.mode.k === 'more') {
      const cmd = line.trim()
      if (cmd === ':done') {
        this.mode = { k: 'idle' }
        return { output: '.' }
      }
      if (cmd === ':q' || cmd === ':Q') return { output: 'Bye!', halted: true }
      return this.continueSearch()
    }

    if (line === ':q' || line === ':Q') return { output: 'Bye!', halted: true }
    if (/^:load\b/.test(line) || /^:l\b/.test(line)) {
      const arg = line.replace(/^:[a-z]+/, '').trim()
      const found = this.resolveLoad(arg)
      if (found === null) return { output: `Could not load \`${arg}': no such virtual file (pick an example from the sidebar or save your own).` }
      const parse = found.natural ? parseNaturalBase : parsePrologBase
      try {
        this.base = parse(found.content)
        this.natural = found.natural
        this.mode = { k: 'idle' }
        return { output: `-- loaded ${this.base.length} clause(s) from \`${arg}\`` }
      } catch (e: unknown) {
        const msg = e && typeof e === 'object' && 'msg' in e ? String((e as { msg: unknown }).msg) : 'Parse error.'
        const col = e && typeof e === 'object' && 'col' in e && typeof (e as { col: unknown }).col === 'number'
          ? (e as { col: number }).col : 1
        return { output: `${' '.repeat(3 + col - 1)}^\n${msg}` }
      }
    }
    if (line.startsWith(':')) return { output: "I don't know this command, sorry." }
    if (line.trim() === '') return { output: '' }

    const parse = this.natural ? parseNaturalQuery : parsePrologQuery
    let goals: Goal[]
    try {
      goals = parse(line)
    } catch (e: unknown) {
      const msg = e && typeof e === 'object' && 'msg' in e ? String((e as { msg: unknown }).msg) : 'Parse error.'
      const col = e && typeof e === 'object' && 'col' in e && typeof (e as { col: unknown }).col === 'number'
        ? (e as { col: number }).col : 1
      return { output: `${' '.repeat(3 + col - 1)}^\n${msg}` }
    }
    const names = new Set<string>()
    goals.forEach((g) => freeVarsGoal(g, names))
    const qvars: QVars = new Map([...names].map((n) => [n, { k: 'var', name: n } as Term]))
    const state: PState = {
      base: this.base,
      pathq: { before: [], current: { goals, qvars }, after: [], dir: 'fwd' },
      counter: 0,
      natural: this.natural,
    }
    return this.drive(state, 0, true)
  }

  private printResult(qvars: QVars): string {
    if (qvars.size === 0) return 'True'
    return [...qvars.entries()].map(([k, v]) => `${k} = ${showTerm(v)}`).join('\n')
  }

  private async drive(state: PState, steps: number, first: boolean): Promise<EngineResult> {
    let cur = state
    let n = steps
    for (;;) {
      if (++n > STEP_BUDGET) {
        this.mode = { k: 'idle' }
        return { output: '… search limit reached (diverging query?). Treated as failure for this demo; try a more specific query.' }
      }
      if ((n & 1023) === 0) {
        await yieldToUI()
        if (this.abort) {
          this.abort = false
          this.mode = { k: 'idle' }
          return { output: 'Interrupted.', interrupted: true }
        }
      }
      if (this.queueSize(cur) > PATH_CAP) {
        this.mode = { k: 'idle' }
        return { output: '… queue limit reached (search fanning out?). Treated as failure for this demo.' }
      }
      const out = step(cur)
      if (out.k === 'searching') { cur = out.state; continue }
      if (out.k === 'failed') {
        if (first) return { output: 'False.' }
        this.mode = { k: 'idle' }
        return { output: 'False.' }
      }
      if (out.k === 'unknown') {
        this.mode = { k: 'idle' }
        return { output: `Unknown predicate: ${out.fn.name}/${out.fn.args.length}.` }
      }
      if (out.k === 'done') {
        this.mode = { k: 'idle' }
        return { output: 'False.' }
      }
      // succeeded: step once more to learn whether to wait for the user
      const after = step(out.state)
      const solved = out.state.pathq as Exclude<Qu, null>
      const text = this.printResult(solved.current.qvars)
      if (after.k === 'redoing') {
        if (first) {
          this.mode = { k: 'more', state: after.state, solutions: 1 }
          return { output: `${text}\n-- more solutions: :next for next, :done to stop` }
        }
        if (this.mode.k === 'more' && this.mode.solutions >= SOLUTION_CAP) {
          this.mode = { k: 'idle' }
          return { output: `${text}\n… solution cap reached.` }
        }
        this.mode = { k: 'more', state: after.state, solutions: (this.mode.k === 'more' ? this.mode.solutions + 1 : 1) }
        return { output: `  or\n\n${text}\n-- more solutions: :next for next, :done to stop` }
      }
      this.mode = { k: 'idle' }
      return { output: text }
    }
  }

  private async continueSearch(): Promise<EngineResult> {
    if (this.mode.k !== 'more') return { output: '' }
    return this.drive(this.mode.state, 0, false)
  }
}
