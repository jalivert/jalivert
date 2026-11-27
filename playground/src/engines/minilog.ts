/**
 * Minilog — browser-native engine.
 *
 * Faithful port of the Haskell implementation (vendored under vendor/minilog):
 *  - lexer: single-case identifier runs (`foo` atom, `FOO` var), `%` comments
 *  - grammar: facts / rules with `:-`, conjunctions, `=` unification goals
 *  - evaluation: the step/resume backtracking machine from Evaluate.Step
 *    with strict occurs-check (X = foo(X) fails)
 *  - REPL: `?- ` prompt, `:load <file>`, `:next` / `:done`, `:q` / `:Q`
 *
 * Search is bounded (step + solution caps) so a diverging query can not hang
 * the browser tab; hitting the cap is reported explicitly.
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
export type Predicate = { k: 'fact'; fn: Struct } | { k: 'rule'; head: Struct; body: Goal[] }

export const showTerm = (t: Term): string =>
  t.k === 'var' ? t.name : t.k === 'atom' ? t.name : t.k === 'wild' ? '_' : showStruct({ name: t.name, args: t.args })
export const showStruct = (s: Struct): string => (s.args.length === 0 ? s.name : `${s.name}(${s.args.map(showTerm).join(', ')})`)
const showGoal = (g: Goal): string => (g.k === 'call' ? showStruct(g.fn) : `${showTerm(g.l)} = ${showTerm(g.r)}`);

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
  | { t: 'eof' }

function lex(src: string): { toks: Tok[] } {
  const toks: Tok[] = []
  let i = 0
  const colOf = (n: number) => n + 1
  while (i < src.length) {
    const c = src[i]!
    if (c === ' ' || c === '\t' || c === '\f' || c === '\v' || c === '\n' || c === '\r') { i++; continue }
    if (c === '%') { while (i < src.length && src[i] !== '\n') i++; continue }
    if (c === ',') { toks.push({ t: ',' }); i++; continue }
    if (c === '.') { toks.push({ t: '.' }); i++; continue }
    if (c === '(') { toks.push({ t: '(' }); i++; continue }
    if (c === ')') { toks.push({ t: ')' }); i++; continue }
    if (c === '_') { toks.push({ t: '_' }); i++; continue }
    if (c === '=') { toks.push({ t: '=' }); i++; continue }
    if (c === ':' && src[i + 1] === '-') { toks.push({ t: ':-' }); i += 2; continue }
    if (c >= 'a' && c <= 'z') {
      let j = i
      while (j < src.length && src[j]! >= 'a' && src[j]! <= 'z') j++
      toks.push({ t: 'atom', v: src.slice(i, j) })
      i = j
      continue
    }
    if (c >= 'A' && c <= 'Z') {
      let j = i
      while (j < src.length && src[j]! >= 'A' && src[j]! <= 'Z') j++
      toks.push({ t: 'var', v: src.slice(i, j) })
      i = j
      continue
    }
    throw { msg: `Lexical error near character \`${c}\`.`, col: colOf(i) }
  }
  toks.push({ t: 'eof' })
  return { toks }
}

// --------------------------------------------------------------- parser ---

class P {
  pos = 0
  constructor(public toks: Tok[]) {}
  peek(): Tok { return this.toks[this.pos]! }
  next(): Tok { return this.toks[this.pos++]! }
  expect(t: Tok['t'], what: string): Tok {
    const got = this.next()
    if (got.t !== t) throw { msg: `Parse error: expected ${what}.`, col: this.pos }
    return got
  }
}

const bare = (name: string): Struct => ({ name, args: [] })

function parseTerm(p: P): Term {
  const t = p.next()
  if (t.t === 'var') return { k: 'var', name: t.v }
  if (t.t === 'atom') {
    if (p.peek().t === '(') {
      p.next()
      const args = parseTerms(p)
      p.expect(')', '`)`')
      return { k: 'compound', name: t.v, args }
    }
    return { k: 'atom', name: t.v }
  }
  if (t.t === '_') return { k: 'wild' }
  throw { msg: 'Parse error: expected a term.', col: p.pos }
}

function parseTerms(p: P): Term[] {
  const first = parseTerm(p)
  const rest: Term[] = [first]
  while (p.peek().t === ',') { p.next(); rest.push(parseTerm(p)) }
  return rest
}

function parseStruct(p: P): Struct {
  const t = p.expect('atom', 'a predicate name') as { t: 'atom'; v: string }
  if (p.peek().t === '(') {
    p.next()
    const args = parseTerms(p)
    p.expect(')', '`)`')
    return { name: t.v, args }
  }
  return bare(t.v)
}

function parseGoal(p: P): Goal {
  const t = p.peek()
  if (t.t === 'atom') {
    // could be `Struct`, bare call, or LHS of `=` starting with atom/struct
    if (p.toks[p.pos + 1]?.t === '(') {
      const s = parseStruct(p)
      if (p.peek().t === '=') { p.next(); const rhs = parseTerm(p); return { k: 'unify', l: { k: 'compound', name: s.name, args: s.args }, r: rhs } }
      return { k: 'call', fn: s }
    }
    p.next()
    if (p.peek().t === '=') { p.next(); const rhs = parseTerm(p); return { k: 'unify', l: { k: 'atom', name: (t as { v: string }).v }, r: rhs } }
    return { k: 'call', fn: bare((t as { v: string }).v) }
  }
  // var / wildcard / compound-term LHS of `=`
  const lhs = parseTerm(p)
  p.expect('=', '`=`')
  const rhs = parseTerm(p)
  return { k: 'unify', l: lhs, r: rhs }
}

function parseGoals(p: P): Goal[] {
  const gs = [parseGoal(p)]
  while (p.peek().t === ',') { p.next(); gs.push(parseGoal(p)) }
  return gs
}

export function parseBase(src: string): Predicate[] {
  const { toks } = lex(src)
  const p = new P(toks)
  const preds: Predicate[] = []
  while (p.peek().t !== 'eof') {
    const t = p.peek()
    if (t.t !== 'atom') throw { msg: 'Parse error: expected a predicate.', col: p.pos }
    const s = parseStruct(p)
    const nx = p.next()
    if (nx.t === '.') { preds.push({ k: 'fact', fn: s }); continue }
    if (nx.t === ':-') {
      const body = parseGoals(p)
      p.expect('.', '`.`')
      preds.push({ k: 'rule', head: s, body })
      continue
    }
    throw { msg: 'Parse error: expected `.` or `:-`.', col: p.pos }
  }
  return preds
}

export function parseQuery(src: string): Goal[] {
  const { toks } = lex(src)
  const p = new P(toks)
  if (p.peek().t === 'eof') throw { msg: 'Empty query.', col: 1 }
  const gs = parseGoals(p)
  p.expect('.', '`.` at the end of the query')
  return gs
}

// ------------------------------------------------------------- evaluate ---

type QVars = Map<string, Term>
interface BtRec { goals: Goal[]; pos: number; qvars: QVars }
interface Proc { base: Predicate[]; qvars: QVars; bt: BtRec[]; goals: Goal[]; pos: number; counter: number }
interface Stalled { base: Predicate[]; bt: BtRec[]; counter: number }
type StepOut = { k: 'search'; proc: Proc } | { k: 'solved'; qvars: QVars; stalled: Stalled } | { k: 'dead'; stalled: Stalled }

const freeVarsTerm = (t: Term, acc: Set<string>): void => {
  if (t.k === 'var') acc.add(t.name)
  else if (t.k === 'compound') t.args.forEach((a) => freeVarsTerm(a, acc))
}
const freeVarsGoal = (g: Goal, acc: Set<string>): void => {
  if (g.k === 'call') g.fn.args.forEach((a) => freeVarsTerm(a, acc))
  else { freeVarsTerm(g.l, acc); freeVarsTerm(g.r, acc) }
}

function lookFor(f: Struct, base: Predicate[], from: number): { pred: Predicate; idx: number } | null {
  for (let i = from; i < base.length; i++) {
    const pr = base[i]!
    const h = pr.k === 'fact' ? pr.fn : pr.head
    if (h.name === f.name && h.args.length === f.args.length) return { pred: pr, idx: i }
  }
  return null
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

function causeBacktracking(f: Struct, base: Predicate[], pos: number, whole: Goal[], qvars: QVars, bt: BtRec[]): BtRec[] {
  const again = lookFor(f, base, pos)
  if (!again) return bt
  return [{ goals: whole, pos: again.idx, qvars: new Map(qvars) }, ...bt]
}

const stallOf = (proc: Proc): Stalled => ({ base: proc.base, bt: proc.bt, counter: proc.counter })
function resume(s: Stalled): Proc | null {
  if (s.bt.length === 0) return null
  const [rec, ...rest] = s.bt
  return { base: s.base, qvars: rec!.qvars, bt: rest, goals: rec!.goals, pos: rec!.pos, counter: s.counter }
}

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

/** Unify one pair; on success rewrite the *remaining* goals + query vars. */
function unifyPair(l: Term, r: Term, rest: Goal[], qvars: QVars): { goals: Goal[]; qvars: QVars } | null {
  // wildcard: delete
  if (l.k === 'wild' || r.k === 'wild') return { goals: rest, qvars }
  // atoms
  if (l.k === 'atom' && r.k === 'atom') return l.name === r.name ? { goals: rest, qvars } : null
  // decompose
  if (l.k === 'compound' && r.k === 'compound') {
    if (l.name !== r.name || l.args.length !== r.args.length) return null
    const eqs: Goal[] = l.args.map((a, i) => ({ k: 'unify', l: a, r: r.args[i]! }) as Goal)
    return { goals: [...eqs, ...rest], qvars }
  }
  // eliminate (var on left)
  if (l.k === 'var') {
    if (r.k === 'var' && r.name === l.name) return { goals: rest, qvars }
    if (occurs(l.name, r)) return null
    const goals = rest.map((g) => substGoal(l.name, r, g))
    const q2: QVars = new Map()
    for (const [k, v] of qvars) q2.set(k, substVal(l.name, r, v))
    return { goals, qvars: q2 }
  }
  // swap
  if (r.k === 'var') return unifyPair(r, l, rest, qvars)
  // atom vs compound etc: conflict
  return null
}

function step(proc: Proc): StepOut {
  const [head, ...rest] = proc.goals
  if (!head) throw new Error('unreachable: empty goal stack stepped')
  if (head.k === 'unify') {
    const u = unifyPair(head.l, head.r, rest, proc.qvars)
    if (!u) return { k: 'dead', stalled: stallOf(proc) }
    if (u.goals.length === 0) return { k: 'solved', qvars: u.qvars, stalled: stallOf({ ...proc, qvars: u.qvars }) }
    return { k: 'search', proc: { ...proc, goals: u.goals, qvars: u.qvars } }
  }
  // call
  const found = lookFor(head.fn, proc.base, proc.pos)
  if (!found) return { k: 'dead', stalled: stallOf(proc) }
  const st = { c: proc.counter, m: new Map<string, string>() }
  let pats: Term[]
  let body: Goal[] = []
  if (found.pred.k === 'fact') {
    pats = found.pred.fn.args.map((a) => renameVal(st, a))
  } else {
    pats = found.pred.head.args.map((a) => renameVal(st, a))
    body = found.pred.body.map((g) => renameGoal(st, g))
  }
  const eqs: Goal[] = head.fn.args.map((a, i) => ({ k: 'unify', l: a, r: pats[i]! }))
  const newGoals = [...eqs, ...body, ...rest]
  const bt = causeBacktracking(head.fn, proc.base, found.idx + 1, proc.goals, proc.qvars, proc.bt)
  const proc2: Proc = { ...proc, bt, counter: st.c, pos: 0 }
  if (newGoals.length === 0) return { k: 'solved', qvars: proc2.qvars, stalled: stallOf(proc2) }
  return { k: 'search', proc: { ...proc2, goals: newGoals } }
}

const STEP_BUDGET = 300_000
const SOLUTION_CAP = 500

// ---------------------------------------------------------------- engine ---

type Mode = { k: 'idle' } | { k: 'more'; stalled: Stalled; solutions: number }

export class MinilogEngine implements Engine {
  readonly id = 'minilog'
  private base: Predicate[] = []
  private mode: Mode = { k: 'idle' }
  private files = new Map<string, string>()
  private editorContent = ''
  private abort = false

  banner(): string {
    return 'Minilog - implementation of simple logic programming language.'
  }
  prompt(): string {
    return '?- '
  }
  editorAliases(): string[] {
    return ['editor.pl', 'demo.pl', 'editor', 'demo']
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
    this.mode = { k: 'idle' }
    this.abort = false
  }

  /** Abort the running search; the loaded base is kept. */
  interrupt(): void {
    this.abort = true
  }

  private resolveLoad(path: string): string | null {
    const name = path.trim()
    if (!name) return null
    if (this.files.has(name)) return this.files.get(name)!
    const base = name.split('/').pop()!
    if (this.files.has(base)) return this.files.get(base)!
    if (this.editorAliases().includes(name) || this.editorAliases().includes(base)) return this.editorContent
    return null
  }

  async handle(rawLine: string): Promise<EngineResult> {
    const line = rawLine.replace(/\r$/, '')
    this.abort = false // a fresh line starts a fresh computation
    // continuation of a multi-solution query
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
      const content = this.resolveLoad(arg)
      if (content === null) return { output: `Could not load \`${arg}': no such virtual file (pick an example or press Load into REPL).` }
      try {
        this.base = parseBase(content)
        return { output: `-- loaded ${this.base.length} clause(s) from \`${arg}\`` }
      } catch (e: unknown) {
        const msg = e && typeof e === 'object' && 'msg' in e ? String((e as { msg: unknown }).msg) : 'Parse error.'
        return { output: msg }
      }
    }
    if (line.startsWith(':')) return { output: "I don't know this command, sorry." }
    if (line.trim() === '') return { output: '' }

    let goals: Goal[]
    try {
      goals = parseQuery(line)
    } catch (e: unknown) {
      const msg = e && typeof e === 'object' && 'msg' in e ? String((e as { msg: unknown }).msg) : 'Parse error.'
      return { output: msg }
    }
    const names = new Set<string>()
    goals.forEach((g) => freeVarsGoal(g, names))
    const qvars: QVars = new Map([...names].map((n) => [n, { k: 'var', name: n } as Term]))
    const proc: Proc = { base: this.base, qvars, bt: [], goals, pos: 0, counter: 0 }
    return this.drive(proc, 0, true)
  }

  private printResult(qvars: QVars): string {
    if (qvars.size === 0) return 'True'
    return [...qvars.entries()].map(([k, v]) => `${k} = ${showTerm(v)}`).join('\n')
  }

  private async drive(proc: Proc, steps: number, first: boolean): Promise<EngineResult> {
    let cur = proc
    let n = steps
    for (;;) {
      if (++n > STEP_BUDGET) {
        this.mode = { k: 'idle' }
        return { output: '… search limit reached (diverging query?). Treated as failure for this demo; try a more specific query.' }
      }
      // Let the UI breathe (and Ctrl+C land) on long searches.
      if ((n & 1023) === 0) {
        await yieldToUI()
        if (this.abort) {
          this.abort = false
          this.mode = { k: 'idle' }
          return { output: 'Interrupted.', interrupted: true }
        }
      }
      const out = step(cur)
      if (out.k === 'search') { cur = out.proc; continue }
      if (out.k === 'dead') {
        const next = resume(out.stalled)
        if (!next) {
          if (first) return { output: 'False.' }
          this.mode = { k: 'idle' }
          return { output: 'False.' }
        }
        cur = next
        continue
      }
      // solved
      const text = this.printResult(out.qvars)
      const next = resume(out.stalled)
      if (!next) {
        this.mode = { k: 'idle' }
        return { output: text }
      }
      if (first) {
        this.mode = { k: 'more', stalled: out.stalled, solutions: 1 }
        return { output: `${text}\n-- more solutions: any key for next, :done to stop` }
      }
      if (this.mode.k === 'more' && this.mode.solutions >= SOLUTION_CAP) {
        this.mode = { k: 'idle' }
        return { output: `${text}\n… solution cap reached.` }
      }
      this.mode = { k: 'more', stalled: out.stalled, solutions: (this.mode.k === 'more' ? this.mode.solutions + 1 : 1) }
      return { output: `  or\n\n${text}\n-- more solutions: any key for next, :done to stop` }
    }
  }

  private async continueSearch(): Promise<EngineResult> {
    if (this.mode.k !== 'more') return { output: '' }
    const next = resume(this.mode.stalled)
    if (!next) { this.mode = { k: 'idle' }; return { output: 'False.' } }
    return this.drive(next, 0, false)
  }
}
