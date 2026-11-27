/**
 * Dependently typed lambda calculus (λΠ) — browser-native engine.
 *
 * Faithful port of the Haskell implementation (vendor/lambda-pie,
 * Dependently/): bidirectional checking where types are terms, Pi types with
 * closure values, application that evaluates the argument into the Pi
 * closure, alpha-invariant value equality, `assume` of *evaluated* types, and
 * the exact REPL (banner, `λΠ >> ` prompt, 6-space result indent, `:exit`
 * quits).
 *
 * Two documented deviations: Happy parse failures print only the first line
 * (the dumped lexer `ParseState` internals are omitted), and the `Pi`
 * operand production keeps the upstream `foldl` nesting order exactly as
 * written (outermost binder last).
 */
import type { Engine, EngineResult } from './engine'

// ----------------------------------------------------------------- tokens ---

type Tok =
  | { t: 'assume'; i: number }
  | { t: 'ident'; v: string; i: number }
  | { t: 'lambda'; i: number }
  | { t: 'pi'; i: number }
  | { t: 'dc'; i: number }
  | { t: 'lp'; i: number }
  | { t: 'rp'; i: number }
  | { t: 'star'; i: number }
  | { t: 'arrow'; i: number }
  | { t: 'dot'; i: number }
  | { t: 'eof'; i: number }

function lexDep(src: string): Tok[] {
  const toks: Tok[] = []
  let i = 0
  const isWord = (c: string) => (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
  const isSpace = (c: string) => c === ' ' || c === '\t' || c === '\f' || c === '\v' || c === '\n' || c === '\r'
  while (i < src.length) {
    const c = src[i]!
    if (isSpace(c)) { i++; continue }
    if (c === 'λ' || c === '\\') { toks.push({ t: 'lambda', i }); i++; continue }
    if (c === '∀' || c === 'Π') { toks.push({ t: 'pi', i }); i++; continue }
    if (c === '(') { toks.push({ t: 'lp', i }); i++; continue }
    if (c === ')') { toks.push({ t: 'rp', i }); i++; continue }
    if (c === '*') { toks.push({ t: 'star', i }); i++; continue }
    if (c === '.') { toks.push({ t: 'dot', i }); i++; continue }
    if (c === ':' && src[i + 1] === ':') { toks.push({ t: 'dc', i }); i += 2; continue }
    if (c === '-' && src[i + 1] === '>') { toks.push({ t: 'arrow', i }); i += 2; continue }
    if (isWord(c)) {
      let j = i + 1
      while (j < src.length && isWord(src[j]!)) j++
      const w = src.slice(i, j)
      if (w === 'assume') toks.push({ t: 'assume', i })
      else if (w === 'lambda') toks.push({ t: 'lambda', i })
      else if (w === 'forall') toks.push({ t: 'pi', i })
      else toks.push({ t: 'ident', v: w, i })
      i = j
      continue
    }
    throw new BT(i)
  }
  toks.push({ t: 'eof', i })
  return toks
}

// -------------------------------------------------------------------- AST ---

export type Name = { g: string } | { l: number; s: string }
export const G = (s: string): Name => ({ g: s })
export const L = (i: number, s: string): Name => ({ l: i, s })
export const eqName = (a: Name, b: Name): boolean =>
  'g' in a ? 'g' in b && a.g === b.g : 'l' in b && a.l === b.l && a.s === b.s;
// NOTE: unlike Simply/SystemF, Local binders print as the bare name.
export const showName = (n: Name): string => ('g' in n ? n.g : n.s)

export type ITm =
  | { k: 'ann'; e: CTm; t: CTm }
  | { k: 'star' }
  | { k: 'pi'; v: string; dom: CTm; cod: CTm }
  | { k: 'bnd'; i: number; n: string }
  | { k: 'free'; n: Name }
  | { k: 'app'; f: ITm; a: CTm }

export type CTm = { k: 'inf'; e: ITm } | { k: 'lam'; v: string; b: CTm }

export const showIT = (t: ITm): string => {
  switch (t.k) {
    case 'ann': return `${showCT(t.e)} :: ${showCT(t.t)}`
    case 'star': return '*'
    case 'pi': return `(Π ${t.v} :: ${showCT(t.dom)} . ${showCT(t.cod)})`
    case 'bnd': return t.n
    case 'free': return showName(t.n)
    case 'app': {
      const r = t.a
      return r.k === 'inf' && r.e.k === 'app' ? `${showIT(t.f)} (${showCT(r)})` : `${showIT(t.f)} ${showCT(r)}`
    }
  }
}

export const showCT = (t: CTm): string =>
  t.k === 'inf' ? showIT(t.e) : `(λ ${t.v} -> ${showCT(t.b)})`;

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

type Command = { k: 'assume'; items: [Name, CTm][] }

function expectIdent(p: P): string {
  const t = p.next()
  if (t.t !== 'ident') throw new BT(t.i)
  return t.v
}

function parseLambda(p: P): CTm {
  // '(' lambda Params '->' Term ')' — '(' and 'lambda' already consumed
  const params: string[] = []
  if (!p.is('ident')) throw new BT(p.peek().i)
  while (p.is('ident')) params.push((p.next() as { t: 'ident'; v: string }).v)
  if (p.next().t !== 'arrow') throw new BT(p.toks[p.pos - 1]!.i)
  const body = parseTerm(p)
  if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
  let acc = body
  for (let k = params.length - 1; k >= 0; k--) acc = { k: 'lam', v: params[k]!, b: acc }
  return acc
}

function parseTypedParams(p: P): [string, CTm][] {
  // var '::' Type  |  OneOrMany('(' var '::' Type ')')
  if (p.is('ident') && p.toks[p.pos + 1]?.t === 'dc') {
    const v = (p.next() as { t: 'ident'; v: string }).v
    p.next()
    return [[v, parseTerm(p)]]
  }
  const out: [string, CTm][] = []
  if (!p.is('lp')) throw new BT(p.peek().i)
  while (p.is('lp')) {
    p.next()
    const v = expectIdent(p)
    if (p.next().t !== 'dc') throw new BT(p.toks[p.pos - 1]!.i)
    const t = parseTerm(p)
    if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
    out.push([v, t])
  }
  return out
}

function parsePi(p: P, params: [string, CTm][], body: CTm): ITm {
  // Upstream builds the operand-level Pi with foldl (outermost binder last).
  let acc: ITm | null = null
  for (const [name, ty] of params) {
    acc = acc === null
      ? { k: 'pi', v: name, dom: ty, cod: body }
      : { k: 'pi', v: name, dom: ty, cod: { k: 'inf', e: acc } }
  }
  if (acc === null) throw new BT(p.peek().i)
  return acc
}

function parseTermPi(p: P, params: [string, CTm][], body: CTm): ITm {
  // Term-level pi uses foldr (normal nesting).
  let acc: ITm | null = null
  for (let k = params.length - 1; k >= 0; k--) {
    const [name, ty] = params[k]!
    acc = acc === null
      ? { k: 'pi', v: name, dom: ty, cod: body }
      : { k: 'pi', v: name, dom: ty, cod: { k: 'inf', e: acc } }
  }
  if (acc === null) throw new BT(p.peek().i)
  return acc
}

/** Top-level Term: base with '::' loop. */
function parseTerm(p: P): CTm {
  let base = parseTermBase(p)
  while (p.is('dc')) {
    p.next()
    const t = parseTerm(p)
    base = { k: 'inf', e: { k: 'ann', e: base, t } }
  }
  return base
}

function parseTermBase(p: P): CTm {
  const t = p.peek()
  if (t.t === 'star') {
    p.next()
    return { k: 'inf', e: { k: 'star' } }
  }
  if (t.t === 'pi') {
    p.next()
    const params = parseTypedParams(p)
    if (p.next().t !== 'dot') throw new BT(p.toks[p.pos - 1]!.i)
    return { k: 'inf', e: parseTermPi(p, params, parseTerm(p)) }
  }
  if (t.t === 'ident') {
    p.next()
    return { k: 'inf', e: { k: 'free', n: G(t.v) } }
  }
  if (t.t === 'lp') {
    p.next()
    if (p.is('lambda')) {
      p.next()
      const lam = parseLambda(p)
      return lam
    }
    // try App, else Term
    const save = p.save()
    try {
      const app = parseApp(p)
      if (!p.is('rp')) throw new BT(p.peek().i)
      p.next()
      return { k: 'inf', e: app }
    } catch (e) {
      if (!(e instanceof BT)) throw e
      p.restore(save)
      const inner = parseTerm(p)
      if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
      return inner
    }
  }
  throw new BT(t.i)
}

function parseApp(p: P): ITm {
  let node = parseAppHead(p)
  const args: CTm[] = []
  for (;;) {
    const a = tryParseAppRight(p)
    if (!a) break
    args.push(a)
  }
  if (args.length === 0) throw new BT(p.peek().i)
  for (const arg of args) node = { k: 'app', f: node, a: arg }
  return node
}

function parseAppHead(p: P): ITm {
  const t = p.peek()
  if (t.t === 'star') {
    p.next()
    return { k: 'star' }
  }
  if (t.t === 'pi') {
    p.next()
    const params = parseTypedParams(p)
    if (p.next().t !== 'dot') throw new BT(p.toks[p.pos - 1]!.i)
    return parsePi(p, params, parseTerm(p))
  }
  if (t.t === 'ident') {
    p.next()
    if (p.is('dc')) {
      p.next()
      const ty = parseTerm(p)
      return { k: 'ann', e: { k: 'inf', e: { k: 'free', n: G(t.v) } }, t: ty }
    }
    return { k: 'free', n: G(t.v) }
  }
  if (t.t === 'lp') {
    p.next()
    if (p.is('lambda')) {
      p.next()
      // '(' Lambda '::' Type ')' — parse the lambda, then require '::'
      const lam = parseLambda(p)
      if (!p.is('dc')) throw new BT(p.peek().i)
      p.next()
      return { k: 'ann', e: lam, t: parseTerm(p) }
    }
    const inner = parseTerm(p)
    if (p.is('dc')) {
      p.next()
      const ty = parseTerm(p)
      if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
      return { k: 'ann', e: inner, t: ty }
    }
    if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
    if (inner.k !== 'inf') throw new BT(p.peek().i)
    return inner.e
  }
  throw new BT(t.i)
}

function tryParseAppRight(p: P): CTm | null {
  const save = p.save()
  try {
    const t = p.peek()
    if (t.t === 'star') {
      p.next()
      return { k: 'inf', e: { k: 'star' } }
    }
    if (t.t === 'pi') {
      p.next()
      const params = parseTypedParams(p)
      if (p.next().t !== 'dot') throw new BT(p.toks[p.pos - 1]!.i)
      return { k: 'inf', e: parsePi(p, params, parseTerm(p)) }
    }
    if (t.t === 'lambda') {
      // can only appear parenthesized; bare lambda is not an operand
      throw new BT(t.i)
    }
    if (t.t === 'ident') {
      p.next()
      return { k: 'inf', e: { k: 'free', n: G(t.v) } }
    }
    if (t.t === 'lp') {
      p.next()
      if (p.is('lambda')) {
        p.next()
        const lam = parseLambda(p)
        if (!p.is('dc')) throw new BT(p.peek().i)
        p.next()
        return { k: 'inf', e: { k: 'ann', e: lam, t: parseTerm(p) } }
      }
      const inner = parseTerm(p)
      if (p.is('dc')) {
        p.next()
        const ty = parseTerm(p)
        if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
        return { k: 'inf', e: { k: 'ann', e: inner, t: ty } }
      }
      if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
      return inner
    }
    throw new BT(t.i)
  } catch (e) {
    if (!(e instanceof BT)) throw e
    p.restore(save)
    return null
  }
}

function parseCommand(p: P): Command {
  p.next() // assume
  const params = parseTypedParams(p)
  return { k: 'assume', items: params.map(([v, t]): [Name, CTm] => [G(v), t]) }
}

// ------------------------------------------------------------- fixpoint ---

function fixC(t: CTm, ctx: string[]): CTm {
  if (t.k === 'lam') return { k: 'lam', v: t.v, b: fixC(t.b, [t.v, ...ctx]) }
  return { k: 'inf', e: fixI(t.e, ctx) }
}

function fixI(t: ITm, ctx: string[]): ITm {
  switch (t.k) {
    case 'ann': return { k: 'ann', e: fixC(t.e, ctx), t: fixC(t.t, ctx) }
    case 'star': return t
    case 'pi': return { k: 'pi', v: t.v, dom: fixC(t.dom, ctx), cod: fixC(t.cod, [t.v, ...ctx]) }
    case 'bnd': return t
    case 'free': {
      if (!('g' in t.n)) return t
      const idx = ctx.indexOf(t.n.g)
      return idx === -1 ? t : { k: 'bnd', i: idx, n: t.n.g }
    }
    case 'app': return { k: 'app', f: fixI(t.f, ctx), a: fixC(t.a, ctx) }
  }
}

// ------------------------------------------------------------ substitute ---

function substI(level: number, rep: ITm, t: ITm): ITm {
  switch (t.k) {
    case 'ann': return { k: 'ann', e: substC(level, rep, t.e), t: substC(level, rep, t.t) }
    case 'star': return t
    case 'pi': return { k: 'pi', v: t.v, dom: substC(level, rep, t.dom), cod: substC(level + 1, rep, t.cod) }
    case 'bnd': return level === t.i ? rep : t
    case 'free': return t
    case 'app': return { k: 'app', f: substI(level, rep, t.f), a: substC(level, rep, t.a) }
  }
}

function substC(level: number, rep: ITm, t: CTm): CTm {
  return t.k === 'inf' ? { k: 'inf', e: substI(level, rep, t.e) } : { k: 'lam', v: t.v, b: substC(level + 1, rep, t.b) }
}

// ------------------------------------------------------------------ eval ---

export type Value =
  | { k: 'star' }
  | { k: 'pi'; v: string; dom: Value; body: CTm; env: Value[] }
  | { k: 'lam'; v: string; b: CTm; env: Value[] }
  | { k: 'free'; n: Name }
  | { k: 'app'; f: Value; a: Value }
export type Env = Value[]

export const showVal = (v: Value): string => {
  switch (v.k) {
    case 'star': return '*'
    case 'pi':
      return v.env.length === 0
        ? `(Π ${v.v} :: ${showVal(v.dom)} . ${showCT(v.body)})`
        : `(Π ${v.v} :: ${showVal(v.dom)} . ${showCT(v.body)})[${v.env.map(showVal).join(',')}]`
    case 'lam':
      return v.env.length === 0
        ? `(λ ${v.v} -> ${showCT(v.b)})`
        : `(λ ${v.v} -> ${showCT(v.b)})[${v.env.map(showVal).join(',')}]`
    case 'free': return showName(v.n)
    case 'app': return `(${showVal(v.f)} @ ${showVal(v.a)})`
  }
}

function evalI(t: ITm, env: Env): Value {
  switch (t.k) {
    case 'ann': return evalC(t.e, env)
    case 'star': return { k: 'star' }
    case 'pi': return { k: 'pi', v: t.v, dom: evalC(t.dom, env), body: t.cod, env }
    case 'bnd': return env[t.i]!
    case 'free': return { k: 'free', n: t.n }
    case 'app': return valApp(evalI(t.f, env), evalC(t.a, env))
  }
}

function valApp(f: Value, a: Value): Value {
  if (f.k === 'lam') return evalC(f.b, [a, ...f.env])
  if (f.k === 'pi') return evalC(f.body, [a, ...f.env])
  return { k: 'app', f, a }
}

function evalC(t: CTm, env: Env): Value {
  return t.k === 'inf' ? evalI(t.e, env) : { k: 'lam', v: t.v, b: t.b, env }
}

const freshVar: Value = { k: 'free', n: G('') }

function eqVal(a: Value, b: Value): boolean {
  if (a.k === 'star') return b.k === 'star'
  if (a.k === 'pi' && b.k === 'pi') {
    if (!eqVal(a.dom, b.dom)) return false
    return eqVal(evalC(a.body, [freshVar, ...a.env]), evalC(b.body, [freshVar, ...b.env]))
  }
  if (a.k === 'lam' && b.k === 'lam') {
    return eqVal(evalC(a.b, [freshVar, ...a.env]), evalC(b.b, [freshVar, ...b.env]))
  }
  if (a.k === 'free' && b.k === 'free') return eqName(a.n, b.n)
  if (a.k === 'app' && b.k === 'app') return eqVal(a.f, b.f) && eqVal(a.a, b.a)
  return false
}

// ------------------------------------------------------------ typecheck ---

export type Ctx = [Name, Value][]
export type Type = Value

function lookupCtx(ctx: Ctx, n: Name): Value | undefined {
  const hit = ctx.find(([m]) => eqName(m, n))
  return hit?.[1]
}

export const showCtx = (ctx: Ctx): string =>
  `[${ctx.map(([n, v]) => `(${showName(n)},${showVal(v)})`).join(',')}]`;

function typeInfer(level: number, ctx: Ctx, t: ITm): Type {
  switch (t.k) {
    case 'ann': {
      typeCheck(level, ctx, t.t, { k: 'star' })
      const ty = evalC(t.t, [])
      typeCheck(level, ctx, t.e, ty)
      return ty
    }
    case 'star':
      return { k: 'star' }
    case 'pi': {
      typeCheck(level, ctx, t.dom, { k: 'star' })
      const dom = evalC(t.dom, [])
      typeCheck(level + 1, [[L(level, t.v), dom], ...ctx], substC(0, { k: 'free', n: L(level, t.v) }, t.cod), { k: 'star' })
      return { k: 'star' }
    }
    case 'free': {
      const ty = lookupCtx(ctx, t.n)
      if (ty !== undefined) return ty
      throw `Unknown identifier ${showName(t.n)}.`
    }
    case 'app': {
      const ft = typeInfer(level, ctx, t.f)
      if (ft.k !== 'pi') throw 'Type error: illegal application! Type of *left* must be a Pi.'
      typeCheck(level, ctx, t.a, ft.dom)
      return valApp(ft, evalC(t.a, []))
    }
    default:
      throw 'Type error: cannot infer the type of this term.'
  }
}

function typeCheck(level: number, ctx: Ctx, t: CTm, ty: Value): void {
  if (t.k === 'inf') {
    const et = typeInfer(level, ctx, t.e)
    if (!eqVal(ty, et)) throw `Type mismatch. type' = ${showVal(ty)}  /= ${showVal(et)}\ncontext= ${showCtx(ctx)}`
    return
  }
  if (ty.k === 'pi') {
    typeCheck(
      level + 1,
      [[L(level, t.v), ty.dom], ...ctx],
      substC(0, { k: 'free', n: L(level, t.v) }, t.b),
      valApp(ty, { k: 'free', n: L(level, t.v) }),
    )
    return
  }
  throw 'Type mismatch. Incorrect shape.'
}

// ---------------------------------------------------------------- engine ---

const IND = '      '

export class DependentlyEngine implements Engine {
  readonly id = 'dependently'
  private ctx: Ctx = []
  private abort = false

  banner(): string {
    return 'REPL for λΠ\n'
  }
  prompt(): string {
    return 'λΠ >> '
  }
  editorAliases(): string[] {
    return ['editor.dep', 'demo.dep', 'editor', 'demo']
  }
  provideFile(_name: string, _content: string): void {}
  dropFile(_name: string): void {}
  setEditorContent(_content: string): void {}
  restart(): void {
    this.ctx = []
    this.abort = false
  }
  interrupt(): void {
    this.abort = true
  }

  async handle(rawLine: string): Promise<EngineResult> {
    const line = rawLine.replace(/\r$/, '')
    this.abort = false
    if (line.trim() === ':exit') return { output: '', halted: true }
    let prog: { cmd: Command } | { tm: CTm }
    try {
      const toks = lexDep(line)
      const p = new P(toks)
      if (p.is('assume')) prog = { cmd: parseCommand(p) }
      else prog = { tm: fixC(parseTerm(p), []) }
      if (!p.is('eof')) throw new BT(p.peek().i)
    } catch (e: unknown) {
      const col = e instanceof BT ? e.at + 1 : 1
      return { output: `${IND}Parse Error: Parse error on line 1, column ${col}.` }
    }
    if ('cmd' in prog) {
      this.ctx = [...prog.cmd.items.map(([n, t]): [Name, Value] => [n, evalC(fixC(t, []), [])]), ...this.ctx]
      return { output: '' }
    }
    try {
      const ty = typeInfer(0, this.ctx, mustInf(prog.tm))
      const val = evalC(prog.tm, [])
      return { output: `${IND}${showVal(val)} :: ${showVal(ty)}` }
    } catch (e: unknown) {
      return { output: `${IND}Type Error: ${String(e)}` }
    }
  }
}

function mustInf(t: CTm): ITm {
  if (t.k !== 'inf') throw "Can't infer a type of an unannotated λ."
  return t.e
}
