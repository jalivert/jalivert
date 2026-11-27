/**
 * Simply typed lambda calculus (λ→) — browser-native engine.
 *
 * Faithful port of the Haskell implementation (vendored under
 * vendor/lambda-pie, Simply/): bidirectional typechecker with de Bruijn
 * `Bound` conversion (`fix`), environment evaluator, and the exact REPL
 * (banner, `λ-> >> ` prompt, 7-space result indent, `:exit` quits,
 * `assume` extends the context).
 *
 * Pragmatic deviation: Happy parse failures print only the first line
 * (`Parse error on line 1, column C.`); the dumped lexer `ParseState`
 * internals are omitted.
 */
import type { Engine, EngineResult } from './engine'

// ----------------------------------------------------------------- tokens ---

type Tok =
  | { t: 'assume'; i: number }
  | { t: 'ident'; v: string; i: number }
  | { t: 'lambda'; i: number }
  | { t: 'dc'; i: number }
  | { t: 'lp'; i: number }
  | { t: 'rp'; i: number }
  | { t: 'star'; i: number }
  | { t: 'arrow'; i: number }
  | { t: 'eof'; i: number }

function lexSimply(src: string): Tok[] {
  const toks: Tok[] = []
  let i = 0
  const isWord = (c: string) => (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
  const isSpace = (c: string) => c === ' ' || c === '\t' || c === '\f' || c === '\v' || c === '\n' || c === '\r'
  while (i < src.length) {
    const c = src[i]!
    if (isSpace(c)) { i++; continue }
    if (c === 'λ' || c === '\\') { toks.push({ t: 'lambda', i }); i++; continue }
    if (c === '(') { toks.push({ t: 'lp', i }); i++; continue }
    if (c === ')') { toks.push({ t: 'rp', i }); i++; continue }
    if (c === '*') { toks.push({ t: 'star', i }); i++; continue }
    if (c === ':' && src[i + 1] === ':') { toks.push({ t: 'dc', i }); i += 2; continue }
    if (c === '-' && src[i + 1] === '>') { toks.push({ t: 'arrow', i }); i += 2; continue }
    if (isWord(c)) {
      let j = i + 1
      while (j < src.length && isWord(src[j]!)) j++
      const w = src.slice(i, j)
      if (w === 'assume') toks.push({ t: 'assume', i })
      else if (w === 'lambda') toks.push({ t: 'lambda', i })
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
  'g' in a ? 'g' in b && a.g === b.g : 'l' in b && a.l === b.l && a.s === b.s
export const showName = (n: Name): string => ('g' in n ? n.g : `${n.s}${n.l}`)

export type Ty = { k: 'tf'; n: Name } | { k: 'arr'; a: Ty; b: Ty }
export const showTy = (t: Ty): string =>
  t.k === 'tf' ? showName(t.n) : `(${showTy(t.a)} -> ${showTy(t.b)})`;
export const eqTy = (a: Ty, b: Ty): boolean =>
  a.k === 'tf'
    ? b.k === 'tf' && eqName(a.n, b.n)
    : b.k === 'arr' && eqTy(a.a, b.a) && eqTy(a.b, b.b);

export type ITm =
  | { k: 'ann'; e: CTm; t: Ty }
  | { k: 'bnd'; i: number; n: string }
  | { k: 'free'; n: Name }
  | { k: 'app'; f: ITm; a: CTm }
  | { k: 'lamA'; v: string; t: Ty; b: ITm }

export type CTm = { k: 'inf'; e: ITm } | { k: 'lam'; v: string; b: CTm }

export const showIT = (t: ITm): string => {
  switch (t.k) {
    case 'ann': return `${showCT(t.e)} :: ${showTy(t.t)}`
    case 'bnd': return `${t.n}${t.i}`
    case 'free': return showName(t.n)
    case 'app': {
      const r = t.a
      return r.k === 'inf' && r.e.k === 'app'
        ? `${showIT(t.f)} (${showCT(r)})`
        : `${showIT(t.f)} ${showCT(r)}`
    }
    case 'lamA': return `(λ ${t.v} :: ${showTy(t.t)} -> ${showIT(t.b)})`
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

type Info = { k: 'kind' } | { k: 'type'; t: Ty }
type Command = { k: 'assume'; items: [Name, Info][] }

function expectIdent(p: P): string {
  const t = p.next()
  if (t.t !== 'ident') throw new BT(t.i)
  return t.v
}

function parseType(p: P): Ty {
  let left: Ty
  if (p.is('lp')) {
    p.next()
    left = parseType(p)
    if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
  } else {
    left = { k: 'tf', n: G(expectIdent(p)) }
  }
  if (p.is('arrow')) {
    p.next()
    return { k: 'arr', a: left, b: parseType(p) }
  }
  return left
}

function parseTypedParam(p: P): [string, Ty] {
  if (p.next().t !== 'lp') throw new BT(p.toks[p.pos - 1]!.i)
  const v = expectIdent(p)
  if (p.next().t !== 'dc') throw new BT(p.toks[p.pos - 1]!.i)
  const t = parseType(p)
  if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
  return [v, t]
}

function parseCheck(p: P): CTm {
  if (p.is('lp')) {
    p.next()
    if (p.is('lambda')) {
      p.next()
      if (p.is('lp')) {
        // annotated lambda: may close the paren, head an application,
        // or be annotated — finish like an inferable head
        const params: [string, Ty][] = []
        while (p.is('lp')) params.push(parseTypedParam(p))
        if (p.next().t !== 'arrow') throw new BT(p.toks[p.pos - 1]!.i)
        const body = parseInfer(p)
        let head: ITm = body
        for (let k = params.length - 1; k >= 0; k--) head = { k: 'lamA', v: params[k]![0], t: params[k]![1], b: head }
        head = finishApp(p, head)
        if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
        return { k: 'inf', e: head }
      }
      // unannotated lambda
      const params: string[] = []
      if (!p.is('ident')) throw new BT(p.peek().i)
      while (p.is('ident')) params.push((p.next() as { t: 'ident'; v: string }).v)
      if (p.next().t !== 'arrow') throw new BT(p.toks[p.pos - 1]!.i)
      const body = parseCheck(p)
      let acc = body
      for (let k = params.length - 1; k >= 0; k--) acc = { k: 'lam', v: params[k]!, b: acc }
      if (p.is('dc')) {
        p.next()
        const t = parseType(p)
        if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
        return { k: 'inf', e: { k: 'ann', e: acc, t } }
      }
      if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
      return acc
    }
    const inner = parseCheck(p)
    if (inner.k === 'inf' && startsAppRight(p.peek())) {
      // application headed by a parenthesized term: (f x), ((lam) y), ...
      const args: CTm[] = []
      while (startsAppRight(p.peek())) args.push(parseAppRight(p))
      let node: ITm = inner.e
      for (const a of args) node = { k: 'app', f: node, a }
      if (p.is('dc')) {
        p.next()
        const t = parseType(p)
        if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
        return { k: 'inf', e: { k: 'ann', e: { k: 'inf', e: node }, t } }
      }
      if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
      return { k: 'inf', e: node }
    }
    if (p.is('dc')) {
      p.next()
      const t = parseType(p)
      if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
      return { k: 'inf', e: { k: 'ann', e: inner, t } }
    }
    if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
    return inner
  }
  return { k: 'inf', e: parseInfer(p) }
}

function parseAppHead(p: P): ITm {
  const t = p.peek()
  if (t.t === 'ident') {
    p.next()
    if (p.is('dc')) {
      p.next()
      return { k: 'ann', e: { k: 'inf', e: { k: 'free', n: G(t.v) } }, t: parseType(p) }
    }
    return { k: 'free', n: G(t.v) }
  }
  if (t.t === 'lp') {
    p.next()
    if (p.is('lambda')) {
      p.next()
      if (!p.is('lp')) throw new BT(p.peek().i) // unannotated lambda is not a valid head
      const params: [string, Ty][] = []
      while (p.is('lp')) params.push(parseTypedParam(p))
      if (p.next().t !== 'arrow') throw new BT(p.toks[p.pos - 1]!.i)
      const body = parseInfer(p)
      if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
      let acc: ITm = body
      for (let k = params.length - 1; k >= 0; k--) acc = { k: 'lamA', v: params[k]![0], t: params[k]![1], b: acc }
      return acc
    }
    const inner = parseCheck(p)
    if (p.is('dc')) {
      p.next()
      const ty = parseType(p)
      if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
      return { k: 'ann', e: inner, t: ty }
    }
    if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
    if (inner.k !== 'inf') throw new BT(p.peek().i)
    return inner.e
  }
  throw new BT(t.i)
}

function parseAppRight(p: P): CTm {
  const t = p.peek()
  if (t.t === 'ident') {
    p.next()
    return { k: 'inf', e: { k: 'free', n: G(t.v) } }
  }
  if (t.t === 'lp') {
    p.next()
    if (p.is('lambda')) {
      p.next()
      if (p.is('lp')) {
        const params: [string, Ty][] = []
        while (p.is('lp')) params.push(parseTypedParam(p))
        if (p.next().t !== 'arrow') throw new BT(p.toks[p.pos - 1]!.i)
        const body = parseInfer(p)
        if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
        let acc: ITm = body
        for (let k = params.length - 1; k >= 0; k--) acc = { k: 'lamA', v: params[k]![0], t: params[k]![1], b: acc }
        return { k: 'inf', e: acc }
      }
      const params: string[] = []
      if (!p.is('ident')) throw new BT(p.peek().i)
      while (p.is('ident')) params.push((p.next() as { t: 'ident'; v: string }).v)
      if (p.next().t !== 'arrow') throw new BT(p.toks[p.pos - 1]!.i)
      const body = parseCheck(p)
      if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
      let acc: CTm = body
      for (let k = params.length - 1; k >= 0; k--) acc = { k: 'lam', v: params[k]!, b: acc }
      return acc
    }
    const inner = parseCheck(p)
    if (p.is('dc')) {
      p.next()
      const ty = parseType(p)
      if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
      return { k: 'inf', e: { k: 'ann', e: inner, t: ty } }
    }
    if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
    return inner
  }
  throw new BT(t.i)
}

function startsAppRight(t: Tok): boolean {
  return t.t === 'ident' || t.t === 'lp'
}

function parseInfer(p: P): ITm {
  const save0 = p.save()
  try {
    return finishApp(p, parseAppHead(p))
  } catch (e) {
    if (!(e instanceof BT)) throw e
    // Not an application head (e.g. an unannotated lambda): the only
    // remaining inferable shape is `check :: Type`.
    p.restore(save0)
    const c = parseCheck(p)
    if (!p.is('dc')) throw new BT(p.peek().i)
    p.next()
    return { k: 'ann', e: c, t: parseType(p) }
  }
}

function finishApp(p: P, head: ITm): ITm {
  let node = head
  for (;;) {
    if (startsAppRight(p.peek())) {
      const args: CTm[] = []
      while (startsAppRight(p.peek())) args.push(parseAppRight(p))
      for (const a of args) node = { k: 'app', f: node, a }
      continue
    }
    if (p.is('dc')) {
      p.next()
      node = { k: 'ann', e: { k: 'inf', e: node }, t: parseType(p) }
      continue
    }
    return node
  }
}

function parseCommand(p: P): Command {
  p.next() // assume
  if (p.is('lp')) {
    const items: [Name, Info][] = []
    while (p.is('lp')) {
      p.next()
      const v = expectIdent(p)
      if (p.next().t !== 'dc') throw new BT(p.toks[p.pos - 1]!.i)
      if (p.is('star')) {
        p.next()
        items.push([G(v), { k: 'kind' }])
      } else {
        items.push([G(v), { k: 'type', t: parseType(p) }])
      }
      if (p.next().t !== 'rp') throw new BT(p.toks[p.pos - 1]!.i)
    }
    return { k: 'assume', items }
  }
  const v = expectIdent(p)
  if (p.next().t !== 'dc') throw new BT(p.toks[p.pos - 1]!.i)
  if (p.is('star')) {
    p.next()
    return { k: 'assume', items: [[G(v), { k: 'kind' }]] }
  }
  return { k: 'assume', items: [[G(v), { k: 'type', t: parseType(p) }]] }
}

// ------------------------------------------------------------- fixpoint ---

function fixC(t: CTm, ctx: string[]): CTm {
  if (t.k === 'lam') return { k: 'lam', v: t.v, b: fixC(t.b, [t.v, ...ctx]) }
  return { k: 'inf', e: fixI(t.e, ctx) }
}

function fixI(t: ITm, ctx: string[]): ITm {
  switch (t.k) {
    case 'ann': return { k: 'ann', e: fixC(t.e, ctx), t: t.t }
    case 'bnd': return t
    case 'free': {
      if (!('g' in t.n)) return t
      const idx = ctx.indexOf(t.n.g)
      return idx === -1 ? t : { k: 'bnd', i: idx, n: t.n.g }
    }
    case 'app': return { k: 'app', f: fixI(t.f, ctx), a: fixC(t.a, ctx) }
    case 'lamA': return { k: 'lamA', v: t.v, t: t.t, b: fixI(t.b, [t.v, ...ctx]) }
  }
}

// ------------------------------------------------------------ substitute ---

function substI(level: number, rep: ITm, t: ITm): ITm {
  switch (t.k) {
    case 'ann': return { k: 'ann', e: substC(level, rep, t.e), t: t.t }
    case 'bnd': return level === t.i ? rep : t
    case 'free': return t
    case 'app': return { k: 'app', f: substI(level, rep, t.f), a: substC(level, rep, t.a) }
    case 'lamA': return { k: 'lamA', v: t.v, t: t.t, b: substI(level + 1, rep, t.b) }
  }
}

function substC(level: number, rep: ITm, t: CTm): CTm {
  return t.k === 'inf' ? { k: 'inf', e: substI(level, rep, t.e) } : { k: 'lam', v: t.v, b: substC(level + 1, rep, t.b) }
}

// ------------------------------------------------------------------ eval ---

export type Value = { k: 'lam'; v: string; b: CTm; env: Value[] } | { k: 'free'; n: string } | { k: 'app'; f: Value; a: Value }
export type Env = Value[]

export const showVal = (v: Value): string =>
  v.k === 'lam' ? '<lambda>' : v.k === 'free' ? v.n : `(${showVal(v.f)} ${showVal(v.a)})`;

function evalI(t: ITm, env: Env): Value {
  switch (t.k) {
    case 'ann': return evalC(t.e, env)
    case 'bnd': return env[t.i]!
    case 'free': return { k: 'free', n: showName(t.n) }
    case 'app': return valApp(evalI(t.f, env), evalC(t.a, env))
    case 'lamA': return { k: 'lam', v: t.v, b: { k: 'inf', e: t.b }, env }
  }
}

function valApp(f: Value, a: Value): Value {
  if (f.k === 'lam') return evalC(f.b, [a, ...f.env])
  return { k: 'app', f, a }
}

function evalC(t: CTm, env: Env): Value {
  return t.k === 'inf' ? evalI(t.e, env) : { k: 'lam', v: t.v, b: t.b, env }
}

// ------------------------------------------------------------ typecheck ---

export type Ctx = [Name, Info][]

function lookupName(ctx: Ctx, n: Name): Info | undefined {
  const hit = ctx.find(([m]) => eqName(m, n))
  return hit?.[1]
}

function kindCheck(ctx: Ctx, t: Ty): void {
  if (t.k === 'tf') {
    const info = lookupName(ctx, t.n)
    if (info?.k === 'kind') return
    if (info) throw `A type var ${showName(t.n)} isn't of a kind *.`
    throw `Unknown type var identifier ${showName(t.n)}.`
  }
  kindCheck(ctx, t.a)
  kindCheck(ctx, t.b)
}

function typeInfer(level: number, ctx: Ctx, t: ITm): Ty {
  switch (t.k) {
    case 'ann':
      kindCheck(ctx, t.t)
      typeCheck(level, ctx, t.e, t.t)
      return t.t
    case 'free': {
      const info = lookupName(ctx, t.n)
      if (info?.k === 'type') return info.t
      if (info) throw `Type error for ${showName(t.n)}.`
      throw 'Unknown identifier.'
    }
    case 'app': {
      const ft = typeInfer(level, ctx, t.f)
      if (ft.k !== 'arr') throw 'Type error: illegal application.'
      typeCheck(level, ctx, t.a, ft.a)
      return ft.b
    }
    case 'lamA': {
      kindCheck(ctx, t.t)
      const out = typeInfer(level + 1, [[L(level, t.v), { k: 'type', t: t.t }], ...ctx], substI(0, { k: 'free', n: L(level, t.v) }, t.b))
      return { k: 'arr', a: t.t, b: out }
    }
    default:
      throw 'Type error: cannot infer the type of this term.'
  }
}

function typeCheck(level: number, ctx: Ctx, t: CTm, ty: Ty): void {
  if (t.k === 'inf') {
    const et = typeInfer(level, ctx, t.e)
    if (!eqTy(ty, et)) throw 'Type mismatch.'
    return
  }
  if (ty.k === 'arr') {
    typeCheck(level + 1, [[L(level, t.v), { k: 'type', t: ty.a }], ...ctx], substC(0, { k: 'free', n: L(level, t.v) }, t.b), ty.b)
    return
  }
  throw 'Type mismatch.'
}

// ---------------------------------------------------------------- engine ---

const IND = '       '

export class SimplyEngine implements Engine {
  readonly id = 'simply'
  private ctx: Ctx = []
  private abort = false

  banner(): string {
    return 'REPL for λ->\n'
  }
  prompt(): string {
    return 'λ-> >> '
  }
  editorAliases(): string[] {
    return ['editor.simply', 'demo.simply', 'editor', 'demo']
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
      const toks = lexSimply(line)
      const p = new P(toks)
      if (p.is('assume')) prog = { cmd: parseCommand(p) }
      else prog = { tm: fixC(parseCheck(p), []) }
      if (!p.is('eof')) throw new BT(p.peek().i)
    } catch (e: unknown) {
      const col = e instanceof BT ? e.at + 1 : 1
      return { output: `${IND}Parse Error: Parse error on line 1, column ${col}.` }
    }
    if ('cmd' in prog) {
      this.ctx = [...prog.cmd.items, ...this.ctx]
      return { output: '' }
    }
    try {
      const ty = typeInfer(0, this.ctx, mustInf(prog.tm))
      const val = evalC(prog.tm, [])
      return { output: `${IND}${showVal(val)} :: ${showTy(ty)}` }
    } catch (e: unknown) {
      return { output: `${IND}Type Error: ${String(e)}` }
    }
  }
}

function mustInf(t: CTm): ITm {
  if (t.k !== 'inf') throw "Can't infer a type of an unannotated λ."
  return t.e
}
