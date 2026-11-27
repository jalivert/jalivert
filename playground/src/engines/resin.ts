/**
 * Resin — browser-native engine.
 *
 * Faithful port of the Haskell implementation (vendored under vendor/resin):
 *  - lexer: unicode (∀∃⊤⊥∧∨¬⟹⟺⊢ᶜ) + ASCII synonyms, `%` comments
 *  - grammar: constants / aliases / axioms / theorems with assumptions,
 *    proofs (lemmas) and `using { }` restrictions
 *  - reasoning: NNF / PNF / skolemisation / CNF + given-clause resolution
 *    with unification (occurs-check) and constructive existential answers
 *  - REPL: `⊤ ⊢ ` prompt, `:check`, `:assume`, `:entails`, `:consistent`,
 *    `:clear`, `:nnf/:pnf/:skolemize/:cnf`, `:q`
 *
 * Resolution is semi-decidable, so the prover is bounded (clause/iteration
 * caps); hitting a cap is reported as "could not prove" for the demo.
 */
import type { Engine, EngineResult } from './engine'
import { yieldToUI } from './engine'

// ------------------------------------------------------------------ AST ---

export type Tm = { k: 'v'; n: string } | { k: 'f'; n: string; a: Tm[] }
export type Rel = { n: string; a: Tm[] }
export type Fm =
  | { k: 't' }
  | { k: 'f' }
  | { k: 'at'; r: Rel }
  | { k: 'not'; p: Fm }
  | { k: 'and'; l: Fm; r: Fm }
  | { k: 'or'; l: Fm; r: Fm }
  | { k: 'imp'; l: Fm; r: Fm }
  | { k: 'eq'; l: Fm; r: Fm }
  | { k: 'all'; v: string; p: Fm }
  | { k: 'ex'; v: string; p: Fm }

export const TrueF: Fm = { k: 't' }
export const FalseF: Fm = { k: 'f' }

const showTm = (t: Tm): string => (t.k === 'v' ? t.n : t.a.length === 0 ? t.n : `${t.n}(${t.a.map(showTm).join(', ')})`)
const isCompound = (p: Fm): boolean => p.k !== 't' && p.k !== 'f' && p.k !== 'at'

export function showFm(p: Fm): string {
  switch (p.k) {
    case 't': return '⊤'
    case 'f': return '⊥'
    case 'at': return p.r.a.length === 0 ? p.r.n : `${p.r.n}(${p.r.a.map(showTm).join(', ')})`
    case 'not': return isCompound(p.p) ? `¬(${showFm(p.p)})` : `¬${showFm(p.p)}`
    case 'and': case 'or': {
      const op = p.k === 'and' ? '∧' : '∨'
      const L = showFm(p.l); const R = showFm(p.r)
      const lc = isCompound(p.l); const rc = isCompound(p.r)
      const sameL = (p.k === 'and' && p.l.k === 'and') || (p.k === 'or' && p.l.k === 'or')
      const sameR = (p.k === 'and' && p.r.k === 'and') || (p.k === 'or' && p.r.k === 'or')
      if (sameL && sameR) return `${L} ${op} ${R}`
      if (sameL && rc) return `${L} ${op} (${R})`
      if (sameR && lc) return `(${L}) ${op} ${R}`
      if (lc && rc) return `(${L}) ${op} (${R})`
      if (lc) return `(${L}) ${op} ${R}`
      if (rc) return `${L} ${op} (${R})`
      return `${L} ${op} ${R}`
    }
    case 'imp': {
      const L = showFm(p.l); const R = showFm(p.r)
      const lc = isCompound(p.l); const rc = isCompound(p.r)
      if (p.r.k === 'imp' && (p.l.k === 'not' || !lc)) return `${L} ==> ${R}`
      if (p.l.k === 'not' && (p.r.k === 'not' || !rc)) return `${L} ==> ${R}`
      if (p.l.k === 'not') return `${L} ==> ${R}`
      if (p.r.k === 'not' && !lc) return `${L} ==> ${R}`
      if (p.r.k === 'not') return `(${L}) ==> ${R}`
      if (!lc && !rc) return `${L} ==> ${R}`
      if (!lc) return `${L} ==> (${R})`
      if (!rc) return `(${L}) ==> ${R}`
      return `(${L}) ==> (${R})`
    }
    case 'eq': return `(${showFm(p.l)}) <==> (${showFm(p.r)})`
    case 'all': return `∀ ${p.v} ${showFm(p.p)}`
    case 'ex': return `∃ ${p.v} ${showFm(p.p)}`
  }
}

// ---------------------------------------------------------------- lexer ---

type Tok =
  | { t: 'upper'; v: string } | { t: 'lower'; v: string } | { t: 'num'; v: string }
  | { t: 'constmark' }
  | { t: ',' } | { t: '.' } | { t: ':' } | { t: '=' }
  | { t: '(' } | { t: ')' } | { t: '[' } | { t: ']' } | { t: '{' } | { t: '}' }
  | { t: 'theorem' } | { t: 'lemma' } | { t: 'proof' } | { t: 'constants' }
  | { t: 'axioms' } | { t: 'aliases' } | { t: 'using' }
  | { t: 'turn' } | { t: 'true' } | { t: 'false' } | { t: 'forall' } | { t: 'exists' }
  | { t: 'not' } | { t: 'and' } | { t: 'or' } | { t: 'imp' } | { t: 'eq' }
  | { t: 'eof' }

const KEYWORDS: Record<string, Tok['t']> = {
  forall: 'forall', exists: 'exists', True: 'true', Tautology: 'true',
  False: 'false', Contradiction: 'false', AND: 'and', OR: 'or', NOT: 'not',
  theorem: 'theorem', lemma: 'lemma', proof: 'proof', constants: 'constants',
  axioms: 'axioms', aliases: 'aliases', using: 'using',
}

function lexResin(src: string): Tok[] {
  const toks: Tok[] = []
  let i = 0
  const isWord = (c: string) => /[A-Za-z0-9]/.test(c)
  const isWordTail = (c: string) => /[A-Za-z0-9_'\-]/.test(c)
  while (i < src.length) {
    const c = src[i]!
    if (/\s/.test(c)) { i++; continue }
    if (c === '%') { while (i < src.length && src[i] !== '\n') i++; continue }
    if (c === '∀') { toks.push({ t: 'forall' }); i++; continue }
    if (c === '∃') { toks.push({ t: 'exists' }); i++; continue }
    if (c === '⊤') { toks.push({ t: 'true' }); i++; continue }
    if (c === '⊥') { toks.push({ t: 'false' }); i++; continue }
    if (c === '∧') { toks.push({ t: 'and' }); i++; continue }
    if (c === '∨') { toks.push({ t: 'or' }); i++; continue }
    if (c === '¬') { toks.push({ t: 'not' }); i++; continue }
    if (c === '⟹') { toks.push({ t: 'imp' }); i++; continue }
    if (c === '⟺') { toks.push({ t: 'eq' }); i++; continue }
    if (c === '⊢') { toks.push({ t: 'turn' }); i++; continue }
    if (c === 'ᶜ') { toks.push({ t: 'constmark' }); i++; continue }
    if (c === ',') { toks.push({ t: ',' }); i++; continue }
    if (c === '.') { toks.push({ t: '.' }); i++; continue }
    if (c === ':') { toks.push({ t: ':' }); i++; continue }
    if (c === '(') { toks.push({ t: '(' }); i++; continue }
    if (c === ')') { toks.push({ t: ')' }); i++; continue }
    if (c === '[') { toks.push({ t: '[' }); i++; continue }
    if (c === ']') { toks.push({ t: ']' }); i++; continue }
    if (c === '{') { toks.push({ t: '{' }); i++; continue }
    if (c === '}') { toks.push({ t: '}' }); i++; continue }
    if (c === '&' && src[i + 1] === '&') { toks.push({ t: 'and' }); i += 2; continue }
    if (c === '|' && src[i + 1] === '|') { toks.push({ t: 'or' }); i += 2; continue }
    if (c === '|' ) { toks.push({ t: 'or' }); i++; continue }
    if (c === '=' && src[i + 1] === '=' && src[i + 2] === '>') { toks.push({ t: 'imp' }); i += 3; continue }
    if (c === '=' && src[i + 1] === '>') { toks.push({ t: 'imp' }); i += 2; continue }
    if (c === '<' && src[i + 1] === '=' && src[i + 2] === '=' && src[i + 3] === '>') { toks.push({ t: 'eq' }); i += 4; continue }
    if (c === '<' && src[i + 1] === '=' && src[i + 2] === '>') { toks.push({ t: 'eq' }); i += 3; continue }
    if (c === '=') { toks.push({ t: '=' }); i++; continue }
    if (/[A-Za-z]/.test(c)) {
      let j = i + 1
      while (j < src.length && isWordTail(src[j]!)) j++
      const w = src.slice(i, j)
      const kw = KEYWORDS[w]
      if (kw) { toks.push({ t: kw } as Tok); i = j; continue }
      toks.push(c >= 'A' && c <= 'Z' ? { t: 'upper', v: w } : { t: 'lower', v: w })
      i = j
      continue
    }
    if (/[0-9]/.test(c)) {
      let j = i + 1
      while (j < src.length && isWord(src[j]!)) j++
      // theorem names like 1-is-nat: absorb trailing -... tails
      let k = j
      while (k < src.length && (src[k] === '-' || src[k] === '_' || src[k] === "'")) {
        let m = k + 1
        while (m < src.length && isWord(src[m]!)) m++
        if (m === k + 1) break
        k = m
      }
      toks.push({ t: 'num', v: src.slice(i, k) })
      i = k
      continue
    }
    throw { msg: `Lexical error near character \`${c}\`.` }
  }
  toks.push({ t: 'eof' })
  return toks
}

// --------------------------------------------------------------- parser ---

interface PCtx {
  constants: Set<string>
  aliases: Map<string, Tm>
  scope: string[][]
}
const scopeFlat = (c: PCtx): string[] => c.scope.flat()

class RP {
  pos = 0
  constructor(public toks: Tok[], public ctx: PCtx) {}
  peek(): Tok { return this.toks[this.pos]! }
  next(): Tok { return this.toks[this.pos++]! }
  at(t: Tok['t']): boolean { return this.peek().t === t }
  expect(t: Tok['t'], what: string): Tok {
    const g = this.next()
    if (g.t !== t) throw { msg: `Parse error: expected ${what} (at token ${this.pos - 1}).` }
    return g
  }
}

function parseTm(p: RP): Tm {
  const t = p.next()
  const ctx = p.ctx
  if (t.t === 'num') {
    if (p.at('constmark')) { p.next(); return { k: 'f', n: t.v, a: [] } }
    if (ctx.constants.has(t.v)) return { k: 'f', n: t.v, a: [] }
    const al = ctx.aliases.get(t.v)
    if (al) return al
    throw { msg: `Parsing Error: Unknown numeric constant \`${t.v}\`.` }
  }
  if (t.t === 'lower') {
    if (p.at('constmark')) {
      p.next()
      return { k: 'f', n: t.v, a: parseTmArgsM(p) ?? [] }
    }
    const args = parseTmArgsM(p)
    if (args) return { k: 'f', n: t.v, a: args }
    if (scopeFlat(ctx).includes(t.v)) return { k: 'v', n: t.v }
    if (ctx.constants.has(t.v)) return { k: 'f', n: t.v, a: [] }
    const al = ctx.aliases.get(t.v)
    if (al) return al
    throw { msg: `Parsing Error: Unbound variable \`${t.v}\`.` }
  }
  if (t.t === 'upper') {
    if (p.at('constmark')) {
      p.next()
      return { k: 'f', n: t.v, a: parseTmArgsM(p) ?? [] }
    }
    const args = parseTmArgsM(p)
    if (args) return { k: 'f', n: t.v, a: args }
    if (ctx.constants.has(t.v)) return { k: 'f', n: t.v, a: [] }
    const al = ctx.aliases.get(t.v)
    if (al) return al
    throw { msg: `Parsing Error: Unknown constant or alias \`${t.v}\`.` }
  }
  if (t.t === '(') { const x = parseTm(p); p.expect(')', '`)`'); return x }
  throw { msg: 'Parse error: expected a term.' }
}

function parseTmArgsM(p: RP): Tm[] | null {
  const t = p.peek()
  let open: Tok['t'] | null = null
  let close: Tok['t'] | null = null
  if (t.t === '(') { open = '('; close = ')' } else if (t.t === '[') { open = '['; close = ']' } else if (t.t === '{') { open = '{'; close = '}' }
  else return null
  p.next()
  const args: Tm[] = []
  if (!p.at(close)) {
    args.push(parseTm(p))
    while (p.at(',')) { p.next(); if (p.at(close)) break; args.push(parseTm(p)) }
  }
  p.expect(close, 'closing bracket')
  void open
  return args
}

/** @internal exported for debugging */
export const _lexResin = lexResin

function parseRel(p: RP): Rel {
  const t = p.expect('upper', 'a relation name') as { t: 'upper'; v: string }
  const args = parseTmArgsM(p) ?? []
  return { n: t.v, a: args }
}

function parseFormula(p: RP): Fm { return parseEq(p) }
function parseEq(p: RP): Fm {
  let l = parseImpl(p)
  if (p.at('eq')) { p.next(); const r = parseEq(p); return { k: 'eq', l, r } }
  return l
}
function parseImpl(p: RP): Fm {
  let l = parseOr(p)
  if (p.at('imp')) { p.next(); const r = parseImpl(p); return { k: 'imp', l, r } }
  return l
}
function parseOr(p: RP): Fm {
  let l = parseAnd(p)
  while (p.at('or')) { p.next(); l = { k: 'or', l, r: parseAnd(p) } }
  return l
}
function parseAnd(p: RP): Fm {
  let l = parseUnary(p)
  while (p.at('and')) { p.next(); l = { k: 'and', l, r: parseUnary(p) } }
  return l
}
function parseUnary(p: RP): Fm {
  if (p.at('not')) { p.next(); return { k: 'not', p: parseUnary(p) } }
  if (p.at('forall') || p.at('exists')) {
    const isAll = p.next().t === 'forall'
    const binders: string[] = []
    while (p.peek().t === 'lower') binders.push((p.next() as { v: string }).v)
    if (binders.length === 0) throw { msg: 'Parse error: expected binder(s) after quantifier.' }
    p.ctx.scope.unshift(binders)
    const body = parseFormula(p)
    p.ctx.scope.shift()
    let f = body
    for (let i = binders.length - 1; i >= 0; i--) f = isAll ? { k: 'all', v: binders[i]!, p: f } : { k: 'ex', v: binders[i]!, p: f }
    return f
  }
  return parsePrimary(p)
}
function parsePrimary(p: RP): Fm {
  const t = p.peek()
  if (t.t === 'true') { p.next(); return TrueF }
  if (t.t === 'false') { p.next(); return FalseF }
  if (t.t === 'upper') return { k: 'at', r: parseRel(p) }
  if (t.t === '(' || t.t === '{' || t.t === '[') {
    p.next()
    const f = parseFormula(p)
    const close = t.t === '(' ? ')' : t.t === '{' ? '}' : ']'
    p.expect(close as Tok['t'], 'closing bracket')
    return f
  }
  throw { msg: 'Parse error: expected a formula.' }
}

// --------------------------------------------------------------- module ---

export interface AssertionT { name: string | null; fm: Fm; allowed: string[] | null }
export interface TheoremT { name: string; assumptions: { name: string | null; fm: Fm }[]; conclusion: Fm; proof: AssertionT[]; allowed: string[] | null }

function parseUsing(p: RP): string[] | null {
  if (!p.at('using')) return null
  p.next()
  p.expect('{', '`{`')
  const names: string[] = []
  while (!p.at('}')) {
    const t = p.next()
    if (t.t !== 'lower' && t.t !== 'upper' && t.t !== 'num') throw { msg: 'Parse error: expected a name in `using`.' }
    names.push((t as { v: string }).v)
    if (p.at(',')) p.next()
  }
  p.expect('}', '`}`')
  return names
}

function tryParseAssumption(p: RP): { name: string | null; fm: Fm } {
  if (p.at('(') && p.toks[p.pos + 1]?.t === 'lower' && p.toks[p.pos + 2]?.t === ':') {
    p.next()
    const nm = (p.next() as { v: string }).v
    p.expect(':', '`:`')
    const fm = parseFormula(p)
    p.expect(')', '`)`')
    p.ctx.scope[0]?.push(nm)
    return { name: nm, fm }
  }
  return { name: null, fm: parseFormula(p) }
}

function parseTheorem(p: RP): TheoremT {
  p.expect('theorem', '`theorem`')
  const nt = p.next()
  if (nt.t !== 'lower' && nt.t !== 'num') throw { msg: 'Parse error: expected a theorem name.' }
  const name = (nt as { v: string }).v
  p.expect(':', '`:`')
  p.ctx.scope.unshift([])
  // Try assumptions form: parse assumption list, require ⊢ afterwards.
  const save = p.pos
  const scopeSave = p.ctx.scope.map((s) => [...s])
  let assumptions: { name: string | null; fm: Fm }[] = []
  let conclusion: Fm | null = null
  try {
    assumptions = [tryParseAssumption(p)]
    while (p.at(',')) { p.next(); assumptions.push(tryParseAssumption(p)) }
    if (!p.at('turn')) throw { msg: 'not-assumptions' }
    p.next()
    conclusion = parseFormula(p)
  } catch (e) {
    const isFallback = e !== null && typeof e === 'object' && 'msg' in e && (e as { msg: string }).msg === 'not-assumptions'
    if (!isFallback) throw e
    p.pos = save
    p.ctx.scope = scopeSave.map((s) => [...s])
    assumptions = []
    conclusion = parseFormula(p)
  }
  let proof: AssertionT[] = []
  if (p.at('proof')) {
    p.next()
    p.expect(':', '`:`')
    p.ctx.scope.unshift([])
    if (!p.at('.')) {
      proof.push(parseAssertion(p))
      while (p.at(',')) { p.next(); if (p.at('.')) break; proof.push(parseAssertion(p)) }
    }
  }
  p.expect('.', '`.`')
  const allowed = parseUsing(p)
  // pop scopes: proof scope (if any) + assumption scope, then record name
  p.ctx.scope.shift()
  if (proof.length > 0 || assumptions.length > 0) p.ctx.scope.shift()
  p.ctx.scope[0]?.push(name)
  return { name, assumptions, conclusion, proof, allowed }
}

function parseAssertion(p: RP): AssertionT {
  let nm: string | null = null
  if (p.at('lemma')) {
    p.next()
    const t = p.next()
    if (t.t !== 'lower' && t.t !== 'num') throw { msg: 'Parse error: expected a lemma name.' }
    nm = (t as { v: string }).v
    p.expect(':', '`:`')
  }
  const fm = parseFormula(p)
  const allowed = parseUsing(p)
  if (nm) p.ctx.scope[0]?.push(nm)
  return { name: nm, fm, allowed }
}

export interface ModuleT { constants: string[]; aliases: [string, Tm][]; axioms: { name: string | null; fm: Fm }[]; theorems: TheoremT[] }

export function parseModule(src: string): ModuleT {
  const ctx: PCtx = { constants: new Set(), aliases: new Map(), scope: [[]] }
  const p = new RP(lexResin(src), ctx)
  const constants: string[] = []
  if (p.at('constants')) {
    p.next(); p.expect(':', '`:`')
    for (;;) {
      const t = p.next()
      if (t.t !== 'lower' && t.t !== 'upper' && t.t !== 'num') throw { msg: 'Parse error: expected a constant.' }
      constants.push((t as { v: string }).v)
      if (p.at(',')) { p.next(); continue }
      break
    }
    p.expect('.', '`.`')
    constants.forEach((c) => ctx.constants.add(c))
  }
  const aliases: [string, Tm][] = []
  if (p.at('aliases')) {
    p.next(); p.expect(':', '`:`')
    for (;;) {
      const t = p.next()
      if (t.t !== 'lower' && t.t !== 'upper' && t.t !== 'num') throw { msg: 'Parse error: expected an alias name.' }
      const an = (t as { v: string }).v
      if (ctx.constants.has(an)) throw { msg: `Parsing Error: Illegal alias \`${an}\`.` }
      if (ctx.aliases.has(an)) throw { msg: `Parsing Error: Illegal alias \`${an}\`.` }
      p.expect('=', '`=`')
      const tm = parseTm(p)
      ctx.aliases.set(an, tm)
      aliases.push([an, tm])
      if (p.at(',')) { p.next(); continue }
      break
    }
    p.expect('.', '`.`')
  }
  const axioms: { name: string | null; fm: Fm }[] = []
  if (p.at('axioms')) {
    p.next(); p.expect(':', '`:`')
    for (;;) {
      if (p.at('(') && p.toks[p.pos + 1]?.t === 'lower' && p.toks[p.pos + 2]?.t === ':') {
        p.next()
        const nm = (p.next() as { v: string }).v
        p.expect(':', '`:`')
        const fm = parseFormula(p)
        p.expect(')', '`)`')
        ctx.scope[0]!.push(nm)
        axioms.push({ name: nm, fm })
      } else {
        axioms.push({ name: null, fm: parseFormula(p) })
      }
      if (p.at(',')) { p.next(); continue }
      break
    }
    p.expect('.', '`.`')
  }
  const theorems: TheoremT[] = []
  while (!p.at('eof')) theorems.push(parseTheorem(p))
  return { constants, aliases, axioms, theorems }
}

export function parseFormulaTop(src: string, ctx?: PCtx): Fm {
  const c: PCtx = ctx ?? { constants: new Set(), aliases: new Map(), scope: [] }
  const p = new RP(lexResin(src), c)
  const f = parseFormula(p)
  return f
}

// --------------------------------------------------------- normal forms ---

const fvt = (t: Tm, acc: Set<string>): void => {
  if (t.k === 'v') acc.add(t.n)
  else t.a.forEach((x) => fvt(x, acc))
}
const fv = (f: Fm, acc = new Set<string>()): Set<string> => {
  switch (f.k) {
    case 'at': f.r.a.forEach((x) => fvt(x, acc)); break
    case 'not': fv(f.p, acc); break
    case 'and': case 'or': case 'imp': case 'eq': fv(f.l, acc); fv(f.r, acc); break
    case 'all': case 'ex': { const s = new Set<string>(); fv(f.p, s); s.delete(f.v); s.forEach((x) => acc.add(x)); break }
    default: break
  }
  return acc
}

const variant = (x: string, vars: Set<string>): string => (vars.has(x) ? variant(x + "'", vars) : x)

type Sub = Map<string, Tm>
const tsubst = (s: Sub, t: Tm): Tm => (t.k === 'v' ? (s.get(t.n) ?? t) : { k: 'f', n: t.n, a: t.a.map((x) => tsubst(s, x)) })
function subst(s: Sub, f: Fm): Fm {
  switch (f.k) {
    case 't': case 'f': return f
    case 'at': return { k: 'at', r: { n: f.r.n, a: f.r.a.map((x) => tsubst(s, x)) } }
    case 'not': return { k: 'not', p: subst(s, f.p) }
    case 'and': return { k: 'and', l: subst(s, f.l), r: subst(s, f.r) }
    case 'or': return { k: 'or', l: subst(s, f.l), r: subst(s, f.r) }
    case 'imp': return { k: 'imp', l: subst(s, f.l), r: subst(s, f.r) }
    case 'eq': return { k: 'eq', l: subst(s, f.l), r: subst(s, f.r) }
    case 'all': case 'ex': {
      // capture-avoiding (mirrors subst'q)
      const rest = fv(f.p)
      rest.delete(f.v)
      const clash = [...rest].some((y) => {
        const tv = s.get(y) ?? ({ k: 'v', n: y } as Tm)
        const vs = new Set<string>(); fvt(tv, vs); return vs.has(f.v)
      })
      const x2 = clash ? variant(f.v, fv(subst(cloneWithout(s, f.v), f.p))) : f.v
      const s2 = new Map(s); s2.set(f.v, { k: 'v', n: x2 })
      return f.k === 'all' ? { k: 'all', v: x2, p: subst(s2, f.p) } : { k: 'ex', v: x2, p: subst(s2, f.p) }
    }
  }
}
const cloneWithout = (s: Sub, k: string): Sub => { const m = new Map(s); m.delete(k); return m }

const psimp = (f: Fm): Fm => {
  if (f.k === 'not' && f.p.k === 'f') return TrueF
  if (f.k === 'not' && f.p.k === 't') return FalseF
  if (f.k === 'not' && f.p.k === 'not') return f.p.p
  if (f.k === 'and' && (f.l.k === 'f' || f.r.k === 'f')) return FalseF
  if (f.k === 'and' && f.r.k === 't') return f.l
  if (f.k === 'and' && f.l.k === 't') return f.r
  if (f.k === 'or' && f.r.k === 'f') return f.l
  if (f.k === 'or' && f.l.k === 'f') return f.r
  if (f.k === 'imp' && f.l.k === 'f') return TrueF
  if (f.k === 'imp' && f.r.k === 't') return TrueF
  if (f.k === 'imp' && f.l.k === 't') return f.r
  if (f.k === 'imp' && f.r.k === 'f') return { k: 'not', p: f.l }
  if (f.k === 'eq' && f.r.k === 't') return f.l
  if (f.k === 'eq' && f.l.k === 't') return f.r
  if (f.k === 'eq' && f.r.k === 'f') return { k: 'not', p: f.l }
  if (f.k === 'eq' && f.l.k === 'f') return { k: 'not', p: f.r }
  return f
}
const simp1 = (f: Fm): Fm => {
  if ((f.k === 'all' || f.k === 'ex') && !fv(f.p).has(f.v)) return f.p
  return psimp(f)
}
function simplify(f: Fm): Fm {
  switch (f.k) {
    case 'not': return simp1({ k: 'not', p: simplify(f.p) })
    case 'and': return simp1({ k: 'and', l: simplify(f.l), r: simplify(f.r) })
    case 'or': return simp1({ k: 'or', l: simplify(f.l), r: simplify(f.r) })
    case 'imp': return simp1({ k: 'imp', l: simplify(f.l), r: simplify(f.r) })
    case 'eq': return simp1({ k: 'eq', l: simplify(f.l), r: simplify(f.r) })
    case 'all': return simp1({ k: 'all', v: f.v, p: simplify(f.p) })
    case 'ex': return simp1({ k: 'ex', v: f.v, p: simplify(f.p) })
    default: return f
  }
}

export function nnf(f: Fm): Fm {
  switch (f.k) {
    case 'and': return { k: 'and', l: nnf(f.l), r: nnf(f.r) }
    case 'or': return { k: 'or', l: nnf(f.l), r: nnf(f.r) }
    case 'imp': return { k: 'or', l: nnf({ k: 'not', p: f.l }), r: nnf(f.r) }
    case 'eq': return { k: 'or', l: { k: 'and', l: nnf(f.l), r: nnf(f.r) }, r: { k: 'and', l: nnf({ k: 'not', p: f.l }), r: nnf({ k: 'not', p: f.r }) } }
    case 'not':
      switch (f.p.k) {
        case 'not': return nnf(f.p.p)
        case 'and': return { k: 'or', l: nnf({ k: 'not', p: f.p.l }), r: nnf({ k: 'not', p: f.p.r }) }
        case 'or': return { k: 'and', l: nnf({ k: 'not', p: f.p.l }), r: nnf({ k: 'not', p: f.p.r }) }
        case 'imp': return { k: 'and', l: nnf(f.p.l), r: nnf({ k: 'not', p: f.p.r }) }
        case 'eq': return { k: 'or', l: { k: 'and', l: nnf(f.p.l), r: nnf({ k: 'not', p: f.p.r }) }, r: { k: 'and', l: nnf({ k: 'not', p: f.p.l }), r: nnf(f.p.r) } }
        case 'all': return { k: 'ex', v: f.p.v, p: nnf({ k: 'not', p: f.p.p }) }
        case 'ex': return { k: 'all', v: f.p.v, p: nnf({ k: 'not', p: f.p.p }) }
        default: return f
      }
    case 'all': return { k: 'all', v: f.v, p: nnf(f.p) }
    case 'ex': return { k: 'ex', v: f.v, p: nnf(f.p) }
    default: return f
  }
}
const negate = (f: Fm): Fm => (f.k === 'not' ? f.p : { k: 'not', p: f })

function pullQuants(f: Fm): Fm {
  if (f.k === 'and' && f.l.k === 'all' && f.r.k === 'all') return pullQ(f, 'all', 'and', f.l.v, f.r.v, f.l.p, f.r.p, true, true)
  if (f.k === 'or' && f.l.k === 'ex' && f.r.k === 'ex') return pullQ(f, 'ex', 'or', f.l.v, f.r.v, f.l.p, f.r.p, true, true)
  if (f.k === 'and' && f.l.k === 'all') return pullQ(f, 'all', 'and', f.l.v, f.l.v, f.l.p, f.r, true, false)
  if (f.k === 'and' && f.r.k === 'all') return pullQ(f, 'all', 'and', f.r.v, f.r.v, f.l, f.r.p, false, true)
  if (f.k === 'or' && f.l.k === 'all') return pullQ(f, 'all', 'or', f.l.v, f.l.v, f.l.p, f.r, true, false)
  if (f.k === 'or' && f.r.k === 'all') return pullQ(f, 'all', 'or', f.r.v, f.r.v, f.l, f.r.p, false, true)
  if (f.k === 'and' && f.l.k === 'ex') return pullQ(f, 'ex', 'and', f.l.v, f.l.v, f.l.p, f.r, true, false)
  if (f.k === 'and' && f.r.k === 'ex') return pullQ(f, 'ex', 'and', f.r.v, f.r.v, f.l, f.r.p, false, true)
  if (f.k === 'or' && f.l.k === 'ex') return pullQ(f, 'ex', 'or', f.l.v, f.l.v, f.l.p, f.r, true, false)
  if (f.k === 'or' && f.r.k === 'ex') return pullQ(f, 'ex', 'or', f.r.v, f.r.v, f.l, f.r.p, false, true)
  return f
}
function pullQ(f: Fm, q: 'all' | 'ex', op: 'and' | 'or', x: string, y: string, p: Fm, qq: Fm, l: boolean, r: boolean): Fm {
  const z = variant(x, fv(f))
  const p2 = l ? subst(new Map([[x, { k: 'v', n: z }]]), p) : p
  const q2 = r ? subst(new Map([[y, { k: 'v', n: z }]]), qq) : qq
  const inner = op === 'and' ? { k: 'and', l: p2, r: q2 } as Fm : { k: 'or', l: p2, r: q2 } as Fm
  return q === 'all' ? { k: 'all', v: z, p: pullQuants(inner) } : { k: 'ex', v: z, p: pullQuants(inner) }
}
function prenex(f: Fm): Fm {
  if (f.k === 'all') return { k: 'all', v: f.v, p: prenex(f.p) }
  if (f.k === 'ex') return { k: 'ex', v: f.v, p: prenex(f.p) }
  if (f.k === 'and') return pullQuants({ k: 'and', l: prenex(f.l), r: prenex(f.r) })
  if (f.k === 'or') return pullQuants({ k: 'or', l: prenex(f.l), r: prenex(f.r) })
  return f
}
const pnf = (f: Fm): Fm => prenex(nnf(simplify(f)))

// skolemisation
const funcsOfTm = (t: Tm, acc: Set<string>): void => {
  if (t.k === 'f') { acc.add(`${t.n}/${t.a.length}`); t.a.forEach((x) => funcsOfTm(x, acc)) }
}
const functionsOf = (f: Fm): Set<string> => {
  const acc = new Set<string>()
  const go = (g: Fm): void => {
    if (g.k === 'at') g.r.a.forEach((x) => funcsOfTm(x, acc))
    else if (g.k === 'not') go(g.p)
    else if (g.k === 'all' || g.k === 'ex') go(g.p)
    else if (g.k !== 't' && g.k !== 'f') { go(g.l); go(g.r) }
  }
  go(f)
  return acc
}
function skolem(f: Fm, fns: Set<string>): [Fm, Set<string>] {
  if (f.k === 'ex') {
    const xs = [...fv(f)]
    const fn = variant(f.v, fns)
    const sk = xs.length === 0 ? `ᶜ${fn}` : `ᶠ${fn}`
    const fx: Tm = { k: 'f', n: sk, a: xs.map((x) => ({ k: 'v', n: x } as Tm)) }
    return skolem(subst(new Map([[f.v, fx]]), f.p), new Set([...fns, fn]))
  }
  if (f.k === 'all') { const [p2, s2] = skolem(f.p, fns); return [{ k: 'all', v: f.v, p: p2 }, s2] }
  if (f.k === 'and' || f.k === 'or' || f.k === 'imp' || f.k === 'eq') {
    const [l2, s2] = skolem(f.l, fns)
    const [r2, s3] = skolem(f.r, s2)
    return [{ k: f.k, l: l2, r: r2 } as Fm, s3]
  }
  return [f, fns]
}
const aSkolemize = (f: Fm): Fm => skolem(nnf(simplify(f)), new Set([...functionsOf(f)].map((s) => s.split('/')[0]!)))[0]
const skolemise = (f: Fm): Fm => pnf(aSkolemize(f))
const specialize = (f: Fm): Fm => (f.k === 'all' ? specialize(f.p) : f)

// ------------------------------------------------------------ resolution ---

// Ordering mirrors Haskell's derived `Ord` (Syntax: True < False < Atom < Not
// < And < Or < Impl < Eq < Forall < Exists; Var < Fn; tuple/list ordering).
// The book's loop stores clauses in `Set`s, i.e. always sorted; the TS port
// must visit given-clauses and mgu premises in the same order or the search
// explores a wildly different (and much larger) space than upstream.
const cmpStr = (a: string, b: string): number => (a < b ? -1 : a > b ? 1 : 0)
const cmpTmList = (a: Tm[], b: Tm[]): number => {
  for (let i = 0; i < Math.min(a.length, b.length); i++) { const c = cmpTm(a[i]!, b[i]!); if (c !== 0) return c }
  return a.length - b.length
}
function cmpTm(s: Tm, t: Tm): number {
  if (s.k !== t.k) return s.k === 'v' ? -1 : 1
  if (s.k === 'v' && t.k === 'v') return cmpStr(s.n, t.n)
  if (s.k === 'f' && t.k === 'f') {
    const c = cmpStr(s.n, t.n)
    return c !== 0 ? c : cmpTmList(s.a, t.a)
  }
  return 0
}
const cmpRel = (a: Rel, b: Rel): number => cmpStr(a.n, b.n) !== 0 ? cmpStr(a.n, b.n) : cmpTmList(a.a, b.a)
const fmRank = (f: Fm): number => (f.k === 't' ? 0 : f.k === 'f' ? 1 : f.k === 'at' ? 2 : f.k === 'not' ? 3 : f.k === 'and' ? 4 : f.k === 'or' ? 5 : f.k === 'imp' ? 6 : f.k === 'eq' ? 7 : f.k === 'all' ? 8 : 9)
function cmpFm(a: Fm, b: Fm): number {
  const r = fmRank(a) - fmRank(b)
  if (r !== 0) return r
  if (a.k === 'at' && b.k === 'at') return cmpRel(a.r, b.r)
  if (a.k === 'not' && b.k === 'not') return cmpFm(a.p, b.p)
  if ((a.k === 'and' || a.k === 'or' || a.k === 'imp' || a.k === 'eq') && (b.k === 'and' || b.k === 'or' || b.k === 'imp' || b.k === 'eq')) {
    const c = cmpFm(a.l, (b as { l: Fm }).l)
    return c !== 0 ? c : cmpFm(a.r, (b as { r: Fm }).r)
  }
  if ((a.k === 'all' || a.k === 'ex') && (b.k === 'all' || b.k === 'ex')) {
    const c = cmpStr(a.v, (b as { v: string }).v)
    return c !== 0 ? c : cmpFm(a.p, (b as { p: Fm }).p)
  }
  return 0
}

type Lit = Fm // Atom | Not Atom | True | False in clauses
type Clause = Lit[]
const listConj = (fs: Fm[]): Fm => (fs.length === 0 ? TrueF : fs.reduce((a, b) => ({ k: 'and', l: a, r: b })))
const listDisj = (fs: Fm[]): Fm => (fs.length === 0 ? FalseF : fs.reduce((a, b) => ({ k: 'or', l: a, r: b })))

const litKey = (l: Lit): string => showFm(l)
const clauseKey = (c: Clause): string => {
  // Clauses are created by substitution during resolution, so register every
  // literal when its key is minted: lookup by key is then always total.
  // Deduplicate: like the book's Set-of-literals clauses, `A ∨ A` is just `A`.
  // Without this, self-resolution mints `A | A`, `A | A | A`, … as distinct
  // keys and the given-clause loop explodes instead of saturating/proving.
  c.forEach((l) => keyToLit.set(litKey(l), l))
  return [...new Set(c.map(litKey))].sort().join(' | ')
}
const isNeg = (l: Lit): boolean => l.k === 'not'
const positive = (l: Lit): boolean => !isNeg(l)

// (CNF below operates on literal-keys to mirror the book's set-of-sets code.)

function pureDnfKeys(f: Fm): Set<Set<string>> {
  if (f.k === 'and') {
    const l = pureDnfKeys(f.l); const r = pureDnfKeys(f.r)
    const out = new Set<Set<string>>()
    for (const s1 of l) for (const s2 of r) out.add(new Set([...s1, ...s2]))
    return out
  }
  if (f.k === 'or') return new Set([...pureDnfKeys(f.l), ...pureDnfKeys(f.r)])
  return new Set([new Set([litKey(f)])])
}
const keyToLit = new Map<string, Lit>()
const litOfKey = (k: string): Lit => keyToLit.get(k)!
function registerLits(f: Fm): void {
  if (f.k === 'and' || f.k === 'or' || f.k === 'imp' || f.k === 'eq') { registerLits(f.l); registerLits(f.r) }
  else if (f.k === 'not') {
    if (f.p.k === 'at' || f.p.k === 't' || f.p.k === 'f') keyToLit.set(litKey(f), f)
    registerLits(f.p)
  }
  else if (f.k === 'all' || f.k === 'ex') registerLits(f.p)
  else keyToLit.set(litKey(f), f)
}
const trivialKeys = (lits: string[]): boolean => {
  const pos = lits.filter((k) => !litOfKey(k).k || positive(litOfKey(k)))
  const neg = lits.filter((k) => isNeg(litOfKey(k)))
  const neged = new Set(neg.map((k) => litKey(negate(litOfKey(k)))))
  return pos.some((k) => neged.has(k))
}
function simpDnf(f: Fm): string[][] {
  if (f.k === 'f') return []
  if (f.k === 't') return [[]]
  registerLits(nnf(f))
  const djs = [...pureDnfKeys(nnf(f))].map((s) => [...s]).filter((d) => !trivialKeys(d))
  const sets = djs.map((d) => new Set(d))
  const simp = sets.filter((d) => !sets.some((o) => o !== d && [...o].every((x) => d.has(x)) && o.size < d.size))
  return simp.map((s) => [...s])
}
function pureCnfKeys(f: Fm): Set<Set<string>> {
  // negate every literal of pure'dnf (nnf (Not fm))
  const dnf = pureDnfKeys(nnf(negate(f)))
  const out = new Set<Set<string>>()
  for (const d of dnf) out.add(new Set([...d].map((k) => litKey(negate(litOfKey(k))))))
  return out
}
const cmpClause = (a: Clause, b: Clause): number => {
  for (let i = 0; i < Math.min(a.length, b.length); i++) { const c = cmpFm(a[i]!, b[i]!); if (c !== 0) return c }
  return a.length - b.length
}
// Clause keys decode back to literal lists for ordering (string order of the
// rendered key is NOT the book's literal order, e.g. `¬` sorts after ASCII).
const cmpClauseKey = (a: string, b: string): number =>
  cmpClause(a === '' ? [] : a.split(' | ').map(litOfKey), b === '' ? [] : b.split(' | ').map(litOfKey))
function simpCnf(f: Fm): Clause[] {
  if (f.k === 'f') return [[FalseF]]
  if (f.k === 't') return []
  registerLits(nnf(f)); registerLits(nnf(negate(f)))
  const cjs = [...pureCnfKeys(f)].map((s) => [...s]).filter((c) => !trivialKeys(c))
  const sets = cjs.map((c) => new Set(c))
  const simp = sets.filter((c) => !sets.some((o) => o !== c && [...o].every((x) => c.has(x)) && o.size < c.size))
  // Haskell's `pure'cnf`/`simp'cnf` produce `Set.toList`-sorted clauses.
  return simp.map((s) => [...s].map(litOfKey)).sort(cmpClause)
}

// unification (book style, env-based)
const isTriv = (env: Sub, x: string, t: Tm): boolean => {
  if (t.k === 'v') {
    if (t.n === x) return true
    const b = env.get(t.n)
    return b !== undefined && isTriv(env, x, b)
  }
  return t.a.some((s) => isTriv(env, x, s))
}
const occursFails = (env: Sub, x: string, t: Tm): boolean => {
  if (t.k === 'v') {
    const b = env.get(t.n)
    return b !== undefined && occursFails(env, x, b)
  }
  return t.a.some((s) => isTriv(env, x, s))
}
function unify(env: Sub, eqs: [Tm, Tm][]): Sub | null {
  if (eqs.length === 0) return env
  const [[s, t], ...rest] = eqs
  if (s.k === 'f' && t.k === 'f') {
    if (s.n !== t.n || s.a.length !== t.a.length) return null
    return unify(env, [...s.a.map((x, i) => [x, t.a[i]!] as [Tm, Tm]), ...rest])
  }
  if (s.k === 'v') {
    const b = env.get(s.n)
    if (b !== undefined) return unify(env, [[b, t], ...rest])
    if (occursFails(env, s.n, t)) return null
    const env2 = isTriv(env, s.n, t) ? env : new Map([...env, [s.n, t]])
    return unify(env2, rest)
  }
  return unify(env, [[t, s], ...rest])
}
const solveSub = (env: Sub): Sub => {
  const env2 = new Map<string, Tm>()
  for (const [k, v] of env) env2.set(k, tsubst(env, v))
  const same = [...env2.entries()].every(([k, v]) => litKeyOfTm(env.get(k)!) === litKeyOfTm(v))
  return same ? env2 : solveSub(env2)
}
const litKeyOfTm = (t: Tm): string => showTm(t)
function unifyLiterals(env: Sub, a: Lit, b: Lit): Sub | null {
  if (a.k === 'at' && b.k === 'at') {
    if (a.r.n !== b.r.n || a.r.a.length !== b.r.a.length) return null
    return unify(env, a.r.a.map((x, i) => [x, b.r.a[i]!] as [Tm, Tm]))
  }
  if (a.k === 'not' && b.k === 'not') return unifyLiterals(env, a.p, b.p)
  if (a.k === 'f' && b.k === 'f') return env
  return null
}
const unifyComplements = (env: Sub, a: Lit, b: Lit): Sub | null => unifyLiterals(env, a, negate(b))
function mgu(lits: Lit[], env: Sub): Sub | null {
  if (lits.length < 2) return solveSub(env)
  const [a, b, ...rest] = lits
  const e2 = unifyLiterals(env, a!, b!)
  return e2 === null ? null : mgu([b!, ...rest], e2)
}
const unifiable = (a: Lit, b: Lit): boolean => unifyLiterals(new Map(), a, b) !== null

const renameClause = (prefix: string, cl: Clause): Clause => {
  const vs = new Set<string>()
  cl.forEach((l) => fv(l).forEach((x) => vs.add(x)))
  const s: Sub = new Map([...vs].map((x) => [x, { k: 'v', n: prefix + x } as Tm]))
  return cl.map((l) => subst(s, l))
}

function resolvents(cl1: Clause, cl2: Clause, p: Lit): Set<string> {
  const acc = new Set<string>()
  const ps2 = cl2.filter((q) => unifiable(negate(p), q))
  if (ps2.length === 0) return acc
  const ps1 = cl1.filter((q) => q !== p && unifiable(p, q))
  const subsets = (arr: Lit[]): Lit[][] => {
    const out: Lit[][] = [[]]
    for (const x of arr) for (const s of [...out]) out.push([...s, x])
    return out
  }
  const s1sets = subsets(ps1).map((s) => [...s, p])
  const s2sets = subsets(ps2).filter((s) => s.length > 0)
  for (const s1 of s1sets) for (const s2 of s2sets) {
    // Haskell feeds `Set.toList (s1 ∪ map negate s2)` (sorted) to mgu; the
    // substitution found (and hence the resolvent) depends on that order.
    const combo = [...s1, ...s2.map(negate)].sort(cmpFm)
    const sub = mgu(combo, new Map())
    if (!sub) continue
    const rest = [...cl1.filter((l) => !s1.includes(l)), ...cl2.filter((l) => !s2.includes(l))]
    const res = rest.map((l) => subst(sub, l))
    acc.add(clauseKey(res))
  }
  return acc
}
const clauseFromKey = (k: string): Clause => (k === '' ? [] : k.split(' | ').map(litOfKey))
function resolveClauses(c1: Clause, c2: Clause): Set<string> {
  const r1 = renameClause('x', c1)
  const r2 = renameClause('y', c2)
  const out = new Set<string>()
  for (const lit of r1) for (const k of resolvents(r1, r2, lit)) out.add(k)
  return out
}

// given-clause loop
// Caps mirror upstream verdicts on all vendored examples (peak observed:
// ~420 iterations / ~130k clauses on list.rin) with headroom, while keeping
// genuinely-unprovable queries from hanging the demo UI (the loop yields to
// the UI and supports interrupt).
const MAX_ITERS = 4000
const MAX_CLAUSES = 200000
export interface Resolution { ok: boolean; answers: [string, Tm][]; capped: boolean }

function containsContradiction(keys: string[]): { answers: [string, Tm][] } | null {
  for (const k of keys) {
    const cl = clauseFromKey(k)
    if (cl.length === 0) return { answers: [] }
    if (cl.every(isAnswer) && new Set(cl.map(answerName)).size === cl.length) {
      return { answers: cl.map(answerPair) }
    }
  }
  return null
}
const isAnswer = (l: Lit): boolean => l.k === 'at' && l.r.n === '_Answer_' && l.r.a.length === 2
const answerName = (l: Lit): string => {
  if (l.k === 'at' && l.r.n === '_Answer_') { const fn = l.r.a[1]!; if (fn.k === 'f') return fn.n }
  throw new Error('expected _Answer_ literal')
}
const answerPair = (l: Lit): [string, Tm] => {
  if (l.k === 'at' && l.r.n === '_Answer_') { const fn = l.r.a[1]!; if (fn.k === 'f' && fn.a.length === 0) return [fn.n, l.r.a[0]!] }
  throw new Error('expected _Answer_ literal')
}

export interface ProverCtl {
  aborted(): boolean
  tick(): Promise<void>
}

async function pureResolution(f: Fm, ctl: ProverCtl): Promise<{ ok: boolean; answers: [string, Tm][]; capped: boolean; aborted?: boolean }> {
  const clauses = simpCnf(specialize(skolemise(f))).map(clauseKey)
  let used: string[] = []
  let unused = [...clauses]
  // immediate contradiction (book's special case)
  for (const k of unused) {
    const hit = containsContradiction([k])
    if (hit) return { ok: true, answers: hit.answers, capped: false }
  }
  let iters = 0
  const seen = new Set<string>(unused)
  while (unused.length > 0) {
    if (++iters > MAX_ITERS || seen.size > MAX_CLAUSES) return { ok: false, answers: [], capped: true }
    if ((iters & 127) === 0) {
      await ctl.tick()
      if (ctl.aborted()) return { ok: false, answers: [], capped: false, aborted: true }
    }
    const [cl, ...rest] = unused
    unused = rest
    used = [cl!, ...used]
    const cur = clauseFromKey(cl!)
    let news = new Set<string>()
    for (const u of used) {
      const other = clauseFromKey(u)
      for (const k of resolveClauses(cur, other)) news.add(k)
    }
    // Haskell appends `Set.toList`-sorted fresh clauses; FIFO order after
    // that is what makes the TS search follow the upstream search path.
    const fresh = [...news].sort(cmpClauseKey).filter((k) => !trivialKeys(k === '' ? [] : k.split(' | ')) && !seen.has(k))
    fresh.forEach((k) => seen.add(k))
    const hit = containsContradiction(fresh)
    if (hit) return { ok: true, answers: hit.answers, capped: false }
    unused = [...unused, ...fresh]
  }
  return { ok: false, answers: [], capped: false }
}

const allExistentials = (f: Fm): string[] => (f.k === 'ex' ? [f.v, ...allExistentials(f.p)] : [])
const allUniversals = (f: Fm): [string[], Fm] => (f.k === 'all' ? (() => { const [xs, q] = allUniversals(f.p); return [[f.v, ...xs], q] as [string[], Fm] })() : [[], f])

async function resolution(assumptions: Fm[], goal: Fm, ctl: ProverCtl): Promise<{ ok: boolean; answers: [string, Tm][]; capped: boolean; aborted?: boolean }> {
  if (goal.k === 'ex') {
    const exs = allExistentials(goal)
    const neg = nnf(negate(goal))
    const [unis, p] = allUniversals(neg)
    const answers: Fm[] = unis.map((u, i) => ({ k: 'at', r: { n: '_Answer_', a: [{ k: 'v', n: u }, { k: 'f', n: exs[i]!, a: [] }] } } as Fm))
    let disj: Fm = listDisj([p, ...answers])
    for (let i = unis.length - 1; i >= 0; i--) disj = { k: 'all', v: unis[i]!, p: disj }
    return pureResolution(listConj([disj, ...assumptions]), ctl)
  }
  return resolutionPrime(assumptions, goal, ctl)
}
function resolutionPrime(assumptions: Fm[], conclusion: Fm, ctl: ProverCtl): Promise<{ ok: boolean; answers: [string, Tm][]; capped: boolean; aborted?: boolean }> {
  return pureResolution(listConj([negate(conclusion), ...assumptions]), ctl)
}
const containsExists = (f: Fm): boolean => {
  switch (f.k) {
    case 'ex': return true
    case 'not': return containsExists(f.p)
    case 'all': return containsExists(f.p)
    case 't': case 'f': case 'at': return false
    default: return containsExists(f.l) || containsExists(f.r)
  }
}

// ----------------------------------------------------------------- engine ---

export class ResinEngine implements Engine {
  readonly id = 'resin'
  private assumptions: Fm[] = [TrueF]
  private files = new Map<string, string>()
  private editorContent = ''
  private abort = false

  private get ctl(): ProverCtl {
    return { aborted: () => this.abort, tick: yieldToUI }
  }

  banner(): string {
    return 'Resin — a toy automated theorem prover for classical First Order Logic.'
  }
  prompt(): string {
    const ctx = this.assumptions.map(showFm).join(', ')
    const short = ctx.length > 15 ? ctx.slice(0, 15) + ' ...' : ctx
    return `${short} ⊢ `
  }
  editorAliases(): string[] {
    return ['editor.rin', 'demo.rin', 'editor', 'demo']
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
    this.assumptions = [TrueF]
    this.abort = false
  }

  /** Abort the running proof; the assumptions are kept. */
  interrupt(): void {
    this.abort = true
  }

  private resolveFile(path: string): string | null {
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
    if (line === ':q' || line === ':Q') return { output: 'Bye!', halted: true }
    const plen = this.prompt().length - 2 // mirrors prompt'len (prompt minus "⊢ ")
    const caret = (cmdLen: number, col: number) => `${' '.repeat(plen + cmdLen + col)}^\n`
    if (/^:check(\s|with\b|:|$)/.test(line) || /^:ch\b/.test(line) || /^:c\b/.test(line)) {
      const m = line.match(/^:(?:check|ch|c)\s*(with\s+)?(.*)$/)
      const withAsm = !!m?.[1]
      const path = (m?.[2] ?? '').trim()
      const content = this.resolveFile(path)
      if (content === null) return { output: `Cannot open \`${path}\`: no such virtual file (pick an example or press Load into REPL).` }
      if (!withAsm && this.assumptions.length > 1)
        return { output: `⚠️ The assumptions from the interactive repl will not be used when checking the module!\nIf you want to include them in the inference for the module, use command \`:check with\`.\n${await this.checkModule(content, [])}` }
      if (withAsm && this.assumptions.length < 2)
        void 0
      return { output: await this.checkModule(content, withAsm ? [...this.assumptions] : []) }
    }
    const assumeM = line.match(/^:(assume|a)\s+(.*)$/)
    if (assumeM) {
      try {
        const fm = parseFormulaTop(assumeM[2]!)
        this.assumptions = [fm, ...this.assumptions]
        return { output: '' }
      } catch (e) {
        return { output: `${caret(assumeM[1]!.length + 2, 0)}${errMsg(e)}` }
      }
    }
    if (/^:show\b/.test(line)) return { output: this.assumptions.map(showFm).join('  ∧  ') }
    const entailsM = line.match(/^:(entails|e|find)\s+(.*)$/)
    if (entailsM) return this.find(entailsM[2]!, plen)
    if (/^:consistent\b/.test(line) || /^:con\b/.test(line)) {
      const r = await pureResolution(listConj(this.assumptions), this.ctl)
      if (r.aborted) return { output: 'Interrupted.', interrupted: true }
      return { output: r.ok ? '❌ the current set of assumptions is not logically consistent' : '✅ the current set of assumptions is logically consistent' }
    }
    if (/^:clear\b/.test(line)) { this.assumptions = [TrueF]; return { output: '' } }
    const skolM = line.match(/^:(skolemize|skol)\s+(.*)$/)
    if (skolM) {
      try {
        const fm = parseFormulaTop(skolM[2]!)
        return { output: showFm(skolemise(fm)) }
      } catch (e) { return { output: `${caret(skolM[1]!.length + 2, 0)}${errMsg(e)}` } }
    }
    if (/^:simp\s+/.test(line)) {
      const src = line.replace(/^:simp\s+/, '')
      try { return { output: showFm(parseFormulaTop(src)) } } catch (e) { return { output: `${caret(6, 0)}${errMsg(e)}` } }
    }
    if (/^:cnf\s+/.test(line)) {
      const src = line.replace(/^:cnf\s+/, '')
      try {
        const fm = parseFormulaTop(src)
        const warn = containsExists(fm)
          ? '⚠️  I can\'t really perform the CNF conversion on a FOL formula containing an existential quantifier.\n   This would require skolemization, a process that would produce only an equisatisfiable formula.\n   The following is a result of doing so, be warned!\n'
          : ''
        const cnf: Fm = specialize(prenex(aSkolemize(fm)))
        return { output: `${warn}${showFm(cnf)}` }
      } catch (e) { return { output: `${caret(5, 0)}${errMsg(e)}` } }
    }
    if (/^:nnf\s+/.test(line)) {
      const src = line.replace(/^:nnf\s+/, '')
      try { return { output: showFm(nnf(simplify(parseFormulaTop(src)))) } } catch (e) { return { output: `${caret(5, 0)}${errMsg(e)}` } }
    }
    if (/^:pnf\s+/.test(line)) {
      const src = line.replace(/^:pnf\s+/, '')
      try { return { output: showFm(pnf(simplify(parseFormulaTop(src)))) } } catch (e) { return { output: `${caret(5, 0)}${errMsg(e)}` } }
    }
    if (/^:repeat\s+/.test(line)) {
      const src = line.replace(/^:repeat\s+/, '')
      try { return { output: showFm(parseFormulaTop(src)) } } catch (e) { return { output: `${caret(8, 0)}${errMsg(e)}` } }
    }
    if (line.startsWith(':')) return { output: "I don't know this command, sorry." }
    if (line.trim() === '') return { output: '' }
    return this.find(line, plen)
  }

  private async find(src: string, plen: number): Promise<EngineResult> {
    let goal: Fm
    try {
      goal = parseFormulaTop(src)
    } catch (e) {
      return { output: `${' '.repeat(plen)}^ \n${errMsg(e)}` }
    }
    const r = await resolution(this.assumptions, goal, this.ctl)
    if (r.aborted) return { output: 'Interrupted.', interrupted: true }
    if (r.ok) {
      const wit = r.answers.map(([x, t]) => `   for \`${x}\` being \`${showTm(t)}\``).join(', ')
      return { output: `✅ the conclusion  \`${showFm(goal)}\`  is a logical consequence of the assumptions${wit ? '\n' + wit : ''}${r.capped ? '' : ''}` }
    }
    const pad = ' '.repeat(plen)
    const extra = r.capped ? `\n${pad}(search capped for the demo — treated as unprovable here)` : ''
    return { output: `❌ \`${showFm(goal)}\`  is not a logical consequence of the assumptions\n${pad} an interpretation where all the assumptions and \`${showFm(nnf(negate(goal)))}\` all hold is possible${extra}` }
  }

  private async checkModule(content: string, extraAsm: Fm[]): Promise<string> {
    let mod: ModuleT
    try {
      mod = parseModule(content)
    } catch (e) {
      return errMsg(e)
    }
    const out: string[] = []
    let proven: { name: string | null; fm: Fm }[] = []
    const axioms = [...mod.axioms.map((a) => ({ name: a.name, fm: a.fm })), ...extraAsm.map((f) => ({ name: null as string | null, fm: f }))]
    for (const th of mod.theorems) {
      const res = await this.tryProve(proven, axioms, th)
      if (res.aborted) return [...out, 'Interrupted.'].join('\n')
      out.push(res.msg)
      if (res.fm) proven = [res.fm, ...proven]
    }
    if (out.length === 0) return '-- no theorems in file.'
    return out.join('\n')
  }

  private async tryProve(proven: { name: string | null; fm: Fm }[], axioms: { name: string | null; fm: Fm }[], th: TheoremT): Promise<{ msg: string; fm: { name: string | null; fm: Fm } | null; aborted?: boolean }> {
    // check proof body
    let asserted: { name: string | null; fm: Fm }[] = []
    for (const a of th.proof) {
      const premises = a.allowed === null
        ? [...axioms.map((x) => x.fm), ...th.assumptions.map((x) => x.fm), ...asserted.map((x) => x.fm)]
        : [...namedOnly([...axioms, ...proven, ...th.assumptions, ...asserted], a.allowed)]
      const r = await resolutionPrime(premises, a.fm, this.ctl)
      if (r.aborted) return { msg: '', fm: null, aborted: true }
      if (!r.ok) {
        return { msg: `❌ theorem \`${th.name}' can not be checked\n            the proof provided is not valid because\n            the assertion \`${a.name ? a.name + ': ' : ''}${showFm(a.fm)}\` is unprovable`, fm: null }
      }
      asserted = [{ name: a.name, fm: a.fm }, ...asserted]
    }
    const thFm: Fm = th.assumptions.reduceRight((acc, a) => ({ k: 'imp', l: a.fm, r: acc } as Fm), th.conclusion)
    if (th.allowed === null) {
      const premises = [...axioms.map((x) => x.fm), ...th.assumptions.map((x) => x.fm), ...asserted.map((x) => x.fm)]
      const r = await resolutionPrime(premises, th.conclusion, this.ctl)
      if (r.aborted) return { msg: '', fm: null, aborted: true }
      if (r.ok) return { msg: `✅ theorem \`${th.name}\` is logically valid`, fm: { name: th.name, fm: thFm } }
      return { msg: `❌ theorem \`${th.name}\` is not logically valid\n            an interpretation where all the assumptions and \`${showFm(nnf(negate(th.conclusion)))}\` all hold is possible`, fm: null }
    }
    const named = namedOnly([...axioms, ...proven, ...asserted], th.allowed)
    const premises = [...named, ...th.assumptions.map((x) => x.fm)]
    const r = await resolutionPrime(premises, th.conclusion, this.ctl)
    if (r.aborted) return { msg: '', fm: null, aborted: true }
    if (r.ok) return { msg: `✅ theorem \`${th.name}\` is logically valid`, fm: { name: th.name, fm: thFm } }
    return { msg: `❌ theorem \`${th.name}\` is not logically valid\n            an interpretation where all the assumptions and all the specified axioms, theorems and lemmas, and \`${showFm(nnf(negate(th.conclusion)))}\` all hold is possible`, fm: null }
  }
}

function namedOnly(pool: { name: string | null; fm: Fm }[], names: string[]): Fm[] {
  const set = new Set(names)
  return pool.filter((x) => x.name !== null && set.has(x.name)).map((x) => x.fm)
}

function errMsg(e: unknown): string {
  if (e !== null && typeof e === 'object' && 'msg' in e) return String((e as { msg: unknown }).msg)
  return 'Parse error.'
}
