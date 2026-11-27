/**
 * Detour — mixed-initiative interactive proof assistant for first-order logic.
 *
 * Faithful browser-native TypeScript port of github.com/jalivert/detour.
 * The checker (Fitch natural deduction + hardcoded `prove` search driven by
 * the What'Next/Inform interaction protocol) is ported 1:1; only the IO
 * driver differs (virtual files + line-based terminal instead of stdin).
 *
 * Deviations from upstream (documented):
 * - The search is fuel-capped (INTERACT_BUDGET user prompts per :load and
 *   STEP_BUDGET checker steps); upstream loops forever on unprovable goals.
 *   Caps surface as explicit errors, never as wrong successes.
 * - `traceM` stderr debug spam is dropped (it never reaches stdout upstream).
 * - `\r\n` is normalized to `\n` on file intake (browsers paste CRLF; the
 *   upstream lexer rejects `\r` with a lexical error).
 */

import type { Engine, EngineResult } from './engine'
import { yieldToUI } from './engine'

// ---------------------------------------------------------------- AST ---

export type Term
  = { k: 'bound', name: string }
  | { k: 'app', c: string, args: Term[] }
  | { k: 'free', name: string }
  | { k: 'rigid', name: string }

export type RelArgs
  = { k: 'terms', args: Term[] }
  | { k: 'formulae', args: Formula[] }

export type Relation
  = { k: 'rel', name: string, args: RelArgs }
  | { k: 'meta', prop: string }

export type Formula
  = { k: 'true' }
  | { k: 'false' }
  | { k: 'atom', rel: Relation }
  | { k: 'not', f: Formula }
  | { k: 'and', l: Formula, r: Formula }
  | { k: 'or', l: Formula, r: Formula }
  | { k: 'impl', l: Formula, r: Formula }
  | { k: 'eq', l: Formula, r: Formula }
  | { k: 'forall', name: string, ts: TypeScheme, body: Formula }
  | { k: 'exists', name: string, ts: TypeScheme, body: Formula }

export type DType
  = { k: 'const', name: string }
  | { k: 'var', name: string }
  | { k: 'fn', a: DType, b: DType }

export interface TypeScheme { vars: string[]; ty: DType }

export type RuleKind
  = { k: 'builtin', name: Builtin }
  | { k: 'custom', name: string }

export type Builtin
  = 'ImplIntro' | 'ImplElim' | 'ConjIntro' | 'ConjElim' | 'DisjIntro' | 'DisjElim'
  | 'NegElim' | 'EquivIntro' | 'EquivElim' | 'TrueIntro' | 'ProofByContradiction'
  | 'ContraElim' | 'ForallIntro' | 'ForallElim' | 'ExistsIntro' | 'ExistsElim'
  | 'Repetition'

export type Justification
  = { k: 'rule', kind: RuleKind, on: string[] }
  | { k: 'theorem', name: string, on: string[] }
  | { k: 'unproved' }
  | { k: 'induction', proofs: CaseProof[] }
  | { k: 'subst', on: Term, using: string }
  | { k: 'cases', on: Term, proofs: CaseProof[] }

export type Assumption
  = { k: 'formula', pairs: [string | null, Formula][] }
  | { k: 'universal', binds: [string, TypeScheme][] }
  | { k: 'existential', binding: [string | null, Formula], binds: [string, TypeScheme][] }

export interface Claim { name: string | null; formula: Formula; just: Justification }
export interface CaseProof { con: string; rigids: string[]; proof: Proof }
export interface Proof { name: string | null; assum: Assumption; ders: Judgment[] }

export type Judgment
  = { k: 'sub', proof: Proof }
  | { k: 'claim', claim: Claim }
  | { k: 'alias', name: string, formula: Formula }
  | { k: 'prove', name: string | null, formula: Formula }

export interface DTheorem {
  name: string; propVars: string[]; assumptions: Formula[];
  conclusion: Formula; proof: Judgment[];
}

export interface JudRule {
  name: string; propVars: string[]; params: [string, DType][];
  premises: Formula[]; conclusion: Formula;
}
export interface Jud { name: string; propVars: string[]; con: [string, DType[]]; rules: JudRule[] }
export interface Ctor { name: string; args: DType[] }

export interface DModule {
  name: string; constants: [string, TypeScheme][]; aliases: [string, Term][];
  axioms: [string, Formula][]; syntax: [string, Ctor[]][];
  judgments: Jud[]; theorems: DTheorem[];
}

// --------------------------------------------------------------- show ---

export function showTerm(t: Term): string {
  switch (t.k) {
    case 'bound': return `${t.name}ᵇ`
    case 'app': return t.args.length === 0 ? `${t.c}ᶜ` : `${t.c}(${t.args.map(showTerm).join(', ')})`
    case 'free': return `${t.name}·?`
    case 'rigid': return `${t.name}®`
  }
}

export function showType(t: DType): string {
  switch (t.k) {
    case 'const': return `${t.name}ᶜ`
    case 'var': return `${t.name}?`
    case 'fn': return `${showType(t.a)} -> ${showType(t.b)}`
  }
}

export function showScheme(s: TypeScheme): string {
  if (s.vars.length === 0) return showType(s.ty)
  return `forall ${s.vars.join(' ')} . ${showType(s.ty)}`
}

function showRelArgs(a: RelArgs): string {
  return a.args.map((x) => (a.k === 'terms' ? showTerm(x as Term) : showFormula(x as Formula))).join(', ')
}

export function showRelation(r: Relation): string {
  if (r.k === 'meta') return `_${r.prop}`
  return `${r.name}(${showRelArgs(r.args)})`
}

function isCompound(f: Formula): boolean {
  return f.k === 'not' || f.k === 'and' || f.k === 'or' || f.k === 'impl'
    || f.k === 'eq' || f.k === 'forall' || f.k === 'exists'
}

export function showFormula(f: Formula): string {
  switch (f.k) {
    case 'true': return '⊤'
    case 'false': return '⊥'
    case 'atom':
      if (f.rel.k === 'rel' && f.rel.args.args.length === 0) return f.rel.name
      return showRelation(f.rel)
    case 'not': return isCompound(f.f) ? `¬(${showFormula(f.f)})` : `¬${showFormula(f.f)}`
    case 'and': {
      const p = f.l; const q = f.r
      const pa = p.k === 'and'; const qa = q.k === 'and'
      const pc = isCompound(p); const qc = isCompound(q)
      if (pa && qa) return `${showFormula(p)} ∧ ${showFormula(q)}`
      if (pa && qc) return `${showFormula(p)} ∧ (${showFormula(q)})`
      if (qa && pc) return `(${showFormula(p)}) ∧ ${showFormula(q)}`
      if (pc && qc) return `(${showFormula(p)}) ∧ (${showFormula(q)})`
      if (pc) return `(${showFormula(p)}) ∧ ${showFormula(q)}`
      if (qc) return `${showFormula(p)} ∧ (${showFormula(q)})`
      return `${showFormula(p)} ∧ ${showFormula(q)}`
    }
    case 'or': {
      const p = f.l; const q = f.r
      const pa = p.k === 'or'; const qa = q.k === 'or'
      const pc = isCompound(p); const qc = isCompound(q)
      if (pa && qa) return `${showFormula(p)} ∨ ${showFormula(q)}`
      if (pa && qc) return `${showFormula(p)} ∨ (${showFormula(q)})`
      if (qa && pc) return `(${showFormula(p)}) ∨ ${showFormula(q)}`
      if (pc && qc) return `(${showFormula(p)}) ∨ (${showFormula(q)})`
      if (pc) return `(${showFormula(p)}) ∨ ${showFormula(q)}`
      if (qc) return `${showFormula(p)} ∨ (${showFormula(q)})`
      return `${showFormula(p)} ∨ ${showFormula(q)}`
    }
    case 'impl': {
      const p = f.l; const q = f.r
      const pn = p.k === 'not'; const qn = q.k === 'not'
      const pi = p.k === 'impl'; const qi = q.k === 'impl'
      const pc = isCompound(p); const qc = isCompound(q)
      if (qi && pn) return `${showFormula(p)} ==> ${showFormula(q)}`
      if (qi && !pc) return `${showFormula(p)} ==> ${showFormula(q)}`
      if (pn && qn) return `${showFormula(p)} ==> ${showFormula(q)}`
      if (pn && !qc) return `${showFormula(p)} ==> ${showFormula(q)}`
      if (pn) return `${showFormula(p)} ==> ${showFormula(q)}`
      if (qn && !pc) return `${showFormula(p)} ==> ${showFormula(q)}`
      if (qn) return `(${showFormula(p)}) ==> ${showFormula(q)}`
      if (!pc && !qc) return `${showFormula(p)} ==> ${showFormula(q)}`
      if (!pc) return `${showFormula(p)} ==> (${showFormula(q)})`
      if (!qc) return `(${showFormula(p)}) ==> ${showFormula(q)}`
      void pi
      return `(${showFormula(p)}) ==> (${showFormula(q)})`
    }
    case 'eq': return `(${showFormula(f.l)}) <==> (${showFormula(f.r)})`
    case 'forall': return `∀ (${f.name} : ${showScheme(f.ts)}) : ${showFormula(f.body)}`
    case 'exists': return `∃ (${f.name} : ${showScheme(f.ts)}) : ${showFormula(f.body)}`
  }
}

function showRigidScheme(pair: [string, TypeScheme]): string {
  return `(${pair[0]},${showScheme(pair[1])})`
}

export function showAssumption(a: Assumption): string {
  switch (a.k) {
    case 'formula':
      return a.pairs.map(([n, fm]) => `${n ?? '_'} : ${showFormula(fm)}\n`).join('')
    case 'universal':
      return `for all ${a.binds.map(showRigidScheme).join(', ')}`
    case 'existential': {
      const [n, fm] = a.binding
      const pre = n === null ? `_ : ${showFormula(fm)}` : `${n} : ${showFormula(fm)}`
      return `${pre} for some ${a.binds.map(showRigidScheme).join(', ')}\n`
    }
  }
}

function showRuleKind(r: RuleKind): string {
  // NOTE: derived Show — constructor names, not surface syntax.
  if (r.k === 'custom') return `Custom "${r.name}"`
  return r.name
}

export function showJust(j: Justification): string {
  switch (j.k) {
    case 'rule': return `rule ${showRuleKind(j.kind)} on ${j.on.join(', ')}`
    case 'theorem': return `theorem ${j.name} on ${j.on.join(', ')}`
    case 'unproved': return 'unproved'
    case 'induction': return `induction : ${j.proofs.map(showCase).join('\n')}`
    case 'subst': return `substitution on ${showTerm(j.on)} using ${j.using}`
    case 'cases': return `case analysis on ${showTerm(j.on)} : ${j.proofs.map(showCase).join('\n')}`
  }
}

function showCase(c: CaseProof): string {
  // derived Show: Case (C "c",[R "x",...]) <proof>
  const rs = c.rigids.map((r) => `R "${r}"`).join(', ')
  return `Case (C "${c.con}",[${rs}]) ${showProof(c.proof)}`
}

export function showClaim(c: Claim): string {
  return `${c.name ?? '_'} : ${showFormula(c.formula)}  by ${showJust(c.just)}`
}

export function showProof(p: Proof): string {
  const head = `${p.name ?? '_'} : | ${showAssumption(p.assum)}\n`
  return head + p.ders.map((d) => showJudgment(d)).join('\n    | ')
}

export function showJudgment(j: Judgment): string {
  switch (j.k) {
    case 'sub': return showProof(j.proof)
    case 'claim': return showClaim(j.claim)
    case 'alias': return `${j.name} := ${showFormula(j.formula)}`
    case 'prove': return j.name !== null ? `${j.name} : prove ${showFormula(j.formula)}` : `prove ${showFormula(j.formula)}`
  }
}

export function showTheorem(t: DTheorem): string {
  // NOTE: upstream always prints the "schema" header, even for plain theorems.
  return `theorem schema ${t.name} for propositions${t.propVars.join(', ')} : `
    + `${t.assumptions.map(showFormula).join(', ')} ⊢ ${showFormula(t.conclusion)}`
    + `\n${t.proof.map(showJudgment).join('\n')}`
}

export function showAssertion(a: Assertion): string {
  switch (a.k) {
    case 'assumed': return `Assumed ${showFormula(a.f)}`
    case 'claimed': return `Claimed ${showFormula(a.f)}`
    case 'axiom': return `Axiom ${showFormula(a.f)}`
    case 'derived': return `Derived ${showAssumption(a.a)} ${showFormula(a.f)}`
  }
}

export type Assertion
  = { k: 'assumed', f: Formula }
  | { k: 'claimed', f: Formula }
  | { k: 'axiom', f: Formula }
  | { k: 'derived', a: Assumption, f: Formula }

// ---------------------------------------------------------------- lexer ---
// Hand-written scanner mirroring Parser/Lexer.x (maximal munch, rule order,
// column layout with Begin/End/Dash). Verified against the real lexer:
// - symbolic operators glue without spaces (A==>B is one Ident)
// - `ᶜ` (U+1D9C) always splits; every other non-ASCII char U+00A1..U+1F8B1 glues
//   (inclusive bound U+1F8B1 and the U+1D9C hole probed from the built lexer)
// - `_` always splits; `"` glues; `,`/`(`/`)`/`[`/`]`/`{`/`}` never glue
// - newline resets the column to 1; the module start column is 1, while
//   pasted proofs (parse'proof) start at column 0 — reproduced via startCol

export type Tok
  = { k: 'ident', v: string }
  | { k: 'constBefore' } | { k: 'module' } | { k: 'comma' } | { k: 'schema' }
  | { k: 'theorem' } | { k: 'judgment' } | { k: 'syntax' } | { k: 'constants' }
  | { k: 'axiom' } | { k: 'aliases' } | { k: 'colon' } | { k: 'turnstile' }
  | { k: 'by' } | { k: 'rule' } | { k: 'induction' } | { k: 'on' } | { k: 'all' }
  | { k: 'for' } | { k: 'some' } | { k: 'object' } | { k: 'proposition' }
  | { k: 'unproved' } | { k: 'case' } | { k: 'analysis' } | { k: 'prove' }
  | { k: 'use' } | { k: 'taut' } | { k: 'contra' } | { k: 'forall' } | { k: 'exists' }
  | { k: 'neg' } | { k: 'and' } | { k: 'or' } | { k: 'impl' } | { k: 'equiv' }
  | { k: 'arrow' } | { k: 'po' } | { k: 'pc' } | { k: 'bo' } | { k: 'bc' }
  | { k: 'co' } | { k: 'cc' } | { k: 'under' } | { k: 'equal' } | { k: 'defines' }
  | { k: 'dash' } | { k: 'begin' } | { k: 'end' } | { k: 'eof' }

export interface LexState {
  constants: string[]
  bound: string[][]
  rigids: string[][]
  pVars: string[]
  aliases: [string, Term][]
  counter: number
}

export function freshLexState(): LexState {
  return { constants: [], bound: [], rigids: [], pVars: [], aliases: [], counter: 0 }
}

export class DetourLexError extends Error {
  constructor(public line: number, public col: number, public detail: string) {
    super(`${line}:${col}\n${detail}`)
  }
}

const ASCII_IDENT_SYMS = '!"#$%&\'*+-./:;<=>?@\\^`|~'

function isIdentChar(cp: number): boolean {
  if (cp < 128) {
    if ((cp >= 48 && cp <= 57) || (cp >= 65 && cp <= 90) || (cp >= 97 && cp <= 122)) return true
    return ASCII_IDENT_SYMS.includes(String.fromCharCode(cp))
  }
  if (cp === 0x1d9c) return false
  return cp >= 0xa1 && cp <= 0x1fb31
}

// Fixed-string keywords. Longest match wins; an equally long Ident loses
// (keywords precede @ident, @line precedes both — handled by call order).
const KEYWORDS: [string, Tok][] = [
  ['<==>', { k: 'equiv' }], ['==>', { k: 'impl' }], [':=', { k: 'defines' }],
  ['<=>', { k: 'equiv' }], ['=>', { k: 'impl' }], ['->', { k: 'arrow' }],
  ['&&', { k: 'and' }],
  ['module', { k: 'module' }], ['schema', { k: 'schema' }],
  ['judgment', { k: 'judgment' }], ['syntax', { k: 'syntax' }],
  ['theorem', { k: 'theorem' }], ['constants', { k: 'constants' }],
  ['axiom', { k: 'axiom' }], ['aliases', { k: 'aliases' }],
  ['propositions', { k: 'proposition' }], ['proposition', { k: 'proposition' }],
  ['objects', { k: 'object' }], ['object', { k: 'object' }],
  ['induction', { k: 'induction' }], ['unproved', { k: 'unproved' }],
  ['analysis', { k: 'analysis' }], ['forall', { k: 'forall' }],
  ['exists', { k: 'exists' }], ['case', { k: 'case' }],
  ['prove', { k: 'prove' }], ['some', { k: 'some' }],
  ['rule', { k: 'rule' }], ['for', { k: 'for' }],
  ['all', { k: 'all' }], ['any', { k: 'all' }],
  ['use', { k: 'use' }], ['TRUE', { k: 'taut' }],
  ['True', { k: 'taut' }], ['Tautology', { k: 'taut' }],
  ['TAUTOLOGY', { k: 'taut' }], ['FALSE', { k: 'contra' }],
  ['CONTRADICTION', { k: 'contra' }], ['Contradiction', { k: 'contra' }],
  ['NOT', { k: 'neg' }], ['AND', { k: 'and' }], ['OR', { k: 'or' }],
  ['by', { k: 'by' }], ['on', { k: 'on' }],
  ['⊤', { k: 'taut' }], ['⊥', { k: 'contra' }],
  ['∀', { k: 'forall' }], ['∃', { k: 'exists' }],
  ['¬', { k: 'neg' }], ['∧', { k: 'and' }], ['∨', { k: 'or' }],
  ['⟹', { k: 'impl' }], ['⟺', { k: 'equiv' }],
  ['⊢', { k: 'turnstile' }], [':', { k: 'colon' }], ['=', { k: 'equal' }],
  ['&', { k: 'and' }],
  ['(', { k: 'po' }], [')', { k: 'pc' }],
  ['[', { k: 'bo' }], [']', { k: 'bc' }],
  ['{', { k: 'co' }], ['}', { k: 'cc' }],
  ['_', { k: 'under' }], ['ᶜ', { k: 'constBefore' }], [',', { k: 'comma' }],
]

export function lexDetour(src: string, startCol: number): PTok[] {
  const toks: PTok[] = []
  const layouts: number[] = []
  let i = 0
  let line = 1
  let col = startCol
  let code: 'zero' | 'behind' | 'eofcode' = 'zero'
  const n = src.length
  const emitAt = (t: Tok, l: number, c: number): void => {
    toks.push({ ...t, line: l, col: c })
  }

  const peekCp = (): number => src.codePointAt(i) ?? -1

  const endLayout = (lcol: number): Tok | null => {
    if (layouts.length === 0) { code = 'zero'; return null }
    const top = layouts[layouts.length - 1]!
    if (lcol <= top) { layouts.pop(); return { k: 'end' } }
    code = 'zero'
    return null
  }

  // pipe'line with the column of the `|`; returns a token or null (dropped)
  const pipeLine = (pcol: number): Tok | null => {
    if (layouts.length === 0) { layouts.push(pcol); return { k: 'begin' } }
    const top = layouts[layouts.length - 1]!
    if (pcol === top) { code = 'zero'; return null }
    if (pcol > top) { layouts.push(pcol); return { k: 'begin' } }
    return null
  }

  for (;;) {
    if (i >= n) {
      if (code !== 'eofcode') { code = 'eofcode'; continue }
      if (layouts.length > 0) { layouts.pop(); emitAt({ k: 'end' }, line, col); continue }
      emitAt({ k: 'eof' }, line, col)
      return toks
    }
    const cp = peekCp()
    let ch = String.fromCodePoint(cp)
    const chLen = ch.length
    let sl = line
    let sc = col

    if (code === 'zero') {
      if (ch === ' ' || ch === '\t' || ch === '\f' || ch === '\v') { i += chLen; col++; continue }
      if (ch === '\n') { i += 1; line++; col = 1; code = 'behind'; continue }
      if (ch === '-' && src[i + 1] === '-') {
        while (i < n && src[i] !== '\n') {
          const ccp = src.codePointAt(i)!
          i += ccp > 0xffff ? 2 : 1
          col += 1
        }
        continue
      }
      if (ch === '|') {
        let j = i + 1
        while (src[j] === '-') j++
        if (j > i + 1) {
          for (let k = i; k < j; k++) col++
          i = j
          code = 'zero'
          emitAt({ k: 'dash' }, sl, sc)
          continue
        }
        // A `|` followed by an ident char belongs to an ident run
        // (maximal munch beats the 1-char pipe rule); otherwise layout.
        const nc = i + 1 < n ? src.codePointAt(i + 1)! : -1
        if (nc < 0 || !isIdentChar(nc)) {
          i += 1
          const t = pipeLine(sc)
          col += 1
          if (t !== null) emitAt(t, sl, sc)
          continue
        }
        // else fall through to the ident/keyword logic below
      }
      // ident run vs keyword, longest wins (tie: keyword)
      let run = 0
      while (i + run < n) {
        const c2 = src.codePointAt(i + run)!
        if (!isIdentChar(c2)) break
        run += c2 > 0xffff ? 2 : 1
      }
      let best: Tok | null = null
      let bestLen = 0
      for (const [kw, tok] of KEYWORDS) {
        if (kw.length > bestLen && src.startsWith(kw, i)) { best = tok; bestLen = kw.length }
      }
      if (best !== null && bestLen >= run) {
        i += bestLen
        col += [...src.slice(i - bestLen, i)].length
        emitAt(best, sl, sc)
        continue
      }
      if (run > 0) {
        const word = src.slice(i, i + run)
        i += run
        col += [...word].length
        emitAt({ k: 'ident', v: word }, sl, sc)
        continue
      }
      throw new DetourLexError(line, col, `Lexical error: unexpected character ${JSON.stringify(ch)}.`)
    } else if (code === 'behind') {
      // In `behind`, runs of spaces/tabs (and `--` comments) are consumed
      // silently: the layout check happens at the first other character
      // (or at `\n`) with the post-space column. Verified against the
      // built lexer: `|`-dash lines, indented content, and comment lines
      // inside nested boxes all behave this way.
      while (ch === ' ' || ch === '\t' || ch === '\f' || ch === '\v') {
        col += ch === '\t' ? 8 - ((((col - 1) % 8) + 8) % 8) : 1
        i += ch.length
        if (i >= n) break
        ch = String.fromCodePoint(src.codePointAt(i)!)
      }
      if (i >= n) continue
      if (ch === '-' && src[i + 1] === '-') {
        while (i < n && src[i] !== '\n') {
          const ccp = src.codePointAt(i)!
          i += ccp > 0xffff ? 2 : 1
          col += 1
        }
        continue
      }
      // positions for layout decisions and error messages are the first
      // non-space character (post-space column)
      sl = line
      sc = col
      if (ch === '\n') {
        const lcol = col
        const t = endLayout(lcol)
        i += 1; line++; col = 1
        if (t !== null) emitAt(t, sl, sc)
        continue
      }
      if (ch === '|') {
        let j = i + 1
        while (src[j] === '-') j++
        if (j > i + 1) {
          for (let k = i; k < j; k++) col++
          i = j
          code = 'zero'
          emitAt({ k: 'dash' }, sl, sc)
          continue
        }
        // A `|` in `behind` always counts as layout (possibly dropped):
        // the ident rule does not exist in this start code.
        i += 1
        {
          const t = pipeLine(sc)
          col += 1
          if (t !== null) emitAt(t, sl, sc)
        }
        continue
      }
      const t = endLayout(sc)
      if (t !== null) { emitAt(t, sl, sc); continue }
      // code is now 'zero'; rescan without consuming
      code = 'zero'
      continue
    } else {
      // eofcode
      if (layouts.length > 0) { layouts.pop(); emitAt({ k: 'end' }, line, col); continue }
      emitAt({ k: 'eof' }, line, col)
      return toks
    }
  }
}

// -------------------------------------------------------------- parser ---
// Recursive-descent mirror of Parser/Parser.y (LALR conflict resolutions
// verified against the built binary):
// - after BEGIN_LAYOUT only a Subproof can follow (a leading `|` in pasted
//   proofs is a parse error at the `by`);
// - `[` after a proposition commits to second-order application (P[A] fails);
// - juxtaposed formulae never extend one another (no application without
//   parens), so greedy premise/conclusion parsing is exact;
// - at most `= First | Second` constructors (a third `|` line errors).

export type PTok = Tok & { line: number; col: number }

export class DetourParseError extends Error {
  constructor(public line: number, public col: number, public detail: string) {
    super(`${line}:${col}\n${detail}`)
  }
}

const isUpperLead = (s: string): boolean => /^\p{Lu}/u.test(s)

function strToRuleKind(s: string): RuleKind {
  switch (s) {
    case '==>-intro': return { k: 'builtin', name: 'ImplIntro' }
    case '==>-elim': return { k: 'builtin', name: 'ImplElim' }
    case '∧-intro': return { k: 'builtin', name: 'ConjIntro' }
    case '∧-elim': return { k: 'builtin', name: 'ConjElim' }
    case '∨-intro': return { k: 'builtin', name: 'DisjIntro' }
    case '∨-elim': return { k: 'builtin', name: 'DisjElim' }
    case '¬-elim': return { k: 'builtin', name: 'NegElim' }
    case '<==>-intro': return { k: 'builtin', name: 'EquivIntro' }
    case '<==>-elim': return { k: 'builtin', name: 'EquivElim' }
    case '⊤-intro': return { k: 'builtin', name: 'TrueIntro' }
    case 'proof-by-contradiction': return { k: 'builtin', name: 'ProofByContradiction' }
    case '⊥-elim': return { k: 'builtin', name: 'ContraElim' }
    case '∀-intro': return { k: 'builtin', name: 'ForallIntro' }
    case '∀-elim': return { k: 'builtin', name: 'ForallElim' }
    case '∃-intro': return { k: 'builtin', name: 'ExistsIntro' }
    case '∃-elim': return { k: 'builtin', name: 'ExistsElim' }
    case 'repetition': return { k: 'builtin', name: 'Repetition' }
    default: return { k: 'custom', name: s }
  }
}

class P {
  pos = 0
  constructor(public toks: PTok[], public st: LexState) {}

  peek(): PTok {
    return this.toks[this.pos] ?? { k: 'eof', line: -1, col: -1 }
  }
  peek2(): PTok {
    return this.toks[this.pos + 1] ?? { k: 'eof', line: -1, col: -1 }
  }
  peek3(): PTok {
    return this.toks[this.pos + 2] ?? { k: 'eof', line: -1, col: -1 }
  }
  next(): PTok {
    const t = this.peek()
    this.pos++
    return t
  }
  err(t: PTok, detail: string): never {
    throw new DetourParseError(t.line, t.col, detail)
  }
  errNear(t: PTok): never {
    const ch = t.k === 'ident' ? t.v.slice(0, 1) : t.k
    this.err(t, `Parse error near character \`${ch}'.`)
  }
  expect(k: Tok['k']): PTok {
    const t = this.next()
    if (t.k !== k) this.errNear(t)
    return t
  }
  ident(): string {
    const t = this.next()
    if (t.k !== 'ident') this.errNear(t)
    return t.v
  }
  propVar(): string {
    const t = this.peek()
    if (t.k !== 'ident') this.errNear(t)
    if (!isUpperLead(t.v)) {
      this.err(t, `Parsing Error: Illegal proposition \`${t.v}'\nPropositions should begin with an upper case character.`)
    }
    this.pos++
    return t.v
  }
  freshName(): string {
    return `_${this.st.counter++}?`
  }

  // ---- types ----
  parseType(): DType {
    const t = this.propVar()
    let ty: DType = { k: 'const', name: t }
    if (this.peek().k === 'arrow') {
      this.next()
      ty = { k: 'fn', a: ty, b: this.parseType() }
    }
    return ty
  }
  // TypeAnn: (name : T) | (n1, n2 : T) | bare name (fresh poly scheme)
  parseTypeAnn(): [string[], TypeScheme] {
    const t = this.peek()
    if (t.k === 'po') {
      this.next()
      const names = this.parseIdents()
      this.expect('colon')
      const ty = this.parseType()
      this.expect('pc')
      return [names, { vars: [], ty }]
    }
    const name = this.ident()
    const n = this.freshName()
    return [[name], { vars: [n], ty: { k: 'var', name: n } }]
  }
  // Idents: IDENT | _ IDENT (, ...)*
  parseIdents(): string[] {
    const out: string[] = []
    for (;;) {
      const t = this.peek()
      if (t.k === 'under') {
        this.next()
        out.push(`_${this.ident()}`)
      } else if (t.k === 'ident') {
        out.push(t.v)
        this.next()
      } else this.errNear(t)
      if (this.peek().k === 'comma') { this.next(); continue }
      return out
    }
  }
  parseTypeAnn1(): [string, TypeScheme] {
    const t = this.peek()
    if (t.k === 'po') {
      this.next()
      const name = this.ident()
      this.expect('colon')
      const pv = this.propVar()
      this.expect('pc')
      return [name, { vars: [], ty: { k: 'const', name: pv } }]
    }
    return [this.ident(), { vars: [], ty: { k: 'var', name: this.freshName() } }]
  }
  parseTypeAnn2(): [string, DType] {
    this.expect('po')
    const name = this.ident()
    this.expect('colon')
    const pv = this.propVar()
    this.expect('pc')
    return [name, { k: 'const', name: pv }]
  }

  // ---- terms ----
  resolveBare(name: string): Term {
    const st = this.st
    if (st.bound.some((f) => f.includes(name))) return { k: 'bound', name }
    if (st.rigids.some((f) => f.includes(name))) return { k: 'rigid', name }
    if (isUpperLead(name) || st.constants.includes(name)) return { k: 'app', c: name, args: [] }
    const hit = st.aliases.find(([n]) => n === name)
    if (hit) return hit[1]
    return { k: 'free', name }
  }
  parseTermArgs(): Term[] | null {
    const t = this.peek()
    if (t.k !== 'po' && t.k !== 'co') return null
    const open = this.next().k
    const close: Tok['k'] = open === 'po' ? 'pc' : 'cc'
    const args: Term[] = []
    if (this.peek().k !== close) {
      args.push(this.parseTerm())
      while (this.peek().k === 'comma') { this.next(); args.push(this.parseTerm()) }
    }
    this.expect(close)
    return args
  }
  parseTerm(): Term {
    const t = this.peek()
    if (t.k === 'po') {
      this.next()
      const e = this.parseTerm()
      this.expect('pc')
      return e
    }
    if (t.k === 'under') {
      this.next()
      const n2 = this.peek()
      if (n2.k !== 'ident') this.errNear(n2)
      const name = `_${n2.v}`
      this.next()
      if (this.peek().k === 'constBefore') {
        this.next()
        const args = this.parseTermArgs() ?? []
        return { k: 'app', c: name, args }
      }
      const args = this.parseTermArgs()
      if (args !== null) return { k: 'app', c: name, args }
      return this.resolveBare(name)
    }
    if (t.k === 'ident') {
      const name = t.v
      this.next()
      if (this.peek().k === 'constBefore') {
        this.next()
        const args = this.parseTermArgs() ?? []
        return { k: 'app', c: name, args }
      }
      const args = this.parseTermArgs()
      if (args !== null) return { k: 'app', c: name, args }
      return this.resolveBare(name)
    }
    this.errNear(t)
  }

  // ---- formulae ----
  startsFormula(t: PTok): boolean {
    return t.k === 'taut' || t.k === 'contra' || t.k === 'neg' || t.k === 'forall'
      || t.k === 'exists' || t.k === 'po' || t.k === 'co' || t.k === 'bo'
      || t.k === 'under' || t.k === 'ident'
  }
  parseFormula(): Formula {
    return this.parseEquiv()
  }
  parseEquiv(): Formula {
    const l = this.parseImpl()
    const t = this.peek()
    if (t.k === 'equiv') {
      this.next()
      return { k: 'eq', l, r: this.parseEquiv() }
    }
    return l
  }
  parseImpl(): Formula {
    const l = this.parseOr()
    const t = this.peek()
    if (t.k === 'impl') {
      this.next()
      return { k: 'impl', l, r: this.parseImpl() }
    }
    return l
  }
  parseOr(): Formula {
    let l = this.parseAnd()
    for (;;) {
      if (this.peek().k !== 'or') return l
      this.next()
      l = { k: 'or', l, r: this.parseAnd() }
    }
  }
  parseAnd(): Formula {
    let l = this.parseUnary()
    for (;;) {
      if (this.peek().k !== 'and') return l
      this.next()
      l = { k: 'and', l, r: this.parseUnary() }
    }
  }
  parseUnary(): Formula {
    const t = this.peek()
    if (t.k === 'neg') {
      this.next()
      return { k: 'not', f: this.parseUnary() }
    }
    if (t.k === 'forall' || t.k === 'exists') {
      const isForall = t.k === 'forall'
      this.next()
      this.st.bound.push([])
      const binders = this.parseBinders()
      this.expect('colon')
      const body = this.parseFormula()
      this.st.bound.pop()
      let acc = body
      for (let k = binders.length - 1; k >= 0; k--) {
        const [n, ts] = binders[k]!
        acc = isForall
          ? { k: 'forall', name: n, ts, body: acc }
          : { k: 'exists', name: n, ts, body: acc }
      }
      return acc
    }
    return this.parseAtom()
  }
  parseBinders(): [string, TypeScheme][] {
    const out: [string, TypeScheme][] = []
    for (;;) {
      const t = this.peek()
      if (t.k !== 'po' && t.k !== 'ident') return out
      if (t.k === 'po') {
        // must be a TypeAnn; a bracketed formula cannot start with `(` IDENT...?
        // disambiguate: TypeAnn `(x : T)` vs formula `(F)` — try TypeAnn shape.
        const save = this.pos
        try {
          const [names, ts] = this.parseTypeAnn()
          for (const n of names) {
            this.st.bound[this.st.bound.length - 1]!.push(n)
            out.push([n, ts])
          }
          continue
        } catch {
          this.pos = save
          return out
        }
      }
      const [names, ts] = this.parseTypeAnn()
      for (const n of names) {
        this.st.bound[this.st.bound.length - 1]!.push(n)
        out.push([n, ts])
      }
    }
  }
  parseAtom(): Formula {
    const t = this.peek()
    if (t.k === 'taut') { this.next(); return { k: 'true' } }
    if (t.k === 'contra') { this.next(); return { k: 'false' } }
    if (t.k === 'po' || t.k === 'co' || t.k === 'bo') {
      const open = this.next().k
      const close: Tok['k'] = open === 'po' ? 'pc' : open === 'co' ? 'cc' : 'bc'
      const f = this.parseFormula()
      this.expect(close)
      return f
    }
    return { k: 'atom', rel: this.parseRelation() }
  }
  parseRelation(): Relation {
    const t = this.peek()
    if (t.k === 'under') {
      this.next()
      return { k: 'meta', prop: this.freshName() }
    }
    const name = this.propVar()
    if (this.peek().k === 'bo') {
      this.next()
      const first = this.parseFormula()
      const rest: Formula[] = [first]
      if (this.peek().k !== 'comma') this.errNear(this.peek())
      while (this.peek().k === 'comma') { this.next(); rest.push(this.parseFormula()) }
      this.expect('bc')
      return { k: 'rel', name, args: { k: 'formulae', args: rest } }
    }
    const args = this.parseTermArgs()
    if (args !== null) return { k: 'rel', name, args: { k: 'terms', args } }
    if (this.st.pVars.includes(name)) return { k: 'meta', prop: name }
    return { k: 'rel', name, args: { k: 'terms', args: [] } }
  }

  // ---- proofs ----
  parseAssumption(): Assumption {
    const t = this.peek()
    if (t.k === 'all' || (t.k === 'for')) {
      if (t.k === 'for') {
        if (this.peek2().k !== 'all') this.errNear(this.peek2())
        this.next(); this.next()
      } else this.next()
      const rigids = this.parseRigids()
      const names = rigids.map(([r]) => r)
      this.st.rigids.push(names)
      return { k: 'universal', binds: rigids }
    }
    // one AssumedFormula, maybe existential
    const first = this.parseAssumedFormula()
    if (first !== null && this.peek().k === 'for') {
      this.next()
      this.expect('some')
      const rigids = this.parseRigids()
      const strs = rigids.map(([r]) => r)
      // the formula was parsed before the rigids were known: frees with the
      // same names become rigids (Substitute: Free ==> Rigid)
      const sub: Subst = strs.map((s) => ({ k: 'free', name: s, term: { k: 'rigid', name: s } as Term }))
      const [nm, fm] = first
      this.st.rigids.push(strs)
      return { k: 'existential', binding: [nm, appFormula(sub, fm)], binds: rigids }
    }
    const pairs: [string | null, Formula][] = first === null ? [] : [first]
    while (this.startsAssumedFormula()) pairs.push(this.parseAssumedFormula()!)
    if (first !== null || pairs.length > 0) {
      this.st.rigids.push([])
      return { k: 'formula', pairs }
    }
    this.st.rigids.push([])
    return { k: 'formula', pairs: [] }
  }
  startsAssumedFormula(): boolean {
    const t = this.peek()
    if ((t.k === 'ident' || t.k === 'under') && this.peek2().k === 'colon') return true
    return this.startsFormula(t) && t.k !== 'for' && t.k !== 'all'
  }
  parseAssumedFormula(): [string | null, Formula] | null {
    const t = this.peek()
    if ((t.k === 'ident' || t.k === 'under') && this.peek2().k === 'colon') {
      const nm = t.k === 'under' ? null : (t as { v: string }).v
      this.next(); this.next()
      return [nm, this.parseFormula()]
    }
    if (!this.startsFormula(t) || t.k === 'for' || t.k === 'all') return null
    return [null, this.parseFormula()]
  }
  parseRigids(): [string, TypeScheme][] {
    const out: [string, TypeScheme][] = [this.parseTypeAnn1()]
    while (this.peek().k === 'comma') { this.next(); out.push(this.parseTypeAnn1()) }
    return out
  }
  parseSubProofAux(): Proof {
    this.expect('begin')
    const assum = this.parseAssumption()
    this.expect('dash')
    const ders = this.parseProof(['end'])
    this.expect('end')
    const rs = this.st.rigids
    if (rs.length === 0) this.err(this.peek(), 'internal error: rigid scope underflow')
    rs.pop()
    return { name: null, assum, ders }
  }
  parseProof(stop: Tok['k'][]): Judgment[] {
    const out: Judgment[] = []
    for (;;) {
      const t = this.peek()
      if (stop.includes(t.k) || t.k === 'eof') return out
      if (t.k === 'begin') {
        const p = this.parseSubProofAux()
        out.push({ k: 'sub', proof: p })
        continue
      }
      if (t.k === 'prove') {
        this.next()
        out.push({ k: 'prove', name: null, formula: this.parseFormula() })
        continue
      }
      if (t.k === 'ident' || t.k === 'under') {
        if (this.peek2().k === 'colon') {
          const nm = t.k === 'under' ? null : (t as { v: string }).v
          const l3 = this.peek3()
          this.next(); this.next()
          if (l3.k === 'begin') {
            const p = this.parseSubProofAux()
            p.name = nm
            out.push({ k: 'sub', proof: p })
            continue
          }
          if (l3.k === 'prove') {
            this.next()
            out.push({ k: 'prove', name: nm, formula: this.parseFormula() })
            continue
          }
          out.push({ k: 'claim', claim: { name: nm, formula: this.parseFormula(), just: this.parseJust() } })
          continue
        }
        if (t.k === 'under') {
          const n2 = this.peek2()
          const n3 = this.peek3()
          if (n2.k === 'ident' && n3.k === 'defines') {
            this.next()
            const pv = this.propVar()
            this.expect('defines')
            out.push({ k: 'alias', name: `_${pv}`, formula: this.parseFormula() })
            continue
          }
        }
        out.push({ k: 'claim', claim: { name: null, formula: this.parseFormula(), just: this.parseJust() } })
        continue
      }
      if (this.startsFormula(t)) {
        out.push({ k: 'claim', claim: { name: null, formula: this.parseFormula(), just: this.parseJust() } })
        continue
      }
      this.errNear(t)
    }
  }
  parseJust(): Justification {
    this.expect('by')
    const t = this.peek()
    if (t.k === 'rule') {
      this.next()
      const kind = strToRuleKind(this.ident())
      return { k: 'rule', kind, on: this.parseOnIdents() }
    }
    if (t.k === 'induction') {
      this.next()
      this.expect('colon')
      return { k: 'induction', proofs: this.parseCases() }
    }
    if (t.k === 'unproved') {
      this.next()
      return { k: 'unproved' }
    }
    if (t.k === 'axiom') {
      this.next()
      return { k: 'rule', kind: { k: 'builtin', name: 'Repetition' }, on: [this.ident()] }
    }
    if (t.k === 'theorem') {
      this.next()
      const name = this.ident()
      return { k: 'theorem', name, on: this.parseOnIdents() }
    }
    if (t.k === 'case') {
      this.next()
      this.expect('analysis')
      this.expect('on')
      const on = this.parseTerm()
      this.expect('colon')
      return { k: 'cases', on, proofs: this.parseCases() }
    }
    this.errNear(t)
  }
  parseOnIdents(): string[] {
    if (this.peek().k !== 'on') return []
    this.next()
    const out: string[] = []
    for (;;) {
      const t = this.peek()
      if (t.k === 'under') {
        this.next()
        out.push(`_${this.ident()}`)
      } else if (t.k === 'ident') {
        out.push(t.v)
        this.next()
      } else break
      if (this.peek().k === 'comma') { this.next(); continue }
      break
    }
    return out
  }
  parseCases(): CaseProof[] {
    const out: CaseProof[] = []
    while (this.peek().k === 'case') out.push(this.parseCase())
    return out
  }
  parseCase(): CaseProof {
    this.expect('case')
    const [con, rigids] = this.parsePattern()
    this.expect('arrow')
    const strs = rigids
    this.st.rigids.push(strs)
    const proof = this.parseSubProofAux()
    {
      const rs = this.st.rigids
      if (rs.length === 0) this.err(this.peek(), 'internal error: rigid scope underflow')
      rs.pop()
    }
    return { con, rigids: strs, proof }
  }
  parsePattern(): [string, string[]] {
    const t = this.peek()
    if (t.k === 'po') {
      this.next()
      const r = this.parsePattern()
      this.expect('pc')
      return r
    }
    const name = this.ident()
    if (this.peek().k === 'constBefore') this.next()
    let rigids: string[] = []
    if (this.peek().k === 'po') {
      this.next()
      if (this.peek().k !== 'pc') {
        rigids.push(this.ident())
        while (this.peek().k === 'comma') { this.next(); rigids.push(this.ident()) }
      }
      this.expect('pc')
    }
    return [name, rigids]
  }

  // ---- module ----
  parseCtor(): Ctor {
    const name = this.ident()
    const args: DType[] = []
    const t = this.peek()
    if (t.k === 'po' || t.k === 'bo') {
      const open = this.next().k
      const close: Tok['k'] = open === 'po' ? 'pc' : 'bc'
      args.push(this.parseType())
      while (this.peek().k === 'comma') { this.next(); args.push(this.parseType()) }
      this.expect(close)
    }
    if (!this.st.constants.includes(name)) this.st.constants.push(name)
    return { name, args }
  }
  parseRule(): JudRule {
    this.expect('rule')
    let name: string
    let propVars: string[] = []
    let params: [string, DType][] = []
    if (this.peek().k === 'schema') {
      this.next()
      name = this.ident()
      let saw = false
      while (this.peek().k === 'for') {
        this.next()
        this.expect('all')
        const t = this.peek()
        if (t.k === 'proposition') {
          this.next()
          const ps = this.parseProps()
          propVars = propVars.concat(ps)
          saw = true
        } else if (t.k === 'object') {
          this.next()
          const first = this.parseTypeAnn2()
          params.push(first)
          while (this.peek().k === 'comma') { this.next(); params.push(this.parseTypeAnn2()) }
          saw = true
        } else this.errNear(t)
      }
      if (!saw) this.err(this.peek(), 'Parsing Error: rule schema needs at least one for-clause.')
    } else {
      name = this.ident()
    }
    this.expect('colon')
    this.expect('begin')
    const premises: Formula[] = []
    while (this.startsFormula(this.peek())) premises.push(this.parseFormula())
    this.expect('dash')
    const dashName = this.ident()
    if (dashName !== name) {
      this.err(this.peek(), `A rule should have the same name as in declaration.\nThe rule \`${name}' has also been given a name \`${dashName}'.\nPick just one!`)
    }
    const conclusion = this.parseFormula()
    this.expect('end')
    return { name, propVars, params, premises, conclusion }
  }
  parseProps(): string[] {
    const out: string[] = [this.propVar()]
    while (this.peek().k === 'comma') { this.next(); out.push(this.propVar()) }
    this.st.pVars = out
    return out
  }
  parseJudgmentDecl(): Jud {
    this.expect('judgment')
    if (this.peek().k === 'schema') {
      this.next()
      const name = this.ident()
      let pv: string[] = []
      if (this.peek().k === 'for') {
        this.next(); this.expect('all'); this.expect('proposition')
        pv = this.parseProps()
      }
      this.expect('equal')
      const con = this.parseCtor()
      const rules: JudRule[] = []
      while (this.peek().k === 'rule') rules.push(this.parseRule())
      return { name, propVars: pv, con: [con.name, con.args], rules }
    }
    const name = this.ident()
    this.expect('equal')
    const con = this.parseCtor()
    const rules: JudRule[] = []
    while (this.peek().k === 'rule') rules.push(this.parseRule())
    return { name, propVars: [], con: [con.name, con.args], rules }
  }
  parseTheorem(): DTheorem {
    this.expect('theorem')
    let name: string
    let propVars: string[] = []
    if (this.peek().k === 'schema') {
      this.next()
      name = this.ident()
      this.expect('for'); this.expect('all'); this.expect('proposition')
      propVars = this.parseProps()
    } else {
      name = this.ident()
    }
    this.expect('colon')
    const first = this.parseFormula()
    let assumptions: Formula[] = []
    let conclusion: Formula
    if (this.peek().k === 'comma') {
      assumptions.push(first)
      while (this.peek().k === 'comma') { this.next(); assumptions.push(this.parseFormula()) }
      this.expect('turnstile')
      conclusion = this.parseFormula()
    } else if (this.peek().k === 'turnstile') {
      assumptions.push(first)
      this.next()
      conclusion = this.parseFormula()
    } else {
      conclusion = first
    }
    const proof = this.parseProof(['theorem'])
    this.st.pVars = []
    return { name, propVars, assumptions, conclusion, proof }
  }
  parseModule(): DModule {
    this.expect('module')
    const name = this.ident()
    let constants: [string, TypeScheme][] = []
    if (this.peek().k === 'constants') {
      this.next()
      this.expect('colon')
      const [ns, ts] = this.parseTypeAnn()
      constants = ns.map((n): [string, TypeScheme] => [n, ts])
      while (this.peek().k === 'comma') {
        this.next()
        const [ms, mts] = this.parseTypeAnn()
        for (const m of ms) constants.push([m, mts])
      }
      for (const [n] of constants) {
        if (!this.st.constants.includes(n)) this.st.constants.push(n)
      }
    }
    const aliases: [string, Term][] = []
    if (this.peek().k === 'aliases') {
      this.next()
      this.expect('colon')
      for (;;) {
        const nm = this.next()
        if (nm.k !== 'ident') this.errNear(nm)
        const aname = nm.v
        if (this.st.constants.includes(aname)) {
          this.err(nm, `Parsing Error: Illegal alias \`${aname}'.\nAliases can not redefine existing constants.`)
        }
        if (aliases.some(([n]) => n === aname)) {
          this.err(nm, `Parsing Error: Illegal alias \`${aname}'.\nAliases can not redefine existing aliases.`)
        }
        this.expect('equal')
        const tm = this.parseTerm()
        aliases.push([aname, tm])
        this.st.aliases.push([aname, tm])
        if (this.peek().k === 'comma') { this.next(); continue }
        break
      }
    }
    const axioms: [string, Formula][] = []
    while (this.peek().k === 'axiom') {
      this.next()
      const nm = this.ident()
      this.expect('colon')
      axioms.push([nm, this.parseFormula()])
    }
    const syntax: [string, Ctor[]][] = []
    while (this.peek().k === 'syntax') {
      this.next()
      const tn = this.propVar()
      let ctors: Ctor[] = []
      if (this.peek().k === 'equal') {
        this.next()
        ctors.push(this.parseCtor())
        while (this.peek().k === 'begin') {
          this.next()
          ctors.push(this.parseCtor())
          this.expect('end')
        }
      }
      syntax.push([tn, ctors])
    }
    const judgments: Jud[] = []
    while (this.peek().k === 'judgment') judgments.push(this.parseJudgmentDecl())
    const theorems: DTheorem[] = []
    while (this.peek().k === 'theorem') theorems.push(this.parseTheorem())
    this.expect('eof')
    return { name, constants, aliases, axioms, syntax, judgments, theorems }
  }
}

export function parseDetourModule(src: string): DModule {
  return new P(lexDetour(src, 1), freshLexState()).parseModule()
}

export function parseDetourProof(src: string, rigids: string[]): Judgment[] {
  const st = freshLexState()
  st.rigids = [rigids]
  return new P(lexDetour(src, 0), st).parseProof(['eof'])
}

// -------------------------------------------------------------- checker ---
// Port of Check.{Check,Module,Theorem,Proof,Rule,Solver,Unify,Substitute,
// Substitution,Substitution,Types,Vars,Assertion,Constraint,State,
// Environment,Error}. Async (the driver pauses at What'Next); errors are
// DetourError (port of `Err String`, `because` stacks with "\nand ").
// Deviations: fuel caps (documented in the engine); traceM stderr spam dropped.

export type Binding
  = { k: 'free'; name: string; term: Term }
  | { k: 'rigid'; name: string; term: Term }
  | { k: 'bound'; name: string; term: Term }
  | { k: 'prop'; name: string; formula: Formula }
  | { k: 'type'; name: string; ty: DType }

export type Subst = Binding[]

export class DetourError extends Error {
  constructor(public msg: string) {
    super(msg)
  }
}

class AbortError extends Error {
  constructor() { super('aborted') }
}

function lookFree(sub: Subst, name: string): Term | undefined {
  const b = sub.find((x): x is Extract<Binding, { k: 'free' }> => x.k === 'free' && x.name === name)
  return b?.term
}
function lookBound(sub: Subst, name: string): Term | undefined {
  const b = sub.find((x): x is Extract<Binding, { k: 'bound' }> => x.k === 'bound' && x.name === name)
  return b?.term
}
function lookRigid(sub: Subst, name: string): Term | undefined {
  const b = sub.find((x): x is Extract<Binding, { k: 'rigid' }> => x.k === 'rigid' && x.name === name)
  return b?.term
}
function lookProp(sub: Subst, name: string): Formula | undefined {
  const b = sub.find((x): x is Extract<Binding, { k: 'prop' }> => x.k === 'prop' && x.name === name)
  return b?.formula
}
function lookType(sub: Subst, name: string): DType | undefined {
  const b = sub.find((x): x is Extract<Binding, { k: 'type' }> => x.k === 'type' && x.name === name)
  return b?.ty
}

// NOTE: upstream `remove` for Free drops every non-Free binding (preserved).
function rmFree(sub: Subst, name: string): Subst {
  return sub.filter((b) => b.k === 'free' && b.name !== name)
}
function rmBound(sub: Subst, name: string): Subst {
  return sub.filter((b) => b.k !== 'bound' || b.name !== name)
}
function rmRigid(sub: Subst, name: string): Subst {
  return sub.filter((b) => b.k !== 'rigid' || b.name !== name)
}
function rmProp(sub: Subst, name: string): Subst {
  return sub.filter((b) => b.k !== 'prop' || b.name !== name)
}
function rmType(sub: Subst, name: string): Subst {
  return sub.filter((b) => b.k !== 'type' || b.name !== name)
}

export function appTerm(sub: Subst, t: Term): Term {
  switch (t.k) {
    case 'bound': return lookBound(sub, t.name) ?? t
    case 'app': return { k: 'app', c: t.c, args: t.args.map((a) => appTerm(sub, a)) }
    case 'free': return lookFree(sub, t.name) ?? t
    case 'rigid': return lookRigid(sub, t.name) ?? t
  }
}
export function appType(sub: Subst, t: DType): DType {
  switch (t.k) {
    case 'var': return lookType(sub, t.name) ?? t
    case 'const': return t
    case 'fn': return { k: 'fn', a: appType(sub, t.a), b: appType(sub, t.b) }
  }
}
export function appScheme(sub: Subst, s: TypeScheme): TypeScheme {
  let r = sub
  for (const v of s.vars) r = rmType(r, v)
  return { vars: s.vars, ty: appType(r, s.ty) }
}
function appRelArgs(sub: Subst, a: RelArgs): RelArgs {
  return a.k === 'terms'
    ? { k: 'terms', args: a.args.map((x) => appTerm(sub, x)) }
    : { k: 'formulae', args: a.args.map((x) => appFormula(sub, x)) }
}
export function appFormula(sub: Subst, f: Formula): Formula {
  switch (f.k) {
    case 'true': case 'false': return f
    case 'atom':
      if (f.rel.k === 'meta') return lookProp(sub, f.rel.prop) ?? f
      return { k: 'atom', rel: { k: 'rel', name: f.rel.name, args: appRelArgs(sub, f.rel.args) } }
    case 'not': return { k: 'not', f: appFormula(sub, f.f) }
    case 'and': return { k: 'and', l: appFormula(sub, f.l), r: appFormula(sub, f.r) }
    case 'or': return { k: 'or', l: appFormula(sub, f.l), r: appFormula(sub, f.r) }
    case 'impl': return { k: 'impl', l: appFormula(sub, f.l), r: appFormula(sub, f.r) }
    case 'eq': return { k: 'eq', l: appFormula(sub, f.l), r: appFormula(sub, f.r) }
    case 'forall': return { k: 'forall', name: f.name, ts: f.ts, body: appFormula(rmBound(sub, f.name), f.body) }
    case 'exists': return { k: 'exists', name: f.name, ts: f.ts, body: appFormula(rmBound(sub, f.name), f.body) }
  }
}
function appBinding(sub: Subst, b: Binding): Binding {
  switch (b.k) {
    case 'free': return { k: 'free', name: b.name, term: appTerm(sub, b.term) }
    case 'rigid': return { k: 'rigid', name: b.name, term: appTerm(sub, b.term) }
    case 'bound': return { k: 'bound', name: b.name, term: appTerm(sub, b.term) }
    case 'prop': return { k: 'prop', name: b.name, formula: appFormula(sub, b.formula) }
    case 'type': return { k: 'type', name: b.name, ty: appType(sub, b.ty) }
  }
}
export function composeSubst(l: Subst, r: Subst): Subst {
  return r.map((b) => appBinding(l, b)).concat(l)
}
function appAssumption(sub: Subst, a: Assumption): Assumption {
  switch (a.k) {
    case 'formula': return { k: 'formula', pairs: a.pairs.map(([n, f]): [string | null, Formula] => [n, appFormula(sub, f)]) }
    case 'universal': return a
    case 'existential': return { k: 'existential', binding: [a.binding[0], appFormula(sub, a.binding[1])], binds: a.binds }
  }
}
function appJust(sub: Subst, j: Justification): Justification {
  switch (j.k) {
    case 'rule': case 'theorem': case 'unproved': case 'induction': return j
    case 'subst': return { k: 'subst', on: appTerm(sub, j.on), using: j.using }
    case 'cases': return { k: 'cases', on: j.on, proofs: j.proofs.map((c) => appCase(sub, c)) }
  }
}
function appClaim(sub: Subst, c: Claim): Claim {
  return { name: c.name, formula: appFormula(sub, c.formula), just: appJust(sub, c.just) }
}
function appCase(sub: Subst, c: CaseProof): CaseProof {
  return { con: c.con, rigids: c.rigids, proof: appProof(sub, c.proof) }
}
function appProof(sub: Subst, p: Proof): Proof {
  return { name: p.name, assum: appAssumption(sub, p.assum), ders: p.ders.map((d) => appJudgment(sub, d)) }
}
function appJudgment(sub: Subst, j: Judgment): Judgment {
  switch (j.k) {
    case 'sub': return { k: 'sub', proof: appProof(sub, j.proof) }
    case 'claim': return { k: 'claim', claim: appClaim(sub, j.claim) }
    case 'alias': return { k: 'alias', name: j.name, formula: appFormula(sub, j.formula) }
    case 'prove': return { k: 'prove', name: j.name, formula: appFormula(sub, j.formula) }
  }
}
function appAssert(sub: Subst, a: Assertion): Assertion {
  switch (a.k) {
    case 'assumed': return { k: 'assumed', f: appFormula(sub, a.f) }
    case 'claimed': return { k: 'claimed', f: appFormula(sub, a.f) }
    case 'axiom': return { k: 'axiom', f: appFormula(sub, a.f) }
    case 'derived': return { k: 'derived', a: appAssumption(sub, a.a), f: appFormula(sub, a.f) }
  }
}

function appSchemeMap(sub: Subst, m: Map<string, TypeScheme>): Map<string, TypeScheme> {
  return new Map([...m.entries()].map(([k, v]): [string, TypeScheme] => [k, appScheme(sub, v)]))
}

function typeEq(a: DType, b: DType): boolean {
  if (a.k !== b.k) return false
  if (a.k === 'const' && b.k === 'const') return a.name === b.name
  if (a.k === 'var' && b.k === 'var') return a.name === b.name
  if (a.k === 'fn' && b.k === 'fn') return typeEq(a.a, b.a) && typeEq(a.b, b.b)
  return false
}

// __PART4B_VARS__
// Free (flexible) variable collection — port of Check.Vars. Bound and Rigid
// variables contribute nothing; Sub'Proof and Alias judgments contribute nothing.

function fvTermInto(t: Term, out: Set<string>): void {
  if (t.k === 'free') out.add(t.name)
  else if (t.k === 'app') for (const a of t.args) fvTermInto(a, out)
}
function fvRelArgsInto(a: RelArgs, out: Set<string>): void {
  for (const x of a.args) {
    if (a.k === 'terms') fvTermInto(x as Term, out)
    else fvFormulaInto(x as Formula, out)
  }
}
function fvFormulaInto(f: Formula, out: Set<string>): void {
  switch (f.k) {
    case 'true': case 'false': break
    case 'atom':
      if (f.rel.k === 'rel') fvRelArgsInto(f.rel.args, out)
      break
    case 'not': fvFormulaInto(f.f, out); break
    case 'and': case 'or': case 'impl': case 'eq':
      fvFormulaInto(f.l, out); fvFormulaInto(f.r, out); break
    case 'forall': case 'exists': fvFormulaInto(f.body, out); break
  }
}
function fvJustInto(j: Justification, out: Set<string>): void {
  if (j.k === 'subst') fvTermInto(j.on, out)
  else if (j.k === 'cases') for (const c of j.proofs) fvProofInto(c.proof, out)
}
function fvClaimInto(c: Claim, out: Set<string>): void {
  fvFormulaInto(c.formula, out)
  fvJustInto(c.just, out)
}
function fvProofInto(p: Proof, out: Set<string>): void {
  fvAssumptionInto(p.assum, out)
  for (const d of p.ders) fvJudgmentInto(d, out)
}
function fvAssumptionInto(a: Assumption, out: Set<string>): void {
  if (a.k === 'formula') for (const [, f] of a.pairs) fvFormulaInto(f, out)
  else if (a.k === 'existential') fvFormulaInto(a.binding[1], out)
}
function fvJudgmentInto(j: Judgment, out: Set<string>): void {
  if (j.k === 'claim') fvClaimInto(j.claim, out)
  else if (j.k === 'alias') fvFormulaInto(j.formula, out)
  else if (j.k === 'prove') fvFormulaInto(j.formula, out)
}
function fvCaseInto(c: CaseProof, out: Set<string>): void {
  fvProofInto(c.proof, out)
}
function freeVarsFormula(f: Formula): Set<string> {
  const out = new Set<string>()
  fvFormulaInto(f, out)
  return out
}
function freeVarsJudgment(j: Judgment): Set<string> {
  const out = new Set<string>()
  fvJudgmentInto(j, out)
  return out
}
function freeVarsBinding(b: [string | null, Formula]): Set<string> {
  const out = new Set<string>()
  fvFormulaInto(b[1], out)
  return out
}

// __PART4C_MONAD__
// The Check monad: environment + state threaded through async methods.
// State is mutated in place (upstream never rolls it back, not even across
// catchError); only the environment is snapshotted by `local`.

export interface DetourCtx {
  theorem: string
  locals: Array<[string, Assertion]>
  theorems: Array<[string, DTheorem]>
  proofCtx: string[]
}
export type DetourCmd = { k: 'idk' } | { k: 'assert'; src: string }
export interface DetourDriver {
  inform(ctx: DetourCtx, msg: string): void
  askNext(ctx: DetourCtx, goal: Formula): Promise<DetourCmd>
}

interface Env {
  lem: boolean
  theorems: Map<string, DTheorem>
  depth: number
  assertScope: Map<string, Assertion>
  currentTheorem: string | null
  rigidVars: string[]
  proofContext: string[]
  contextPrefix: string
}
interface St {
  counter: number
  termC: Array<[Term, Term]>
  formulaC: Array<[Formula, Formula]>
  typeC: Array<[DType, DType]>
  freeDepth: Map<string, number>
  rigidDepth: Map<string, number>
  typingCtx: Map<string, TypeScheme>
  judgments: Jud[]
  syntax: Array<[string, Ctor[]]>
}

function cmpStr(a: string, b: string): number {
  const aa = Array.from(a)
  const bb = Array.from(b)
  const n = Math.min(aa.length, bb.length)
  for (let k = 0; k < n; k++) {
    const x = aa[k]!.codePointAt(0)!
    const y = bb[k]!.codePointAt(0)!
    if (x !== y) return x - y
  }
  return aa.length - bb.length
}
function sortedEntries<T>(m: Map<string, T>): Array<[string, T]> {
  return [...m.entries()].sort(([a], [b]) => cmpStr(a, b))
}

export const STEP_BUDGET = 200000
export const INTERACT_BUDGET = 200

export class Checker {
  env: Env
  st: St
  steps = 0
  prompts = 0
  aborted = false
  constructor(public driver: DetourDriver, lem: boolean) {
    this.env = {
      lem, theorems: new Map(), depth: 0, assertScope: new Map(),
      currentTheorem: null, rigidVars: [], proofContext: [], contextPrefix: '',
    }
    this.st = {
      counter: 0, termC: [], formulaC: [], typeC: [],
      freeDepth: new Map(), rigidDepth: new Map(), typingCtx: new Map(),
      judgments: [], syntax: [],
    }
  }

  async step(): Promise<void> {
    this.steps++
    if ((this.steps & 511) === 0) {
      await yieldToUI()
      if (this.aborted) throw new AbortError()
      if (this.steps > STEP_BUDGET) {
        throw new DetourError(
          'Solver budget exceeded (this demo caps runaway searches at 200000 steps). ' +
          'Try guiding the search with pasted proof steps.')
      }
    }
  }

  // -- names --
  freshName(): string {
    return `_${this.st.counter++}`
  }
  async freshFree(): Promise<string> {
    const n = this.freshName()
    this.st.freeDepth = new Map(this.st.freeDepth)
    this.st.freeDepth.set(n, this.env.depth)
    return n
  }
  freshConstant(): string {
    return this.freshName()
  }
  freshType(): DType {
    return { k: 'var', name: this.freshName() }
  }
  freshTypeConst(): DType {
    return { k: 'const', name: this.freshName() }
  }
  freshBound(): string {
    return this.freshName()
  }
  freshProp(): Formula {
    return { k: 'atom', rel: { k: 'meta', prop: this.freshName() } }
  }
  freeLevel(f: string): number {
    const l = this.st.freeDepth.get(f)
    if (l === undefined) throw new DetourError(`Internal Error. The free variable \`${f}·' is not recorded in the context.`)
    return l
  }
  rigidLevel(r: string): number {
    const l = this.st.rigidDepth.get(r)
    if (l === undefined) throw new DetourError(`Internal Error. The rigid variable \`${r}' is not recorded in the context.`)
    return l
  }

  // -- errors / scoping --
  // NOTE: tryError/catchError restore the pre-action state on failure
  // (InteractT tryError discards the action's state on Left). Every
  // speculative attempt therefore starts clean.
  snapshotState(): St {
    return {
      counter: this.st.counter,
      termC: this.st.termC.slice(),
      formulaC: this.st.formulaC.slice(),
      typeC: this.st.typeC.slice(),
      freeDepth: new Map(this.st.freeDepth),
      rigidDepth: new Map(this.st.rigidDepth),
      typingCtx: new Map(this.st.typingCtx),
      judgments: this.st.judgments,
      syntax: this.st.syntax,
    }
  }
  restoreState(s: St): void {
    this.st.counter = s.counter
    this.st.termC = s.termC
    this.st.formulaC = s.formulaC
    this.st.typeC = s.typeC
    this.st.freeDepth = s.freeDepth
    this.st.rigidDepth = s.rigidDepth
    this.st.typingCtx = s.typingCtx
  }
  async because<T>(msg: string, fn: () => Promise<T>): Promise<T> {
    try {
      return await fn()
    } catch (e) {
      if (e instanceof DetourError) throw new DetourError(`${msg}\nand ${e.msg}`)
      throw e
    }
  }
  async tryError<T>(fn: () => Promise<T>): Promise<{ k: 'left'; err: DetourError } | { k: 'right'; v: T }> {
    const save = this.snapshotState()
    try {
      return { k: 'right', v: await fn() }
    } catch (e) {
      if (e instanceof DetourError) {
        this.restoreState(save)
        return { k: 'left', err: e }
      }
      throw e
    }
  }
  async local<T>(mod: (e: Env) => Env, fn: () => Promise<T>): Promise<T> {
    const save = this.env
    this.env = mod({ ...this.env })
    try {
      return await fn()
    } finally {
      this.env = save
    }
  }

  // -- driver --
  getContext(): DetourCtx {
    const th = this.env.currentTheorem
    if (th === null) throw new DetourError('internal error: theorem name is not present even though I am checking some theorem')
    return {
      theorem: th,
      locals: sortedEntries(this.env.assertScope),
      theorems: sortedEntries(this.env.theorems),
      proofCtx: this.env.proofContext,
    }
  }
  informAbout(msg: string): void {
    this.driver.inform(this.getContext(), msg)
  }
  async askForNext(fm: Formula): Promise<DetourCmd> {
    this.prompts++
    if (this.prompts > INTERACT_BUDGET) {
      throw new DetourError(
        'Too many interactions (this demo caps a single check at 200 prompts). ' +
        'Abandoning this check; paste fuller proof steps to guide the search.')
    }
    return this.driver.askNext(this.getContext(), fm)
  }

  // -- constraints --
  collectTerm(a: Term, b: Term): void {
    this.st.termC.unshift([a, b])
  }
  collectFormula(a: Formula, b: Formula): void {
    this.st.formulaC.unshift([a, b])
  }
  collectType(a: DType, b: DType): void {
    this.st.typeC.unshift([a, b])
  }
  async unifyTerm(a: Term, b: Term): Promise<void> {
    await this.step()
    this.collectTerm(a, b)
    await this.solve()
  }
  async unifyFormula(a: Formula, b: Formula): Promise<void> {
    await this.step()
    this.collectFormula(a, b)
    await this.solve()
  }
  async unifyType(a: DType, b: DType): Promise<void> {
    await this.step()
    this.collectType(a, b)
    await this.solve()
  }
  async unifyAssert(a: Assertion, fm: Formula): Promise<void> {
    switch (a.k) {
      case 'assumed': return this.unifyFormula(a.f, fm)
      case 'claimed': return this.unifyFormula(a.f, fm)
      case 'axiom': return this.unifyFormula(a.f, fm)
      case 'derived': throw new DetourError('Unification on derived judgments (sub-proofs) and formulae does not make sense!')
    }
  }
  async unifyListTerm(a: Term[], b: Term[]): Promise<void> {
    if (a.length !== b.length) throw new DetourError('Unification Error. Can not unify two lists with differing lengths.')
    for (let k = 0; k < a.length; k++) await this.unifyTerm(a[k]!, b[k]!)
  }
  async unifyListFormula(a: Formula[], b: Formula[]): Promise<void> {
    if (a.length !== b.length) throw new DetourError('Unification Error. Can not unify two lists with differing lengths.')
    for (let k = 0; k < a.length; k++) await this.unifyFormula(a[k]!, b[k]!)
  }
  async unifyFreeConst(f: string, c: string): Promise<void> {
    await this.unifyTerm({ k: 'free', name: f }, { k: 'app', c, args: [] })
  }
  async solve(): Promise<void> {
    await this.getSubst()
  }

  // -- types --
  async instantiateScheme(s: TypeScheme): Promise<DType> {
    const mappings: Subst = []
    for (const v of s.vars) mappings.push({ k: 'type', name: v, ty: this.freshType() })
    return appType(mappings, s.ty)
  }
  async instantiateSchemeAt(s: TypeScheme, types: DType[]): Promise<DType> {
    const mappings: Subst = []
    for (let k = 0; k < s.vars.length; k++) {
      mappings.push({ k: 'type', name: s.vars[k]!, ty: k < types.length ? types[k]! : this.freshType() })
    }
    return appType(mappings, s.ty)
  }
  lookUpTheorem(name: string): DTheorem {
    const t = this.env.theorems.get(name)
    if (!t) throw new DetourError(`Unknown theorem \`${name}'.`)
    return t
  }
  async lookUpType(name: string): Promise<DType> {
    const ts = this.st.typingCtx.get(name)
    if (!ts) throw new DetourError(`Type Error. I don't know a variable or a constant named \`${name}'.`)
    return this.instantiateScheme(ts)
  }
  async typeOf(t: Term): Promise<DType> {
    if (t.k === 'free' || t.k === 'rigid') {
      const ts = this.st.typingCtx.get(t.name)
      if (!ts) throw new DetourError(`I can not get a type of a variable \`${t.name}' because I don't know it.`)
      return this.instantiateScheme(ts)
    }
    if (t.k === 'app') {
      const ts = this.st.typingCtx.get(t.c)
      if (!ts) throw new DetourError(`I can not get a type of a constant \`${t.c}' because I don't know it.`)
      let ty = await this.instantiateScheme(ts)
      for (const a of t.args) {
        const at = await this.typeOf(a)
        const par = this.freshType()
        const res = this.freshType()
        this.collectType({ k: 'fn', a: par, b: res }, ty)
        this.collectType(at, par)
        ty = res
      }
      return ty
    }
    throw new Error('internal error: typeOf Bound')
  }

  // -- occurs / escape --
  occursFreeTerm(f: string, t: Term): boolean {
    if (t.k === 'bound') return false
    if (t.k === 'app') return t.args.some((a) => this.occursFreeTerm(f, a))
    if (t.k === 'free') return t.name === f
    return false
  }
  occursPropFormula(p: string, f: Formula): boolean {
    switch (f.k) {
      case 'true': case 'false': return false
      case 'atom':
        if (f.rel.k === 'meta') return f.rel.prop === p
        return false
      case 'not': return this.occursPropFormula(p, f.f)
      case 'and': case 'or': case 'impl': case 'eq':
        return this.occursPropFormula(p, f.l) || this.occursPropFormula(p, f.r)
      case 'forall': case 'exists': return this.occursPropFormula(p, f.body)
    }
  }
  occursTypeVar(s: string, t: DType): boolean {
    if (t.k === 'var') return t.name === s
    if (t.k === 'const') return false
    return this.occursTypeVar(s, t.a) || this.occursTypeVar(s, t.b)
  }
  async escapesTo(t: Term, depth: number): Promise<boolean> {
    if (t.k === 'bound') throw new Error('internal error: Bound variable participating in unification.')
    if (t.k === 'app') {
      for (const a of t.args) if (await this.escapesTo(a, depth)) return true
      return false
    }
    if (t.k === 'free') return false
    return depth < this.rigidLevel(t.name)
  }

  // __PART4D_MGU__
  // -- most general unification (port of Check.Solver Unifier) --
  async mguTerm(a: Term, b: Term): Promise<Subst> {
    await this.step()
    if (a.k === 'bound' && b.k === 'bound') {
      if (a.name === b.name) return []
      throw new DetourError(`I could not unify two non-identical bound variables, the \`${a.name}ᵇ' with the \`${b.name}ᵇ'.`)
    }
    if (a.k === 'bound') throw new DetourError(`I could not unify the bound variable \`${a.name}ᵇ' with the term \`${showTerm(b)}'.`)
    if (b.k === 'bound') throw new DetourError(`I could not unify the bound variable \`${b.name}ᵇ' with the term \`${showTerm(a)}'.`)
    if (a.k === 'rigid' && b.k === 'rigid') {
      if (a.name === b.name) return []
      throw new DetourError(`I could not unify two non-identical quantification variables, the \`${a.name}®' with the \`${b.name}®.`)
    }
    if (a.k === 'app' && b.k === 'app') {
      if (a.c !== b.c) throw new DetourError(`I could not unify \`${showTerm(a)}' with \`${showTerm(b)}'.`)
      return this.mguListTerm(a.args, b.args)
    }
    if (a.k === 'free' && b.k === 'free') {
      const t = await this.lookUpType(a.name)
      const t2 = await this.lookUpType(b.name)
      const sub = await this.mguType(t, t2)
      this.collectType(t, t2)
      if (a.name === b.name) return sub
      const l = this.freeLevel(a.name)
      const l2 = this.freeLevel(b.name)
      if (l2 <= l) return composeSubst(sub, [{ k: 'free', name: a.name, term: b }])
      return composeSubst(sub, [{ k: 'free', name: b.name, term: a }])
    }
    if (a.k === 'free') return this.mguFreeTerm(a.name, b)
    if (b.k === 'free') return this.mguFreeTerm(b.name, a)
    if (a.k === 'rigid') throw new DetourError(`I could not unify the quantification variable \`${a.name}®' with the term \`${showTerm(b)}'.`)
    throw new DetourError(`I could not unify the quantification variable \`${(b as { name: string }).name}®' with the term \`${showTerm(a)}'.`)
  }
  async mguFreeTerm(f: string, t: Term): Promise<Subst> {
    if (this.occursFreeTerm(f, t)) {
      throw new DetourError(`occurs check failed. A free variable \`${f}·' occurs in the term \`${showTerm(t)}'.`)
    }
    const ty = await this.lookUpType(f)
    const ty2 = await this.typeOf(t)
    const sub = await this.mguType(ty, ty2)
    this.collectType(ty, ty2)
    const i = this.freeLevel(f)
    if (await this.escapesTo(t, i)) {
      throw new DetourError(`escape check failed. Some quantification variable from \`${showTerm(t)}' attempted to escape through the variable \`${f}·?'.`)
    }
    return composeSubst(sub, [{ k: 'free', name: f, term: t }])
  }
  async mguListTerm(a: Term[], b: Term[]): Promise<Subst> {
    if (a.length !== b.length) throw new DetourError('I could not unify differently sized lists.')
    let acc: Subst = []
    let aa = a
    let bb = b
    while (aa.length > 0) {
      const s1 = await this.mguTerm(aa[0]!, bb[0]!)
      aa = aa.slice(1).map((x) => appTerm(s1, x))
      bb = bb.slice(1).map((x) => appTerm(s1, x))
      acc = composeSubst(s1, acc)
    }
    void bb
    return acc
  }
  async mguFormula(a: Formula, b: Formula): Promise<Subst> {
    await this.step()
    if (a.k === 'true' && b.k === 'true') return []
    if (a.k === 'false' && b.k === 'false') return []
    if (a.k === 'atom' && a.rel.k === 'meta') {
      if (showFormula(a) === showFormula(b)) return []
      if (this.occursPropFormula(a.rel.prop, b)) {
        throw new DetourError(`occurs check failed. A propositional meta-variable \`_${a.rel.prop}' occurs in the formula \`${showFormula(b)}'.`)
      }
      return [{ k: 'prop', name: a.rel.prop, formula: b }]
    }
    if (b.k === 'atom' && b.rel.k === 'meta') return this.mguFormula(b, a)
    if (a.k === 'atom' && b.k === 'atom' && a.rel.k === 'rel' && b.rel.k === 'rel') {
      if (a.rel.name !== b.rel.name) throw new DetourError(`I could not unify \`${showFormula(a)}' with \`${showFormula(b)}'.`)
      const aa = a.rel.args
      const ba = b.rel.args
      if (aa.k !== ba.k) throw new DetourError(`I could not unify \`${showFormula(a)}' with \`${showFormula(b)}'.`)
      if (aa.k === 'terms' && ba.k === 'terms') {
        for (let k = 0; k < Math.min(aa.args.length, ba.args.length); k++) {
          this.collectTerm(aa.args[k]! as Term, ba.args[k]! as Term)
        }
        return this.mguListTerm(aa.args as Term[], ba.args as Term[])
      }
      if (aa.k === 'formulae' && ba.k === 'formulae') {
        for (let k = 0; k < Math.min(aa.args.length, ba.args.length); k++) {
          this.collectFormula(aa.args[k]! as Formula, ba.args[k]! as Formula)
        }
        return this.mguListFormula(aa.args as Formula[], ba.args as Formula[])
      }
      throw new DetourError(`I could not unify \`${showFormula(a)}' with \`${showFormula(b)}'.`)
    }
    if (a.k === 'not' && b.k === 'not') return this.mguFormula(a.f, b.f)
    if (a.k === 'and' && b.k === 'and') return this.mguListFormula([a.l, a.r], [b.l, b.r])
    if (a.k === 'or' && b.k === 'or') return this.mguListFormula([a.l, a.r], [b.l, b.r])
    if (a.k === 'impl' && b.k === 'impl') return this.mguListFormula([a.l, a.r], [b.l, b.r])
    if (a.k === 'eq' && b.k === 'eq') return this.mguListFormula([a.l, a.r], [b.l, b.r])
    if (a.k === 'forall' && b.k === 'forall') return this.mguQuant(a.name, a.ts, a.body, b.name, b.ts, b.body, 'forall')
    if (a.k === 'exists' && b.k === 'exists') return this.mguQuant(a.name, a.ts, a.body, b.name, b.ts, b.body, 'exists')
    throw new DetourError(`I could not unify \`${showFormula(a)}' with \`${showFormula(b)}'.`)
  }
  async mguQuant(n1: string, t1: TypeScheme, b1: Formula, n2: string, t2: TypeScheme, b2: Formula, _q: 'forall' | 'exists'): Promise<Subst> {
    const t = await this.instantiateScheme(t1)
    const t2i = await this.instantiateScheme(t2)
    await this.mguType(t, t2i)
    this.collectType(t, t2i)
    const n = this.freshName()
    const bodyA = appFormula([{ k: 'bound', name: n1, term: { k: 'bound', name: n } }], b1)
    const bodyB = appFormula([{ k: 'bound', name: n2, term: { k: 'bound', name: n } }], b2)
    return this.mguFormula(bodyA, bodyB)
  }
  async mguListFormula(a: Formula[], b: Formula[]): Promise<Subst> {
    if (a.length !== b.length) throw new DetourError('I could not unify differently sized lists.')
    let acc: Subst = []
    let aa = a
    let bb = b
    while (aa.length > 0) {
      const s1 = await this.mguFormula(aa[0]!, bb[0]!)
      aa = aa.slice(1).map((x) => appFormula(s1, x))
      bb = bb.slice(1).map((x) => appFormula(s1, x))
      acc = composeSubst(s1, acc)
    }
    void bb
    return acc
  }
  async mguType(a: DType, b: DType): Promise<Subst> {
    await this.step()
    if (a.k === 'const' && b.k === 'const') {
      if (a.name === b.name) return []
      throw new DetourError(`I could not unify two non-identical types, the \`${a.name}' with \`${b.name}'.`)
    }
    if (a.k === 'var' && b.k === 'var') {
      if (a.name === b.name) return []
      return [{ k: 'type', name: a.name, ty: b }]
    }
    if (a.k === 'var') return [{ k: 'type', name: a.name, ty: b }]
    if (b.k === 'var') return this.mguType(b, a)
    if (a.k === 'fn' && b.k === 'fn') {
      const s1 = await this.mguType(a.a, b.a)
      const s2 = await this.mguType(appType(s1, a.b), appType(s1, b.b))
      return composeSubst(s2, s1)
    }
    throw new DetourError(`I could not unify \`${showType(a)}' with \`${showType(b)}'.`)
  }

  // -- constraint solving (port of Check.Solver solve/get'subst) --
  async solveCsTerm(cs: Array<[Term, Term]>, sub: Subst): Promise<Subst> {
    let work = cs.slice()
    let acc = sub
    while (work.length > 0) {
      const [[a, b], ...rest] = work as [[Term, Term], ...Array<[Term, Term]>]
      const s = await this.mguTerm(a, b)
      this.st.typingCtx = appSchemeMap(s, this.st.typingCtx)
      work = rest.map(([x, y]): [Term, Term] => [appTerm(s, x), appTerm(s, y)])
      acc = composeSubst(s, acc)
    }
    return acc
  }
  async solveCsFormula(cs: Array<[Formula, Formula]>, sub: Subst): Promise<Subst> {
    let work = cs.slice()
    let acc = sub
    while (work.length > 0) {
      const [[a, b], ...rest] = work as [[Formula, Formula], ...Array<[Formula, Formula]>]
      const s = await this.mguFormula(a, b)
      this.st.typingCtx = appSchemeMap(s, this.st.typingCtx)
      work = rest.map(([x, y]): [Formula, Formula] => [appFormula(s, x), appFormula(s, y)])
      acc = composeSubst(s, acc)
    }
    return acc
  }
  async solveCsType(cs: Array<[DType, DType]>, sub: Subst): Promise<Subst> {
    let work = cs.slice()
    let acc = sub
    while (work.length > 0) {
      const [[a, b], ...rest] = work as [[DType, DType], ...Array<[DType, DType]>]
      const s = await this.mguType(a, b)
      this.st.typingCtx = appSchemeMap(s, this.st.typingCtx)
      work = rest.map(([x, y]): [DType, DType] => [appType(s, x), appType(s, y)])
      acc = composeSubst(s, acc)
    }
    return acc
  }
  async getSubst(): Promise<Subst> {
    const tsub = await this.solveCsTerm(this.st.termC, [])
    const fsub = await this.solveCsFormula(
      this.st.formulaC.map(([a, b]): [Formula, Formula] => [appFormula(tsub, a), appFormula(tsub, b)]), tsub)
    const ysub = await this.solveCsType(
      this.st.typeC.map(([a, b]): [DType, DType] => [appType(fsub, a), appType(fsub, b)]), fsub)
    return ysub
  }

  // __PART4E_CHECK__
  // -- interaction helper shared by the Assert paths --
  async handleAssert(source: string, fm: Formula): Promise<void> {
    const rs = [...this.st.rigidDepth.keys()]
    let judgments: Judgment[]
    try {
      judgments = parseDetourProof(source, rs)
    } catch (e) {
      throw new DetourError(`The proof given to me does not parse. Parser reports this error:\n${e instanceof Error ? e.message : String(e)}`)
    }
    await this.inScopeOfAll(judgments, () => this.proofSearch(fm))
  }
  async findM<T>(xs: T[], fn: (x: T) => Promise<boolean>): Promise<T | null> {
    for (const x of xs) {
      const save = this.snapshotState()
      let ok = false
      try {
        ok = await fn(x)
      } catch (e) {
        if (e instanceof DetourError) {
          this.restoreState(save)
          ok = false
        } else throw e
      }
      if (ok) return x
    }
    return null
  }
  async tryAny(fns: Array<() => Promise<void>>): Promise<boolean> {
    for (const fn of fns) {
      const save = this.snapshotState()
      try {
        await fn()
        return true
      } catch (e) {
        if (e instanceof DetourError) {
          this.restoreState(save)
          continue
        }
        throw e
      }
    }
    return false
  }

  // -- judgments --
  lastDerivation(ders: Judgment[]): Judgment {
    if (ders.length === 0) throw new DetourError('Unexpected empty sub-proof.')
    return ders[ders.length - 1]!
  }
  assertsFormula(a: Assertion): Formula {
    switch (a.k) {
      case 'assumed': case 'claimed': case 'axiom': return a.f
      case 'derived': throw new DetourError('Unexpected sub-proof. I was expecting an assertion of a formula (claim/axiom/assumption) but was given a name of a proof.')
    }
  }
  async idToAssert(id: string): Promise<Assertion> {
    const a = this.env.assertScope.get(id)
    if (!a) throw new DetourError(`Unknown identifier \`${id}'.`)
    return a
  }
  async checkAll(ders: Judgment[]): Promise<void> {
    if (ders.length === 0) throw new DetourError('Empty proofs are not allowed.')
    if (ders.length === 1) return this.checkJudgment(ders[0]!)
    await this.checkJudgment(ders[0]!)
    return this.inScopeOf(ders[0]!, () => this.checkAll(ders.slice(1)))
  }
  async inScopeOf(j: Judgment, m: () => Promise<void>): Promise<void> {
    if (j.k === 'sub') {
      const p = j.proof
      if (p.name === null) return m()
      const last = this.lastDerivation(p.ders)
      let formula: Formula
      if (last.k === 'claim') formula = last.claim.formula
      else if (last.k === 'prove') formula = last.formula
      else if (last.k === 'sub') throw new DetourError('The last derivation must be a claim not a sub-proof.')
      else throw new DetourError('The last derivation must be a claim not an alias.')
      if (this.env.assertScope.has(p.name)) throw new DetourError(`The name \`${p.name}' is already used.`)
      return this.local((e) => ({
        ...e,
        assertScope: new Map([[p.name as string, { k: 'derived', a: p.assum, f: formula } as Assertion], ...e.assertScope]),
      }), m)
    }
    if (j.k === 'claim') {
      if (j.claim.name === null) return m()
      if (this.env.assertScope.has(j.claim.name)) throw new DetourError(`The name \`${j.claim.name}' is already used.`)
      const nm = j.claim.name
      const f = j.claim.formula
      return this.local((e) => ({
        ...e, assertScope: new Map([[nm, { k: 'claimed', f }] as [string, Assertion], ...e.assertScope]),
      }), m)
    }
    if (j.k === 'alias') return m()
    await this.checkJudgment(j)
    if (j.name === null) return m()
    const nm = j.name
    const f = j.formula
    return this.local((e) => ({
      ...e, assertScope: new Map([[nm, { k: 'claimed', f }] as [string, Assertion], ...e.assertScope]),
    }), m)
  }
  async inScopeOfAll(js: Judgment[], m: () => Promise<void>): Promise<void> {
    if (js.length === 0) throw new DetourError('Empty proofs are not allowed.')
    if (js.length === 1) {
      await this.checkJudgment(js[0]!)
      return this.inScopeOf(js[0]!, m)
    }
    await this.checkJudgment(js[0]!)
    return this.inScopeOf(js[0]!, () => this.inScopeOfAll(js.slice(1), m))
  }
  async checkJudgment(j: Judgment): Promise<void> {
    await this.step()
    if (j.k === 'sub') return this.checkProof(j.proof)
    if (j.k === 'claim') {
      const n = j.claim.name ?? '_'
      return this.because(`I was checking a claim \`${n}'`, () => this.justifies(j.claim.just, j.claim.formula))
    }
    if (j.k === 'alias') {
      this.collectFormula({ k: 'atom', rel: { k: 'meta', prop: j.name } }, j.formula)
      return this.solve()
    }
    return this.proofSearch(j.formula)
  }
  async checkProof(p: Proof): Promise<void> {
    await this.step()
    const d = this.env.depth
    if (p.assum.k === 'universal') {
      const frees: string[] = []
      for (const j of p.ders) for (const f of freeVarsJudgment(j)) if (!frees.includes(f)) frees.push(f)
      const rigidVs = p.assum.binds.map(([r]) => r)
      const freePatch = new Map(frees.map((f): [string, number] => [f, d + 1]))
      const rigidPatch = new Map(p.assum.binds.map(([r]): [string, number] => [r, d + 1]))
      const typingPatch = new Map(p.assum.binds.map(([s, t]): [string, TypeScheme] => [s, t]))
      const typingPatch2 = new Map<string, TypeScheme>()
      for (const f of frees) typingPatch2.set(f, { vars: [], ty: this.freshType() })
      this.st.freeDepth = new Map([...freePatch, ...this.st.freeDepth])
      this.st.rigidDepth = new Map([...rigidPatch, ...this.st.rigidDepth])
      this.st.typingCtx = new Map([...typingPatch, ...typingPatch2, ...this.st.typingCtx])
      return this.local((e) => ({ ...e, depth: d + 1, rigidVars: [...rigidVs, ...e.rigidVars] }),
        () => this.checkAll(p.ders))
    }
    if (p.assum.k === 'existential') {
      const frees: string[] = []
      for (const j of p.ders) for (const f of freeVarsJudgment(j)) if (!frees.includes(f)) frees.push(f)
      for (const f of freeVarsBinding(p.assum.binding)) if (!frees.includes(f)) frees.push(f)
      const rigidVs = p.assum.binds.map(([r]) => r)
      const freePatch = new Map(frees.map((f): [string, number] => [f, d + 1]))
      const rigidPatch = new Map(p.assum.binds.map(([r]): [string, number] => [r, d + 1]))
      const patch = new Map<string, Assertion>()
      if (p.assum.binding[0] !== null) patch.set(p.assum.binding[0], { k: 'assumed', f: p.assum.binding[1] })
      const typingPatch = new Map(p.assum.binds.map(([s, t]): [string, TypeScheme] => [s, t]))
      const typingPatch2 = new Map<string, TypeScheme>()
      for (const f of frees) typingPatch2.set(f, { vars: [], ty: this.freshType() })
      this.st.rigidDepth = new Map([...rigidPatch, ...this.st.rigidDepth])
      this.st.freeDepth = new Map([...freePatch, ...this.st.freeDepth])
      this.st.typingCtx = new Map([...typingPatch, ...typingPatch2, ...this.st.typingCtx])
      return this.local((e) => ({
        ...e,
        assertScope: new Map([...patch, ...e.assertScope]),
        depth: d + 1, rigidVars: [...rigidVs, ...e.rigidVars],
      }), () => this.checkAll(p.ders))
    }
    const frees: string[] = []
    for (const j of p.ders) for (const f of freeVarsJudgment(j)) if (!frees.includes(f)) frees.push(f)
    for (const b of p.assum.pairs) for (const f of freeVarsBinding(b)) if (!frees.includes(f)) frees.push(f)
    const freePatch = new Map(frees.map((f): [string, number] => [f, d + 1]))
    const assertions: Array<[string, Assertion]> = []
    for (const [n, a] of p.assum.pairs) if (n !== null) assertions.push([n, { k: 'assumed', f: a }])
    const patch = new Map(assertions)
    const typingPatch = new Map<string, TypeScheme>()
    for (const f of frees) typingPatch.set(f, { vars: [], ty: this.freshType() })
    this.st.freeDepth = new Map([...freePatch, ...this.st.freeDepth])
    this.st.typingCtx = new Map([...typingPatch, ...this.st.typingCtx])
    return this.local((e) => ({
      ...e, assertScope: new Map([...patch, ...e.assertScope]), depth: d + 1,
    }), () => this.checkAll(p.ders))
  }

  // -- proves: a known fact justifying a goal (port of Check.Proof proves) --
  async proves(a: Formula, b: Formula): Promise<void> {
    await this.step()
    if (a.k === 'true' || a.k === 'false' || a.k === 'atom' || a.k === 'not' || a.k === 'or' || a.k === 'eq') {
      return this.unifyFormula(a, b)
    }
    if (a.k === 'and') {
      this.informAbout(`|~ does fm' \`${showFormula(a)}'  prove the goal \`${showFormula(b)}'`)
      const ok = await this.tryAny([
        () => this.unifyFormula(a, b),
        () => this.unifyFormula(a.l, b),
        () => this.unifyFormula(a.r, b),
      ])
      if (!ok) throw new DetourError(`Can not prove \`${showFormula(b)}' using a conjunction \`${showFormula(a)}'`)
      return
    }
    if (a.k === 'impl') {
      this.informAbout(`|~ does fm' \`${showFormula(a)}'  prove the goal \`${showFormula(b)}'`)
      if (b.k === 'impl') return this.unifyFormula(a, b)
      await this.unifyFormula(a.r, b)
      return this.proofSearch(a.l)
    }
    if (a.k === 'forall') {
      if (b.k === 'forall') {
        this.informAbout(`|~ does fm' \`${showFormula(a)}'  prove the goal \`${showFormula(b)}'`)
        return this.unifyFormula(a, b)
      }
      this.informAbout(`|~ does fm' \`${showFormula(a)}'  prove the goal \`${showFormula(b)}'`)
      const n = this.freshName()
      this.st.typingCtx = new Map(this.st.typingCtx)
      this.st.typingCtx.set(n, a.ts)
      this.st.freeDepth = new Map(this.st.freeDepth)
      if (!this.st.freeDepth.has(n)) this.st.freeDepth.set(n, this.env.depth + 1)
      const body = appFormula([{ k: 'bound', name: a.name, term: { k: 'free', name: n } }], a.body)
      return this.proves(body, b)
    }
    if (b.k === 'exists' && a.k !== 'exists') {
      this.informAbout(`|~ does fm' \`${showFormula(a)}'  prove the goal \`${showFormula(b)}'`)
      const n = this.freshName()
      this.st.typingCtx = new Map(this.st.typingCtx)
      this.st.typingCtx.set(n, b.ts)
      this.st.freeDepth = new Map(this.st.freeDepth)
      if (!this.st.freeDepth.has(n)) this.st.freeDepth.set(n, this.env.depth + 1)
      // NOTE: upstream builds a Free (not Bound) binding here, which never
      // fires on the bound body — the goal is effectively NOT instantiated.
      // This clause is unreachable upstream (every fact shape matches an
      // earlier clause); kept for fidelity.
      const body = appFormula([{ k: 'free', name: b.name, term: { k: 'free', name: n } }], b.body)
      return this.proves(a, body)
    }
    if (a.k === 'exists' && b.k === 'exists') {
      this.informAbout(`|~ does fm' \`${showFormula(a)}'  prove the goal \`${showFormula(b)}'`)
      return this.unifyFormula(a, b)
    }
    // a.k === 'exists' (non-Exists goal)
    this.informAbout(`|~ does fm' \`${showFormula(a)}'  prove the goal \`${showFormula(b)}'`)
    const n = this.freshName()
    this.st.typingCtx = new Map(this.st.typingCtx)
    this.st.typingCtx.set(n, a.ts)
    this.st.rigidDepth = new Map(this.st.rigidDepth)
    if (!this.st.rigidDepth.has(n)) this.st.rigidDepth.set(n, this.env.depth + 1)
    const body = appFormula([{ k: 'bound', name: a.name, term: { k: 'rigid', name: n } }], a.body)
    return this.local((e) => ({ ...e, rigidVars: [n, ...e.rigidVars] }), () => this.proves(body, b))
  }

  // __PART4F_SEARCH__
  // -- interactive proof search (port of Check.Proof proof'search) --
  async proofSearch(fm: Formula): Promise<void> {
    await this.step()
    switch (fm.k) {
      case 'true': return
      case 'false': throw new DetourError('proof search for ⊥ not implemented yet')
      case 'atom':
        if (fm.rel.k === 'meta') {
          throw new DetourError('proof search for meta-relation variable is not a thing. This is probably an internal error.')
        }
        return this.proofSearchAtom(fm)
      case 'not': throw new DetourError('proof search for ¬ not implemented yet')
      case 'and': return this.proofSearchAnd(fm)
      case 'or': throw new DetourError('proof search for ∨ not implemented yet')
      case 'impl': {
        const n = this.freshName()
        return this.local((e) => ({
          ...e, assertScope: new Map([[n, { k: 'assumed', f: fm.l }] as [string, Assertion], ...e.assertScope]),
        }), () => this.proofSearch(fm.r))
      }
      case 'eq': throw new DetourError('proof search for <==> not implemented yet')
      case 'exists': return this.proofSearchExists(fm)
      case 'forall': return this.proofSearchForall(fm)
    }
  }
  showAsserts(asserts: Array<[string, Assertion]>): string {
    return `[${asserts.map(([n, a]) => `(${JSON.stringify(n)},${showAssertion(a)})`).join(', ')}]`
  }
  showTheorems(theors: Array<[string, DTheorem]>): string {
    return `[${theors.map(([n, t]) => `(${JSON.stringify(n)},${showTheorem(t)})`).join(', ')}]`
  }
  async proveWithAsserts(asserts: Array<[string, Assertion]>, fm: Formula, claimed: boolean): Promise<[string, Assertion] | null> {
    // NOTE: failures must propagate (not be swallowed) so findM rolls back
    // the attempt's constraints — mirroring catchError placement upstream.
    return this.findM(asserts, async ([, a]) => {
      if (a.k === 'derived') return false
      if (claimed && a.k === 'claimed') {
        try {
          this.informAbout(`does fm' = ${showFormula(a.f)}  prove fm = ${showFormula(fm)}`)
          await this.proves(a.f, fm)
          return true
        } catch (e) {
          if (e instanceof DetourError) {
            this.informAbout(`the fm' = ${showFormula(a.f)}  does not prove fm = ${showFormula(fm)}\nthe reason was ${e.msg}`)
          }
          throw e
        }
      }
      await this.proves(this.assertsFormula(a), fm)
      return true
    })
  }
  async proveWithTheorems(theors: Array<[string, DTheorem]>, fm: Formula, freshen: boolean, informEach: boolean): Promise<[string, DTheorem] | null> {
    return this.findM(theors, async ([, t]) => {
      let assumptions = t.assumptions
      let conclusion = t.conclusion
      if (freshen) {
        const sub: Subst = t.propVars.map((s) => ({
          k: 'prop', name: s, formula: { k: 'atom', rel: { k: 'meta', prop: this.freshName() } },
        } as Binding))
        assumptions = assumptions.map((x) => appFormula(sub, x))
        conclusion = appFormula(sub, conclusion)
      }
      const chain = assumptions.reduceRight((acc, a) => ({ k: 'impl', l: a, r: acc } as Formula), conclusion)
      if (informEach) {
        this.informAbout(`[][]\ntrying a theorem \`${t.name}'  this means checking that \`${showFormula(chain)}    proves    \`${showFormula(fm)}'`)
      }
      await this.proves(chain, fm)
      return true
    })
  }
  async proofSearchAtom(fm: Formula): Promise<void> {
    if (fm.k !== 'atom' || fm.rel.k !== 'rel') throw new DetourError('internal error: proofSearchAtom on non-atom')
    const name = fm.rel.name
    this.informAbout(`| searching for a proof of \`${showFormula(fm)}'`)
    const juds = this.st.judgments
    const subst = await this.getSubst()
    const response = await this.askForNext(appFormula(subst, fm))
    if (response.k === 'assert') {
      await this.handleAssert(response.src, fm)
      return
    }
    const jud = juds.find((j) => j.con[0] === name)
    if (!jud) throw new DetourError(`the goal \`${showFormula(fm)}' is formed by an unknown judgment.`)
    const results: boolean[] = []
    for (const r of jud.rules) results.push(await this.conclMatches(r, fm))
    if (results.some(Boolean)) {
      const s = await this.getSubst()
      this.informAbout(`I solved a goal \`${showFormula(appFormula(s, fm))}' using some judgment rule.`)
      return
    }
    const asserts = sortedEntries(this.env.assertScope)
    this.informAbout(`I will be looking for some assertion that justifies my goal \`${showFormula(fm)}\nall the assertions are: ${this.showAsserts(asserts)}`)
    const found = await this.proveWithAsserts(asserts, fm, true)
    if (found) {
      this.informAbout(`I found a local assertion \`${found[0]}' that justifies my goal \`${showFormula(fm)}'\nthe assertion was = \`${showAssertion(found[1])}'.`)
      return
    }
    const theors = sortedEntries(this.env.theorems)
    const foundT = await this.proveWithTheorems(theors, fm, true, true)
    if (foundT) {
      this.informAbout(`I found a theorem \`${foundT[0]}' that justifies my goal \`${showFormula(fm)}'.`)
      return
    }
    const s = await this.getSubst()
    const cmd = await this.askForNext(appFormula(s, fm))
    if (cmd.k === 'idk') {
      throw new DetourError(`I didn't find any local assertion or theorems that would prove the goal \`${showFormula(fm)}'.`)
    }
    await this.handleAssert(cmd.src, fm)
  }
  async proofSearchAnd(fm: Formula): Promise<void> {
    if (fm.k !== 'and') throw new DetourError('internal error: proofSearchAnd on non-and')
    this.informAbout(`| searching for a proof of \`${showFormula(fm)}'`)
    const subst = await this.getSubst()
    const response = await this.askForNext(appFormula(subst, fm))
    if (response.k === 'assert') {
      await this.handleAssert(response.src, fm)
      return
    }
    const asserts = sortedEntries(this.env.assertScope)
    this.informAbout(`I will be looking for some assertion that justifies my goal \`${showFormula(fm)}\nall the assertions are: ${this.showAsserts(asserts)}`)
    const found = await this.proveWithAsserts(asserts, fm, true)
    if (found) {
      this.informAbout(`I found a local assertion \`${found[0]}' that justifies my goal \`${showFormula(fm)}'\nthe assertion was = \`${showAssertion(found[1])}'.`)
      return
    }
    const theors = sortedEntries(this.env.theorems)
    const foundT = await this.proveWithTheorems(theors, fm, true, true)
    if (foundT) {
      this.informAbout(`I found a theorem \`${foundT[0]}' that justifies my goal \`${showFormula(fm)}'.`)
      return
    }
    await this.proofSearch(fm.l)
    await this.proofSearch(fm.r)
  }
  async proofSearchExists(fm: Formula): Promise<void> {
    if (fm.k !== 'exists') throw new DetourError('internal error: proofSearchExists on non-exists')
    const response = await this.askForNext(fm)
    if (response.k === 'assert') {
      await this.handleAssert(response.src, fm)
      return
    }
    const asserts = sortedEntries(this.env.assertScope)
    const found = await this.proveWithAsserts(asserts, fm, false)
    if (found) {
      this.informAbout(`I found a local assertion \`${found[0]}' that justifies my goal \`${showFormula(fm)}'\nthe assertion was = \`${showAssertion(found[1])}'.`)
      return
    }
    this.informAbout(`|| my goal \`${showFormula(fm)}'  wasn't proved by any local assert, I am going to try theorems`)
    const theors = sortedEntries(this.env.theorems)
    const foundT = await this.proveWithTheorems(theors, fm, false, false)
    if (foundT) {
      this.informAbout(`I found a theorem \`${foundT[0]}' that justifies my goal \`${showFormula(fm)}'.`)
      return
    }
    const f = this.freshName()
    const body = appFormula([{ k: 'bound', name: fm.name, term: { k: 'free', name: f } }], fm.body)
    this.st.typingCtx = new Map(this.st.typingCtx)
    this.st.typingCtx.set(f, fm.ts)
    this.st.freeDepth = new Map(this.st.freeDepth)
    this.st.freeDepth.set(f, this.env.depth + 1)
    this.informAbout(`... I couldn't find a theorem or assertion so I am instantiating \`${showFormula(fm)}'\nmy current goal is \`${showFormula(body)}'`)
    const prefix = this.env.contextPrefix
    return this.local((e) => ({
      ...e,
      proofContext: [`${prefix}instantiating ∃ ${f} : ${showFormula(body)}    the goal is = ${showFormula(body)}`, ...e.proofContext],
      contextPrefix: `  ${prefix}`,
    }), () => this.proofSearch(body))
  }
  async proofSearchForall(fm: Formula): Promise<void> {
    if (fm.k !== 'forall') throw new DetourError('internal error: proofSearchForall on non-forall')
    const t = await this.instantiateScheme(fm.ts)
    const f = await this.freshFree()
    const fm2 = appFormula([{ k: 'bound', name: fm.name, term: { k: 'free', name: f } }], fm.body)
    if (t.k !== 'const') {
      throw new DetourError(`I can't prove the formula \`${showFormula(fm)}' by induction, its first binder has a confusing type \`${showType(t)}'.`)
    }
    const syn = this.st.syntax.find(([s]) => s === t.name)
    if (!syn) {
      throw new DetourError(`I can't prove the formula \`${showFormula(fm)}' by induction, I don't know the type of its first binder type \`${showType(t)}'.\nPerhaps you forgot to write a corresponding syntax section?`)
    }
    const goals: Array<[Formula, Ctor, string[]]> = []
    for (const c of syn[1]) {
      const [rs, pat] = await this.conToGoal(c)
      goals.push([appFormula([{ k: 'free', name: f, term: pat }], fm2), c, rs])
    }
    const prefix = this.env.contextPrefix
    return this.local((e) => ({
      ...e,
      proofContext: [`${prefix}using induction on  ∀ ${f}· : ${showFormula(fm2)}    for goal = ${showFormula(fm)}`, ...e.proofContext],
      contextPrefix: `  ${prefix}`,
    }), async () => {
      for (const g of goals) await this.searchCase(f, t, fm2, g)
    })
  }
  async conToGoal(c: Ctor): Promise<[string[], Term]> {
    const freshAndTyped: Array<[string, DType]> = []
    for (const t of c.args) freshAndTyped.push([this.freshName(), t])
    const tPatch = new Map(freshAndTyped.map(([n, t]): [string, TypeScheme] => [n, { vars: [], ty: t }]))
    const dPatch = new Map(freshAndTyped.map(([n]): [string, number] => [n, this.env.depth + 1]))
    this.st.typingCtx = new Map([...tPatch, ...this.st.typingCtx])
    this.st.rigidDepth = new Map([...dPatch, ...this.st.rigidDepth])
    const rigids = freshAndTyped.map(([n]) => n)
    return [rigids, { k: 'app', c: c.name, args: rigids.map((r): Term => ({ k: 'rigid', name: r })) }]
  }
  async searchCase(f: string, t: DType, fm: Formula, g: [Formula, Ctor, string[]]): Promise<void> {
    const [goal, ctor, rs] = g
    const typed = rs.map((r, i): [string, DType | undefined] => [r, ctor.args[i]]).filter(([, typ]) => typ !== undefined && typeEq(typ, t))
    const hyps = typed.map(([r]) => appFormula([{ k: 'free', name: f, term: { k: 'rigid', name: r as string } }], fm))
    const names: string[] = []
    for (const h of hyps) {
      void h
      names.push(this.freshName())
    }
    const patch = new Map(names.map((n, i): [string, Assertion] => [n, { k: 'assumed', f: hyps[i]! }]))
    const prefix = this.env.contextPrefix
    return this.local((e) => ({
      ...e,
      assertScope: new Map([...e.assertScope, ...patch]),
      rigidVars: [...rs, ...e.rigidVars],
      proofContext: [`${prefix}case ${ctor.name}(${rs.join(', ')}) ->     for goal = ${showFormula(goal)}`, ...e.proofContext],
      contextPrefix: `  ${prefix}`,
      depth: e.depth + 1,
    }), () => this.proofSearch(goal))
  }
  async conclMatches(rule: JudRule, fm: Formula): Promise<boolean> {
    const freshTyped: Array<[string, string, DType]> = []
    for (const [n, t] of rule.params) freshTyped.push([n, this.freshName(), t])
    let subst: Subst = []
    for (const [old, nw, typ] of freshTyped) {
      subst.push({ k: 'free', name: old, term: { k: 'free', name: nw } })
      this.st.typingCtx = new Map(this.st.typingCtx)
      this.st.typingCtx.set(nw, { vars: [], ty: typ })
      this.st.freeDepth = new Map(this.st.freeDepth)
      this.st.freeDepth.set(nw, this.env.depth + 1)
    }
    for (const s of rule.propVars) {
      subst.push({ k: 'prop', name: s, formula: { k: 'atom', rel: { k: 'meta', prop: this.freshName() } } })
    }
    const concl = appFormula(subst, rule.conclusion)
    const save = this.snapshotState()
    try {
      await this.unifyFormula(fm, concl)
      const premises = rule.premises.map((p) => appFormula(subst, p))
      const s = await this.getSubst()
      const newGoals = premises.map((p) => appFormula(s, p))
      const prefix = this.env.contextPrefix
      await this.local((e) => ({
        ...e,
        proofContext: [`${prefix}using the rule ${rule.name} the matched goal = ${showFormula(concl)} the new goals = ${newGoals.map(showFormula).join(`\n  ${prefix}`)}    the original goal was = ${showFormula(fm)}`, ...e.proofContext],
      }), async () => {
        for (const g of newGoals) await this.proofSearch(g)
      })
      const s2 = await this.getSubst()
      this.informAbout(`I had a goal = ${showFormula(fm)} and I solved it using a rule ${rule.name}  I unified it with ${showFormula(appFormula(s2, concl))}  and got to solve some sub-goals (${dShowList(newGoals, dShowFormula)})and those are done.\nthe original conclusion was = ${showFormula(rule.conclusion)}\nthe subst is = ${dShowList(subst, dShowBinding)}\nthe s = ${dShowList(s2, dShowBinding)}`)
      return true
    } catch (e) {
      if (e instanceof DetourError) {
        this.restoreState(save)
        return false
      }
      throw e
    }
  }

  // __PART4G_JUSTIFY__
  // -- deterministic justification checking (port of Check.Rule + induction) --
  findRule(name: string): JudRule {
    for (const j of this.st.judgments) {
      const r = j.rules.find((x) => x.name === name)
      if (r) return r
    }
    throw new DetourError(`I don't know the rule named \`${name}'.`)
  }
  async instantiate(e: Formula, binds: Array<[string, TypeScheme]>): Promise<Formula> {
    if (e.k === 'exists') return this.instantiateExistTo(e, binds)
    if (e.k === 'forall') return this.instantiateUniversalTo(e, binds)
    throw new DetourError(`I was trying to instantiate the formula \`${showFormula(e)}' but it isn't a quantified formula.`)
  }
  async instantiateExistTo(fm: Formula, binds: Array<[string, TypeScheme]>): Promise<Formula> {
    if (binds.length === 0) return fm
    if (fm.k !== 'exists') {
      throw new DetourError(`Instantiation error. The \`${showFormula(fm)}' is not an existentially quantified formula and there are some instantiation-arguments (terms) left.`)
    }
    const [[r, ts], ...rest] = binds as [[string, TypeScheme], ...Array<[string, TypeScheme]>]
    const tc = this.freshTypeConst()
    const t = await this.instantiateSchemeAt(fm.ts, [tc])
    const t2 = await this.instantiateSchemeAt(ts, [tc])
    await this.unifyType(t, t2)
    return this.instantiateExistTo(appFormula([{ k: 'bound', name: fm.name, term: { k: 'rigid', name: r } }], fm.body), rest)
  }
  async instantiateUniversalTo(fm: Formula, binds: Array<[string, TypeScheme]>): Promise<Formula> {
    if (binds.length === 0) return fm
    if (fm.k !== 'forall') {
      // NOTE: upstream says "existentially" here too (preserved verbatim).
      throw new DetourError(`Instantiation error. The \`${showFormula(fm)}' is not an existentially quantified formula and there are some instantiation-arguments (terms) left.`)
    }
    const [[r, ts], ...rest] = binds as [[string, TypeScheme], ...Array<[string, TypeScheme]>]
    const tc = this.freshTypeConst()
    const t = await this.instantiateSchemeAt(fm.ts, [tc])
    const t2 = await this.instantiateSchemeAt(ts, [tc])
    await this.unifyType(t, t2)
    return this.instantiateUniversalTo(appFormula([{ k: 'bound', name: fm.name, term: { k: 'rigid', name: r } }], fm.body), rest)
  }
  decomposeExists(fm: Formula): [[string, TypeScheme][], Formula] {
    const out: [string, TypeScheme][] = []
    let cur = fm
    while (cur.k === 'exists') {
      out.push([cur.name, cur.ts])
      cur = cur.body
    }
    return [out, cur]
  }
  decomposeForall(fm: Formula): [[string, TypeScheme][], Formula] {
    const out: [string, TypeScheme][] = []
    let cur = fm
    while (cur.k === 'forall') {
      out.push([cur.name, cur.ts])
      cur = cur.body
    }
    return [out, cur]
  }
  async unifyWithInstance(general: Formula, inst: Formula, q: 'exists' | 'forall'): Promise<void> {
    const [bindsL, bodyL] = q === 'exists' ? this.decomposeExists(general) : this.decomposeForall(general)
    const [bindsR] = q === 'exists' ? this.decomposeExists(inst) : this.decomposeForall(inst)
    if (!(bindsL.length > bindsR.length)) {
      throw new DetourError(`The supposedly more general formula \`${showFormula(general)}' does not have a longer prefix than its supposed instantiation \`${showFormula(inst)}'.`)
    }
    const diff = bindsL.length - bindsR.length
    const prefix = bindsL.slice(0, diff)
    const rest = bindsL.slice(diff)
    const bs: Array<[string, string, TypeScheme]> = []
    for (const [s, ts] of prefix) bs.push([s, await this.freshFree(), ts])
    const sub: Subst = bs.map(([b, f]) => ({ k: 'bound', name: b, term: { k: 'free', name: f } }))
    const tPatch = new Map(bs.map(([, f, ts]): [string, TypeScheme] => [f, ts]))
    const fold = q === 'exists'
      ? rest.reduceRight((acc: Formula, [n, ts]) => ({ k: 'exists', name: n, ts, body: acc } as Formula), bodyL)
      : rest.reduceRight((acc: Formula, [n, ts]) => ({ k: 'forall', name: n, ts, body: acc } as Formula), bodyL)
    const formula = appFormula(sub, fold)
    this.st.typingCtx = new Map([...tPatch, ...this.st.typingCtx])
    if (q === 'exists') {
      return this.because(
        `I was trying to unify \n  \`${showFormula(general)}'\nwith its supposed instance \n  \`${showFormula(inst)}'\nI instantiated the existential to\n  \`${showFormula(formula)}'.`,
        () => this.unifyFormula(formula, inst))
    }
    return this.because(
      `I was trying to unify \n  \`${showFormula(formula)}' () with its supposed instance \n  \`${showFormula(inst)}'.`,
      () => this.unifyFormula(formula, inst))
  }
  async justifies(j: Justification, fm: Formula): Promise<void> {
    await this.step()
    if (j.k === 'rule') {
      const asserts: Assertion[] = []
      for (const id of j.on) asserts.push(await this.idToAssert(id))
      return this.checkRule(j.kind, asserts, fm)
    }
    if (j.k === 'theorem') {
      const t = this.lookUpTheorem(j.name)
      const sub: Subst = t.propVars.map((s) => ({
        k: 'prop', name: s, formula: { k: 'atom', rel: { k: 'meta', prop: this.freshName() } },
      } as Binding))
      const assumptions = t.assumptions.map((x) => appFormula(sub, x))
      const conclusion = appFormula(sub, t.conclusion)
      const asserts: Assertion[] = []
      for (const id of j.on) asserts.push(await this.idToAssert(id))
      await this.unifyAssertList(asserts, assumptions)
      return this.unifyFormula(fm, conclusion)
    }
    if (j.k === 'unproved') return
    if (j.k === 'induction') {
      if (fm.k !== 'forall') {
        throw new DetourError(`I can't prove the formula \`${showFormula(fm)}' by induction because it's not in the correct shape.`)
      }
      const t = await this.instantiateScheme(fm.ts)
      const f = await this.freshFree()
      const fm2 = appFormula([{ k: 'bound', name: fm.name, term: { k: 'free', name: f } }], fm.body)
      if (t.k !== 'const') {
        throw new DetourError(`I can't prove the formula \`${showFormula(fm)}' by induction, its first binder has a confusing type \`${showType(t)}'.`)
      }
      const syn = this.st.syntax.find(([s]) => s === (t as { name: string }).name)
      if (!syn) {
        throw new DetourError(`I can't prove the formula \`${showFormula(fm)}' by induction, I don't know the type of its first binder type \`${showType(t)}'.\nPerhaps you forgot to write a corresponding syntax section?`)
      }
      return this.checkInductionCases(j.proofs, syn[1], t, [f, fm2])
    }
    if (j.k === 'cases') {
      const t = await this.typeOf(j.on)
      if (t.k !== 'const') {
        throw new DetourError(`I can't do case analysis on \`${showTerm(j.on)}' it has a confusing type \`${showType(t)}'.`)
      }
      const syn = this.st.syntax.find(([s]) => s === (t as { name: string }).name)
      if (!syn) {
        throw new DetourError(`I can't do case analysis on \`${showTerm(j.on)}' I don't know its type \`${showType(t)}'.\nPerhaps you forgot to write a corresponding syntax section?`)
      }
      return this.checkCases(j.proofs, syn[1], fm, j.on)
    }
    throw new DetourError('Proof by substitution is not implemented yet.')
  }
  async unifyAssertList(asserts: Assertion[], fms: Formula[]): Promise<void> {
    if (asserts.length !== fms.length) {
      throw new DetourError('Unification Error. Can not unify two lists with differing lengths.')
    }
    for (let k = 0; k < asserts.length; k++) await this.unifyAssert(asserts[k]!, fms[k]!)
  }
  async checkInductionCases(cases: CaseProof[], ctors: Ctor[], typ: DType, goal: [string, Formula]): Promise<void> {
    await this.handleCases(cases, ctors, typ, goal, true)
  }
  async handleCases(cases: CaseProof[], constrs: Ctor[], typ: DType, goal: [string, Formula] | null, induction: boolean, formula?: Formula, subject?: Term): Promise<void> {
    void typ
    void goal
    void formula
    void subject
    if (cases.length === 0 && constrs.length === 0) return
    if (constrs.length === 0) {
      const p = cases[0]!
      throw new DetourError(`I found a redundant case in the case analysis.\nDrop the case for \`(${dShowConst(p.con)},[${p.rigids.map(dShowRigid).join(', ')}])'.`)
    }
    const [constr, ...rest] = constrs as [Ctor, ...Ctor[]]
    const matching: CaseProof[] = []
    const notMatching: CaseProof[] = []
    for (const c of cases) {
      if (await this.caseMatches(c, constr)) matching.push(c)
      else notMatching.push(c)
    }
    if (matching.length === 0) {
      throw new DetourError(`there's a case missing in the case analysis.\nI can't find a case for \`${dShowCtor(constr)}'.`)
    }
    if (matching.length > 1) {
      throw new DetourError(`there are too many cases matching the constructor \`${dShowCtor(constr)}'.`)
    }
    const theCase = matching[0]!
    if (induction) await this.checkInductionCase(goal!, typ, constr, theCase)
    else await this.checkCase(formula!, subject!, constr, theCase)
    return this.handleCases(notMatching, rest, typ, goal, induction, formula, subject)
  }
  async checkInductionCase(goal: [string, Formula], typ: DType, ctor: Ctor, c: CaseProof): Promise<void> {
    const [f, goalFm] = goal
    await this.checkProof(c.proof)
    const goal2 = appFormula([{ k: 'free', name: f, term: { k: 'app', c: c.con, args: c.rigids.map((r): Term => ({ k: 'rigid', name: r })) } }], goalFm)
    if (c.proof.assum.k !== 'formula') {
      throw new DetourError('the induction cases are not supposed to have quantified assumptions.')
    }
    if (c.proof.assum.pairs.length > 0) {
      const typed = c.rigids.map((r, i): [string, DType | undefined] => [r, ctor.args[i]]).filter(([, t]) => t !== undefined && typeEq(t, typ))
      const hyps = typed.map(([r]) => appFormula([{ k: 'free', name: f, term: { k: 'rigid', name: r as string } }], goalFm))
      await this.unifyAssertList(
        c.proof.assum.pairs.map(([, x]) => ({ k: 'assumed', f: x } as Assertion)),
        hyps)
      void hyps
    }
    const last = this.lastDerivation(c.proof.ders)
    if (last.k === 'claim') return this.unifyFormula(last.claim.formula, goal2)
    if (last.k === 'prove') return this.unifyFormula(last.formula, goal2)
    if (c.proof.ders.length === 0) throw new DetourError('Missing conclusion.')
    throw new DetourError('I found a wrong-shaped conclusion in the body of the case.')
  }
  async checkCases(cases: CaseProof[], ctors: Ctor[], formula: Formula, subject: Term): Promise<void> {
    const toHandle: Ctor[] = []
    for (const c of ctors) {
      if (await this.unifiable(await this.conToPat(c), subject)) toHandle.push(c)
    }
    return this.handleCases(cases, toHandle, { k: 'const', name: '' }, null, false, formula, subject)
  }
  async caseMatches(c: CaseProof, constr: Ctor): Promise<boolean> {
    const d = this.env.depth
    const pat = { k: 'app', c: c.con, args: c.rigids.map((r): Term => ({ k: 'rigid', name: r })) } as Term
    const term = await this.conToPat(constr)
    const mappings = new Map<string, TypeScheme>()
    for (const r of c.rigids) mappings.set(r, { vars: [], ty: this.freshType() })
    this.st.typingCtx = new Map([...mappings, ...this.st.typingCtx])
    const dm = new Map<string, number>()
    for (const r of c.rigids) dm.set(r, d + 1)
    this.st.rigidDepth = new Map([...dm, ...this.st.rigidDepth])
    if (!(await this.unifiable(term, pat))) return false
    await this.unifyTerm(pat, term)
    return true
  }
  async conToPat(c: Ctor): Promise<Term> {
    const freshAndTyped: Array<[string, DType]> = []
    for (const t of c.args) freshAndTyped.push([this.freshName(), t])
    const tPatch = new Map(freshAndTyped.map(([n, t]): [string, TypeScheme] => [n, { vars: [], ty: t }]))
    const dPatch = new Map(freshAndTyped.map(([n]): [string, number] => [n, this.env.depth + 1]))
    this.st.typingCtx = new Map([...tPatch, ...this.st.typingCtx])
    this.st.freeDepth = new Map([...dPatch, ...this.st.freeDepth])
    return { k: 'app', c: c.name, args: freshAndTyped.map(([n]): Term => ({ k: 'free', name: n })) }
  }
  async unifiable(l: Term, r: Term): Promise<boolean> {
    const subst = await this.getSubst()
    const save = this.snapshotState()
    try {
      await this.matchMgu(appTerm(subst, l), appTerm(subst, r))
      return true
    } catch (e) {
      if (e instanceof DetourError) {
        this.restoreState(save)
        return false
      }
      throw e
    }
  }
  async matchMgu(p: Term, t: Term): Promise<Subst> {
    if (t.k === 'rigid') return [{ k: 'rigid', name: t.name, term: p }]
    return this.mguTerm(p, t)
  }
  async checkCase(goal: Formula, subject: Term, constr: Ctor, c: CaseProof): Promise<void> {
    const pat = { k: 'app', c: c.con, args: c.rigids.map((r): Term => ({ k: 'rigid', name: r })) } as Term
    const subst = await this.getSubst()
    const s2 = await this.matchMgu(appTerm(subst, pat), appTerm(subst, subject))
    const s = composeSubst(subst, s2)
    await this.checkProof(appProof(s, c.proof))
    const goal2 = appFormula(s, goal)
    const p2 = appProof(s, c.proof)
    if (p2.assum.k !== 'formula' || p2.assum.pairs.length > 0) {
      throw new DetourError('the cases are not supposed to have assumptions.')
    }
    const last = this.lastDerivation(p2.ders)
    if (last.k === 'claim') return this.unifyFormula(last.claim.formula, goal2)
    if (last.k === 'prove') return this.unifyFormula(last.formula, goal2)
    if (p2.ders.length === 0) throw new DetourError('Missing conclusion.')
    throw new DetourError('I found a wrong-shaped conclusion in the body of the case.')
  }

  // __PART4H_RULE__
  async checkImplIntro(a: Assertion, impl: Formula): Promise<void> {
    if (a.k !== 'derived' || a.a.k === 'universal' || a.a.k === 'existential') {
      if (a.k === 'derived' && a.a.k === 'universal') {
        throw new DetourError('A sub-proof justifying implication can not have universal as its assumption.')
      }
      if (a.k === 'derived') {
        throw new DetourError('A sub-proof justifying implication can not have existential as its assumption.')
      }
      throw new DetourError('Wrong justification for ==>-intro. It needs to be a sub-proof.')
    }
    const formulae = a.a.pairs.map(([, f]) => f)
    const metaProps: Formula[] = []
    for (const _ of a.a.pairs) {
      void _
      metaProps.push(this.freshProp())
    }
    const metaConcl = this.freshProp()
    const meta = metaProps.reduceRight((acc, x) => ({ k: 'impl', l: x, r: acc } as Formula), metaConcl)
    await this.because('I was trying to check a rule ==>-intro, specifically the premises',
      () => this.unifyAssertList(formulae.map((f) => ({ k: 'assumed', f } as Assertion)), metaProps))
    await this.unifyFormula(a.f, metaConcl)
    const s = await this.getSubst()
    return this.because(
      `I was trying to check a rule ==>-intro\n  the implication \`${showFormula(impl)}'\n  the meta-implication \`${showFormula(appFormula(s, meta))}'`,
      () => this.unifyFormula(impl, appFormula(s, meta)))
  }
  async checkRule(kind: RuleKind, asserts: Assertion[], fm: Formula): Promise<void> {
    await this.step()
    if (kind.k === 'custom') {
      const rule = this.findRule(kind.name)
      const triples: Array<[string, string, DType]> = []
      for (const [n, t] of rule.params) {
        const v = await this.freshFree()
        triples.push([n, v, t])
      }
      let sub: Subst = triples.map(([old, nw]) => ({ k: 'free', name: old, term: { k: 'free', name: nw } } as Binding))
      for (const s of rule.propVars) {
        sub.push({ k: 'prop', name: s, formula: { k: 'atom', rel: { k: 'meta', prop: this.freshName() } } })
      }
      const premises = rule.premises.map((p) => appFormula(sub, p))
      const conclusion = appFormula(sub, rule.conclusion)
      const tPatch = new Map(triples.map(([, f, t]): [string, TypeScheme] => [f, { vars: [], ty: t }]))
      this.st.typingCtx = new Map([...tPatch, ...this.st.typingCtx])
      await this.unifyAssertList(asserts, premises)
      return this.unifyFormula(fm, conclusion)
    }
    const b = kind.name
    const need = (n: number, rule: string): void => {
      if (asserts.length !== n) throw new DetourError(`I saw wrong number or shapes of arguments to the rule ${rule}.`)
    }
    const wrong = (): never => {
      throw new DetourError('This is a wrong justification.')
    }
    switch (b) {
      case 'ImplIntro': {
        need(1, '==>-intro')
        return this.checkImplIntro(asserts[0]!, fm)
      }
      case 'ImplElim': {
        if (asserts.length < 1) throw new DetourError('I saw wrong number or shapes of arguments to the rule ==>-elim.')
        const impl = this.assertsFormula(asserts[0]!)
        const prems = asserts.slice(1).map((a) => this.assertsFormula(a))
        const meta = prems.reduceRight((acc, x) => ({ k: 'impl', l: x, r: acc } as Formula), fm)
        return this.because(
          `I was trying to check the rule ==>-elim to justify \`${showFormula(fm)}'\n  the implication to eliminate \`${showFormula(impl)}'\n  and the proved premises ${prems.map((p) => `\`${showFormula(p)}'`).join(', ')}`,
          () => this.unifyFormula(impl, meta))
      }
      case 'ConjIntro': {
        need(2, '∧-intro')
        const x = this.assertsFormula(asserts[0]!)
        const y = this.assertsFormula(asserts[1]!)
        return this.because('I was trying to check the rule ∧-intro', () => this.unifyFormula(fm, { k: 'and', l: x, r: y }))
      }
      case 'ConjElim': {
        need(1, '∧-elim')
        const ab = this.assertsFormula(asserts[0]!)
        const x = this.freshProp()
        const y = this.freshProp()
        await this.unifyFormula(ab, { k: 'and', l: x, r: y })
        const saveCE = this.snapshotState()
        return this.because(
          'I was trying to check the rule ∧-elim',
          async () => {
            try {
              await this.unifyFormula(fm, x)
              await this.solve()
            } catch (e) {
              if (e instanceof DetourError) {
                this.restoreState(saveCE)
                return this.unifyFormula(fm, y)
              }
              throw e
            }
          })
      }
      case 'DisjIntro': {
        need(1, '∨-intro')
        const f = this.assertsFormula(asserts[0]!)
        const x = this.freshProp()
        const y = this.freshProp()
        await this.because('I was trying to check the rule ∨-intro and it seems that the formula is not even a disjunction.',
          () => this.unifyFormula(fm, { k: 'or', l: x, r: y }))
        const saveDI = this.snapshotState()
        return this.because(
          'I was trying to check the rule ∨-intro',
          async () => {
            try {
              await this.unifyFormula(f, x)
              await this.solve()
            } catch (e) {
              if (e instanceof DetourError) {
                this.restoreState(saveDI)
                return this.unifyFormula(f, y)
              }
              throw e
            }
          })
      }
      case 'DisjElim': {
        if (asserts.length !== 3) throw new DetourError('I saw wrong number or shapes of arguments to the rule ∨-elim.')
        const d0 = asserts[0]!
        const d1 = asserts[1]!
        const d2 = asserts[2]!
        if (d1.k !== 'derived' || d1.a.k !== 'formula' || d1.a.pairs.length !== 1) {
          throw new DetourError('I saw wrong number or shapes of arguments to the rule ∨-elim.')
        }
        if (d2.k !== 'derived' || d2.a.k !== 'formula' || d2.a.pairs.length !== 1) {
          throw new DetourError('I saw wrong number or shapes of arguments to the rule ∨-elim.')
        }
        const disj = this.assertsFormula(d0)
        const x = d1.a.pairs[0]![1]
        const gx = d1.f
        const y = d2.a.pairs[0]![1]
        const gy = d2.f
        await this.because('I was trying to check the rule ∨-elim and it seems that the formula is not even a disjunction.',
          () => this.unifyFormula(disj, { k: 'or', l: x, r: y }))
        await this.because('I was trying to check the rule ∨-elim and it seems that those two sub-proofs don\'t have the same goal.',
          () => this.unifyFormula(gx, gy))
        return this.because('I was trying to check the rule ∨-elim and it seems that the formula is not the same as the goals of those sub-proofs.',
          () => this.unifyFormula(fm, gx))
      }
      case 'NegElim': {
        need(2, '¬-elim')
        if (fm.k !== 'false') throw new DetourError('I saw wrong number or shapes of arguments to the rule ¬-elim.')
        const x = this.assertsFormula(asserts[0]!)
        const y = this.assertsFormula(asserts[1]!)
        return this.because('I was trying to check the rule ¬-elim.',
          async () => {
            const saveNE = this.snapshotState()
            try {
              await this.unifyFormula({ k: 'not', f: x }, y)
              await this.solve()
            } catch (e) {
              if (e instanceof DetourError) {
                this.restoreState(saveNE)
                return this.unifyFormula(x, { k: 'not', f: y })
              }
              throw e
            }
          })
      }
      case 'EquivIntro': {
        need(2, '<==>-intro')
        const ab = this.assertsFormula(asserts[0]!)
        const ba = this.assertsFormula(asserts[1]!)
        const x = this.freshProp()
        const y = this.freshProp()
        await this.because('I was trying to check the rule <==>-intro and it seems that the first argument is not even a concjunction.',
          () => this.unifyFormula(ab, { k: 'impl', l: x, r: y }))
        await this.because('I was trying to check the rule <==>-intro and it seems that the second argument is not even a concjunction.',
          () => this.unifyFormula(ba, { k: 'impl', l: y, r: x }))
        const saveEI = this.snapshotState()
        return this.because(
          'I was trying to check the rule <==>-intro and it seems that the formula is not correct equivalence.',
          async () => {
            try {
              await this.unifyFormula(fm, { k: 'eq', l: x, r: y })
              await this.solve()
            } catch (e) {
              if (e instanceof DetourError) {
                this.restoreState(saveEI)
                return this.unifyFormula(fm, { k: 'eq', l: y, r: x })
              }
              throw e
            }
          })
      }
      case 'EquivElim': {
        need(1, '<==>-elim')
        const eq = this.assertsFormula(asserts[0]!)
        const x = this.freshProp()
        const y = this.freshProp()
        await this.because('I was trying to check the rule <==>-elim.', () => this.unifyFormula(eq, { k: 'eq', l: x, r: y }))
        const saveEE = this.snapshotState()
        return this.because(
          'I was trying to check the rule <==>-elim.',
          async () => {
            try {
              await this.unifyFormula(fm, { k: 'impl', l: x, r: y })
              await this.solve()
            } catch (e) {
              if (e instanceof DetourError) {
                this.restoreState(saveEE)
                return this.unifyFormula(fm, { k: 'impl', l: y, r: x })
              }
              throw e
            }
          })
      }
      case 'TrueIntro': {
        if (fm.k !== 'true') return wrong()
        need(0, '⊤-intro')
        return
      }
      case 'ProofByContradiction': {
        if (asserts.length !== 1) throw new DetourError('I saw wrong number or shapes of arguments to the rule `contradiction\'.')
        const d = asserts[0]!
        if (d.k !== 'derived' || d.a.k !== 'formula' || d.a.pairs.length !== 1 || d.a.pairs[0]![1].k !== 'not') {
          throw new DetourError('I saw wrong number or shapes of arguments to the rule `contradiction\'.')
        }
        if (!this.env.lem) throw new DetourError('Proof by contradiction is disallowed.')
        const a = d.a.pairs[0]![1]
        await this.because('I was trying to check the proof by contradiction and it seems that the goal is not even a ⊥.',
          () => this.unifyFormula({ k: 'false' }, d.f))
        return this.because('I was trying to check the proof by contradiction and it seems that the formula is not a negation of the assumption.',
          () => this.unifyFormula(a.f, fm))
      }
      case 'ContraElim': {
        need(1, '⊥-elim')
        const f = this.assertsFormula(asserts[0]!)
        return this.because('I was trying to check the rule ⊥-elim.', () => this.unifyFormula(f, { k: 'false' }))
      }
      case 'ForallIntro': {
        if (asserts.length !== 1) throw new DetourError('I saw wrong number or shapes of arguments to the rule ∀-intro.')
        const d = asserts[0]!
        if (d.k !== 'derived' || d.a.k !== 'universal') {
          throw new DetourError('I saw wrong number or shapes of arguments to the rule ∀-intro.')
        }
        const body = await this.instantiate(fm, d.a.binds)
        return this.because(`I was trying to check the rule ∀-intro |\n  body ${showFormula(body)}\n\n  formula ${showFormula(d.f)}\n\n  universal ${showFormula(fm)}`,
          () => this.unifyFormula(body, d.f))
      }
      case 'ForallElim': {
        need(1, '∀-elim')
        const u = this.assertsFormula(asserts[0]!)
        return this.unifyWithInstance(u, fm, 'forall')
      }
      case 'ExistsIntro': {
        need(1, '∃-intro')
        const f = this.assertsFormula(asserts[0]!)
        return this.because(`I was trying to check rule ∃-intro justifying \`${showFormula(fm)}'`,
          () => this.unifyWithInstance(fm, f, 'exists'))
      }
      case 'ExistsElim': {
        if (asserts.length !== 2) throw new DetourError('I saw wrong number or shapes of arguments to the rule ∃-elim.')
        const ex = asserts[0]!
        const d = asserts[1]!
        if (d.k !== 'derived' || d.a.k !== 'existential') {
          throw new DetourError('I saw wrong number or shapes of arguments to the rule ∃-elim.')
        }
        const dassum = d.a
        const assum = await this.instantiate(this.assertsFormula(ex), dassum.binds)
        await this.because('I was trying to check the rule ∃-elim.', () => this.unifyFormula(assum, dassum.binding[1]))
        return this.because('I was trying to check the rule ∃-elim.', () => this.unifyFormula(d.f, fm))
      }
      case 'Repetition': {
        need(1, 'repetition')
        const f = this.assertsFormula(asserts[0]!)
        return this.because('I was trying to check the rule repetition.', () => this.unifyFormula(fm, f))
      }
    }
    return wrong()
  }

  // -- theorem / module --
  async checkConclusion(c: Judgment, fm: Formula): Promise<void> {
    if (c.k === 'claim') return this.unifyFormula(c.claim.formula, fm)
    if (c.k === 'prove') return this.unifyFormula(c.formula, fm)
    throw new DetourError('Wrong conclusion.')
  }
  async checkTheorem(t: DTheorem): Promise<void> {
    for (const s of t.propVars) {
      const n = this.freshName()
      await this.unifyFormula(
        { k: 'atom', rel: { k: 'meta', prop: s } },
        { k: 'atom', rel: { k: 'rel', name: n, args: { k: 'terms', args: [] } } })
    }
    const d = this.env.depth
    const frees: string[] = []
    for (const j of t.proof) for (const f of freeVarsJudgment(j)) if (!frees.includes(f)) frees.push(f)
    for (const f of t.assumptions) for (const x of freeVarsFormula(f)) if (!frees.includes(x)) frees.push(x)
    const freePatch = new Map(frees.map((f): [string, number] => [f, d]))
    const typingPatch = new Map<string, TypeScheme>()
    for (const f of frees) typingPatch.set(f, { vars: [], ty: this.freshType() })
    const implUniversals: string[] = [...freeVarsFormula(t.conclusion)]
    for (const f of t.assumptions) for (const x of freeVarsFormula(f)) if (!implUniversals.includes(x)) implUniversals.push(x)
    for (const f of implUniversals) {
      await this.unifyFreeConst(f, this.freshConstant())
    }
    this.st.freeDepth = new Map([...freePatch, ...this.st.freeDepth])
    this.st.typingCtx = new Map([...typingPatch, ...this.st.typingCtx])
    await this.checkAll(t.proof)
    if (t.proof.length === 0) throw new DetourError('Missing conclusion.')
    const last = t.proof[t.proof.length - 1]!
    if (last.k === 'sub') {
      const p = last.proof
      if (p.assum.k === 'universal') {
        throw new DetourError('Introducing universal variables is not allowed in the premise of a theorem proof.')
      }
      if (p.assum.k === 'existential') {
        throw new DetourError('Introducing existential assumptions is not allowed in the premise of a theorem proof.')
      }
      await this.unifyAssertList(t.assumptions.map((f) => ({ k: 'assumed', f } as Assertion)), p.assum.pairs.map(([, f]) => f))
      if (p.ders.length === 0) throw new DetourError('Missing conclusion.')
      const inner = p.ders[p.ders.length - 1]!
      await this.checkConclusion(inner, t.conclusion)
    } else if (last.k === 'claim' || last.k === 'prove') {
      await this.checkConclusion(last, t.conclusion)
    } else {
      throw new DetourError('The last judgment of a theorem needs to be a claim or a proof, not an alias.')
    }
    await this.solve()
  }
  async checkModule(m: DModule): Promise<Array<[string, DetourError | null]>> {
    const patch = new Map(m.axioms.map(([n, fm]): [string, Assertion] => [n, { k: 'axiom', f: fm }]))
    return this.local((e) => ({
      ...e, assertScope: new Map([...e.assertScope, ...patch]),
    }), () => this.tryTheorems(m.theorems, m))
  }
  async tryTheorems(ts: DTheorem[], m: DModule): Promise<Array<[string, DetourError | null]>> {
    if (ts.length === 0) return []
    const [th, ...rest] = ts as [DTheorem, ...DTheorem[]]
    const res = await this.tryTheorem(th, m)
    if (res[1] !== null) {
      return [res, ...(await this.tryTheorems(rest, m))]
    }
    this.env.theorems = new Map([...this.env.theorems, [res[0], th]])
    return [res, ...(await this.tryTheorems(rest, m))]
  }
  async tryTheorem(th: DTheorem, m: DModule): Promise<[string, DetourError | null]> {
    this.cleanState(m)
    const r = await this.tryError(() => this.local((e) => ({ ...e, currentTheorem: th.name }), () => this.checkTheorem(th)))
    if (r.k === 'left') return [th.name, r.err]
    return [th.name, null]
  }
  cleanState(m: DModule): void {
    const tctx = new Map<string, TypeScheme>()
    for (const [n, ts] of m.constants) tctx.set(n, ts)
    for (const [, syn] of m.syntax) {
      for (const c of syn) {
        if (tctx.has(c.name)) {
          throw new DetourError('Constants section might not define syntax constructors.')
        }
      }
    }
    for (const [tn, syn] of m.syntax) {
      for (const c of syn) {
        tctx.set(c.name, {
          vars: [],
          ty: c.args.reduceRight((acc: DType, t): DType => ({ k: 'fn', a: t, b: acc }), { k: 'const', name: tn }),
        })
      }
    }
    this.st.counter = 0
    this.st.termC = []
    this.st.formulaC = []
    this.st.typeC = []
    this.st.freeDepth = new Map()
    this.st.rigidDepth = new Map()
    this.st.typingCtx = tctx
    this.st.judgments = m.judgments
    this.st.syntax = m.syntax.map(([n, s]): [string, Ctor[]] => [n, s])
  }
}

// __PART4I_DSHOW__
// Derived (structural) Show replicas — used only inside search-trace output
// (the `I had a goal ...` inform and case-analysis errors), mirroring the
// Haskell `deriving Show` output rather than the pretty printers above.

function dStr(s: string): string {
  return JSON.stringify(s)
}
function dShowFree(f: string): string {
  return `F ${dStr(f)}`
}
function dShowRigid(r: string): string {
  return `R ${dStr(r)}`
}
function dShowBound(b: string): string {
  return `B ${dStr(b)}`
}
function dShowConst(c: string): string {
  return `C ${dStr(c)}`
}
function dShowProp(p: string): string {
  return `Prop'Var ${dStr(p)}`
}
function dShowType(t: DType): string {
  if (t.k === 'const') return `Type'Const ${dStr(t.name)}`
  if (t.k === 'var') return `Type'Var ${dStr(t.name)}`
  return `Type'Fn (${dShowType(t.a)}) (${dShowType(t.b)})`
}
function dShowScheme(s: TypeScheme): string {
  return `Forall'T [${s.vars.map(dStr).join(', ')}] (${dShowType(s.ty)})`
}
function dShowTerm(t: Term): string {
  if (t.k === 'bound') return `Bound (${dShowBound(t.name)})`
  if (t.k === 'app') return `App (${dShowConst(t.c)}) [${t.args.map(dShowTerm).join(', ')}]`
  if (t.k === 'free') return `Var (Free (${dShowFree(t.name)}))`
  return `Var (Rigid (${dShowRigid(t.name)}))`
}
function dShowRelArgs(a: RelArgs): string {
  return a.k === 'terms'
    ? `RL'Terms [${a.args.map((x) => dShowTerm(x as Term)).join(', ')}]`
    : `RL'Formulae [${a.args.map((x) => dShowFormula(x as Formula)).join(', ')}]`
}
function dShowRel(r: Relation): string {
  return r.k === 'meta' ? `Meta'Rel (${dShowProp(r.prop)})` : `Rel ${dStr(r.name)} (${dShowRelArgs(r.args)})`
}
function dShowFormula(f: Formula): string {
  switch (f.k) {
    case 'true': return 'True'
    case 'false': return 'False'
    case 'atom': return `Atom (${dShowRel(f.rel)})`
    case 'not': return `Not (${dShowFormula(f.f)})`
    case 'and': return `And (${dShowFormula(f.l)}) (${dShowFormula(f.r)})`
    case 'or': return `Or (${dShowFormula(f.l)}) (${dShowFormula(f.r)})`
    case 'impl': return `Impl (${dShowFormula(f.l)}) (${dShowFormula(f.r)})`
    case 'eq': return `Eq (${dShowFormula(f.l)}) (${dShowFormula(f.r)})`
    case 'forall': return `Forall ((${dStr(f.name)},${dShowScheme(f.ts)})) (${dShowFormula(f.body)})`
    case 'exists': return `Exists ((${dStr(f.name)},${dShowScheme(f.ts)})) (${dShowFormula(f.body)})`
  }
}
function dShowBinding(b: Binding): string {
  switch (b.k) {
    case 'free': return `Free'2'Term (${dShowFree(b.name)}) (${dShowTerm(b.term)})`
    case 'rigid': return `Rigid'2'Term (${dShowRigid(b.name)}) (${dShowTerm(b.term)})`
    case 'bound': return `Bound'2'Term (${dShowBound(b.name)}) (${dShowTerm(b.term)})`
    case 'prop': return `Prop'2'Formula (${dShowProp(b.name)}) (${dShowFormula(b.formula)})`
    case 'type': return `Meta'2'Type ${dStr(b.name)} (${dShowType(b.ty)})`
  }
}
function dShowList<T>(xs: T[], fn: (x: T) => string): string {
  return `[${xs.map(fn).join(', ')}]`
}
function dShowCtor(c: Ctor): string {
  return `Constructor ${dStr(c.name)} [${c.args.map(dShowType).join(', ')}]`
}
// --------------------------------------------------------------- engine ---

export class DetourEngine implements Engine {
  readonly id = 'detour'
  private files = new Map<string, string>()
  private editorContent = ''
  private lem = false
  private checker: Checker | null = null
  private runActive = false
  private runInterrupted = false
  private epoch = 0
  private paused: { resume: (c: DetourCmd) => void; reject: (e: Error) => void } | null = null
  private pausedCtx: DetourCtx | null = null
  private pausedGoal: Formula | null = null
  private pasteBuf: string[] = []
  private outbox: string[] = []
  private wake: (() => void) | null = null

  private driver: DetourDriver = {
    inform: (ctx, msg) => {
      if (!this.checker) return
      this.outbox.push(['', `I am solving a theorem \`${ctx.theorem}'`, msg].join('\n'))
    },
    askNext: (ctx, goal) => {
      if (!this.checker) return Promise.reject(new AbortError())
      this.outbox.push(['', `I am solving a theorem \`${ctx.theorem}'`, ...[...ctx.proofCtx].reverse(), `My current goal is: \`${showFormula(goal)}'`].join('\n'))
      return new Promise<DetourCmd>((resolve, reject) => {
        this.paused = { resume: resolve, reject }
        this.pausedCtx = ctx
        this.pausedGoal = goal
        if (this.wake) {
          const w = this.wake
          this.wake = null
          w()
        }
      })
    },
  }

  banner(): string {
    return [
      'Detour — mixed-initiative proof assistant for first-order logic.',
      'Commands: `:load FILE` check it (you may be asked for guidance) · `:lem` / `:no-lem` classical rule · `:q` quit',
      'While proving: Enter = carry on · `list theorems` / `list locals` + Enter · paste proof lines, blank line submits · `:q` abandons the check',
    ].join('\n')
  }
  prompt(): string {
    return this.paused ? '> ' : 'detour> '
  }
  editorAliases(): string[] {
    return ['editor.dt', 'demo.dt', 'editor', 'demo']
  }
  provideFile(name: string, content: string): void {
    this.files.set(name, content.replace(/\r\n?/g, '\n'))
  }
  dropFile(name: string): void {
    this.files.delete(name)
  }
  setEditorContent(content: string): void {
    this.editorContent = content.replace(/\r\n?/g, '\n')
  }
  restart(): void {
    this.epoch++
    this.pasteBuf = []
    this.outbox = []
    this.paused = null
    this.pausedCtx = null
    this.pausedGoal = null
    if (this.checker) this.checker.aborted = true
    this.checker = null
    this.runActive = false
    this.runInterrupted = false
  }
  interrupt(): void {
    if (this.checker && this.runActive && !this.paused) this.checker.aborted = true
  }

  private resolveLoad(path: string): string | null {
    const name = path.trim()
    if (!name) return null
    const hit = this.files.get(name) ?? this.files.get(name.split('/').pop()!)
    if (hit !== undefined) return hit
    if (this.editorAliases().includes(name) || this.editorAliases().includes(name.split('/').pop()!)) {
      return this.editorContent
    }
    return null
  }
  private flush(): string {
    const out = this.outbox.join('\n')
    this.outbox = []
    return out
  }
  private settle(): Promise<void> {
    if (!this.runActive || this.paused) return Promise.resolve()
    return new Promise<void>((res) => {
      this.wake = res
    })
  }
  private startRun(mod: DModule): void {
    const ep = this.epoch
    this.runActive = true
    this.runInterrupted = false
    this.checker = new Checker(this.driver, this.lem)
    void (async () => {
      try {
        const results = await this.checker!.checkModule(mod)
        if (ep !== this.epoch) return
        for (const [name, err] of results) {
          if (err) this.outbox.push(`❌ theorem \`${name}' failed because\n${err.msg}`)
          else this.outbox.push(`✅ theorem \`${name}' checked successfully`)
        }
        if (results.every(([, e]) => e === null)) this.outbox.push('\n✅ The whole module checked successfully.')
      } catch (e) {
        if (ep !== this.epoch) return
        if (e instanceof AbortError) {
          this.outbox.push('Interrupted.')
          this.runInterrupted = true
        } else if (e instanceof DetourError) {
          this.outbox.push(`❌ ${e.msg}`)
        } else {
          this.outbox.push(`Internal error: ${e instanceof Error ? e.message : String(e)}`)
        }
      } finally {
        // always release waiters, even when superseded by restart()/abandon
        this.runActive = false
        this.checker = null
        if (this.wake) {
          const w = this.wake
          this.wake = null
          w()
        }
      }
    })()
  }

  async handle(rawLine: string): Promise<EngineResult> {
    const line = rawLine.replace(/\r$/, '')
    if (this.paused) {
      const t = line.trim()
      if (t === ':q' || t === ':exit') {
        this.epoch++
        const r = this.paused.reject
        this.paused = null
        this.pausedCtx = null
        this.pausedGoal = null
        this.pasteBuf = []
        this.runActive = false
        this.checker = null
        r(new AbortError())
        const out = this.flush()
        return { output: out ? `${out}\n-- check abandoned.` : '-- check abandoned.' }
      }
      if (t === '') {
        const submitted = this.pasteBuf.join('\n')
        this.pasteBuf = []
        const tt = submitted.trim()
        if (tt === 'list theorems' || tt === 'list locals') {
          const ctx = this.pausedCtx
          if (ctx && this.checker) {
            const lines = tt === 'list theorems'
              ? sortedEntries(this.checker.env.theorems).map(([n, th]) => `(${JSON.stringify(n)},${showTheorem(th)})`)
              : sortedEntries(this.checker.env.assertScope).map(([n, a]) => `(${JSON.stringify(n)},${showAssertion(a)})`)
            this.outbox.push(`${tt === 'list theorems' ? 'Proven theorems:' : 'Local assertions:'}\n${lines.join('\n')}`)
            const goal = this.pausedGoal
            if (goal) {
              this.outbox.push(['', `I am solving a theorem \`${ctx.theorem}'`, ...[...ctx.proofCtx].reverse(), `My current goal is: \`${showFormula(goal)}'`].join('\n'))
            }
          }
          return { output: this.flush() }
        }
        const cmd: DetourCmd = tt === '' ? { k: 'idk' } : { k: 'assert', src: submitted }
        const r = this.paused.resume
        this.paused = null
        this.pausedCtx = null
        this.pausedGoal = null
        r(cmd)
        await this.settle()
        if (this.paused) return { output: this.flush() }
        const interrupted = this.runInterrupted
        this.runInterrupted = false
        return { output: this.flush(), interrupted: interrupted || undefined }
      }
      this.pasteBuf.push(line)
      return { output: '' }
    }

    const cmd = line.trim()
    if (cmd === ':q' || cmd === ':exit') return { output: 'Bye!', halted: true }
    const loadArg = /^\s*:(?:load|l)\b\s*/.exec(line)
    if (loadArg) {
      const arg = line.slice(loadArg[0].length).trim()
      const found = this.resolveLoad(arg)
      if (found === null) {
        return { output: `Could not load \`${arg}': no such virtual file (pick an example from the sidebar or save your own).` }
      }
      let mod: DModule
      try {
        mod = parseDetourModule(found)
      } catch (e) {
        const msg = e instanceof Error ? e.message : String(e)
        return { output: `error at ${arg}:${msg}` }
      }
      this.outbox.push(`Checking module \`${mod.name}'\n`)
      this.startRun(mod)
      await this.settle()
      if (this.paused) return { output: this.flush() }
      const interrupted = this.runInterrupted
      this.runInterrupted = false
      return { output: this.flush(), interrupted: interrupted || undefined }
    }
    if (cmd === ':lem') {
      this.lem = true
      return { output: 'Classical rule proof-by-contradiction allowed (--lem).' }
    }
    if (cmd === ':no-lem') {
      this.lem = false
      return { output: 'Classical rule proof-by-contradiction disallowed (default --no-lem).' }
    }
    if (cmd.startsWith(':')) return { output: "I don't know this command, sorry." }
    if (cmd === '') return { output: '' }
    return { output: 'Type `:load FILE` to check a module (see the sidebar). `prove` goals run inside a checked file.' }
  }
}
