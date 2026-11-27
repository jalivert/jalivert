import { MinilogEngine } from '../src/engines/minilog'
import { ResinEngine } from '../src/engines/resin'
import { PloverEngine } from '../src/engines/plover'
import { SimplyEngine } from '../src/engines/simply'
import { SystemFEngine } from '../src/engines/systemf'
import { DependentlyEngine } from '../src/engines/dependently'
import { FreaEngine } from '../src/engines/frea'
import { DetourEngine } from '../src/engines/detour'
import { lexGlaskRaw, parseGlaskModule, parseGlaskExpr, parseGlaskDecls, parseGlaskType, type GTok } from '../src/engines/glask'
import { GlaskEngine } from '../src/engines/glask'
import * as fs from 'fs'
import * as path from 'path'

// Resolved from the working directory: `npm run test:engines` always runs
// with cwd set to the package root, locally and on CI. (A hardcoded absolute
// path used to live here and broke every CI run.)
const VENDOR = path.resolve('vendor')
const readVendor = (p: string): string => fs.readFileSync(`${VENDOR}/${p}`, 'utf8')

async function main(): Promise<void> {
let failures = 0
const check = (name: string, cond: boolean, extra = '') => {
  if (cond) console.log(`ok   ${name}`)
  else { failures++; console.log(`FAIL ${name} ${extra}`) }
}

// ---------------- Minilog ----------------
{
  const m = new MinilogEngine()
  let r = await m.handle(':load nosuch.pl')
  check('minilog unknown file errors', /no such virtual file/.test(r.output), r.output)
  m.setEditorContent('plus(z, N, N).\nplus(s(N), M, s(R)) :- plus(N, M, R).\n')
  m.provideFile('empty.pl', '')
  r = await m.handle(':load empty.pl')
  check('minilog empty file loads as empty base (faithful)', /loaded 0 clause/.test(r.output), r.output)
  m.provideFile('demo.pl', 'plus(z, N, N).\nplus(s(N), M, s(R)) :- plus(N, M, R).\n')
  r = await m.handle(':load demo.pl')
  check('minilog load', /loaded 2 clause/.test(r.output), r.output)
  r = await m.handle('plus(s(z), s(z), R).')
  check('minilog plus', /R = s\(s\(z\)\)/.test(r.output), r.output)
  r = await m.handle('X = foo(X).')
  check('minilog occurs-check rejects', /False/.test(r.output), r.output)
  r = await m.handle('plus(N, M, s(s(z))).')
  check('minilog first solution offers more', /N = z/.test(r.output) && /more solutions/.test(r.output), r.output)
  r = await m.handle(':next')
  check('minilog :next continues', /or/.test(r.output) && /N = s\(z\)/.test(r.output), r.output)
  r = await m.handle(':next')
  check('minilog third solution (more pending in bt, faithful)', /or/.test(r.output) && /N = s\(s\(z\)\)/.test(r.output) && /more solutions/.test(r.output), r.output)
  r = await m.handle(':done')
  check('minilog :done stops', r.output === '.', JSON.stringify(r.output))
  r = await m.handle(':bogus')
  check('minilog unknown cmd', /don't know/.test(r.output), r.output)
  // Ctrl+C: interrupt a diverging query, program (and base) stays alive
  m.provideFile('loop.pl', 'loop :- loop.\n')
  r = await m.handle(':load loop.pl')
  const pending = m.handle('loop.')
  m.interrupt()
  const ri = await pending
  check('minilog interrupt halts search', ri.interrupted === true && ri.output === 'Interrupted.', ri.output)
  r = await m.handle('X = z.')
  check('minilog alive after interrupt', /X = z/.test(r.output), r.output)
  r = await m.handle(':q')
  check('minilog quit halts', r.halted === true && /Bye/.test(r.output), r.output)
}

// ---------------- Resin ----------------
{
  const g = new ResinEngine()
  check('resin prompt', g.prompt() === '⊤ ⊢ ', JSON.stringify(g.prompt()))
  let r = await g.handle('P(aᶜ) ==> P(aᶜ)')
  check('resin tautology entails', /✅/.test(r.output), r.output)
  r = await g.handle(':assume A ==> B')
  check('resin assume silent', r.output === '', JSON.stringify(r.output))
  r = await g.handle(':assume A')
  r = await g.handle('B')
  check('resin modus ponens', /✅/.test(r.output), r.output)
  r = await g.handle(':show')
  check('resin show', /A.*∧.*A ==> B/.test(r.output), r.output)
  r = await g.handle(':consistent')
  check('resin consistent', /logically consistent/.test(r.output), r.output)
  r = await g.handle(':clear')
  r = await g.handle(':show')
  check('resin clear', r.output === '⊤', JSON.stringify(r.output))
  r = await g.handle(':nnf NOT (A AND B)')
  check('resin nnf', r.output === '(¬A) ∨ (¬B)', r.output)
  r = await g.handle(':pnf forall x P(x) AND Q(aᶜ)')
  check('resin pnf', /∀/.test(r.output), r.output)
  r = await g.handle(':cnf A ==> B')
  check('resin cnf', r.output === '(¬A) ∨ B', JSON.stringify(r.output))
  // module check (starter)
  g.setEditorContent(`constants: zero .
aliases: 0 = zero .
axioms: Nat(0), forall n Nat(n) ==> Nat(suc(n)) .
theorem one-is-nat: Nat(suc(0)) .
theorem some-nats: exists n Nat(n) .
`)
  g.provideFile('demo.rin', `constants: zero .
aliases: 0 = zero .
axioms: Nat(0), forall n Nat(n) ==> Nat(suc(0)) .
theorem one-is-nat: Nat(suc(0)) .
theorem some-nats: exists n Nat(n) .
`)
  r = await g.handle(':check demo.rin')
  check(
    'resin check module',
    /✅ theorem `one-is-nat` is logically valid/.test(r.output) && /✅ theorem `some-nats` is logically valid/.test(r.output),
    r.output,
  )
  // proof + using
  const th = `theorem double-prop-modus-ponens: (a-b: A ==> B), B ==> C, (a: A) ⊢ C
proof: lemma have-b: B using { a-b, a }, lemma have-c: C . using { have-c }`
  g.setEditorContent(th)
  g.provideFile('demo.rin', th)
  r = await g.handle(':check demo.rin')
  check('resin proof+using', /✅ theorem `double-prop-modus-ponens` is logically valid/.test(r.output), r.output)
  // regression: vendored parity (the reported `fact.rin` mismatch was a
  // prover-divergence bug: duplicate-literal keys + unordered search space)
  const gFact = new ResinEngine()
  gFact.provideFile('fact.rin', readVendor('resin/fact.rin'))
  r = await gFact.handle(':check fact.rin')
  check(
    'resin fact.rin all valid',
    /✅ theorem `fact-0-is-1` is logically valid/.test(r.output) &&
      /✅ theorem `fact-1-is-1` is logically valid/.test(r.output) &&
      !/not logically valid/.test(r.output),
    r.output,
  )
  const gCur = new ResinEngine()
  gCur.provideFile('curiosity.rin', readVendor('resin/curiosity.rin'))
  r = await gCur.handle(':check curiosity.rin')
  check(
    'resin curiosity.rin all valid',
    /✅ theorem `did-curiosity-kill-cat` is logically valid/.test(r.output) &&
      /✅ theorem `curiosity-is-monster-implies-jack/.test(r.output) &&
      !/not logically valid/.test(r.output),
    r.output,
  )
  const gMan = new ResinEngine()
  gMan.provideFile('manual.rin', readVendor('resin/manual.rin'))
  r = await gMan.handle(':check manual.rin')
  check(
    'resin manual.rin parity (no-simple rejected upstream too)',
    /✅ theorem `some-simple` is logically valid/.test(r.output) &&
      /❌ theorem `no-simple` is not logically valid/.test(r.output),
    r.output,
  )
  r = await g.handle(':q')
  check('resin quit halts', r.halted === true, r.output)
  // interrupt flag hygiene: stray interrupt must not poison the next query
  g.interrupt()
  r = await g.handle('A ==> A')
  check('resin alive after stray interrupt', /✅/.test(r.output), r.output)
}

// ---------------- Plover ----------------
{
  const p = new PloverEngine()
  p.provideFile('natural.pl', readVendor('plover/natural.pl'))
  p.provideFile('natural.nad', readVendor('plover/natural.nad'))
  p.provideFile('factorial.pl', readVendor('plover/factorial.pl'))
  p.provideFile('factorial.nad', readVendor('plover/factorial.nad'))
  p.provideFile('backtrack.pl', readVendor('plover/backtrack.pl'))
  let r = await p.handle(':load nosuch.pl')
  check('plover unknown file errors', /no such virtual file/.test(r.output), r.output)
  // BFS finds solutions despite the rule coming first (Minilog would loop)
  r = await p.handle(':load natural.pl')
  check('plover load pl', /loaded 2 clause/.test(r.output), r.output)
  r = await p.handle('nat(N).')
  check('plover bfs first solution', /^N = z/.test(r.output) && /more solutions/.test(r.output), r.output)
  r = await p.handle(':next')
  check('plover bfs second solution', /or/.test(r.output) && /N = s\(z\)/.test(r.output), r.output)
  r = await p.handle(':done')
  check('plover :done stops', r.output === '.', JSON.stringify(r.output))
  r = await p.handle('foo(bar).')
  check('plover unknown predicate', /Unknown predicate: foo\/1\./.test(r.output), r.output)
  // natural-deduction syntax, selected by .nad suffix
  r = await p.handle(':load natural.nad')
  check('plover load nad', /loaded 2 clause/.test(r.output), r.output)
  r = await p.handle('is-nat(N)')
  check('plover nad query', /^N = z/.test(r.output) && /more solutions/.test(r.output), r.output)
  r = await p.handle(':done')
  r = await p.handle(':load factorial.nad')
  r = await p.handle('fact(s(s(z)), R)')
  check('plover nad factorial', /R = s\(s\(z\)\)/.test(r.output), r.output)
  r = await p.handle(':done')
  // occurs-check still strict
  r = await p.handle(':load factorial.pl')
  r = await p.handle('X = foo(X).')
  check('plover occurs-check rejects', /False\./.test(r.output), r.output)
  r = await p.handle(':q')
  check('plover quit halts', r.halted === true && /Bye/.test(r.output), r.output)
}

// ---------------- lambda-pie: simply ----------------
{
  const s = new SimplyEngine()
  check('simply prompt', s.prompt() === 'λ-> >> ', JSON.stringify(s.prompt()))
  let r = await s.handle('assume (id :: T -> T) (T :: *) (Bool :: *) (a :: T) (b :: T) (c :: Bool)')
  check('simply assume silent', r.output === '', JSON.stringify(r.output))
  r = await s.handle('id a')
  check('simply id a', r.output === '       (id a) :: T', JSON.stringify(r.output))
  r = await s.handle('id b')
  check('simply id b', r.output === '       (id b) :: T', JSON.stringify(r.output))
  r = await s.handle('((\\ (x :: T) -> x) (a :: T))')
  check('simply beta', r.output === '       a :: T', JSON.stringify(r.output))
  r = await s.handle('((\\ (x :: T) -> x) (c :: Bool))')
  check('simply type error', /Type Error: Type mismatch/.test(r.output), r.output)
  r = await s.handle('(\\ x -> x)')
  check('simply unannotated lambda', /Can't infer a type of an unannotated/.test(r.output), r.output)
  r = await s.handle('foo')
  check('simply unknown identifier', /Unknown identifier/.test(r.output), r.output)
  r = await s.handle('(((')
  check('simply parse error', /Parse Error: Parse error/.test(r.output), r.output)
  r = await s.handle(':exit')
  check('simply exit halts', r.halted === true && r.output === '', JSON.stringify(r.output))
}

// ---------------- lambda-pie: systemf ----------------
{
  const s = new SystemFEngine()
  check('systemf prompt', s.prompt() === 'λ2 >> ', JSON.stringify(s.prompt()))
  let r = await s.handle('(/\\ T . (\\ (t :: T) -> t))')
  check('systemf poly id', r.output === '      <type lambda> :: (forall T . (T -> T))', JSON.stringify(r.output))
  r = await s.handle('assume (Nat :: *) (fst :: forall T . T -> T -> T) (snd :: forall T . T -> T -> T)')
  check('systemf assume silent', r.output === '', JSON.stringify(r.output))
  r = await s.handle('assume pickone :: (forall T . T -> T -> T) -> (forall T . T -> T -> T) -> (forall T . T -> T -> T)')
  r = await s.handle('pickone fst snd')
  check('systemf pickone', r.output === '      ((pickone fst) snd) :: (forall T . (T -> (T -> T)))', JSON.stringify(r.output))
  r = await s.handle('((/\\ T . (\\ (t :: T) -> t)) [Nat])')
  check('systemf type application', r.output === '      <lambda> :: (Nat -> Nat)', JSON.stringify(r.output))
  r = await s.handle('((\\ (x :: T) -> x) (a :: Bool))')
  check('systemf type error', /Type Error/.test(r.output), r.output)
  r = await s.handle(':exit')
  check('systemf exit halts', r.halted === true && r.output === '', JSON.stringify(r.output))
}

// ---------------- lambda-pie: dependently ----------------
{
  const s = new DependentlyEngine()
  check('dep prompt', s.prompt() === 'λΠ >> ', JSON.stringify(s.prompt()))
  let r = await s.handle('(lambda t x -> x) :: (forall (t :: *) . (forall (x :: t) . t))')
  check('dep poly id', r.output === '      (λ t -> (λ x -> x)) :: (Π t :: * . (Π x :: t . t))', JSON.stringify(r.output))
  r = await s.handle('assume (Bool :: *)')
  check('dep assume silent', r.output === '', JSON.stringify(r.output))
  r = await s.handle('(lambda x -> x) :: (forall (t :: Bool) . Bool)')
  check('dep bool id', r.output === '      (λ x -> x) :: (Π t :: Bool . Bool)', JSON.stringify(r.output))
  r = await s.handle('*')
  check('dep star', r.output === '      * :: *', JSON.stringify(r.output))
  r = await s.handle('(lambda x -> x) :: Bool')
  check('dep mismatch', /Type mismatch/.test(r.output), r.output)
  r = await s.handle('nope')
  check('dep unknown', /Unknown identifier/.test(r.output), r.output)
  r = await s.handle(':exit')
  check('dep exit halts', r.halted === true && r.output === '', JSON.stringify(r.output))
}

// ---------------- Frea ----------------
{
  const f = new FreaEngine()
  // Frea accumulates lines until an empty line (like the Haskell REPL);
  // only :exit / :load / :q submit immediately.
  const run = async (lines: string[]): Promise<string> => {
    let out = ''
    for (const l of lines) {
      const rr = await f.handle(l)
      if (rr.output !== '') out = rr.output
    }
    return out
  }
  check('frea prompt', f.prompt() === 'frea \u03bb > ', JSON.stringify(f.prompt()))
  let out = await run([':t -23', ''])
  check('frea :t int', out === '         -23 :: Int', JSON.stringify(out))
  out = await run([':t 23.23', ''])
  check('frea :t double', out === '         23.23 :: Double', JSON.stringify(out))
  out = await run([":t 'c'", ''])
  check('frea :t char', out === "         'c' :: Char", JSON.stringify(out))
  out = await run([':t "hello"', ''])
  check('frea :t string', out === '         "hello" :: List Char', JSON.stringify(out))
  out = await run([':t (1, "s", \'c\')', ''])
  check('frea :t tuple', out === "         (1, \"s\", 'c') :: (Int, List Char, Char)", JSON.stringify(out))
  out = await run([':t ()', ''])
  check('frea :t unit', out === '         () :: ()', JSON.stringify(out))
  out = await run([':t (\\ x -> x + 1)', ''])
  check('frea :t lambda', out === '         (\\ x -> x + 1) :: Int -> Int', JSON.stringify(out))
  out = await run(['let { f = \\ x -> x } in (f 1, f True)', ''])
  check('frea let-poly', out === '         (1, True)', JSON.stringify(out))
  out = await run(['if True then 23 else 42', ''])
  check('frea if', out === '         23', JSON.stringify(out))
  out = await run(['let { fact = \\ n -> if n == 0 then 1 else n * (fact (n - 1)) } in fact 5', ''])
  check('frea fact', out === '         120', JSON.stringify(out))
  out = await run(['which-Maybe (Just 42) 0 (\\ x -> x + 1)', ''])
  check('frea which-Maybe', out === '         43', JSON.stringify(out))
  out = await run(['let { double = \\ x -> 2 * x ; map = \\ f lst -> which-List lst [] (\\ h t -> (f h) : (map f t)) } in map double [1, 2, 3]', ''])
  check('frea map', out === '         [2, 4, 6]', JSON.stringify(out))
  out = await run(['let { ones = 1 : ones ; take = \\ n lst -> if n == 0 then [] else which-List lst [] (\\ h t -> h : (take (n - 1) t)) } in take 5 ones', ''])
  check('frea lazy infinite', out === '         [1, 1, 1, 1, 1]', JSON.stringify(out))
  out = await run(['plus 23 42', ''])
  check('frea prelude plus', out === '         65', JSON.stringify(out))
  out = await run(['nnum', ''])
  check('frea prelude nnum', out === '         65', JSON.stringify(out))
  out = await run([':t fact', ''])
  check('frea :t prelude fact', out === '         fact :: Int -> Int', JSON.stringify(out))
  out = await run(['1 + True', ''])
  check('frea type error', /Type Error/.test(out), out)
  out = await run([':k Int -> Bool', ''])
  check('frea :k arrow', out === '         Int -> Bool :: *', JSON.stringify(out))
  out = await run([':k List', ''])
  check('frea :k higher', out === '         List :: * -> *', JSON.stringify(out))
  // `#`-led operators lex like upstream ($symbol includes `#`): unknown ones
  // parse as infix and fail at typecheck, exactly like the Haskell implementation
  out = await run(['1 #: [2]', ''])
  check('frea hash-cons unknown', out === 'Type Error: Unknown variable #:', JSON.stringify(out))
  out = await run(['((#:))', ''])
  check('frea hash-cons paren unknown', out === 'Type Error: Unknown variable #:', JSON.stringify(out))
  out = await run(['1 #foo 2', ''])
  check('frea unknown hash op', out === 'Type Error: Unknown variable #foo', JSON.stringify(out))
  // bare `=` is not an infix operator (upstream rejects `x = 5` at parse)
  out = await run(['x = 5', ''])
  check('frea bare eq rejected', /Parse Error/.test(out), JSON.stringify(out))
  // `#`-led operators cannot start an application (matches upstream rejections)
  out = await run(['(#head [1])', ''])
  check('frea hash prefix rejected', /Parse Error/.test(out), JSON.stringify(out))
  // stale vendor files are rejected by upstream too (no module header / bare let);
  // the TS port must reject them the same way (parse error, not lexical error)
  f.provideFile('basic.frea', readVendor('frea/basic.frea'))
  const rBasic = await f.handle(':load basic.frea')
  check('frea basic rejected like upstream', /Parse error inside module/.test(rBasic.output) && !/Lexical/.test(rBasic.output), JSON.stringify(rBasic.output))
  f.provideFile('module.frea', readVendor('frea/module.frea'))
  const rModule = await f.handle(':load module.frea')
  check('frea module rejected like upstream', /Parse error inside module/.test(rModule.output), JSON.stringify(rModule.output))
  let r2 = await f.handle(':load nosuchfile.frea')
  check('frea :load missing', /Error: cannot open/.test(r2.output), r2.output)
  r2 = await f.handle('let { a = 1')
  check('frea multiline buffers', r2.output === '' && f.prompt() === '         ', JSON.stringify(r2.output) + JSON.stringify(f.prompt()))
  r2 = await f.handle('} in a')
  check('frea multiline continues', r2.output === '' && f.prompt() === '         ', JSON.stringify(r2.output))
  r2 = await f.handle('')
  check('frea multiline evaluates', r2.output === '         1', JSON.stringify(r2.output))
  r2 = await f.handle(':exit')
  check('frea :exit halts', r2.halted === true && r2.output === 'Bye!', JSON.stringify(r2.output))
}

// ---------------- Detour ----------------
{
  const d = new DetourEngine()
  check('detour prompt', d.prompt() === 'detour> ', JSON.stringify(d.prompt()))
  check('detour banner', /Detour/.test(d.banner()), d.banner())
  // drive a :load to completion; answer every What'Next with `answer`
  const drive = async (eng: DetourEngine, file: string, content: string, answer: (goal: string) => string[], cap = 120): Promise<string> => {
    eng.provideFile(file, content)
    let out = (await eng.handle(`:load ${file}`)).output
    let guard = 0
    while (/My current goal is:/.test(out) && guard++ < cap) {
      const m = /My current goal is: `([^`]*)'/.exec(out)
      for (const a of answer(m ? m[1] : '')) {
        const r = await eng.handle(a)
        out = `${out}\n${r.output}`
      }
    }
    return out
  }
  const idk = (_goal: string): string[] => ['']
  let out = await drive(d, 'simplest.dt', readVendor('detour/simplest.dt'), idk)
  check('detour simplest', /✅ theorem `simplest' checked successfully/.test(out) && /The whole module checked successfully/.test(out), out)
  out = await drive(d, 'impl.dt', readVendor('detour/impl.dt'), idk)
  check('detour impl', /✅ theorem `foo' checked successfully/.test(out), out)
  out = await drive(d, 'exists-intro.dt', readVendor('detour/exists-intro.dt'), idk)
  check('detour exists-intro', /✅ theorem `only-some' checked successfully/.test(out), out)
  out = await drive(d, 'axioms.dt', readVendor('detour/axioms.dt'), idk)
  check('detour axioms', /✅ theorem `one' checked successfully/.test(out), out)
  out = await drive(d, 'wrong-exists-intro.dt', readVendor('detour/wrong-exists-intro.dt'), idk)
  check('detour wrong-exists-intro fails', /❌ theorem `wrong' failed because/.test(out) && /∃-intro/.test(out), out)
  const implSrc = readVendor('detour/impl.dt')
  out = await drive(d, 'bad-ident.dt', implSrc.replace('on p, p1', 'on p, nosuch'), idk)
  check('detour unknown identifier', /❌ theorem `foo' failed because/.test(out) && /Unknown identifier/.test(out), out)
  out = await drive(d, 'bad-thm.dt', implSrc.replace('by rule ==>-elim on p, p1', 'by theorem nosuchthm on p, p1'), idk)
  check('detour unknown theorem', /❌ theorem `foo' failed because/.test(out) && /Unknown theorem/.test(out), out)
  out = await drive(d, 'axioms-only.dt', readVendor('detour/axioms-only.dt'), idk)
  check('detour axioms-only vacuous', /The whole module checked successfully/.test(out), out)
  out = await drive(d, 'garbage.dt', 'this is not valid detour @@@ ###', idk)
  check('detour garbage parse error', /^error at garbage\.dt:/.test(out), out)
  const dne = [
    'module dnetest',
    '',
    'theorem dne : ¬(¬(A)) ⊢ A',
    '| nn : ¬(¬(A))',
    '|----------------------------',
    '|',
    '| c : | n : ¬(A)',
    '|     |--------------------------------',
    '|     |',
    '|     | f : ⊥ by rule ¬-elim on nn, n',
    '| A by rule proof-by-contradiction on c',
    '',
  ].join('\n')
  out = await drive(d, 'dne.dt', dne, idk)
  check('detour dne disallowed without lem', /❌ theorem `dne' failed because/.test(out) && /disallowed/.test(out), out)
  {
    const e2 = new DetourEngine()
    e2.provideFile('dne.dt', dne)
    let r2 = await e2.handle(':lem')
    check('detour :lem', /allowed/.test(r2.output), r2.output)
    out = await drive(e2, 'dne.dt', dne, idk)
    check('detour dne allowed with lem', /✅ theorem `dne' checked successfully/.test(out), out)
    r2 = await e2.handle(':no-lem')
    check('detour :no-lem', /disallowed/.test(r2.output), r2.output)
    r2 = await e2.handle(':bogus')
    check('detour unknown cmd', /don't know/.test(r2.output), r2.output)
    r2 = await e2.handle(':q')
    check('detour quit halts', r2.halted === true && r2.output === 'Bye!', JSON.stringify(r2.output))
  }
  // interactive: paste a proof at the prompt (no leading pipes upstream)
  {
    const e3 = new DetourEngine()
    const paste = [
      'module pastetest',
      '',
      'syntax N = Zero',
      '         | Suc(N)',
      '',
      'judgment t = T(N)',
      '',
      'rule schema t-zero for all objects (n : N) :',
      '|',
      '|-------------------------------------- t-zero',
      '| T(Zero)',
      '',
      'theorem tri : T(Suc(Zero))',
      'prove T(Suc(Zero))',
      '',
    ].join('\n')
    let pasted = false
    out = await drive(e3, 'paste.dt', paste, () => {
      if (!pasted) {
        pasted = true
        return ['c : T(Suc(Zero)) by unproved', '']
      }
      return ['']
    })
    check('detour pasted proof asks then checks', pasted && /✅ theorem `tri' checked successfully/.test(out), out)
  }
  // interactive: list commands + abandon
  {
    const e4 = new DetourEngine()
    e4.provideFile('paste.dt', 'module m\n\ntheorem tri : P\nprove P\n')
    let r4 = await e4.handle(':load paste.dt')
    check('detour unknown judgment asks', /My current goal is:/.test(r4.output), r4.output)
    r4 = await e4.handle('list theorems')
    check('detour list buffers', r4.output === '', JSON.stringify(r4.output))
    r4 = await e4.handle('')
    check('detour list theorems', /Proven theorems:/.test(r4.output) && /My current goal is:/.test(r4.output), r4.output)
    r4 = await e4.handle('list locals')
    r4 = await e4.handle('')
    check('detour list locals', /Local assertions:/.test(r4.output), r4.output)
    r4 = await e4.handle(':q')
    check('detour :q abandons check', /abandoned/.test(r4.output) && r4.halted !== true, r4.output)
  }
  // differential outcomes mirrored from the Haskell implementation (all-IDK)
  {
    const e5 = new DetourEngine()
    out = await drive(e5, 'sum-auto.dt', readVendor('detour/sum-auto.dt'), idk)
    check('detour sum-auto n+0=n', /✅ theorem `n\+0=n' checked successfully/.test(out), out)
    check('detour sum-auto M+N=M', /✅ theorem `M\+N=M' checked successfully/.test(out), out)
    check('detour sum-auto total', /✅ theorem `total' checked successfully/.test(out), out)
    check('detour sum-uniq-commutes needs guidance',
      /❌ theorem `sum-uniq-commutes' failed because/.test(out)
      && /didn't find any local assertion/.test(out), out)
    out = await drive(e5, 'sum-uniq.dt', readVendor('detour/sum-uniq.dt'), idk)
    check('detour sum-uniq manual', /✅ theorem `sum-uniq-commutes-manual' checked successfully/.test(out), out)
    out = await drive(e5, 'naturals.dt', readVendor('detour/naturals.dt'), idk)
    check('detour naturals totality', /✅ theorem `totality' checked successfully/.test(out), out)
    out = await drive(e5, 'nmn.dt', readVendor('detour/archive/nmn.dt'), idk)
    check('detour nmn fails like upstream',
      /❌ theorem `N\+M=N' failed because/.test(out)
      && /❌ theorem `M\+N=N' failed because/.test(out), out)
    const e6 = new DetourEngine()
    e6.provideFile('q.dt', readVendor('detour/archive/quantifiers.dt'))
    const r6 = await e6.handle(':load q.dt')
    check('detour legacy header rejected', /^error at q\.dt:/.test(r6.output), r6.output)
  }
}

// ---------------- Glask: lexer ----------------
{
  const shape = (t: GTok): string => {
    switch (t.k) {
      case 'var': return `var:${t.name}`
      case 'con': return `con:${t.name}`
      case 'op': return `op:${t.name}`
      case 'opcon': return `opcon:${t.name}`
      case 'hole': return `hole:${t.name}`
      case 'int': return `int:${t.value}`
      case 'double': return `double:${t.value}`
      case 'char': return `char:${JSON.stringify(t.value)}`
      case 'string': return `string:${JSON.stringify(t.value)}`
      case 'arrow': return 'op:->'
      case 'fatArrow': return 'op:=>'
      case 'eqD': return 'op:='
      case 'pipeD': return 'op:|'
      case 'dotdot': return 'op:..'
      case 'atD': return 'op:@'
      case 'dotD': return 'op:.'
      default: return t.k
    }
  }
  const lexShapes = (src: string): string[] => lexGlaskRaw(src).map(shape)
  const eq = (a: string[], b: string[]): boolean => a.length === b.length && a.every((x, i) => x === b[i])
  check('glask lex keyword', eq(lexShapes('data'), ['data', 'eof']), lexShapes('data').join(' '))
  check('glask lex hole', eq(lexShapes('_'), ['hole:_', 'eof']), lexShapes('_').join(' '))
  check('glask lex lambda', eq(lexShapes('\\'), ['lambda', 'eof']), lexShapes('\\').join(' '))
  check('glask lex hastype', eq(lexShapes('::'), ['hastype', 'eof']), lexShapes('::').join(' '))
  check('glask lex int', eq(lexShapes('23'), ['int:23', 'eof']), lexShapes('23').join(' '))
  check('glask lex neg int glued', eq(lexShapes('-23'), ['int:-23', 'eof']), lexShapes('-23').join(' '))
  check('glask lex spaced minus', eq(lexShapes('- 23'), ['op:-', 'int:23', 'eof']), lexShapes('- 23').join(' '))
  check('glask lex octal', eq(lexShapes('0o17'), ['int:15', 'eof']), lexShapes('0o17').join(' '))
  check('glask lex hex', eq(lexShapes('0xFF'), ['int:255', 'eof']), lexShapes('0xFF').join(' '))
  check('glask lex neg hex', eq(lexShapes('-0xFF'), ['int:-255', 'eof']), lexShapes('-0xFF').join(' '))
  check('glask lex double', eq(lexShapes('3.14'), ['double:3.14', 'eof']), lexShapes('3.14').join(' '))
  check('glask lex double exp', eq(lexShapes('1e+10'), ['double:10000000000', 'eof']), lexShapes('1e+10').join(' '))
  check('glask lex unsigned exp splits', eq(lexShapes('1e10'), ['int:1', 'var:e10', 'eof']), lexShapes('1e10').join(' '))
  check('glask lex char', eq(lexShapes("'a'"), ['char:"a"', 'eof']), lexShapes("'a'").join(' '))
  check('glask lex char escape', eq(lexShapes("'\\n'"), ['char:"\\n"', 'eof']), lexShapes("'\\n'").join(' '))
  check('glask lex string', eq(lexShapes('"hi"'), ['string:"hi"', 'eof']), lexShapes('"hi"').join(' '))
  check('glask lex string escapes', eq(lexShapes('"a\\n\\"b\\\\"'), ['string:"a\\n\\"b\\\\"', 'eof']), lexShapes('"a\\n\\"b\\\\"').join(' '))
  check('glask lex string strip backslash', eq(lexShapes('"a\\qb"'), ['string:"aqb"', 'eof']), lexShapes('"a\\qb"').join(' '))
  check('glask lex opcon colon', eq(lexShapes(':'), ['opcon::', 'eof']), lexShapes(':').join(' '))
  check('glask lex opcon cons', eq(lexShapes(':::'), ['opcon::::', 'eof']), lexShapes(':::').join(' '))
  check('glask lex colon abc splits', eq(lexShapes(':abc'), ['opcon::', 'var:abc', 'eof']), lexShapes(':abc').join(' '))
  check('glask lex operators', eq(lexShapes('=>'), ['op:=>', 'eof']) && eq(lexShapes('->'), ['op:->', 'eof']) && eq(lexShapes('=='), ['op:==', 'eof']) && eq(lexShapes('/='), ['op:/=', 'eof']) && eq(lexShapes('>>='), ['op:>>=', 'eof']), '')
  check('glask lex comment line', eq(lexShapes('-- hello\n42'), ['int:42', 'eof']), lexShapes('-- hello\n42').join(' '))
  check('glask lex comment only', eq(lexShapes('-- just a comment\n'), ['eof']), lexShapes('-- just a comment\n').join(' '))
  check('glask lex empty', eq(lexShapes(''), ['eof']), lexShapes('').join(' '))
  check('glask lex let layout', eq(lexShapes('let a = 0\n    b = 1\nin a'),
    ['let', 'lbrace', 'var:a', 'op:=', 'int:0', 'semi', 'var:b', 'op:=', 'int:1', 'rbrace', 'in', 'var:a', 'eof']),
    lexShapes('let a = 0\n    b = 1\nin a').join(' '))
  check('glask lex continuation', eq(lexShapes('foo = bar\n  + baz'),
    ['var:foo', 'op:=', 'var:bar', 'op:+', 'var:baz', 'eof']),
    lexShapes('foo = bar\n  + baz').join(' '))
  check('glask lex dedent closes', eq(lexShapes('where\n  foo = 23\n'),
    ['where', 'lbrace', 'var:foo', 'op:=', 'int:23', 'rbrace', 'eof']),
    lexShapes('where\n  foo = 23\n').join(' '))
  check('glask lex case alts', eq(lexShapes('case x of\n  A -> 1\n  B -> 2'),
    ['case', 'var:x', 'of', 'lbrace', 'con:A', 'op:->', 'int:1', 'semi', 'con:B', 'op:->', 'int:2', 'rbrace', 'eof']),
    lexShapes('case x of\n  A -> 1\n  B -> 2').join(' '))
  check('glask lex explicit braces', eq(lexShapes('let { a = 0 } in a'),
    ['let', 'lbrace', 'var:a', 'op:=', 'int:0', 'rbrace', 'in', 'var:a', 'eof']),
    lexShapes('let { a = 0 } in a').join(' '))
  check('glask lex comment newline', eq(lexShapes('let a = 0\n-- comment\n    b = 1\nin a'),
    ['let', 'lbrace', 'var:a', 'op:=', 'int:0', 'semi', 'var:b', 'op:=', 'int:1', 'rbrace', 'in', 'var:a', 'eof']),
    lexShapes('let a = 0\n-- comment\n    b = 1\nin a').join(' '))
}

// ---------------- Glask: parser ----------------
{
  const J = (x: unknown): string => JSON.stringify(x)
  check('glask parse var', J(parseGlaskExpr('x')) === J({ k: 'id', id: { k: 'var', name: 'x' } }), J(parseGlaskExpr('x')))
  check('glask parse con', J(parseGlaskExpr('True')) === J({ k: 'id', id: { k: 'con', name: 'True' } }), J(parseGlaskExpr('True')))
  check('glask parse int', J(parseGlaskExpr('23')) === J({ k: 'lit', lit: { k: 'int', v: 23 } }), J(parseGlaskExpr('23')))
  check('glask parse string desugars', J(parseGlaskExpr('"hi"')) === J({ k: 'list', exprs: [{ k: 'lit', lit: { k: 'char', v: 'h' } }, { k: 'lit', lit: { k: 'char', v: 'i' } }] }), J(parseGlaskExpr('"hi"')))
  check('glask parse flat app', J(parseGlaskExpr('f x y')) === J({ k: 'app', exprs: [{ k: 'id', id: { k: 'var', name: 'f' } }, { k: 'id', id: { k: 'var', name: 'x' } }, { k: 'id', id: { k: 'var', name: 'y' } }] }), J(parseGlaskExpr('f x y')))
  check('glask parse flat infix', J(parseGlaskExpr('3 + 5')) === J({ k: 'app', exprs: [{ k: 'lit', lit: { k: 'int', v: 3 } }, { k: 'op', id: { k: 'var', name: '+' } }, { k: 'lit', lit: { k: 'int', v: 5 } }] }), J(parseGlaskExpr('3 + 5')))
  check('glask parse backtick var', J(parseGlaskExpr('f `add` x')) === J({ k: 'app', exprs: [{ k: 'id', id: { k: 'var', name: 'f' } }, { k: 'op', id: { k: 'var', name: 'add' } }, { k: 'id', id: { k: 'var', name: 'x' } }] }), J(parseGlaskExpr('f `add` x')))
  check('glask parse paren op', J(parseGlaskExpr('(+)')) === J({ k: 'op', id: { k: 'var', name: '+' } }), J(parseGlaskExpr('(+)')))
  check('glask parse paren con op', J(parseGlaskExpr('(:)')) === J({ k: 'op', id: { k: 'con', name: ':' } }), J(parseGlaskExpr('(:)')))
  check('glask parse unit', J(parseGlaskExpr('()')) === J({ k: 'id', id: { k: 'con', name: '()' } }), J(parseGlaskExpr('()')))
  check('glask parse tuple', J(parseGlaskExpr('(1, 2)')) === J({ k: 'tuple', exprs: [{ k: 'lit', lit: { k: 'int', v: 1 } }, { k: 'lit', lit: { k: 'int', v: 2 } }] }), J(parseGlaskExpr('(1, 2)')))
  check('glask parse list', J(parseGlaskExpr('[1, 2]')) === J({ k: 'list', exprs: [{ k: 'lit', lit: { k: 'int', v: 1 } }, { k: 'lit', lit: { k: 'int', v: 2 } }] }), J(parseGlaskExpr('[1, 2]')))
  check('glask parse arith seq', J(parseGlaskExpr('[1, 2 .. 10]')) === J({ k: 'arith', lo: { k: 'lit', lit: { k: 'int', v: 1 } }, step: { k: 'lit', lit: { k: 'int', v: 2 } }, hi: { k: 'lit', lit: { k: 'int', v: 10 } } }), J(parseGlaskExpr('[1, 2 .. 10]')))
  check('glask parse if', J(parseGlaskExpr('if True then 1 else 0')) === J({ k: 'if', cond: { k: 'id', id: { k: 'con', name: 'True' } }, then: { k: 'lit', lit: { k: 'int', v: 1 } }, els: { k: 'lit', lit: { k: 'int', v: 0 } } }), J(parseGlaskExpr('if True then 1 else 0')))
  check('glask parse lambda', J(parseGlaskExpr('\\x -> x')) === J({ k: 'abs', pat: { k: 'id', id: { k: 'var', name: 'x' } }, body: { k: 'id', id: { k: 'var', name: 'x' } } }), J(parseGlaskExpr('\\x -> x')))
  check('glask parse case', J(parseGlaskExpr('case xs of { (y : ys) -> y }')) === J({ k: 'case', expr: { k: 'id', id: { k: 'var', name: 'xs' } }, alts: [[{ k: 'app', pats: [{ k: 'id', id: { k: 'var', name: 'y' } }, { k: 'op', id: { k: 'con', name: ':' } }, { k: 'id', id: { k: 'var', name: 'ys' } }] }, { k: 'id', id: { k: 'var', name: 'y' } }]] }), J(parseGlaskExpr('case xs of { (y : ys) -> y }')))
  check('glask parse hole', J(parseGlaskExpr('_hole')) === J({ k: 'hole', name: '_hole' }), J(parseGlaskExpr('_hole')))
  check('glask parse dot app', J(parseGlaskExpr('f . g')) === J({ k: 'app', exprs: [{ k: 'id', id: { k: 'var', name: 'f' } }, { k: 'op', id: { k: 'var', name: '.' } }, { k: 'id', id: { k: 'var', name: 'g' } }] }), J(parseGlaskExpr('f . g')))
  check('glask parse decl binding', J(parseGlaskDecls('num = 42')) === J([{ k: 'binding', pat: { k: 'id', id: { k: 'var', name: 'num' } }, expr: { k: 'lit', lit: { k: 'int', v: 42 } } }]), J(parseGlaskDecls('num = 42')))
  check('glask parse decl op binding', J(parseGlaskDecls('(+) x y = x')) === J([{ k: 'binding', pat: { k: 'app', pats: [{ k: 'id', id: { k: 'var', name: '+' } }, { k: 'id', id: { k: 'var', name: 'x' } }, { k: 'id', id: { k: 'var', name: 'y' } }] }, expr: { k: 'id', id: { k: 'var', name: 'x' } } }]), J(parseGlaskDecls('(+) x y = x')))
  check('glask parse decl sig', J(parseGlaskDecls('f :: Int')) === J([{ k: 'sig', name: 'f', preds: [], ty: { k: 'id', id: { k: 'con', name: 'Int' } } }]), J(parseGlaskDecls('f :: Int')))
  check('glask parse decl data', J(parseGlaskDecls('data Maybe a = Nothing | Just a')) === J([{ k: 'data', name: 'Maybe', params: ['a'], ctors: [{ k: 'con', name: 'Nothing', tys: [] }, { k: 'con', name: 'Just', tys: [{ k: 'id', id: { k: 'var', name: 'a' } }] }] }]), J(parseGlaskDecls('data Maybe a = Nothing | Just a')))
  check('glask parse decl fixity', J(parseGlaskDecls('infixl 5 +')) === J([{ k: 'fixity', fix: 'infix', assoc: 'left', prec: 5, ops: ['+'] }]), J(parseGlaskDecls('infixl 5 +')))
  check('glask parse decl class', J(parseGlaskDecls('class C a')) === J([{ k: 'class', name: 'C', param: 'a', supers: [], decls: [] }]), J(parseGlaskDecls('class C a')))
  check('glask parse decl instance', J(parseGlaskDecls('instance Num Int')) === J([{ k: 'instance', ctx: [], head: { k: 'is', cls: 'Num', ty: { k: 'id', id: { k: 'con', name: 'Int' } } }, decls: [] }]), J(parseGlaskDecls('instance Num Int')))
  check('glask parse type app', J(parseGlaskType('Maybe a')) === J({ k: 'app', tys: [{ k: 'id', id: { k: 'con', name: 'Maybe' } }, { k: 'id', id: { k: 'var', name: 'a' } }] }), J(parseGlaskType('Maybe a')))
  check('glask parse type arrow', J(parseGlaskType('a -> b -> c')) === J({ k: 'arrow', tys: [{ k: 'id', id: { k: 'var', name: 'a' } }, { k: 'arrow', tys: [{ k: 'id', id: { k: 'var', name: 'b' } }, { k: 'id', id: { k: 'var', name: 'c' } }] }] }), J(parseGlaskType('a -> b -> c')))
  check('glask parse type forall', J(parseGlaskType('forall a . a -> a')) === J({ k: 'forall', vars: [{ k: 'var', name: 'a' }], preds: [], ty: { k: 'arrow', tys: [{ k: 'id', id: { k: 'var', name: 'a' } }, { k: 'id', id: { k: 'var', name: 'a' } }] } }), J(parseGlaskType('forall a . a -> a')))
  // golden parse dumps: declaration counts must match the checked-in snapshots,
  // and every brace/layout twin pair must produce identical declarations
  const gPos = `${VENDOR}/glask/examples/positive`
  const twinPairs: Array<[string, number]> = [
    ['annotations/forall', 7], ['classes/class', 6], ['classes/higherkinded', 7],
    ['classes/super', 12], ['data/bool', 5], ['data/records', 6],
    ['evaluate/arith', 3], ['evaluate/lazy', 21], ['evaluate/matching', 67],
    ['layout/basic', 8], ['operators/infix', 11], ['operators/implicit', 25],
    ['operators/prefix', 12], ['operators/prefix-postfix', 12],
    ['prenex/branch', 10], ['prenex/local', 12], ['prenex/nested', 19],
    ['showcase/expr', 31], ['showcase/sieve', 45], ['showcase/rankn', 16],
  ]
  for (const [base, count] of twinPairs) {
    const a = parseGlaskModule(readVendor(`glask/examples/positive/${base}.glask`))
    check(`glask golden ${base} count`, a.length === count, `${a.length}`)
    if (base === 'layout/basic') continue // no .layout twin exists
    const b = parseGlaskModule(readVendor(`glask/examples/positive/${base}.layout.glask`))
    check(`glask layout twin ${base}`, J(a) === J(b), `${J(a).length} vs ${J(b).length}`)
  }
  void gPos
}

// ---------------- Glask: engine (REPL + :load + dictionary elaboration) ----------------
{
  // Mirror the upstream golden REPL transcripts (test/golden/repl/*.golden):
  // each query is submitted, then an empty line submits the buffer.
  const runScript = async (file: string, queries: string[]): Promise<string[]> => {
    const e = new GlaskEngine('')
    e.provideFile('t.glask', readVendor(file))
    const l = await e.handle(':load t.glask')
    if (l.output !== '') return [`LOAD-ERR: ${l.output}`]
    const outs: string[] = []
    for (const q of queries) {
      const r1 = await e.handle(q)
      if (r1.output !== '') { outs.push(r1.output); continue }
      outs.push((await e.handle('')).output)
    }
    return outs
  }
  const eqLines = (a: string[], b: string[]): boolean => a.length === b.length && a.every((x, i) => x === b[i])
  const goldenRepl: Array<[string, string, string[]]> = [
    ['arith-errors', 'glask/examples/positive/evaluate/arith.glask', [":t unknown'var", '2 + 3', ':t True', ':q']],
    ['nested-eval', 'glask/examples/positive/prenex/nested.glask', ['f 1 2', 'apply inc 3', 'g 0 5', "t'double'ann", ':q']],
    ['nested-introspect', 'glask/examples/positive/prenex/nested.glask', [':t inc', ':p apply inc 3', ':k Int', ':q']],
    ['branch-introspect', 'glask/examples/positive/prenex/branch.glask', [':t br1', ":t t'if'then", ':p if True then 1 else 2', ':q']],
    ['lazy-introspect', 'glask/examples/positive/evaluate/lazy.glask', [':t length', ':t take', ':p take 2 [1]', ':k Bool', ':q']],
    ['showcase-expr', 'glask/examples/positive/showcase/expr.glask', ["answer'int", 'check', ":t answer'expr", ':q']],
    ['showcase-rankn', 'glask/examples/positive/showcase/rankn.glask', ["first'both", ":t apply'both", ':t both', ':q']],
    ['showcase-sieve', 'glask/examples/positive/showcase/sieve.glask', ["at 9 first'primes", ':t sieve', ':t divides', ':q']],
  ]
  for (const [name, file, queries] of goldenRepl) {
    const expected = readVendor(`glask/test/golden/repl/${name}.golden`).split('\n')
    if (expected.length > 0 && expected[expected.length - 1] === '') expected.pop()
    const outs = await runScript(file, queries)
    check(`glask repl ${name}`, eqLines(outs, expected), `\n got: ${JSON.stringify(outs)}\n exp: ${JSON.stringify(expected)}`)
  }
  // arith-introspect golden includes :c/:d (whose dict-passing shape differs
  // by design, see below); compare the :t/:p/:k/:q lines only.
  {
    const golden = readVendor('glask/test/golden/repl/arith-introspect.golden').split('\n')
    const outs = await runScript('glask/examples/positive/evaluate/arith.glask', [':t 2 + 3', ':p 2 + 3', ':k Int', ':q'])
    check('glask repl arith-introspect', eqLines(outs, [golden[0]!, golden[1]!, golden[2]!, golden[7]!]), `\n got: ${JSON.stringify(outs)}`)
  }
  // :c/:d show elaborated core without dictionary passing (documented
  // deviation: mangled static instances instead of `op dict args` shape).
  {
    const outs = await runScript('glask/examples/positive/evaluate/arith.glask', [':c 2 + 3', ':d 2 + 3', ':q'])
    check('glask :c shows core', outs[0] === 'Core:\nd-Num-Int-_plus_ 2 3', JSON.stringify(outs[0]))
    check('glask :d shows desugared', outs[1] === 'Desugared:\nd-Num-Int-_plus_ 2 3', JSON.stringify(outs[1]))
    check('glask :q quits', outs[2] === 'Bye!', JSON.stringify(outs[2]))
  }
  // all positive examples load; layout twins are covered by the parser tests
  {
    const walk = (dir: string): string[] => {
      const out: string[] = []
      for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
        const p = path.join(dir, e.name)
        if (e.isDirectory()) out.push(...walk(p))
        else if (e.name.endsWith('.glask')) out.push(p)
      }
      return out
    }
    const files = walk(`${VENDOR}/glask/examples/positive`).sort()
    let loaded = 0
    let firstErr = ''
    for (const f of files) {
      const e = new GlaskEngine('')
      e.provideFile('t.glask', fs.readFileSync(f, 'utf8'))
      const r = await e.handle(':load t.glask')
      if (r.output === '') loaded++
      else if (firstErr === '') firstErr = `${path.relative(VENDOR, f)}: ${r.output.slice(0, 120)}`
    }
    check(`glask all positive examples load (${loaded}/${files.length})`, loaded === files.length, firstErr)
  }
  // interrupt + quit hygiene (self-contained looping program)
  {
    const e = new GlaskEngine('')
    e.provideFile('t.glask', [
      'module Main where',
      '{ data Bool = True | False',
      '; data String = String [Char]',
      '; class Show a where',
      '  { show :: a -> String }',
      '; instance Show Int where',
      '  { show x = String (int#show x) }',
      '; loop :: Int -> Int',
      '; loop n = loop n',
      '}',
    ].join('\n'))
    const l = await e.handle(':load t.glask')
    check('glask loop program loads', l.output === '', JSON.stringify(l.output))
    await e.handle('loop 0')
    const pending = e.handle('')
    e.interrupt()
    const ri = await pending
    check('glask interrupt halts search', ri.interrupted === true && ri.output === 'Interrupted.', JSON.stringify(ri.output))
    // program (and base) stays alive after an interrupt
    await e.handle(':t 1')
    const alive = await e.handle('')
    check('glask alive after interrupt', /::/.test(alive.output), JSON.stringify(alive.output))
    const r = await e.handle(':q')
    check('glask quit halts', r.halted === true && r.output === 'Bye!', JSON.stringify(r.output))
  }
}

if (failures > 0) { console.log(`\n${failures} FAILURES`); throw new Error('engine test failures') }
console.log('\nall engine checks passed')
}

main().catch((e) => {
  console.error(e)
  throw e
})
