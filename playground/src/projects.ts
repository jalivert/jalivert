import type { Engine } from './engines/engine'
import { MinilogEngine } from './engines/minilog'
import { ResinEngine } from './engines/resin'
import { PloverEngine } from './engines/plover'
import { FreaEngine } from './engines/frea'
import { SimplyEngine } from './engines/simply'
import { SystemFEngine } from './engines/systemf'
import { DependentlyEngine } from './engines/dependently'
import { DetourEngine } from './engines/detour'
import { GlaskEngine } from './engines/glask'

import minilogReadme from '../vendor/minilog/README.md?raw'
import minilogCommit from '../vendor/minilog/COMMIT.txt?raw'
import minilogFactorial from '../vendor/minilog/factorial.pl?raw'
import minilogNatural from '../vendor/minilog/natural.pl?raw'
import resinReadme from '../vendor/resin/README.md?raw'
import resinCommit from '../vendor/resin/COMMIT.txt?raw'
import resinNats from '../vendor/resin/nats.rin?raw'
import resinFact from '../vendor/resin/fact.rin?raw'
import resinManual from '../vendor/resin/manual.rin?raw'
import resinCuriosity from '../vendor/resin/curiosity.rin?raw'
import resinList from '../vendor/resin/list.rin?raw'
import resinModi from '../vendor/resin/modi.rin?raw'
import resinSiblings from '../vendor/resin/siblings.rin?raw'
import resinTransitive from '../vendor/resin/transitive.rin?raw'
import resinWest from '../vendor/resin/west.rin?raw'
import ploverReadme from '../vendor/plover/README.md?raw'
import ploverCommit from '../vendor/plover/COMMIT.txt?raw'
import freaReadme from '../vendor/frea/README.md?raw'
import freaCommit from '../vendor/frea/COMMIT.txt?raw'
import freaPrelude from '../vendor/frea/prelude.frea?raw'
import freaModule from '../vendor/frea/module.frea?raw'
import freaBasic from '../vendor/frea/basic.frea?raw'
import ploverBacktrack from '../vendor/plover/backtrack.pl?raw'
import ploverFactorialPl from '../vendor/plover/factorial.pl?raw'
import ploverFactorialNad from '../vendor/plover/factorial.nad?raw'
import ploverNaturalPl from '../vendor/plover/natural.pl?raw'
import ploverNaturalNad from '../vendor/plover/natural.nad?raw'
import lambdaPieReadme from '../vendor/lambda-pie/README.md?raw'
import lambdaPieCommit from '../vendor/lambda-pie/COMMIT.txt?raw'
import detourReadme from '../vendor/detour/README.md?raw'
import detourCommit from '../vendor/detour/COMMIT.txt?raw'
import detourSimplest from '../vendor/detour/simplest.dt?raw'
import detourImpl from '../vendor/detour/impl.dt?raw'
import detourModusPonens from '../vendor/detour/modus-ponens.dt?raw'
import detourAxioms from '../vendor/detour/axioms.dt?raw'
import detourAxiomsOnly from '../vendor/detour/axioms-only.dt?raw'
import detourExistsIntro from '../vendor/detour/exists-intro.dt?raw'
import detourNaturals from '../vendor/detour/naturals.dt?raw'
import detourNaturalsRules from '../vendor/detour/naturals-rules.dt?raw'
import detourNaturalsTyped from '../vendor/detour/naturals-typed.dt?raw'
import detourSumAuto from '../vendor/detour/sum-auto.dt?raw'
import detourSumInduction from '../vendor/detour/sum-induction.dt?raw'
import detourSumUniq from '../vendor/detour/sum-uniq.dt?raw'
import detourWrongExistsIntro from '../vendor/detour/wrong-exists-intro.dt?raw'
import detourWrongExistsElim from '../vendor/detour/wrong-exists-elim.dt?raw'
import detourWrongForallIntro from '../vendor/detour/wrong-forall-intro.dt?raw'
import glaskReadme from '../vendor/glask/README.md?raw'
import glaskCommit from '../vendor/glask/COMMIT.txt?raw'
import glaskNegativeAnnotationsOne from '../vendor/glask/examples/negative/annotations/one.glask?raw'
import glaskNegativeAnnotationsTwo from '../vendor/glask/examples/negative/annotations/two.glask?raw'
import glaskNegativeClassesOne from '../vendor/glask/examples/negative/classes/one.glask?raw'
import glaskNegativeClassesSuper from '../vendor/glask/examples/negative/classes/super.glask?raw'
import glaskNegativeClassesTwo from '../vendor/glask/examples/negative/classes/two.glask?raw'
import glaskNegativeHolesExplicit from '../vendor/glask/examples/negative/holes/explicit.glask?raw'
import glaskNegativeHolesImplicit from '../vendor/glask/examples/negative/holes/implicit.glask?raw'
import glaskNegativeRankOne from '../vendor/glask/examples/negative/rank/one.glask?raw'
import glaskPositiveAnnotationsForall from '../vendor/glask/examples/positive/annotations/forall.glask?raw'
import glaskPositiveAnnotationsForallLayout from '../vendor/glask/examples/positive/annotations/forall.layout.glask?raw'
import glaskPositiveClassesClass from '../vendor/glask/examples/positive/classes/class.glask?raw'
import glaskPositiveClassesClassLayout from '../vendor/glask/examples/positive/classes/class.layout.glask?raw'
import glaskPositiveClassesHigherkinded from '../vendor/glask/examples/positive/classes/higherkinded.glask?raw'
import glaskPositiveClassesHigherkindedLayout from '../vendor/glask/examples/positive/classes/higherkinded.layout.glask?raw'
import glaskPositiveClassesQualified from '../vendor/glask/examples/positive/classes/qualified.glask?raw'
import glaskPositiveClassesQualifiedLayout from '../vendor/glask/examples/positive/classes/qualified.layout.glask?raw'
import glaskPositiveClassesSuper from '../vendor/glask/examples/positive/classes/super.glask?raw'
import glaskPositiveClassesSuperLayout from '../vendor/glask/examples/positive/classes/super.layout.glask?raw'
import glaskPositiveClassesTcSuper from '../vendor/glask/examples/positive/classes/tc-super.glask?raw'
import glaskPositiveClassesTcSuperLayout from '../vendor/glask/examples/positive/classes/tc-super.layout.glask?raw'
import glaskPositiveDataBool from '../vendor/glask/examples/positive/data/bool.glask?raw'
import glaskPositiveDataBoolLayout from '../vendor/glask/examples/positive/data/bool.layout.glask?raw'
import glaskPositiveDataPhantom from '../vendor/glask/examples/positive/data/phantom.glask?raw'
import glaskPositiveDataPhantomLayout from '../vendor/glask/examples/positive/data/phantom.layout.glask?raw'
import glaskPositiveDataRecords from '../vendor/glask/examples/positive/data/records.glask?raw'
import glaskPositiveDataRecordsLayout from '../vendor/glask/examples/positive/data/records.layout.glask?raw'
import glaskPositiveEvaluateArith from '../vendor/glask/examples/positive/evaluate/arith.glask?raw'
import glaskPositiveEvaluateArithLayout from '../vendor/glask/examples/positive/evaluate/arith.layout.glask?raw'
import glaskPositiveEvaluateEvArith from '../vendor/glask/examples/positive/evaluate/ev-arith.glask?raw'
import glaskPositiveEvaluateEvArithLayout from '../vendor/glask/examples/positive/evaluate/ev-arith.layout.glask?raw'
import glaskPositiveEvaluateEvData from '../vendor/glask/examples/positive/evaluate/ev-data.glask?raw'
import glaskPositiveEvaluateEvDataLayout from '../vendor/glask/examples/positive/evaluate/ev-data.layout.glask?raw'
import glaskPositiveEvaluateEvLazy from '../vendor/glask/examples/positive/evaluate/ev-lazy.glask?raw'
import glaskPositiveEvaluateEvLazyLayout from '../vendor/glask/examples/positive/evaluate/ev-lazy.layout.glask?raw'
import glaskPositiveEvaluateEvNest from '../vendor/glask/examples/positive/evaluate/ev-nest.glask?raw'
import glaskPositiveEvaluateEvNestLayout from '../vendor/glask/examples/positive/evaluate/ev-nest.layout.glask?raw'
import glaskPositiveEvaluateEvOps from '../vendor/glask/examples/positive/evaluate/ev-ops.glask?raw'
import glaskPositiveEvaluateEvOpsLayout from '../vendor/glask/examples/positive/evaluate/ev-ops.layout.glask?raw'
import glaskPositiveEvaluateLazy from '../vendor/glask/examples/positive/evaluate/lazy.glask?raw'
import glaskPositiveEvaluateLazyLayout from '../vendor/glask/examples/positive/evaluate/lazy.layout.glask?raw'
import glaskPositiveEvaluateMatching from '../vendor/glask/examples/positive/evaluate/matching.glask?raw'
import glaskPositiveEvaluateMatchingLayout from '../vendor/glask/examples/positive/evaluate/matching.layout.glask?raw'
import glaskPositiveHigherKindedHigherkinded from '../vendor/glask/examples/positive/higher-kinded/higherkinded.glask?raw'
import glaskPositiveHigherKindedHigherkindedLayout from '../vendor/glask/examples/positive/higher-kinded/higherkinded.layout.glask?raw'
import glaskPositiveHigherKindedLists from '../vendor/glask/examples/positive/higher-kinded/lists.glask?raw'
import glaskPositiveHigherKindedListsLayout from '../vendor/glask/examples/positive/higher-kinded/lists.layout.glask?raw'
import glaskPositiveHigherRankBasic from '../vendor/glask/examples/positive/higher-rank/basic.glask?raw'
import glaskPositiveHigherRankBasicLayout from '../vendor/glask/examples/positive/higher-rank/basic.layout.glask?raw'
import glaskPositiveHigherRankCase from '../vendor/glask/examples/positive/higher-rank/case.glask?raw'
import glaskPositiveHigherRankCaseLayout from '../vendor/glask/examples/positive/higher-rank/case.layout.glask?raw'
import glaskPositiveHigherRankData from '../vendor/glask/examples/positive/higher-rank/data.glask?raw'
import glaskPositiveHigherRankDataLayout from '../vendor/glask/examples/positive/higher-rank/data.layout.glask?raw'
import glaskPositiveLayoutBasic from '../vendor/glask/examples/positive/layout/basic.glask?raw'
import glaskPositiveOperatorsImplicit from '../vendor/glask/examples/positive/operators/implicit.glask?raw'
import glaskPositiveOperatorsImplicitLayout from '../vendor/glask/examples/positive/operators/implicit.layout.glask?raw'
import glaskPositiveOperatorsInfix from '../vendor/glask/examples/positive/operators/infix.glask?raw'
import glaskPositiveOperatorsInfixLayout from '../vendor/glask/examples/positive/operators/infix.layout.glask?raw'
import glaskPositiveOperatorsPrefixPostfix from '../vendor/glask/examples/positive/operators/prefix-postfix.glask?raw'
import glaskPositiveOperatorsPrefixPostfixLayout from '../vendor/glask/examples/positive/operators/prefix-postfix.layout.glask?raw'
import glaskPositiveOperatorsPrefix from '../vendor/glask/examples/positive/operators/prefix.glask?raw'
import glaskPositiveOperatorsPrefixLayout from '../vendor/glask/examples/positive/operators/prefix.layout.glask?raw'
import glaskPositivePrenexBranch from '../vendor/glask/examples/positive/prenex/branch.glask?raw'
import glaskPositivePrenexBranchLayout from '../vendor/glask/examples/positive/prenex/branch.layout.glask?raw'
import glaskPositivePrenexLocal from '../vendor/glask/examples/positive/prenex/local.glask?raw'
import glaskPositivePrenexLocalLayout from '../vendor/glask/examples/positive/prenex/local.layout.glask?raw'
import glaskPositivePrenexNested from '../vendor/glask/examples/positive/prenex/nested.glask?raw'
import glaskPositivePrenexNestedLayout from '../vendor/glask/examples/positive/prenex/nested.layout.glask?raw'
import glaskPositiveShowcaseExpr from '../vendor/glask/examples/positive/showcase/expr.glask?raw'
import glaskPositiveShowcaseExprLayout from '../vendor/glask/examples/positive/showcase/expr.layout.glask?raw'
import glaskPositiveShowcaseRankn from '../vendor/glask/examples/positive/showcase/rankn.glask?raw'
import glaskPositiveShowcaseRanknLayout from '../vendor/glask/examples/positive/showcase/rankn.layout.glask?raw'
import glaskPositiveShowcaseSieve from '../vendor/glask/examples/positive/showcase/sieve.glask?raw'
import glaskPositiveShowcaseSieveLayout from '../vendor/glask/examples/positive/showcase/sieve.layout.glask?raw'
import glaskPreludeMicrolude from '../vendor/glask/examples/prelude/microlude.glask?raw'
import glaskPreludeMinilude from '../vendor/glask/examples/prelude/minilude.glask?raw'
import glaskPreludePrelude from '../vendor/glask/examples/prelude/prelude.glask?raw'
import glaskPreludeProtolude from '../vendor/glask/examples/prelude/protolude.glask?raw'

export interface ExampleFile {
  label: string
  file: string
  content: string
}

export interface ProjectDef {
  id: string
  name: string
  tagline: string
  github: string
  commit: string
  readme: string
  engine: () => Engine
  editorLang: string
  defaultFile: string
  examples: ExampleFile[]
  quickref: string
  symbols: string[]
}

const MINILOG_STARTER = `% demo.pl — your knowledge base. Save (Ctrl+S), then load it:
%   ?- :load demo.pl.
% and query it:
%   ?- plus(s(z), s(z), R).
%   ?- fact(s(s(z)), R).

plus(z, N, N).
plus(s(N), M, s(R)) :- plus(N, M, R).

times(z, _, z).
times(s(N), M, A) :- times(N, M, R), plus(R, M, A).

fact(z, s(z)).
fact(s(N), R) :- fact(N, PR), times(s(N), PR, R).
`

const RESIN_STARTER = `% demo.rin — save (Ctrl+S), then check it:
%   :check demo.rin
% or drive the REPL by hand.
% Try typing:   Nat(suc(0))
% Try typing:   :assume Nat(blah)
% Try typing:   :show

constants: zero .

aliases: 0 = zero .

axioms: Nat(0)
      , forall n Nat(n) ==> Nat(suc(n)) .

theorem one-is-nat: Nat(suc(0)) .

theorem some-nats: exists n Nat(n) .
`

const PLOVER_STARTER_PL = `% demo.pl — save (Ctrl+S), then load it:
%   :load demo.pl
% and query it (breadth-first: solutions arrive even rule-first):
%   ?- nat(N).   then :next :next ... :done

nat(s(N)) :- nat(N).
nat(z).
`

const PLOVER_STARTER_NAD = `% demo.nad — save (Ctrl+S), then load it:
%   :load demo.nad
% (the .nad suffix picks natural-deduction syntax; queries need no period):
%   is-nat(N)

is-nat(N)
------------- is-nat-suc
is-nat(s(N))


------- is-nat-z
is-nat(z)
`

const SIMPLY_STARTER = `assume (T :: *) (id :: T -> T) (a :: T) (b :: T)
id a
id b
(\\ (x :: T) -> x)
((\\ (x :: T) -> x) (a :: T))
`

const SYSTEMF_STARTER = `assume (Nat :: *)
(/\\ T . (\\ (t :: T) -> t))
assume (fst :: forall T . T -> T -> T) (snd :: forall T . T -> T -> T)
assume pickone :: (forall T . T -> T -> T) -> (forall T . T -> T -> T) -> (forall T . T -> T -> T)
pickone fst snd
((/\\ T . (\\ (t :: T) -> t)) [Nat])
`

const DEPENDENTLY_STARTER = `assume (Bool :: *)
(lambda t x -> x) :: (forall (t :: *) . (forall (x :: t) . t))
(lambda x -> x) :: (forall (t :: Bool) . Bool)
*
`

const FREA_STARTER = `module Demo where {

; double x = x + x

; quad x = double (double x)

}
`

const DETOUR_STARTER = `-- demo.dt — save (Ctrl+S), then check it:
--   detour> :load demo.dt
-- The first two theorems check on their own. The third one opens a
-- mixed-initiative proof search: press Enter to let it carry on alone,
-- or type \`list theorems\` / \`list locals\` (then Enter), or paste proof
-- lines and submit them with a blank line. Try pasting:
--   c : Sum(Suc(Zero), Zero, Suc(Zero)) by unproved
-- (no leading | on pasted lines) followed by a blank line, then Enter.

module demo

syntax N = Zero
         | Suc(N)

judgment sum = Sum(N, N, N)

rule schema sum-zero for all objects (n : N) :
|
|-------------------------------------- sum-zero
| Sum(Zero, n, n)

rule schema sum-suc for all objects (m : N), (n : N), (o : N) :
| Sum(m, n, o)
|-------------------------------------- sum-suc
| Sum(Suc(m), n, Suc(o))

theorem zero-plus-zero : Sum(Zero, Zero, Zero)
prove Sum(Zero, Zero, Zero)

theorem successor : ∀ (m : N) : Sum(Suc(m), Zero, Suc(m))
prove ∀ (m : N) : Sum(Suc(m), Zero, Suc(m))
`

const GLASK_STARTER = `-- demo.glask — save (Ctrl+S), then load it:
--   glask λ > :load demo.glask
-- and evaluate it (an empty line submits; try :t and :p too):
--   glask λ > answer
--
--   glask λ > :t answer
--   glask λ > :p answer
--   glask λ > :k Int
-- Type classes resolve through dictionaries behind the scenes;
-- operators need a fixity declaration to be used in expressions.

module Main where
{ infixl 6 +
; infixl 7 *
; class Num a where
  { (+) :: a -> a -> a
  ; (*) :: a -> a -> a }
; instance Num Int where
  { (+) x y = int#+ (x, y)
  ; (*) x y = int#* (x, y) }
; data String = String [Char]
; class Show a where
  { show :: a -> String }
; instance Show Int where
  { show x = String (int#show x) }
; answer = 2 + 3 * 4
}
`

export const PROJECTS: ProjectDef[] = [
  {
    id: 'minilog',
    name: 'Minilog',
    tagline: 'a tiny logic-programming language (Prolog subset, strict occurs-check)',
    github: 'https://github.com/jalivert/minilog',
    commit: minilogCommit.split('\n')[0]!.trim(),
    readme: minilogReadme,
    engine: () => new MinilogEngine(),
    editorLang: 'minilog',
    defaultFile: 'demo.pl',
    examples: [
      { label: '▶ starter: demo.pl', file: 'demo.pl', content: MINILOG_STARTER },
      { label: 'factorial.pl', file: 'factorial.pl', content: minilogFactorial },
      { label: 'natural.pl', file: 'natural.pl', content: minilogNatural },
    ],
    quickref:
      '<b>MINILOG</b> // <code>:load FILE</code> load knowledge base · <code>QUERY.</code> ask · <code>any key</code>/<code>:done</code> next/stop · <code>:q</code> quit · <code>Ctrl+C</code> interrupt',
    symbols: [],
  },
  {
    id: 'resin',
    name: 'Resin',
    tagline: 'a toy automated theorem prover for classical FOL (resolution)',
    github: 'https://github.com/jalivert/resin',
    commit: resinCommit.split('\n')[0]!.trim(),
    readme: resinReadme,
    engine: () => new ResinEngine(),
    editorLang: 'resin',
    defaultFile: 'demo.rin',
    examples: [
      { label: '▶ starter: demo.rin', file: 'demo.rin', content: RESIN_STARTER },
      { label: 'nats.rin', file: 'nats.rin', content: resinNats },
      { label: 'fact.rin', file: 'fact.rin', content: resinFact },
      { label: 'manual.rin', file: 'manual.rin', content: resinManual },
      { label: 'curiosity.rin', file: 'curiosity.rin', content: resinCuriosity },
      { label: 'list.rin', file: 'list.rin', content: resinList },
      { label: 'modi.rin', file: 'modi.rin', content: resinModi },
      { label: 'siblings.rin', file: 'siblings.rin', content: resinSiblings },
      { label: 'transitive.rin', file: 'transitive.rin', content: resinTransitive },
      { label: 'west.rin', file: 'west.rin', content: resinWest },
    ],
    quickref:
      '<b>RESIN</b> // <code>:check FILE</code> check theorems · <code>FORMULA</code> entailment test · <code>:assume F</code> add assumption · <code>:show</code> · <code>:clear</code> · <code>:q</code> quit · <code>Ctrl+C</code> interrupt',
    symbols: ['∀', '∃', '¬', '∧', '∨', '⟹', '⟺', '⊤', '⊥', '⊢', 'ᶜ'],
  },
  {
    id: 'plover',
    name: 'Plover',
    tagline: 'a toy prover with complete (breadth-first) search — Minilog, but it terminates',
    github: 'https://github.com/jalivert/plover',
    commit: ploverCommit.split('\n')[0]!.trim(),
    readme: ploverReadme,
    engine: () => new PloverEngine(),
    editorLang: 'plover',
    defaultFile: 'demo.pl',
    examples: [
      { label: '▶ starter: demo.pl', file: 'demo.pl', content: PLOVER_STARTER_PL },
      { label: 'starter: demo.nad', file: 'demo.nad', content: PLOVER_STARTER_NAD },
      { label: 'backtrack.pl', file: 'backtrack.pl', content: ploverBacktrack },
      { label: 'natural.pl', file: 'natural.pl', content: ploverNaturalPl },
      { label: 'factorial.pl', file: 'factorial.pl', content: ploverFactorialPl },
      { label: 'natural.nad', file: 'natural.nad', content: ploverNaturalNad },
      { label: 'factorial.nad', file: 'factorial.nad', content: ploverFactorialNad },
    ],
    quickref:
      '<b>PLOVER</b> // <code>:load FILE</code> load it (<code>.nad</code> picks natural-deduction syntax) · <code>QUERY.</code> or <code>QUERY</code> · <code>:next</code>/<code>:done</code> · <code>:q</code> quit · <code>Ctrl+C</code> interrupt',
    symbols: [],
  },
  {
    id: 'simply',
    name: 'λ→',
    tagline: 'simply typed lambda calculus — typecheck and evaluate as you type',
    github: 'https://github.com/jalivert/lambda-pie',
    commit: lambdaPieCommit.split('\n')[0]!.trim(),
    readme: lambdaPieReadme,
    engine: () => new SimplyEngine(),
    editorLang: 'lambdapie',
    defaultFile: 'demo.simply',
    examples: [{ label: '▶ starter: demo.simply', file: 'demo.simply', content: SIMPLY_STARTER }],
    quickref:
      '<b>SIMPLY λ→</b> // <code>EXPR</code> typecheck + evaluate · <code>assume ...</code> extend the context · no file loading upstream — paste lines from the sidebar file · <code>:exit</code> quit',
    symbols: ['λ'],
  },
  {
    id: 'systemf',
    name: 'λ2',
    tagline: 'System F — polymorphic lambda calculus with type abstraction',
    github: 'https://github.com/jalivert/lambda-pie',
    commit: lambdaPieCommit.split('\n')[0]!.trim(),
    readme: lambdaPieReadme,
    engine: () => new SystemFEngine(),
    editorLang: 'lambdapie',
    defaultFile: 'demo.systemf',
    examples: [{ label: '▶ starter: demo.systemf', file: 'demo.systemf', content: SYSTEMF_STARTER }],
    quickref:
      '<b>SYSTEM F λ2</b> // <code>EXPR</code> typecheck + evaluate · <code>/\\</code> type lambda · <code>[T]</code> type application · <code>forall</code> types · <code>assume ...</code> · no file loading upstream — paste lines · <code>:exit</code> quit',
    symbols: ['λ', '/\\'],
  },
  {
    id: 'dependently',
    name: 'λΠ',
    tagline: 'dependently typed lambda calculus — types are terms',
    github: 'https://github.com/jalivert/lambda-pie',
    commit: lambdaPieCommit.split('\n')[0]!.trim(),
    readme: lambdaPieReadme,
    engine: () => new DependentlyEngine(),
    editorLang: 'lambdapie',
    defaultFile: 'demo.dep',
    examples: [{ label: '▶ starter: demo.dep', file: 'demo.dep', content: DEPENDENTLY_STARTER }],
    quickref:
      '<b>DEPENDENT λΠ</b> // <code>EXPR</code> typecheck + evaluate · <code>forall</code>/<code>Π</code>/<code>∀</code> binders · <code>*</code> is a term · <code>assume ...</code> (types evaluated) · no file loading upstream — paste lines · <code>:exit</code> quit',
    symbols: ['λ', 'Π', '∀'],
  },
  {
    id: 'frea',
    name: 'Frea',
    tagline: 'a small lazy functional language with HM inference (prelude auto-loads)',
    github: 'https://github.com/jalivert/frea',
    commit: freaCommit.split('\n')[0]!.trim(),
    readme: freaReadme,
    engine: () => new FreaEngine(),
    editorLang: 'frea',
    defaultFile: 'demo.frea',
    examples: [
      { label: '▶ starter: demo.frea', file: 'demo.frea', content: FREA_STARTER },
      { label: 'prelude.frea', file: 'prelude.frea', content: freaPrelude },
      { label: 'module.frea', file: 'module.frea', content: freaModule },
      { label: 'examples/basic.frea', file: 'basic.frea', content: freaBasic },
    ],
    quickref:
      '<b>FREA</b> // <code>EXPR</code> typecheck + lazy eval · <code>empty line</code> submits (multi-line input) · <code>:t EXPR</code> types · <code>:k TYPE</code> kinds · <code>:load FILE</code> (declarations) · <code>:exit</code>/<code>:q</code> quit · <code>Ctrl+C</code> interrupt',
    symbols: [],
  },
  {
    id: 'detour',
    name: 'Detour',
    tagline: 'a mixed-initiative interactive proof assistant for first-order logic (Fitch style)',
    github: 'https://github.com/jalivert/detour',
    commit: detourCommit.split('\n')[0]!.trim(),
    readme: detourReadme,
    engine: () => new DetourEngine(),
    editorLang: 'detour',
    defaultFile: 'demo.dt',
    examples: [
      { label: '▶ starter: demo.dt', file: 'demo.dt', content: DETOUR_STARTER },
      { label: 'simplest.dt', file: 'simplest.dt', content: detourSimplest },
      { label: 'impl.dt', file: 'impl.dt', content: detourImpl },
      { label: 'modus-ponens.dt', file: 'modus-ponens.dt', content: detourModusPonens },
      { label: 'axioms.dt', file: 'axioms.dt', content: detourAxioms },
      { label: 'axioms-only.dt', file: 'axioms-only.dt', content: detourAxiomsOnly },
      { label: 'exists-intro.dt', file: 'exists-intro.dt', content: detourExistsIntro },
      { label: 'naturals.dt', file: 'naturals.dt', content: detourNaturals },
      { label: 'naturals-rules.dt', file: 'naturals-rules.dt', content: detourNaturalsRules },
      { label: 'naturals-typed.dt', file: 'naturals-typed.dt', content: detourNaturalsTyped },
      { label: 'sum-auto.dt', file: 'sum-auto.dt', content: detourSumAuto },
      { label: 'sum-induction.dt', file: 'sum-induction.dt', content: detourSumInduction },
      { label: 'sum-uniq.dt', file: 'sum-uniq.dt', content: detourSumUniq },
      { label: 'wrong-exists-intro.dt', file: 'wrong-exists-intro.dt', content: detourWrongExistsIntro },
      { label: 'wrong-exists-elim.dt', file: 'wrong-exists-elim.dt', content: detourWrongExistsElim },
      { label: 'wrong-forall-intro.dt', file: 'wrong-forall-intro.dt', content: detourWrongForallIntro },
    ],
    quickref:
      '<b>DETOUR</b> // <code>:load FILE</code> check it (search may ask for guidance) · <code>Enter</code> = carry on · <code>list theorems</code>/<code>list locals</code> + Enter · paste proof lines, blank line submits · <code>:lem</code>/<code>:no-lem</code> classical rule · <code>:q</code> abandon/quit · <code>Ctrl+C</code> interrupt',
    symbols: ['∀', '∃', '¬', '∧', '∨', '⟹', '⟺', '⊤', '⊥', '⊢'],
  },

  {
    id: 'glask',
    name: 'Glask',
    tagline: 'a small lazy pure functional language with type classes (Haskell spirit, dictionaries in the browser)',
    github: 'https://github.com/jalivert/glask',
    commit: glaskCommit.split('\n')[0]!.trim(),
    readme: glaskReadme,
    engine: () => new GlaskEngine(),
    editorLang: 'glask',
    defaultFile: 'demo.glask',
    examples: [
      { label: '▶ starter: demo.glask', file: 'demo.glask', content: GLASK_STARTER },
    { label: 'negative/annotations/one.glask', file: 'negative/annotations/one.glask', content: glaskNegativeAnnotationsOne },
    { label: 'negative/annotations/two.glask', file: 'negative/annotations/two.glask', content: glaskNegativeAnnotationsTwo },
    { label: 'negative/classes/one.glask', file: 'negative/classes/one.glask', content: glaskNegativeClassesOne },
    { label: 'negative/classes/super.glask', file: 'negative/classes/super.glask', content: glaskNegativeClassesSuper },
    { label: 'negative/classes/two.glask', file: 'negative/classes/two.glask', content: glaskNegativeClassesTwo },
    { label: 'negative/holes/explicit.glask', file: 'negative/holes/explicit.glask', content: glaskNegativeHolesExplicit },
    { label: 'negative/holes/implicit.glask', file: 'negative/holes/implicit.glask', content: glaskNegativeHolesImplicit },
    { label: 'negative/rank/one.glask', file: 'negative/rank/one.glask', content: glaskNegativeRankOne },
    { label: 'positive/annotations/forall.glask', file: 'positive/annotations/forall.glask', content: glaskPositiveAnnotationsForall },
    { label: 'positive/annotations/forall.layout.glask', file: 'positive/annotations/forall.layout.glask', content: glaskPositiveAnnotationsForallLayout },
    { label: 'positive/classes/class.glask', file: 'positive/classes/class.glask', content: glaskPositiveClassesClass },
    { label: 'positive/classes/class.layout.glask', file: 'positive/classes/class.layout.glask', content: glaskPositiveClassesClassLayout },
    { label: 'positive/classes/higherkinded.glask', file: 'positive/classes/higherkinded.glask', content: glaskPositiveClassesHigherkinded },
    { label: 'positive/classes/higherkinded.layout.glask', file: 'positive/classes/higherkinded.layout.glask', content: glaskPositiveClassesHigherkindedLayout },
    { label: 'positive/classes/qualified.glask', file: 'positive/classes/qualified.glask', content: glaskPositiveClassesQualified },
    { label: 'positive/classes/qualified.layout.glask', file: 'positive/classes/qualified.layout.glask', content: glaskPositiveClassesQualifiedLayout },
    { label: 'positive/classes/super.glask', file: 'positive/classes/super.glask', content: glaskPositiveClassesSuper },
    { label: 'positive/classes/super.layout.glask', file: 'positive/classes/super.layout.glask', content: glaskPositiveClassesSuperLayout },
    { label: 'positive/classes/tc-super.glask', file: 'positive/classes/tc-super.glask', content: glaskPositiveClassesTcSuper },
    { label: 'positive/classes/tc-super.layout.glask', file: 'positive/classes/tc-super.layout.glask', content: glaskPositiveClassesTcSuperLayout },
    { label: 'positive/data/bool.glask', file: 'positive/data/bool.glask', content: glaskPositiveDataBool },
    { label: 'positive/data/bool.layout.glask', file: 'positive/data/bool.layout.glask', content: glaskPositiveDataBoolLayout },
    { label: 'positive/data/phantom.glask', file: 'positive/data/phantom.glask', content: glaskPositiveDataPhantom },
    { label: 'positive/data/phantom.layout.glask', file: 'positive/data/phantom.layout.glask', content: glaskPositiveDataPhantomLayout },
    { label: 'positive/data/records.glask', file: 'positive/data/records.glask', content: glaskPositiveDataRecords },
    { label: 'positive/data/records.layout.glask', file: 'positive/data/records.layout.glask', content: glaskPositiveDataRecordsLayout },
    { label: 'positive/evaluate/arith.glask', file: 'positive/evaluate/arith.glask', content: glaskPositiveEvaluateArith },
    { label: 'positive/evaluate/arith.layout.glask', file: 'positive/evaluate/arith.layout.glask', content: glaskPositiveEvaluateArithLayout },
    { label: 'positive/evaluate/ev-arith.glask', file: 'positive/evaluate/ev-arith.glask', content: glaskPositiveEvaluateEvArith },
    { label: 'positive/evaluate/ev-arith.layout.glask', file: 'positive/evaluate/ev-arith.layout.glask', content: glaskPositiveEvaluateEvArithLayout },
    { label: 'positive/evaluate/ev-data.glask', file: 'positive/evaluate/ev-data.glask', content: glaskPositiveEvaluateEvData },
    { label: 'positive/evaluate/ev-data.layout.glask', file: 'positive/evaluate/ev-data.layout.glask', content: glaskPositiveEvaluateEvDataLayout },
    { label: 'positive/evaluate/ev-lazy.glask', file: 'positive/evaluate/ev-lazy.glask', content: glaskPositiveEvaluateEvLazy },
    { label: 'positive/evaluate/ev-lazy.layout.glask', file: 'positive/evaluate/ev-lazy.layout.glask', content: glaskPositiveEvaluateEvLazyLayout },
    { label: 'positive/evaluate/ev-nest.glask', file: 'positive/evaluate/ev-nest.glask', content: glaskPositiveEvaluateEvNest },
    { label: 'positive/evaluate/ev-nest.layout.glask', file: 'positive/evaluate/ev-nest.layout.glask', content: glaskPositiveEvaluateEvNestLayout },
    { label: 'positive/evaluate/ev-ops.glask', file: 'positive/evaluate/ev-ops.glask', content: glaskPositiveEvaluateEvOps },
    { label: 'positive/evaluate/ev-ops.layout.glask', file: 'positive/evaluate/ev-ops.layout.glask', content: glaskPositiveEvaluateEvOpsLayout },
    { label: 'positive/evaluate/lazy.glask', file: 'positive/evaluate/lazy.glask', content: glaskPositiveEvaluateLazy },
    { label: 'positive/evaluate/lazy.layout.glask', file: 'positive/evaluate/lazy.layout.glask', content: glaskPositiveEvaluateLazyLayout },
    { label: 'positive/evaluate/matching.glask', file: 'positive/evaluate/matching.glask', content: glaskPositiveEvaluateMatching },
    { label: 'positive/evaluate/matching.layout.glask', file: 'positive/evaluate/matching.layout.glask', content: glaskPositiveEvaluateMatchingLayout },
    { label: 'positive/higher-kinded/higherkinded.glask', file: 'positive/higher-kinded/higherkinded.glask', content: glaskPositiveHigherKindedHigherkinded },
    { label: 'positive/higher-kinded/higherkinded.layout.glask', file: 'positive/higher-kinded/higherkinded.layout.glask', content: glaskPositiveHigherKindedHigherkindedLayout },
    { label: 'positive/higher-kinded/lists.glask', file: 'positive/higher-kinded/lists.glask', content: glaskPositiveHigherKindedLists },
    { label: 'positive/higher-kinded/lists.layout.glask', file: 'positive/higher-kinded/lists.layout.glask', content: glaskPositiveHigherKindedListsLayout },
    { label: 'positive/higher-rank/basic.glask', file: 'positive/higher-rank/basic.glask', content: glaskPositiveHigherRankBasic },
    { label: 'positive/higher-rank/basic.layout.glask', file: 'positive/higher-rank/basic.layout.glask', content: glaskPositiveHigherRankBasicLayout },
    { label: 'positive/higher-rank/case.glask', file: 'positive/higher-rank/case.glask', content: glaskPositiveHigherRankCase },
    { label: 'positive/higher-rank/case.layout.glask', file: 'positive/higher-rank/case.layout.glask', content: glaskPositiveHigherRankCaseLayout },
    { label: 'positive/higher-rank/data.glask', file: 'positive/higher-rank/data.glask', content: glaskPositiveHigherRankData },
    { label: 'positive/higher-rank/data.layout.glask', file: 'positive/higher-rank/data.layout.glask', content: glaskPositiveHigherRankDataLayout },
    { label: 'positive/layout/basic.glask', file: 'positive/layout/basic.glask', content: glaskPositiveLayoutBasic },
    { label: 'positive/operators/implicit.glask', file: 'positive/operators/implicit.glask', content: glaskPositiveOperatorsImplicit },
    { label: 'positive/operators/implicit.layout.glask', file: 'positive/operators/implicit.layout.glask', content: glaskPositiveOperatorsImplicitLayout },
    { label: 'positive/operators/infix.glask', file: 'positive/operators/infix.glask', content: glaskPositiveOperatorsInfix },
    { label: 'positive/operators/infix.layout.glask', file: 'positive/operators/infix.layout.glask', content: glaskPositiveOperatorsInfixLayout },
    { label: 'positive/operators/prefix-postfix.glask', file: 'positive/operators/prefix-postfix.glask', content: glaskPositiveOperatorsPrefixPostfix },
    { label: 'positive/operators/prefix-postfix.layout.glask', file: 'positive/operators/prefix-postfix.layout.glask', content: glaskPositiveOperatorsPrefixPostfixLayout },
    { label: 'positive/operators/prefix.glask', file: 'positive/operators/prefix.glask', content: glaskPositiveOperatorsPrefix },
    { label: 'positive/operators/prefix.layout.glask', file: 'positive/operators/prefix.layout.glask', content: glaskPositiveOperatorsPrefixLayout },
    { label: 'positive/prenex/branch.glask', file: 'positive/prenex/branch.glask', content: glaskPositivePrenexBranch },
    { label: 'positive/prenex/branch.layout.glask', file: 'positive/prenex/branch.layout.glask', content: glaskPositivePrenexBranchLayout },
    { label: 'positive/prenex/local.glask', file: 'positive/prenex/local.glask', content: glaskPositivePrenexLocal },
    { label: 'positive/prenex/local.layout.glask', file: 'positive/prenex/local.layout.glask', content: glaskPositivePrenexLocalLayout },
    { label: 'positive/prenex/nested.glask', file: 'positive/prenex/nested.glask', content: glaskPositivePrenexNested },
    { label: 'positive/prenex/nested.layout.glask', file: 'positive/prenex/nested.layout.glask', content: glaskPositivePrenexNestedLayout },
    { label: 'positive/showcase/expr.glask', file: 'positive/showcase/expr.glask', content: glaskPositiveShowcaseExpr },
    { label: 'positive/showcase/expr.layout.glask', file: 'positive/showcase/expr.layout.glask', content: glaskPositiveShowcaseExprLayout },
    { label: 'positive/showcase/rankn.glask', file: 'positive/showcase/rankn.glask', content: glaskPositiveShowcaseRankn },
    { label: 'positive/showcase/rankn.layout.glask', file: 'positive/showcase/rankn.layout.glask', content: glaskPositiveShowcaseRanknLayout },
    { label: 'positive/showcase/sieve.glask', file: 'positive/showcase/sieve.glask', content: glaskPositiveShowcaseSieve },
    { label: 'positive/showcase/sieve.layout.glask', file: 'positive/showcase/sieve.layout.glask', content: glaskPositiveShowcaseSieveLayout },
    { label: 'prelude/microlude.glask', file: 'prelude/microlude.glask', content: glaskPreludeMicrolude },
    { label: 'prelude/minilude.glask', file: 'prelude/minilude.glask', content: glaskPreludeMinilude },
    { label: 'prelude/prelude.glask', file: 'prelude/prelude.glask', content: glaskPreludePrelude },
    { label: 'prelude/protolude.glask', file: 'prelude/protolude.glask', content: glaskPreludeProtolude },
    ],
    quickref:
      '<b>GLASK</b> // <code>:load FILE</code> load it · <code>EXPR</code> typecheck + lazy eval (empty line submits multi-line input) · <code>:t EXPR</code>/<code>:p EXPR</code>/<code>:k TYPE</code>/<code>:c</code>/<code>:d</code> inspect · <code>:q</code> quit · <code>Ctrl+C</code> interrupt',
    symbols: [],
  },
]
