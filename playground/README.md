# PL&TT — Logic Playground

Interactive showcase of the PL/TT/logic projects: an **editor + CRT REPL**
per project, running entirely in the browser. Deployed to GitHub Pages from
this directory (see `.github/workflows/deploy.yml` at the repo root).

Live here (all Haskell upstream; all engines are browser-native ports
behind the `Engine` interface in `src/engines/engine.ts`):

- **Minilog** (`minilog.ts`) — `%` comments, facts/rules with `:-`, `=`
  unification goals, strict occurs-check, step/resume backtracking machine,
  `?- ` prompt, `:load`, `:next`/`:done`, `:q`.
- **Resin** (`resin.ts`) — unicode + ASCII syntax,
  constants/aliases/axioms/theorems with proofs and `using { }`, NNF/PNF/skolem/CNF,
  given-clause resolution with constructive existential answers, `⊤ ⊢ ` prompt,
  `:check`, `:assume`, `:entails`, `:consistent`, `:clear`, `:q`.
- **Plover** (`plover.ts`) — Minilog's twin with a complete breadth-first style
  search (before/after queue + direction flag) instead of DFS, both Prolog
  (`.pl`) and natural-deduction (`.nad`, picked by file suffix) syntaxes,
  `Unknown predicate: name/arity.` program errors, `?- ` prompt, `:load`,
  `:next`/`:done`, `:q`.
- **lambda-pie** (`simply.ts`, `systemf.ts`, `dependently.ts`) — three REPLs:
  simply typed λ→, System F λ2 (type abstraction `/\`, type application `[T]`,
  alpha-invariant `forall` equality, type-erasure evaluation), and dependently
  typed λΠ (terms as types, Pi closures, `assume` of evaluated types). Each with
  its banner (`REPL for λ->/λ2/λΠ`), prompt, result indentation and `:exit`.

- **Frea** (`frea.ts`) — lazy functional language with HM inference, kinds,
  ADTs eliminated via `which-` eliminators, type synonyms and a lazy memoized
  evaluator. Full grammar (layout braces, infix/backtick operators, strings,
  chars, tuples, lists), constraint HM + SCC generalisation, kind inference,
  synonym expansion with cycle checks, prelude auto-load. Multi-line input
  until an empty line, `:t`/`:k`/`:load`, `Bye!`.
- **Detour** (`detour.ts`) — mixed-initiative FOL proof assistant: Fitch
  notation with column layout, deterministic ND rule checker (custom rules,
  induction, case analysis), and the hardcoded `prove` search that pauses to
  ask for guidance (`Enter` = carry on, `list theorems`/`list locals`, paste
  proof lines + blank line submits). `:load`, `:lem`/`:no-lem`, `:q`.

Queued (sources vendored under `vendor/`; full-fidelity ports in progress):

- **Glask** — thesis language (type classes, higher-rank types, custom fixity,
  layout, lazy evaluation). Largest port; staged parser → HM → elaboration →
  evaluator, validated against `examples/positive`.

The `Engine` interface is the seam for real `*.wasm` builds later — see
`scripts/build-wasm.sh`. The UI (picker, README pane, Monaco editor, xterm.js
CRT) does not care which implementation sits behind it.

## Layout

- `index.html` + `src/main.ts` — picker, README rendering, wiring
- `src/projects.ts` — project registry (README, examples, engine factory)
- `src/engines/` — `engine.ts` interface + one file per calculus/prover
- `src/ui/` — `terminal.ts` (xterm CRT), `editor.ts` (Monaco + grammars),
  `files.ts` (sidebar file store with save/dirty + localStorage)
- `vendor/` — latest sources copied from GitHub (`fetch-latest.sh` refreshes)
- `scripts/fetch-latest.sh` — pull latest of every project, refresh `vendor/`
- `scripts/build-wasm.sh` — plan/scaffold for real GHC WASM builds
- `eng-test/test.ts` — regression suite (`npm run test:engines`)

## Run it

```sh
cd playground
npm install
npm run dev      # local playground
npm run build    # static dist/ (deployed to GitHub Pages by CI)
```

## Behaviour contract (matches the Haskell REPLs)

- The editor is a **file explorer** (sidebar, `Ctrl+S` saves, double-click renames,
  files persist in localStorage): the REPL reads **saved** file content, so
  `:load demo.pl` and `:check demo.nad` see exactly what you saved.
- Quitting (`:q`, `:Q`, `:exit`) **halts** the program: the terminal prints
  `-- PROGRAM TERMINATED --` and only accepts `start`.
- `Ctrl+C` interrupts a running computation (back to the prompt, program alive);
  `Ctrl+L` clears the CRT screen.
- Search is **bounded** (step/queue/clause caps) so a diverging query can not
  hang the tab; hitting a cap is reported in the terminal.

## Refreshing from GitHub

```sh
PLTT_ROOT=/Users/liam/Projects/PL\&TT ./scripts/fetch-latest.sh   # pulls origin/main for every project into vendor/
```

(`PLTT_ROOT` points at the checkouts; it defaults to the playground's
parent directory.) After a refresh, bump `STORE_VERSION` in
`src/ui/files.ts` (and `STORAGE_VERSION` in `src/main.ts`) so visitors pick
up the new examples, then `npm run test:engines && npm run build`.
