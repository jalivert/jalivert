#!/usr/bin/env bash
# Build real minilog.wasm / resin.wasm from the Haskell sources.
#
# STATUS: scaffold, not yet wired into the demo.
# The demo currently ships browser-native TypeScript engines
# (src/engines/minilog.ts, src/engines/resin.ts) that implement the same
# grammars, REPL commands and proof search as the Haskell originals.
# They satisfy the `Engine` interface in src/engines/engine.ts, so swapping
# in real WASM builds later is a drop-in: implement `Engine` over the WASM
# module and register it in src/projects.ts. The virtual-file contract is:
#   - Minilog `:load <file>` resolves against Engine.provideFile()
#   - Resin `:check <file>` resolves against Engine.provideFile()
#
# To produce the real artifacts you need a GHC JS/WASM toolchain, e.g.:
#
#   ghcup install ghc 9.10.1 --target javascript-unknown-ghcjs
#   # or: ghcup install ghc 9.8.2 --target wasm32-wasi   (ghc-wasm)
#
# then, per project (adapted Main with a virtual FS + JS FFI exports):
#
#   cd vendor-src/minilog
#   javascript-unknown-ghcjs-cabal build ...
#
# Binary-size and `directory`/`filepath` shims for the browser FS are the
# known work items. Until that lands, `npm run build` ships the TS engines.
set -euo pipefail
echo "build-wasm.sh is a scaffold — see the header comments for the plan."
echo "Nothing to compile yet; the demo uses the TS engines in src/engines/."
