#!/usr/bin/env bash
# Fetch the latest of every PL&TT project from GitHub and refresh vendor/ copies.
# Run from the web-demo directory:  ./scripts/fetch-latest.sh
set -euo pipefail

ROOT="${PLTT_ROOT:-$(cd "$(dirname "$0")/../.." && pwd)}"
WEB="$(cd "$(dirname "$0")/.." && pwd)"

pull_one() {
  local repo="$1"
  if [ ! -d "$repo/.git" ]; then
    echo "!! $repo is not a git checkout, skipping pull (copying as-is)."
    return
  fi
  echo "== pulling $(basename "$repo") =="
  git -C "$repo" fetch origin
  git -C "$repo" pull --ff-only 2>&1 | tail -n 2
}

for p in minilog resin plover lambda-pie frea detour glask; do
  pull_one "$ROOT/$p"
done

echo "== refreshing vendor/ =="
for p in minilog resin plover lambda-pie frea detour glask; do
  mkdir -p "$WEB/vendor/$p"
  git -C "$ROOT/$p" rev-parse HEAD > "$WEB/vendor/$p/COMMIT.txt"
  git -C "$ROOT/$p" log --oneline -1 >> "$WEB/vendor/$p/COMMIT.txt"
  cp "$ROOT/$p/README.md" "$WEB/vendor/$p/README.md"
  cp "$ROOT/$p/"*.cabal "$WEB/vendor/$p/" 2>/dev/null || true
done

cp "$ROOT/minilog/factorial.pl" "$ROOT/minilog/natural.pl" "$ROOT/minilog/WRITEUP.md" "$WEB/vendor/minilog/"
cp "$ROOT/resin/examples/"*.rin "$WEB/vendor/resin/"
cp "$ROOT/plover/"*.pl "$ROOT/plover/"*.nad "$WEB/vendor/plover/"
cp "$ROOT/frea/prelude.frea" "$ROOT/frea/module.frea" "$WEB/vendor/frea/"
cp "$ROOT/frea/examples/"*.frea "$WEB/vendor/frea/"
# top-level examples flat; the archive/ sketches keep their subdirectory
# (names collide otherwise: archive/naturals.dt vs naturals.dt).
cp "$ROOT/detour/examples/"*.dt "$WEB/vendor/detour/"
mkdir -p "$WEB/vendor/detour/archive"
cp "$ROOT/detour/examples/archive/"*.dt "$WEB/vendor/detour/archive/" 2>/dev/null || true
cp "$ROOT/detour/hatra24.pdf" "$WEB/vendor/detour/" 2>/dev/null || true
mkdir -p "$WEB/vendor/glask/examples"
cp -r "$ROOT/glask/examples/positive" "$ROOT/glask/examples/negative" "$ROOT/glask/examples/prelude" "$WEB/vendor/glask/examples/"
mkdir -p "$WEB/vendor/glask/test/golden/repl"
cp "$ROOT/glask/test/golden/repl/"*.golden "$WEB/vendor/glask/test/golden/repl/"

echo "done. Re-run the site build to pick up the new vendor/ files."
