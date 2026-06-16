#!/usr/bin/env bash
set -euo pipefail

for f in \
  SN_Haskell.hs \
  SN_Haskell_Named.hs \
  SN_Haskell_Trace.hs \
  SN_Haskell_HenkExamples.hs
do
  echo "== typechecking $f =="
  ghc -Wall -Werror -fforce-recomp -fno-code "$f"
done

for f in \
  SN_Haskell.hs \
  SN_Haskell_Named.hs \
  SN_Haskell_Trace.hs \
  SN_Haskell_HenkExamples.hs
do
  echo "== running $f =="
  runghc "$f"
done

if command -v jscoq >/dev/null 2>&1; then
  echo "== checking SN_Haskell_Coq.v =="
  jscoq run -v -l SN_Haskell_Coq.v
else
  echo "jscoq is not on PATH; skipping Coq check."
  echo "Run: npx jscoq run -v -l SN_Haskell_Coq.v"
fi
