#!/bin/sh
set -eu
for f in \
  SN_Haskell.hs \
  SN_Haskell_Named.hs \
  SN_Haskell_Trace.hs \
  SN_Haskell_HenkExamples.hs
do
  ghc -Wall -Werror -fforce-recomp -fno-code "$f"
done
runghc SN_Haskell.hs
runghc SN_Haskell_Named.hs
runghc SN_Haskell_Trace.hs
runghc SN_Haskell_HenkExamples.hs
if command -v rocq >/dev/null 2>&1; then
  rocq compile SN_Haskell_Rocq.v
elif command -v coqc >/dev/null 2>&1; then
  coqc SN_Haskell_Rocq.v
else
  echo "No rocq/coqc found; skipping Rocq check." >&2
fi
