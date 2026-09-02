#!/usr/bin/env sh
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

# If jsCoq is installed:
# jscoq run -v -l SN_Haskell_Coq.v
