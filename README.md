# SN_Haskell

This repository contains the code artifact for **de Vrijer's Strong
Normalization in Haskell**.

## Contents

- `SN_Haskell.hs` — the main higher-order/final Haskell implementation.
- `SN_Haskell_Named.hs` — a named, environment-passing implementation kept for comparison.
- `SN_Haskell_Trace.hs` — a first-order trace program that prints reduction steps.
- `SN_Haskell_HenkExamples.hs` — checks the examples from Henk Barendregt's note.
- `SN_Haskell_Coq.v` — a Coq formalization of the normalization proof.
- `checks/` — logs from the last successful Haskell and Coq checks.
- `paper/` — the current paper source and PDF for context.

## Haskell checks

The Haskell files use only `base`.  With GHC available, run:

```sh
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
```

The first two programs print `2`.  The trace program prints the reduction
traces.  The examples checker reports success if all checked examples pass.

## Coq check

The Coq development was checked here with jsCoq using:

```sh
jscoq run -v -l SN_Haskell_Coq.v
```

or, if using `npx`:

```sh
npx jscoq run -v -l SN_Haskell_Coq.v
```

The Coq proof is a formal proof of the mathematical normalization argument
used by the paper.  It uses intrinsically typed de Bruijn syntax as the
proof-assistant representation, while the Haskell program uses a compact
higher-order/final representation.

## Reproducing the paper

The paper files are in `paper/`:

```sh
cd paper
pdflatex SN_Haskell.tex
bibtex8 SN_Haskell
pdflatex SN_Haskell.tex
pdflatex SN_Haskell.tex
```
