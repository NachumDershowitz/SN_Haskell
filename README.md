# SN_Haskell

Haskell implementations and a Rocq formalization of de Vrijer's decreasing measure for strong normalization of the simply typed lambda-calculus.

## Contents

- `SN_Haskell.hs` — the main higher-order/final Haskell implementation.
- `SN_Haskell_Named.hs` — a named, environment-passing Haskell implementation kept for comparison.
- `SN_Haskell_Trace.hs` — a trace program that prints reduction steps.
- `SN_Haskell_HenkExamples.hs` — checks the examples from Henk Barendregt's note.
- `SN_Haskell_Rocq.v` — a Rocq formalization of the measurement algebra, intrinsically typed de Bruijn syntax, substitution, full contextual beta-reduction, strict decrease, and strong normalization.
- `checks/` — check logs and status notes.

## Haskell checks

With GHC available, run:

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

The first two programs print `2`. The trace program prints reduction traces. The examples checker reports success if all checked examples pass.

## Rocq check

With Rocq 9:

```sh
rocq compile SN_Haskell_Rocq.v
```

Some Rocq installations also provide the compatibility command:

```sh
coqc SN_Haskell_Rocq.v
```

The Rocq file machine-checks the mathematical decreasing-measure argument in an intrinsically typed de Bruijn representation and uses the same measurement equations implemented by the Haskell programs. The proof makes no unproved assumptions other than the correctness of the standard libraries.

## Repository note

This repository intentionally contains the code and proof artifacts only, not the paper.
