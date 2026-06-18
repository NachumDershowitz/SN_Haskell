# SN_Haskell

Haskell implementations and a Coq formalization of de Vrijer's decreasing
measure for strong normalization of the simply typed lambda-calculus.

## Contents

- `SN_Haskell.hs` — the main higher-order/final Haskell implementation.
- `SN_Haskell_Named.hs` — a named, environment-passing implementation kept for comparison.
- `SN_Haskell_Trace.hs` — a small tracer that prints reduction steps and measures.
- `SN_Haskell_HenkExamples.hs` — checks the examples from Henk Barendregt's note.
- `SN_Haskell_Coq.v` — a Coq formalization of the measure construction and proof.
- `checks/` — logs from successful Haskell and Coq checks, if included in the checkout.

## Haskell checks

The Haskell files use only the standard `base` library. With GHC available,
run:

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

The first two programs print `2`. The trace program prints the reduction
traces. The examples checker reports success if all checked examples pass.

## Coq check

The Coq file was checked with jsCoq using:

```sh
jscoq run -v -l SN_Haskell_Coq.v
```

or, with `npx`:

```sh
npx jscoq run -v -l SN_Haskell_Coq.v
```

The Coq development formalizes de Vrijer's semantic domains, the decreasing
measure, typed syntax, substitution, full contextual beta-reduction, and the
strong-normalization argument. It also includes a mathematical model of the
pure higher-order fragment used by the main Haskell implementation, with bridge
lemmas connecting that model to the source-term semantics.

## Expected artifact status

A clean checkout should contain the Haskell files, the Coq file, this README,
and any optional check logs. It should not require generated build artifacts.
