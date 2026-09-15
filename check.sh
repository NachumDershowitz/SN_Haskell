#!/usr/bin/env bash
# Run the real tools; a missing tool is an error, not a successful check.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd -P)"
for tool in ghc runghc rocq; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    printf 'Required tool is not on PATH: %s\nNo complete check was performed.\n' "$tool" >&2
    exit 2
  fi
done
files=(SN_Haskell.hs SN_Haskell_Named.hs SN_Haskell_Trace.hs SN_Haskell_HenkExamples.hs)
for file in "${files[@]}" SN_Haskell_Rocq.v; do
  test -f "$ROOT/$file" || { printf 'Missing source: %s\n' "$file" >&2; exit 2; }
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/SN_Haskell-check.XXXXXX")"
trap 'rm -rf -- "$TMP"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
for file in "${files[@]}" SN_Haskell_Rocq.v; do cp "$ROOT/$file" "$TMP/$file"; done
cd "$TMP"
ghc --version
rocq -v
for file in "${files[@]}"; do
  printf '\n== Typechecking %s ==\n' "$file"
  ghc -Wall -Werror -fforce-recomp -fno-code "$file"
done
for file in SN_Haskell.hs SN_Haskell_Named.hs; do
  printf '\n== Running %s ==\n' "$file"
  result="$(runghc "$file")"
  printf '%s\n' "$result"
  test "$result" = 2 || { printf 'Expected exactly 2.\n' >&2; exit 1; }
done
for file in SN_Haskell_Trace.hs SN_Haskell_HenkExamples.hs; do
  printf '\n== Running %s ==\n' "$file"
  runghc "$file"
done
printf '\n== Compiling the Rocq proof ==\n'
rocq compile SN_Haskell_Rocq.v
cat > Audit_Assumptions.v <<'ROCq'
Require Import SN_Haskell_Rocq.
Print Assumptions eval_subst0.
Print Assumptions step_decreases.
Print Assumptions star_decreases.
Print Assumptions strong_normalization_all.
Print Assumptions strong_normalization_closed.
Print Assumptions ex_star.
ROCq
printf '\n== Assumptions of the principal theorems ==\n'
rocq compile Audit_Assumptions.v
printf '\nAll Haskell executions, Haskell typechecks, and Rocq compilations above completed successfully.\n'
