# Correspondence between the paper, Haskell, and Rocq

This document accompanies **de Vrijer's Strong Normalization in Haskell**,
the ten-page main-text version. It collects the correspondence tables and
formalization details moved out of the paper. The source files are
[`SN_Haskell.hs`](SN_Haskell.hs) and [`SN_Haskell_Rocq.v`](SN_Haskell_Rocq.v).

## The common measurement algebra

| Mathematical construction | Haskell | Rocq |
| --- | --- | --- |
| Measurement domain $D_\tau$ | `Meas a` | `den t` |
| Base carrier $\mathbb{N}$ | `Natural`, stored by `N` | `nat` |
| Arrow carrier $(D_\sigma\to D_\tau)\times\mathbb{N}$ | `F` stores a function and a star component | A function–natural-number pair |
| Star component $a^\ast$ | `star` | `star` |
| Dot application $f^\bullet(a)$ | `dot`, `app` | `dot`, `appD` |
| Charge lifting $\mathsf{add}_k(a)$ | `add` | `add` |
| Canonical measurement $\mathsf{c}_\tau(n)$ | `canon` | `canon` |
| Abstraction operation | `lam` | `lamD` |

Haskell's `type Term a = Meas a` makes the representation final:
constructing a source term with `var`, `app`, and `lam` computes its
measurement. Rocq uses intrinsically typed de Bruijn syntax, `tm Gamma t`,
and its `eval` function folds that syntax into the same measurement
algebra. The relation $\simeq_\tau$ defined in the paper compares Haskell
values with mathematical measurements recursively by type.

## Correspondence with the proof statements

The statement numbers below are unchanged in the ten-page paper.

| Paper statement | Rocq definitions and results |
| --- | --- |
| Definition 1: orders and admissibility | `ge`, `gt`, `adm`, together with `gt_ge`, `ge_star`, and `gt_star` |
| Proposition 2: the Haskell program implements the equations | Proved in the paper by compatibility of `add` and `canon` with $\simeq$, followed by structural induction on the source term |
| Lemma 3: auxiliary operations, Equations (4)–(12) | `star_add`, `add_ge_same`, `add_gt_same`, `add_ge_by_k`, `add_gt_by_k`, `add_adm`, `add_positive`, `canon_ge`, `canon_gt`, and `canon_adm`; the star component of `canon` follows directly from its definition |
| Lemma 4: representation invariant and monotonicity | `eval_adm_ge`, with projections `eval_adm` and `eval_ge` |
| Lemma 5: substitution | Typed `rename` and `subst`, followed by `eval_rename`, `eval_subst`, and the one-variable theorem `eval_subst0` |
| Lemma 6: decrease under full contextual reduction | The four-constructor relation `step` and theorem `step_decreases` |
| Theorem 7: one-step numerical decrease and strong normalization | `star_decreases`, `strong_normalization`, `strong_normalization_all`, and `strong_normalization_closed` |
| Theorem 7: the numerical sequence-length bound | Derived in the paper by iterating the machine-checked one-step theorem `star_decreases` |
| Proposition 8: Haskell/de Bruijn correspondence, Equation (14) | Proved in the paper by Proposition 2 and structural induction on the named source term; the Rocq development starts from `tm` and `eval` |
| Running example | `id_o_tm`, `eta_o_tm`, `ex_tm`, `ex_star`, `ex_one`, and `ex_sn` |

The order comparisons at arrow type quantify over admissible arguments.
Admissibility requires preservation of admissibility and both non-strict
and strict monotonicity on admissible inputs. The non-strict comparison
is a quasi-order.

## Substitution and contextual reduction

The theorem `eval_subst0` states the indexed form of Lemma 5:

$$
\mathsf{eval}_\rho(\mathsf{subst0}\ N\ M)
=\mathsf{eval}_{\mathsf{eval}_\rho(N)::\rho}(M).
$$

Here extension by $a::\rho$ is implemented by `val_ext`: index zero
receives $a$, and successor indices use the previous valuation.

The relation `step` has constructors for contraction at a root beta-redex,
reduction in the function position of an application, reduction in its
argument position, and reduction beneath an abstraction. Thus it is the
full contextual reduction relation of Lemma 6. Under an admissible
valuation, `step_decreases` proves decrease in the recursively defined
strict order; `star_decreases` projects that result to the natural-number
component.

## Strong normalization and the length bound

Rocq defines `SN M` as accessibility for the inverse of `step`.
The theorem `strong_normalization` uses well-founded induction on
`star t (eval rho M)`. The theorem `strong_normalization_all` supplies a
canonical admissible valuation for an arbitrary context, and
`strong_normalization_closed` specializes the result to closed terms.

The paper obtains the numerical bound by observing that each step lowers
the natural-number star component by at least one. The finite-sequence
length bound is this mathematical consequence of `star_decreases`;
the Rocq accessibility theorems establish strong normalization.

## The running example

With index zero denoting the nearest binder, the named term
$E=(\lambda f^{o\to o}.\lambda x^o.fx)(\lambda x^o.x)$ becomes

$$
(\lambda^{o\to o}.\lambda^o.\underline{1}\,\underline{0})
(\lambda^o.\underline{0}).
$$

In the doubly nested body, `TVar vz` represents $x$ and
`TVar (vs vz)` represents $f$. This is the term `ex_tm` in the source.
The checked example `ex_star` states that its star component is $2$;
`ex_one` supplies a reduction step, and `ex_sn` derives its strong
normalization.

## Proof assumptions

The source contains completed proofs and uses functional extensionality
from Rocq's standard library for equality of function components.
The repository's `check.sh` reports the assumptions of the principal
theorems.
