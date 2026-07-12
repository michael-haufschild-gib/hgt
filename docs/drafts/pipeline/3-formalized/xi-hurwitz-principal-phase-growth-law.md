# Xi--Hurwitz principal-phase growth law

- **ID:** `xi-hurwitz-principal-phase-growth-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (`NOVELTY UNVERIFIED`)
- **Source:** Hurwitz monodromy character values on the Xi divisor and the fixed-width rectangular Weil carrier

## Statement

For every Xi divisor point `rho` in the open critical strip, let

\[
q(\rho)=\exp(-2\pi i\rho).
\]

The open-strip branch removes the usual argument ambiguity:

\[
\operatorname{Arg}(-q(\rho))=-2\pi\left(\operatorname{Re}\rho-\tfrac12\right).
\]

Consequently, on the positive transverse Xi divisor,

\[
\sup_{\operatorname{Re}\rho>1/2}
  \frac{|\operatorname{Arg}(-q(\rho))|}{2\pi}
=\sup_{\operatorname{Re}\rho>1/2}
  \left(\operatorname{Re}\rho-\tfrac12\right)
=\delta_\Xi.
\]

For every fixed width `L>0`, the already formalized rectangular growth theorem identifies
`delta_Xi` with the sharp power exponent of the logarithmically sampled rectangular Weil values.
Thus the supremal principal phase of the Hurwitz monodromy character is exactly the sharp power
growth exponent of one scalar Weil sequence.

## Lean theorem surface

- `monoScalar_neg_arg_openCriticalStrip`
- `xiHurwitzRightPrincipalPhase_eq_transverse`
- `xiHurwitzRightPrincipalPhaseSet_eq_transverseSet`
- `xiHurwitzRightPrincipalPhaseSup_eq_transverseSup`
- `riemannHypothesis_iff_xiHurwitzRightPrincipalPhaseSup_eq_zero`
- `not_riemannHypothesis_iff_xiHurwitzRightPrincipalPhaseSup_pos`
- `xiHurwitzPrincipalPhaseSup_is_sharp_rectangular_power_exponent`
- `xiHurwitzPrincipalPhaseSup_is_sharp_rectangular_power_exponent_of_not_rh`
- `riemannHypothesis_iff_rectangular_weil_norm_subpower`
- `riemannHypothesis_iff_exists_rectangularWeilTailSubpowerLower`

The implementation is
`formal/GaloisForLFunctions/RHTower/XiHurwitzPrincipalPhaseGrowth.lean`.

## Status registers

- [PROVED IN LEAN] The exact principal-argument identity holds on the full open strip with no
  branch exception.
- [PROVED IN LEAN] The normalized absolute principal phase equals the positive transverse
  displacement pointwise.
- [PROVED IN LEAN] The two value sets and their suprema are equal.
- [PROVED IN LEAN] RH is equivalent to vanishing of the supremal principal phase.
- [PROVED IN LEAN] For every fixed `L>0`, on the nonempty positive-transverse branch this phase
  supremum is the sharp rectangular power exponent.
- [PROVED IN LEAN] The separate divisor-nonemptiness hypothesis is discharged by `not RH`.
- [PROVED IN LEAN] RH is equivalent to an `n^o(1)` norm upper bound for the fixed-width sequence.
- [PROVED IN LEAN] More weakly, RH is equivalent to the existence of one tail with the one-sided
  lower loss `Q(L,n) >= -C_epsilon n^epsilon` for every positive `epsilon`; no positivity,
  absolute-value bound, or tail-admissibility interface remains.
- [NOVELTY UNVERIFIED] The branch identity is standard complex analysis.  The coupled HGT-value /
  sharp-Weil-growth law requires a parent-theory and literature audit before any scientific-novelty
  claim.

## Positive boundary statement

When the positive transverse divisor is empty, every Xi zero is on the critical line and the
rectangular family is uniformly bounded.  The law therefore has a positive zero-phase boundary,
not a no-go branch.

## Preliminary parent-theory audit

Lagarias and Li compute the multivalued continuation and monodromy functions of the Lerch zeta
function, including the exponential coordinate `z=exp(2 pi i a)`.  Their work supplies the closest
monodromy parent but does not identify Xi-zero-indexed character phases with a sharp Weil growth
exponent:

- J. C. Lagarias and W.-C. W. Li, *The Lerch Zeta Function II. Analytic Continuation*,
  <https://arxiv.org/abs/1005.4967>.
- J. C. Lagarias and W.-C. W. Li, *The Lerch Zeta Function III. Polylogarithms and Special
  Values*, <https://arxiv.org/abs/1506.06161>.

Classical and explicit zero-density work measures horizontal displacement statistically; for
example, Simonič bounds the number of zeros to the right of a line.  This is distinct from the
present exact equality between a supremal HGT character value and the sharp exponent of one Weil
carrier: <https://arxiv.org/abs/1910.08274>.

No exact parent result was located in this preliminary pass.  This supports only
`NOVELTY UNVERIFIED`, not a scientific-novelty claim; a specialist bibliography audit is still
required.

## Remaining RH-bearing theorem

The weakest current burden is now explicit.  For one fixed `L>0`, prove from the source-defined
Gamma integral, moving von Mangoldt tent, and polar boundary square that their rectangular value
has one tail satisfying

\[
  Q_{L,n}\ge -C_\varepsilon n^\varepsilon
  \qquad(\varepsilon>0,\ n\gg1).
\]

Two analytic steps remain outside Lean:

1. the exact Guinand--Weil identification of the piecewise-linear rectangular source coefficient
   with `xiRectangularWeilLogCoefficient`;
2. the one-sided subpower lower estimate for that completed source coefficient.

The first is a bridge theorem at bounded-variation regularity.  The second is the RH-bearing
source estimate; the present work does not claim it.

## Verification

- The exact module and its Lake target compile with the repository toolchain.
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for every capstone.
- The module contains no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration.
