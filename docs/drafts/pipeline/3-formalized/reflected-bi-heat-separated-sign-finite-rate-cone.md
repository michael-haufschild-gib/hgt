# Reflected bi-heat separated-sign finite-rate cone

- **ID:** RBH-SSF
- **Stage:** 3-formalized
- **Type:** MULTI-RATE INCOMMENSURATE SIGNED RECEIVER CLASSIFICATION
- **Parent:** RBH-ATR / RBH-FCC
- **Frontier-map policy:** read only

## Frozen conjecture

Let finite nonempty low- and high-rate blocks have positive magnitudes `p_i,q_j`
and positive rates `lambda_i,mu_j`.  Suppose one separator `kappa>0` satisfies

`lambda_i < kappa ≤ mu_j`

for every low index `i` and high index `j`.  Define

`F(t) = -Σ_i p_i sinh(lambda_i*t) + Σ_j q_j sinh(mu_j*t)`

and its wall derivative

`D = Σ_j q_j*mu_j - Σ_i p_i*lambda_i`.

Prove the exact classification

`(∀t, F(t)=0 ↔ t=0) ↔ 0≤D`.

Then prove finite arbitrary-real-power physical aperture factorization and an RH
equivalence for every separated-sign packet satisfying `0≤D`.

## Corpus basis

- `sinh_div_self_strictMonoOn`: `sinh u/u` strictly increases on `(0,∞)`.
- `tendsto_sinh_div`: exact divided-sinh germ at zero.
- RBH-ATR: unequal-rate quotient tends to infinity and arbitrary-real-power
  physical normalization.
- `HTGeometry.ExponentialSumZeros` explicitly records sign-change combinatorics
  as missing from its multiplicity-bound half of Descartes/Laguerre theory.
- Mandatory corpus search found no separated-sign finite hyperbolic packet theorem.

## Expected consequence

Closes an arbitrary-cardinality, genuinely incommensurate signed RBH chamber.
Within this chamber no higher nonlinear rate interaction creates extra wall roots:
the complete cone is the single linear first-derivative inequality `0≤D`.

## Provisional literature audit

- arXiv:2304.02307 and arXiv:1708.05530 concern Descartes sign rules for
  ordinary polynomials.
- arXiv:1601.05826 gives a multivariate circuit version.
- Search found no source stating this separated hyperbolic-sine packet cone or
  its RBH aperture interpretation.

Priority remains provisional pending broader expert review.

## Status

- Mandatory corpus search complete.
- Conjecture frozen.
- Paper proof dependency-closed.
- Formalized in
  `GaloisForLFunctions.RHTower.ReflectedBiHeatSeparatedSignFiniteRateCone`.
- Direct `lake env lean` check passed.
- Targeted module build passed.
- Axiom audit passed: only `propext`, `Classical.choice`, and `Quot.sound`.

## Formal theorem package

- `reflectedBiHeatSeparatedSignReporter_pos`
- `tendsto_sinh_rate_mul_div_self_nhdsGT_zero`
- `tendsto_reflectedBiHeatSeparatedSignReporter_div_self_nhdsGT_zero`
- `tendsto_reflectedBiHeatLowRateSum_div_sinh_atTop`
- `exists_pos_reflectedBiHeatSeparatedSignReporter_eq_zero_of_derivative_neg`
- `reflectedBiHeatSeparatedSignWallSelective_iff`
- `reflectedBiHeatSeparatedSignApertureGap_eq_reporter`
- `reflectedBiHeatSeparatedSignApertureGap_eq_zero_iff`
- `riemannHypothesis_iff_reflectedBiHeatSeparatedSignApertureGap_eq_zero`

## New exact insight

For arbitrary finite nonempty sign-separated rate blocks, all nonlinear
hyperbolic cancellation is governed exactly by one first-order wall datum:

`F` has only its forced wall zero iff `F'(0)≥0`.

The forward direction uses strict monotonicity of `sinh(u)/u` around one rate
separator.  The converse is constructive: `F'(0)<0` gives a negative value
immediately right of the wall, while any one high-rate positive atom dominates
the complete finite low block at infinity, forcing an additional positive root.
This remains exact for arbitrary cardinalities and irrational rates.

Canonical real-power aperture normalization transports the entire chamber to
physical RBH gaps and makes every packet satisfying the derivative inequality
an exact RH receiver.

## Remaining boundary

- Coefficient patterns with two or more rate-order sign changes.
- Rate collisions without a strict low/high separator.
- Source-derived coefficient laws rather than receiver-cone membership.
- Infinite/non-polynomial packets and non-diagonal collision channels.
