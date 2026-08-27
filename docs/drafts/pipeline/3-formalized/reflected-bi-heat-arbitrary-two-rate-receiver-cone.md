# Reflected bi-heat arbitrary two-rate receiver cone

- **ID:** RBH-ATR
- **Stage:** 3-formalized
- **Type:** INCOMMENSURATE SIGNED RECEIVER CLASSIFICATION
- **Parent:** RBH-FCC / RBH-STS
- **Frontier-map policy:** read only

## Frozen conjecture

For real rates `0 < lambda < mu` and coefficients `a,b`, define

`F(t) = a sinh(lambda t) + b sinh(mu t)`.

Prove the exact classification

`(∀ t, F(t)=0 ↔ t=0)` iff

`(b=0 ∧ a≠0) ∨ (b≠0 ∧ 0≤b(lambda*a+mu*b))`.

The analytic core must prove that

`t ↦ sinh(mu*t)/sinh(lambda*t)`

maps `(0,∞)` continuously and strictly increasingly onto
`(mu/lambda,∞)`.  Then prove arbitrary real-power physical aperture
factorization at `x^lambda` and `x^mu`, and obtain an exact RH receiver for
every pair in the classified cone.

## Corpus basis

- `sinh_div_self_strictMonoOn`: strict increase of `sinh u/u` on `(0,∞)`.
- `tendsto_real_sinh_div_self_nhdsNE_zero`: divided-sinh germ at zero.
- `div_sinh_strictAntiOn` and `sinh_lt_mul_cosh`: hyperbolic quotient tools.
- RBH-STS physical leading-jet normalization and wall classification pattern.
- Mandatory corpus searches found no arbitrary-real-rate RBH receiver cone.

## Expected consequence

Closes every two-channel diagonal RBH receiver, including genuinely
incommensurate aperture rates.  Shows cone boundary is determined only by the
first wall derivative `lambda*a+mu*b`, despite nonlinear transcendental rates.

## Provisional literature audit

- arXiv:0903.1676 studies inverse-hyperbolic monotonicity inequalities.
- arXiv:1212.4681 studies generalized hyperbolic-sine inequalities.
- arXiv:math/0401074 studies zeros of exponential sums.
- arXiv:1904.12438 studies the xi heat flow.

No audited source states this RBH coefficient cone or physical RH receiver.
Priority remains provisional pending broader expert review.

## Status

- Mandatory corpus search complete.
- Conjecture frozen.
- Paper proof dependency-closed.
- Formalized in
  `GaloisForLFunctions.RHTower.ReflectedBiHeatArbitraryTwoRateReceiverCone`.
- Direct `lake env lean` check passed.
- Targeted module build passed.
- Axiom audit passed: only `propext`, `Classical.choice`, and `Quot.sound`.

## Formal theorem package

- `self_mul_cosh_div_sinh_strictMonoOn`
- `sinh_rate_ratio_strictMonoOn`
- `mu_div_lambda_lt_sinh_rate_ratio`
- `tendsto_sinh_rate_ratio_nhdsNE_zero`
- `tendsto_sinh_rate_ratio_atTop`
- `exists_pos_sinh_rate_ratio_eq_iff`
- `reflectedBiHeatArbitraryTwoRateWallSelective_iff`
- `reflectedBiHeatWeightedRealPowerApertureGap_eq_sinh`
- `reflectedBiHeatArbitraryTwoRateApertureGap_eq_reporter`
- `reflectedBiHeatArbitraryTwoRateApertureGap_eq_zero_iff`
- `riemannHypothesis_iff_reflectedBiHeatArbitraryTwoRateApertureGap_eq_zero`
- `riemannHypothesis_iff_reflectedBiHeatIrrationalTwoRateApertureGap_eq_zero`

## New exact insight

For every `0 < lambda < mu`, the transcendental quotient
`sinh(mu*t)/sinh(lambda*t)` maps `(0,∞)` strictly increasingly and onto
`(mu/lambda,∞)`.  Therefore the entire two-rate signed wall-selective region is
the semialgebraic cone

`(b=0 ∧ a≠0) ∨ (b≠0 ∧ 0≤b(lambda*a+mu*b))`.

Only the first wall derivative controls the boundary, even for irrational rate
ratio.  Canonical real-power normalization transports this classification to
physical RBH apertures.  Rates `(1,sqrt 2)` and weights `(-sqrt 2,1)` give an
explicit genuinely incommensurate exact RH receiver.

## Remaining boundary

- Three or more incommensurate signed rates: multiple off-wall roots can occur.
- Collision-grouped non-diagonal matrix channels.
- Infinite or non-polynomial aperture packets.
