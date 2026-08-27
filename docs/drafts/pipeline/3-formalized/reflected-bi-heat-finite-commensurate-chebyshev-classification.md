# Reflected bi-heat finite commensurate Chebyshev classification

- **ID:** RBH-FCC
- **Stage:** 3-formalized
- **Type:** ARBITRARY FINITE SIGNED RECEIVER CLASSIFICATION
- **Parent:** RBH-S3S / RBH-STS
- **Frontier-map policy:** read only

## Frozen conjecture

For arbitrary finite real coefficients `a_i`, define

`F_a(t)=Σ_{i=0}^{N-1} a_i sinh((i+1)t)`

and the explicit second-kind Chebyshev polynomial

`Q_a(X)=Σ_i a_i U_i(X)`.

Prove:

1. `F_a(t)=sinh(t) Q_a(cosh(t))` for every real `t`;
2. `t=0` is the only real zero of `F_a` iff `Q_a(u)≠0` for every `u>1`;
3. the physical finite aperture packet at `x^(i+1)`, with canonical weights
   `x^((i+1)/2)`, equals the common nonzero RBH coefficient times `F_a`;
4. every Chebyshev-wall-selective packet gives an RH-equivalent receiver.

This must include `N=0` without side assumptions and recover two- and
three-scale results as low-degree shadows.

## Corpus basis

- RBH-S3S all-natural-power aperture normalization.
- Mathlib theorem `Polynomial.Chebyshev.U_real_cosh` in active toolchain:
  `U_n(cosh t) sinh t = sinh((n+1)t)`.
- RBH-S3S `arcosh` converse pattern.
- Mandatory corpus search found no finite commensurate RBH Chebyshev theorem.

## Expected consequence

This closes arbitrary finite signed cancellation for commensurate diagonal RBH
apertures.  Analytic receiver design reduces exactly to real-polynomial
nonvanishing on `(1,∞)`; remaining signed RBH escapes require incommensurate
rates, non-diagonal collision structure, or infinite/non-polynomial packets.

## Status

- Mandatory corpus search complete.
- Conjecture frozen.
- Paper proof dependency-closed.
- Formalized in
  `GaloisForLFunctions.RHTower.ReflectedBiHeatFiniteCommensurateChebyshevClassification`.
- Direct `lake env lean` check passed.
- Targeted module build passed.
- Axiom audit passed: only `propext`, `Classical.choice`, and `Quot.sound`.

## Formal theorem package

- `reflectedBiHeatFiniteCommensurateReporter_factor`
- `reflectedBiHeatFiniteCommensurateWallSelective_iff`
- `reflectedBiHeatFiniteCommensurateApertureGap_eq_reporter`
- `reflectedBiHeatFiniteCommensurateApertureGap_eq_zero_iff`
- `riemannHypothesis_iff_reflectedBiHeatFiniteCommensurateApertureGap_eq_zero`

## New exact insight

Arbitrary finite signed diagonal RBH cancellation at commensurate aperture rates is
not a separate transcendental problem: it is exactly root avoidance for one
explicit second-kind Chebyshev polynomial on `(1,∞)`.  This equivalence includes
the empty packet without side assumptions, and the physical multiplicity-leading
packet inherits the same factorization.  Therefore every such polynomial with no
root on `(1,∞)` is an unconditional exact RH receiver.

## Remaining boundary

- Incommensurate finite rates, where no one-variable polynomial reduction exists.
- Non-diagonal matrix channels after rate-collision grouping.
- Infinite or non-polynomial aperture packets.

## Provisional literature audit

- arXiv:1708.08360 uses Chebyshev recurrences for hyperbolic matrix functions.
- arXiv:1504.01141 studies generalized second-kind Chebyshev polynomials.
- arXiv:1904.12438 studies the xi heat flow.

No audited source states this RBH aperture-packet classification or its Lean
formalization.  Priority claim remains provisional pending broader expert review.
