# HCF rational pair / centered-shift exact correction

- **ID:** HCF-RP2-SHIFT-CORRECTION
- **Stage:** 2-fully-proven finite theorem; contour continuation in progress
- **Type:** THEOREM survivor
- **Source:** Route HCF; `XiEntireGaussianReflectionFibreCovariance` +
  `XiCenteredRealShiftDiagonalExtractor`

## Goal

Replace exponentially growing entire-Gaussian pair kernel by fixed-pole rational kernel and prove
that its prescribed pole correction is exactly existing source-only centered positive-real shift
extractor. This is missing algebraic connector for a bounded, pre-divisor pair covariance.

## Exact finite statement

For `eps ≠ 0`, away from prescribed collisions `z-w=±eps`, let

`K_eps(z,w) = (z-w)^2 / ((z-w)^2-eps^2)`.

Then

`1-K_eps(z,w) = eps/2 * ((w+eps-z)⁻¹-(w-eps-z)⁻¹)`.

Consequently, for any finite weighted packet,

`totalMass - centeredShiftDiagonalRow_eps(w) = rationalPairRow_eps(w)`,

and after weighting and summing in `w`,

`totalMass^2 - centeredShiftDiagonalCovariance_eps = rationalPairCovariance_eps`.

All shifts and poles are chosen before any divisor expansion. No limiting interchange, zero-fitted
window, simplicity assumption, or numerical input occurs.

## Corpus audit

- `meromorphicCauchyPairKernel_eq_resolventDifference` proves fixed-pole partial fractions but not
  identification with centered source shift.
- `centeredPrimeArchRealShiftDiagonalExtractor` supplies exact continued pole–Gamma–von-Mangoldt
  centered shifts and converges to analytic multiplicity.
- `HedenmalmSubmicroscopicScalarDiagonalCovarianceNoGo` kills scalar diagonal minorants at finite
  displacement; pair complement is the positive survivor.
- Entire Gaussian pair covariance has exact nested source landing but exponential horizontal-edge
  blow-up. Rational kernel avoids that amplification.
- Whole-corpus research found no theorem equating total mass minus centered shift with rational
  pair covariance.

## Remaining after finite theorem

1. Extend proved analytic-cofactor two-pole contour identity through finite Xi factorization:
   rational pair source contour equals zero-pair row plus prescribed centered-shift pole
   correction.
2. Apply source-native integer-harmonic dephasing to retain equal-ordinate fibres.
3. Find a source-only linear normalization or direct HCF domination.
4. Prove quantitative pole–Gamma upper at the reflected HCF ceiling `15872/21125`.

The finite theorem moves source architecture but does not prove 75%.

## Verification

- Lean module:
  `GaloisForLFunctions/RHTower/XiCenteredRealShiftCauchyPairExactCorrection.lean`.
- Direct source check: pass.
- Targeted `lake build`: pass.
- `#print axioms` for all nine public theorems: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella integration deferred while `RHTower.lean` is contested by concurrent work.

## Log

- 2026-08-29 — conjectured from fixed-pole resolvent decomposition and centered real-shift
  multiplicity extractor; scalar and entire-Gaussian alternatives failed hostile sign/growth
  checks; Lean formalization started.
- 2026-08-29 — exact atomic, weighted-row, and full covariance identities proved in Lean at
  arbitrary finite displacement; reciprocal-scale specialization matches existing rational pair
  covariance definition.
- 2026-08-30 — proved local rectangle cofactor theorem: rational pair kernel against any analytic
  row equals `2πi` times its centered positive-real shift when both prescribed poles are enclosed.
  Added zero-free log-derivative and reciprocal-scale corollaries whose right side is definitionally
  the existing centered real-shift extractor. Direct source check, targeted build, and axioms audit
  pass.
