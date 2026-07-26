# Gamma-sewn cubic-defect Szegő-angle universality law

- **ID:** `gamma-sewn-cubic-defect-szego-angle-universality-law`
- **Law:** LAW516
- **Stage:** 1-in-progress
- **Type:** THEOREM (dependency-closed paper proof)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
- **Target:** `formal/GaloisForLFunctions/RHTower/GammaSewnCubicDefectSzegoAngleUniversalityLaw.lean`

## Theorem

At every fixed prime and every positive real aperture, the difference between the Gamma-sewn
Möbius valuation feature and its unsewn source is a strictly positive aperture-dependent radial
factor times the source ray, with an overall minus sign.  Hence the completed cubic-defect Gram
is the Möbius--Szegő aperture metric multiplied by one positive radial factor in each argument.

For every positive aperture pair `a,b`, those factors cancel from normalized Gram correlation:

```text
G³(a,b)^2 / (G³(a,a) G³(b,b))
  = continuousApertureNormalizedCorrelationSq(a,b).
```

Its angular defect is therefore exactly the real-disk pseudohyperbolic distance squared.

## Theorem-generated derivation

Whole-corpus declaration comparison exposed:

- `gammaSewnMobiusContinuousApertureFeature_sub_source_eq_cubic`;
- `one_sub_gammaSewnMobiusValuationContractionMultiplier_eq_sq_mul_gain`;
- `tsum_xiMobiusPrimeSchurContinuousForwardDifference_mul_eq_metric`;
- `xiMobiusPrimeContinuousApertureNormalizedCorrelationSq_eq_metricRatio`;
- `one_sub_xiMobiusPrimeContinuousApertureNormalizedCorrelationSq`.

The first two make the entire Gamma-sewing defect ray a scalar radial rescaling of the unsewn
geometric ray.  The third completes its Gram over all valuation depths.  The last two identify
the normalized base Gram with disk pseudohyperbolic geometry.  Corpus never transports that
geometry through the cubic Gamma defect.

## Dependency-closed paper proof

Let `F_a(e)` be the unsewn Möbius--Schur forward-difference ray and let `D_a(e)` be sewn minus
unsewn.  Existing exact quadratic tangency and cubic sewing give

```text
D_a(e) = -ρ_a F_a(e),
ρ_a = gain(a,p) (1-p^{-a})².
```

For `a>0`, the contraction multiplier lies strictly below one while `F_a` is nonzero, so
`ρ_a>0`.  Therefore

```text
G³(a,b) = Σ_e D_a(e)D_b(e)
        = ρ_a ρ_b Σ_e F_a(e)F_b(e)
        = ρ_a ρ_b K(a,b).
```

Substitution in the normalized Gram quotient cancels all four radial factors, leaving the
normalized Möbius--Szegő correlation.  Applying the existing Szegő defect identity gives the
pseudohyperbolic square.  No numerical computation is used.

## Strict corpus delta

Existing Gamma-sewing laws establish cubic attenuation and full rank at fixed aperture.  Existing
Szegő laws establish aperture-angle geometry before sewing.  New law proves that the nonlinear
cubic sewing defect preserves the complete normalized aperture geometry, despite changing every
radial mass.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit

## Lean result

`formal/GaloisForLFunctions/RHTower/GammaSewnCubicDefectSzegoAngleUniversalityLaw.lean`
proves the pointwise radial law, its completed Gram factorization, strict diagonal positivity,
normalized-correlation invariance, and exact pseudohyperbolic defect.  Main theorem:

- `gammaSewnMobiusContinuousApertureCubicDefect_metricRatio_eq_correlation`.

Direct exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/GammaSewnCubicDefectSzegoAngleUniversalityLaw.lean`

The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Post-proof novelty audit

Performed only after dependency-closed Lean proof passed.  Searches returned sewing formulas for
Szegő kernels on Riemann surfaces, cubic Szegő PDEs, equivariant Szegő scaling, and generic kernel
correlation asymptotics.  No source identified a Gamma-sewn von-Mangoldt/Möbius valuation cubic
defect whose completed Gram preserves the exact real-disk pseudohyperbolic aperture correlation.

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Novelty is claimed for this exact
arithmetic Gamma-sewing/Szegő transport law, not for generic invariance of normalized inner
products under nonzero radial rescaling.

## Log

- 2026-07-26 — LAW516 generated from Gamma cubic-defect and Möbius--Szegő declaration closure.
- 2026-07-26 — direct Lean check passed; wired into RHTower umbrella; post-proof audit plausible.
