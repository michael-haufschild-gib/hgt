# Explicit power-log positivity and conductor confinement

- **ID:** explicit-power-log-positivity-and-confinement
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ../../../reports/review-3110/obstacles-summary.md, A1
- **Statement:** Replace the unspecified conductor-confinement constant by a proved explicit constant and sharpen the accuracy and overlap exponents in complete Weil positivity.

## Mathematical targets

1. Explicit conductor confinement, uniformly in the horizon: squared projection error at most `η` for `log R ≤ C (K + 1) / η^p`, with numerical `C` and improved `p`.
2. An explicit reverse defect gap and numerical positive overlap exponent.
3. Optimized low-band, projection-accuracy, and high-cutoff exponents in all-vector positivity, with the residual and confinement ceilings accounted for.

## Existing bounds

`ConductorBandTopTailBounds` proves `p = 3` with an unspecified constant. `TheCompleteWeilMatrixIsPositiveAtPowerOfLogOverlap` uses `Q₁ = floor((log N)^(1/12))`, squared error `η ≍ c⁻¹⁰`, cutoff `log R ≪ c⁴⁶`, and `α < min(1/500, 1/(60 C_cut))`. The constant originates in smooth–rough conditioning.

## Gates

- [x] Precise target and source dependencies identified.
- [ ] Dependency-closed proof of the strengthened bounds.
- [ ] Lean formalization, direct file audit, and transitive axiom audit.
