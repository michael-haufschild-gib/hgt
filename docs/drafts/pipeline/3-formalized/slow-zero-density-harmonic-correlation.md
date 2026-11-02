# Harmonic correlation at slowly vanishing prime density

- **ID:** slow-zero-density-harmonic-correlation
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Γ12; `power-regular-density-twins.md`.
- **Result:** Relative logarithmic density `κ<1/2` forces cofinal harmonic growth beyond every exponent `α<1−2κ`, without a power-error hypothesis.

## Boundary

Zero Euler mass forces `A_P(N)>C(1+log N)^α` at arbitrarily large
horizons for every `α<1` and `C`. Thus no fixed power-error theorem
includes the zero-Euler-mass endpoint.

## Theorem and proof

For every `0≤α<1` and `G`, arbitrarily large `N` satisfy
`Σ_(n≤N)ω_P(n)/n > G(1+log N)^α`.

General form: if `A_P(N)/(1+log N)→κ≥0`, the same conclusion holds
for every `0≤α<1−2κ`. There is no quantitative density-error premise.

Derivation at `κ=0`: choose `α<β<1`. Mertens and `A_P=o(log)` give the
one-sided prime-mean bound `primeMean(ω_P,N)≥β log N−C`.
The corpus Euler-product and Abel estimates then give
`F_P(1+σ)≫σ^(−β)`. A global bound on the harmonic sum by
`G(1+log N)^α` would give `F_P(1+σ)≪σ^(−α)`, a contradiction.
Absorbing a finite initial segment makes the violation cofinal. For
general `κ`, choose `α<β<1−2κ` and use the same one-sided bound.

This establishes cofinal large correlation; it
does not give an eventual lower bound or the relative spectral tail.

## Lean

`RenormalizedIntersectionTheory/TheSparseFlipRetainsLargeHarmonicCorrelation.lean`:

- `exists_gaugeHarmonicSum_gt_rpow_of_primeMean_lower`
- `frequently_gaugeHarmonicSum_gt_rpow_of_logMass_ratio_tendsto`
- `frequently_gaugeHarmonicSum_gt_rpow_of_logMass_ratio_tendsto_zero`

Kernel check passed; both density-limit capstones use only
`propext`, `Classical.choice`, and `Quot.sound`.

## Remaining analytic question

Does the signed harmonic sum vary regularly with logarithmic horizon
under `A_P=o(log)`? The nonnegative convolution `1*ω_P` provides a
positive smoothed mean, but deconvolution needs control of signed
oscillation. Such control must be proved before using it in a
conductor-series sufficiency argument.
