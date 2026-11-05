# The Weil symbol has an integrable logarithmic remainder

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The literal archimedean Weil multiplier is `(1/2)log(1+ξ²)+c₀` minus the Fourier transform of a positive, bounded, integrable even kernel.

## Proof

For `t>0`, put `r(t)=ω(t)-exp(-t)/(2t)`. Since
`1-exp(-2t)≤2t` and `exp(-t)≤exp(-t/2)`, one has `r(t)≥0`.
The existing estimate `2ω(t)≤1/t+1/2`, together with
`1-exp(-t)≤t`, gives `r(t)≤3/4`.
Thus `r` is integrable near zero. Its positive tail is dominated by the
integrable tail of `ω`; reflection makes `r(|t|)` integrable on the line.
Boundedness also places it in L².

The Abel logarithmic identity gives
`∫₀∞ exp(-t)(1-cos(ξt))/(2t) dt=(1/4)log(1+ξ²)`.
Subtract this from the literal Gamma Lévy identity to obtain

`2θ′(ξ)=(1/2)log(1+ξ²)+c₀-2∫₀∞r(t)cos(ξt)dt`,

where `c₀=2θ′(0)+2∫₀∞r(t)dt`.
Evenness identifies the last term with the Fourier transform at the exact
unitary Fourier frequency. Convolution by `r(|t|)` is bounded on L² and
self-adjoint because its Fourier multiplier is real. For `|f|≤C` almost
everywhere, its convolution is bounded by `C∫ℝr(|t|)dt`.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheWeilSymbolIsALogarithmicMultiplierPlusABoundedKernel.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `archLogRemainder_nonneg`, `archLogRemainder_le_three_quarters`
- `integrable_archLogRemainder_abs`
- `gammaHardyPhaseRate_eq_log_reference_fourier`
- `archLogConvolution_coeFn`, `archLogConvolution_isSelfAdjoint`
- `archLogConvolution_bound`

Production plain audit passed. Transitive axioms are exactly
`[propext, Classical.choice, Quot.sound]`; the umbrella imports the module.
The identity is spectral. Identification of the completed logarithmic
Dirichlet equation and its half-line Green kernel remain separate proofs.
