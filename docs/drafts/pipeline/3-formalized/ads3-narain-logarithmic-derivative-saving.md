# Arithmetic saving for every logarithmic-clock derivative

- **ID:** W11-NQD
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Universal saving](ads3-narain-universal-saving-constant.md) · [Schwartz source](ads3-narain-boundary-schwartz.md)

## Theorem

For positive target heights, put
`R(y)=yA_YZ(y)+(3/π)log y−B_YZ`, `H(L)=exp(L/2)R(exp(−L))` and
`w(L)=(log L)^(−2/3)(log log L)^(−5/3)/10^8`.
There are `C>0` and `L₀` such that, for every `L≥L₀` and every integer `n≥0`,

`|H^(n)(L)|≤C n! (16/π)^n exp(−Lw(L)/128)`.

The radius and saving exponent are universal. The prefactor and threshold
may depend on target heights, but neither depends on derivative order.

## Proof

The compact spectral rectangle and high-frequency envelope give
`|M(it)|≤C exp(−π|t|/4)`, where `M=narainMellinMean Y Z`.
Consequently
`B(z)=(2π)^(−1)∫ℝ exp(izt)M(it)dt`
is holomorphic on `|Im z|<π/4` and equals the literal clock `H` on the real axis.

For complex frequency `z`, apply the real-clock rectangle estimate to
`exp(i Im(z) u)M(u)`. On `|Im z|≤π/8`, this twist consumes only part
of the vertical exponential decay. Horizontal edges and discarded tails
remain bounded by a polynomial times `exp(−πT/8)`.

On the disk `|z−L|≤π/16`, choose `T=L`. The left-edge width satisfies
`d(L)≤1/8`, so replacing `Re z` by `L` costs at most `exp(π/128)`.
The tail is at most `exp(−d(L)L)`. Universal polynomial absorption
therefore gives `|B(z)|≤C exp(−Lw(L)/128)` throughout the disk.

Cauchy's estimate on radius `π/16` gives the factorial bound with the
same threshold for all orders. Local complex-to-real jet transport and
the exact source identity give the stated derivatives of `H`.

## Lean

- `ComplexMellinShift`: finite rectangle bound at complex frequency.
- `NarainMeanBoundaryExponential`: global exponential majorant, complex integrability and uniform tails.
- `NarainMeanComplexVKContour`: actual complex-frequency contour estimate.
- `NarainMeanComplexClock`: holomorphic extension and exact physical-clock identification.
- `NarainMeanClockDisk`: `exists_narainMeanClock_disk_universal_vk_bound`.
- `NarainMeanClockDerivatives`: `exists_narainMeanClock_factorial_universal_vk_bound` and `narainScalarHeatAverage_clock_derivatives_universal_vk`.

All six modules passed final direct Lean checks and are imported by the
umbrella. All eleven endpoint axiom audits contain only `propext`,
`Classical.choice` and `Quot.sound`.

## Unproved negative-clock refinement

For every `0<γ<1/2`, the proposed bound
`|H^(n)(L)|≤Cγ n! (16/π)^n exp(γL)` as `L→−∞`, with a common threshold
for all orders, remains unformalized. So does the proposed sharp endpoint
law `exp(−L/2)H(L)/(−L)→3/π`. Neither is needed for the theorem above
or for the already proved Schwartz regularity.

## Gates

- [x] 0 → 1: actual Fourier identity, exponential envelope and jet transport audited.
- [x] 1 → 2: complex contour, universal disk saving and common factorial bound proved.
- [x] 2 → 3: final direct Lean checks, transitive axiom audits and umbrella imports.
