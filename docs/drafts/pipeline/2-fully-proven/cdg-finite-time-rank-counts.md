# Finite-time return counts from the collective rank profile

- **ID:** CDG-COUNT
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); Lean verification in progress
- **Statement:** Convert the uniform small-form rank bound into actual
  return-measure estimates, retaining its smaller dimension exponent.

## Statement

For `k` distinct primes, rank threshold `1≤r≤k`, integer `N≥2`, and `T≥0`, let
`Δ=Δ_r(N−1)` be the proved collective depth floor. The bound,
uniform over an interval of length `T` and every target phase vector, is

`vol{t: every prime phase is within chord distance 1/(2N) of target}`
`  ≤ (5π/2)·4^k·max(T/2,Δ⁻¹)/N^(k−r+1)`.

## Proof

Expand the squared modulus of the normalized sum over exponent vectors
`{0,…,N−1}^k`. All differences with logarithmic frequency below `Δ`
lie in one rational subspace of dimension at most `r−1`. An injective
coordinate projection bounds each affine fibre by `N^(r−1)`, hence the
normalized weight of close pairs by `N^(−(k−r+1))`.

Put `W₀=max(T/2,Δ⁻¹)`, centre the time interval at `c=A+T/2`,
and apply the proved Fejér sparse mean-value inequality to frequencies
`ω_a/(2π)` with coefficient `exp(i(ω_a c−Σa_j θ_j))` and
Fourier width `1/(2πW₀)`. Its window condition is exactly
`2π·(1/(2πW₀))·W₀=1`. Its surviving pairs satisfy
`|ω_a−ω_b|<1/W₀≤Δ`, so the preceding arithmetic pair bound applies.
The interval integral of the squared normalized smooth-box sum is at most
`(5π/2)W₀/N^(k−r+1)`. Target phases leave coefficient moduli equal to one.
The Fejér transform vanishes outside this frequency window, so there is
no separate far-frequency error to absorb.

For a returning coordinate with phase `z`, `|z−1|≤1/(2N)` and `|z|=1`.
The telescoping identity gives `|z^a−1|≤a|z−1|≤1/2` for `a<N`.
Consequently the normalized coordinate sum has modulus at least `1/2`.
The smooth-box sum factors into these coordinate sums, so its squared
normalized modulus is at least `4^(−k)` on the return set. Integration
and the preceding mass bound give the stated measure estimate.

Radian returns at precision `1/(2N)` satisfy the same chord condition,
since `|exp(ix)−1|≤|x|` after removing an integral multiple of `2π`.

## Quantitative boundary

For `T≥2/Δ`, the return fraction is at most
`(5π/4)·4^k N^(−(k−r+1))`. Its required horizon is polynomial in resolution `N`;
at half rank, the exponent coefficient has degree linear in dimension.
Elementary separation instead gives an exponential-in-`N` horizon. The
formalized scalar Baker bound used in CDG-RANK has a quadratic dimension
degree. For growing dimension and sufficiently large `N`, the collective
bound therefore improves the horizon for a partial-dimensional density
estimate. It does not assert the full torus density `N^(−k)`.

This is an arithmetic application of the collective theorem, not a new
Fourier inequality or an improvement over the strongest published
transcendence estimates. The external benchmark remains
[Gaudron's simultaneous bound](../3-formalized/cdg-simultaneous-logarithm-bounds.md#external-benchmark).

The result concerns shrinking precision. Fixed Fourier height is already
served by stronger elementary separation; this argument does not supply
constant-precision breadth or exclude the first return.

## Existing mechanisms

`HTGeometry.ReplicaCrowdingSpectralDimensionLaw` already converts abstract
near-frequency rank into spectral-moment bounds. The time-window input is
`RHTower.Sieve.integral_Icc_normSq_finiteFrequencyPoly_le_collisionWeight`
in `HeathBrownSparseMeanValueBasic.lean`; its proof uses the triangular
Fourier kernel and absolute bounds for complex coefficients.
The missing arithmetic application is an actual return set, with the
collective threshold discharged and the dimension dependence retained.
No generic conditional rank receiver alone qualifies as the result.

## Lean

Target: `CollectiveDiophantineGeometry/FiniteTimeReturnCounts.lean`.
The final theorem must discharge the arithmetic threshold and bound the
actual return-window measure. Source verification and axiom audit remain.
