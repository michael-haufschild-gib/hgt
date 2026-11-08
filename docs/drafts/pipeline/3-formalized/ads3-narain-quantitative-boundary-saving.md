# Quantitative saving beyond the Narain half-power boundary

- **ID:** W11-NQ
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Boundary contour](../3-formalized/ads3-narain-average-boundary-rate.md)

## Theorem

For every positive target-height pair, write
`R(y)=yA_YZ(y)+(3/π)log y−B_YZ` and `L=log(1/y)`. There are `C,c>0`
such that, for all sufficiently small positive `y`,

`|R(y)|≤C y^(1/2) exp(−cL/[(log L)^(2/3)(log log L)^(5/3)])`.

This implies every proposed logarithmic saving. It gives no fixed
power above `1/2` and no RH-strength estimate.

**Uniform-exponent candidate.** The saving constant `c` should be
independent of `Y,Z`: the strip width comes entirely from the uniform
reciprocal-zeta theorem, while target heights affect the numerator
bounds. Constants `C` may depend on the targets. This stronger
quantifier order is not yet formalized by the fixed-pair construction.

## Proof

Write `M(u)=narainMellinMean Y Z u`.

`RHTower.Sieve.exists_bound_invZeta_vk_uniform` in
`Sieve/VinogradovKorobovInvZeta.lean` supplies actual nonvanishing and

`|invZeta(s)| ≤ C log(K+1)^7 [1+2/w(K+1)]^7`

on `|Im s|≤K`, `1−min(δ,w(K+1))/4≤Re s≤2`, where
`w(t)=(log t)^(−2/3)(log log t)^(−5/3)/10^8`.
Its proof includes both signs and the compact low-height region.
No extra reciprocal estimate is assumed.

For the actual mean boundary integral, shift the truncated contour
from `Re u=0` to `Re u=−c w(2T+1)`. The existing exact mean quotient
and proved strip bound retain exponential vertical decay up to the
reciprocal-zeta factor. Transporting the uniform VK estimate bounds
that factor by a polynomial in `T`. The horizontal edges and discarded
boundary tails are then `O(T^N exp(−aT))`; the shifted vertical integral
is `O(T^N exp(−cL w(2T+1)))`. Taking `T=L` and absorbing the polynomial
factor gives the theorem.

More precisely, set `d(T)=min(min(δ,1),w(2T+1))/8` and
`Q(T)=log(2T+1)^7[1+2/w(2T+1)]^7`. The finite rectangle and tail estimate give

`|∫ℝ exp(iLt)M(it)dt| ≤ C(1+T)^N Q(T)[exp(−d(T)L)+exp(−πT/4)]`.

Compact analyticity controls the removable center uniformly; the
high-ordinate bound supplies the rest of the rectangle. Crude vertical
length `2T` suffices. The boundary exponential envelope controls both
discarded tails. `ConjugateDiagonalGeometry.WindowPortFlux.eventually_inv_log_le_vkWidth`
proves that the same VK width eventually exceeds `1/log T`; this implies
`Q(T)≤3^7 log(2T+1)^14` and absorbs every
polynomial loss into `exp(d(T)T/2)`. The full profile is retained because
`d(T)≥min(δ,1)w(T)/64`. The exact source normalization is
`|R(y)|=√y/(2π)|∫ℝ exp(iLt)M(it)dt|`, `L=−log y`.

Proved Lean inputs in `ModularBootstrap`:

- `NarainMeanVKStrip` — `exists_narainMellinMean_vk_strip`: actual rectangle analyticity and high-ordinate exponential envelope.
- `NarainVKParameters`: width monotonicity, retained width fraction and `Q(T)≥1`.
- `NarainMeanVKEnvelope` — `exists_narainMellinMean_vk_envelope`: the envelope at every ordinate, using one fixed compact rectangle.
- `FiniteMellinShift` — `norm_finite_mellin_shift_le`: explicit left-edge and horizontal-edge bounds.
- `ExponentialMellinTail` — `norm_integral_sub_truncated_le`: two discarded tails bounded by `(2C/a)exp(−aT)`.
- `NarainMeanBoundaryTail` — `exists_narainMeanBoundary_tail_bound`: actual-source tails bounded by `C exp(−πT/4)`, uniformly in logarithmic frequency.
- `NarainMeanVKContour` — `exists_narainMeanBoundary_vk_contour_bound`: the displayed full-line moving-contour estimate for the actual mean.
- `NarainVKDilation` — `narainVKWidth_ge_profile`: `d(T)≥min(δ,1)w(T)/64`, using `w(2T+1)≥w(T)/8`.
- `NarainVKCost`: eventual bounds `Q(T)≤3^7 log(2T+1)^14` and `d(T)≥min(δ,1)/[8log(2T+1)]`.
- `NarainVKAbsorption` — `exists_narainVK_saving`: polynomial losses and the discarded exponential tail are absorbed into `C exp(−cLw(L))`.
- `NarainMeanBoundaryIdentity`: exact complex Fourier normalization and the displayed physical norm identity.
- `NarainAverageVKRate` — `narainScalarHeatAverage_vk_log_rate`: the displayed unconditional bound for the actual averaged source.

All transitive axiom audits contain only `propext`, `Classical.choice`
and `Quot.sound`. All twelve modules passed final direct Lean checks and are imported by
the umbrella; all twenty-four endpoint audits have the stated axiom set.

The weaker saving `exp(−cL/log L)` follows as well. Neither saving
provides a fixed power above `1/2`.

The [logarithmic-derivative extension](../1-in-progress/ads3-narain-logarithmic-derivative-saving.md)
applies the same contour to `u^k M(u)`. It remains a separate candidate;
the scalar bound alone does not control derivatives of its error.

A [universal-constant refinement](../1-in-progress/ads3-narain-universal-saving-constant.md)
uses eventual inactivity of the fixed width ceiling to target the explicit
exponent `Lw(L)/128` for every target pair. It remains unformalized.

## Gates

- [x] 0 → 1: actual mean strip and boundary inputs audited; uniform VK estimate identified.
- [x] 1 → 2: normalized source identity and contour saving give the stated physical rate.
- [x] 2 → 3: direct Lean checks, transitive axiom audits and umbrella imports.
