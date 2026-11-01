# Rational correlation Grams at one universal critical overlap

- **ID:** finite-rational-correlation-grams-at-critical-overlap
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/reports/review-0111/route-SC.md`, obligation 1.

## Statement

Put `c*(N)=loglog N·(logloglog N)²`. One fixed nonnegative smooth profile
`φ=beurlingUnitProfile`, supported in `[0,1]` with integral one, realizes
**every** finite rational correlation Gram at overlap `2c*(N)`.
For each finite family `q_i`, there are horizons `N_m→∞` and real vectors
`v_{m,i}` such that

`G_m ⟨completeWeilMatrix φ (2c*(N_m)) N_m · v_{m,i}, v_{m,j}⟩ → ratCorr(q_i⁻¹q_j)`,

where `G_m=∫ atomDilate φ (2c*(N_m)/N_m)²` is eventually positive.
The profile and multiple `2` are independent of the finite family.

Consequently, positivity of every rational Weil Gram on its boost-mass-zero
hyperplane is equivalent to eventual positivity of the complete Weil family
on its pole hyperplane at this **single** fixed overlap. Both are equivalent
to RH. This proves the realization and equivalence, not the positivity input.

## Proof

**Fixed profile.** Starting from the smooth nonnegative unit bump
`steklovBase`, iterate Steklov averages with radii

`r_j=(1/√log(j+3)−1/√log(j+4))/8`.

Their tails telescope. All derivative sequences are uniformly Cauchy, giving
a smooth nonnegative limit `ψ` supported in `[-1,1]`, with integral one.
The logarithmic increment bound and rationalization give

`r_j ≥ 1/(16(j+4)log(j+4)√log(j+4))`,

hence

`∏_{j<q} r_j⁻¹ ≤ (64/√log(q+3))^q · q! · log(q+3)^(2q)`.

The derivative bounds pass to the limit. Since `64/√log(q+3)→0`, for every
`b>0` there is `A>0` with `∫|ψ⁽q⁾|≤A b^q dcLogWeight(q)` for all `q`.
Set `φ(u)=2ψ(2u−1)`.

**Universal synthesis.** Express the rational Gram using translates of the
cubic spline. For their common support radius `R`, set `B=blockSize(R+1)`
and choose derivative type `b=1/(48eB)`. Then `24ebB=1/2<1`, so the
bounded-rate synthesis theorem applies at dilation `N/dcScale N`.
The constant `A` changes the eventual error bound, not the overlap.
Mollification handles the spline's `C²` regularity. Choosing successive
entry errors `1/(m+1)` yields the simultaneous Gram limit.

**Complete matrix.** For atom width `w=c/N`, divide packet coefficients by
`w`. Recentering gives the exact energy identity; real polarization gives
every mixed entry, with the atom mass `G=∫φ(u/w)²du` restored. At
`c=2dcScale N`, the recentred dilation is exactly `N/dcScale N`.

**Hyperplane.** Nonnegativity on one real hyperplane bounds complex negative
index by one: real and imaginary coefficient vectors satisfy the same
constraint. Compression and entrywise Gram limits preserve this bound.
Thus `κ(ratCorr)≤1`; the exact zeta index identity and parity force `κ(K_ζ)=0`.
Conversely, RH makes every complete Weil energy nonnegative. Exact pole-moment
preservation by packet approximation is unnecessary.

## Lean and audit

- `TransMetzlerWeilPositivity/ReceiverRate/AProfileAtEveryLogarithmicType.lean`:
  `exists_beurlingDCProfile_bound`, with smoothness, nonnegativity and unit mass.
- `TransMetzlerWeilPositivity/ReceiverRate/EveryFiniteGramFitsOneCriticalOverlap.lean`:
  `exists_ratCorr_completeWeil_gram_limit_at_universal_critical_overlap`.
- `RenormalizedIntersectionTheory/TheHodgeIndexAtCriticalOverlap.lean`:
  `riemannHypothesis_iff_beurlingUnitProfile_hodgeIndex_universal_critical` and
  `ratCorr_hyperplane_nonneg_iff_beurlingUnitProfile_hodgeIndex_universal_critical`.

Dependencies compiled; final direct Hodge leaf audit passed. The profile,
complete Gram limit, both equivalences and bump nonnegativity use only
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella imports are wired.

The original Steklov profile retains its separately verified family-dependent
Gram realization and receiver quantified over every fixed `K≥1`.
