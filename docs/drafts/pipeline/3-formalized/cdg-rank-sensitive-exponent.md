# A reciprocal-rank exponent and uniform approximation rank profile

- **ID:** CDG-EXP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Explicit simultaneous-form and approximation-rank bounds
  with exponent degree at most `100k(k+1)/r`.

## Statement

Let `p_1,…,p_k` be distinct primes, `1≤r≤k`, `d=k−r`,
`W=ceil(Σ log p_j)+1`, `h=floor(d/r)+1`, and

`U=10⁴(W+1)(k+1)²`, `C=U^(100h(k+1))`.

For `H≥1`, define

`Δ_r(H)=exp(−C(log(r!H^r)+2))/(r·r!H^(r−1))`.

Every rank-`r` integer matrix with entries bounded by `H` has a row whose
prime-logarithm form has absolute value at least `Δ_r(H)`.
Consequently, for integral `H`, all integer vectors `ν` with `|ν_j|≤H` and
`|Σν_j log p_j|<ε≤Δ_r(H)` span at most `r−1` dimensions over `ℚ`.
Their number is at most `(2H+1)^(r−1)`.

The exponent degree `e=100h(k+1)` satisfies `re≤100k(k+1)`.
At `r≥k−r`, `e≤200(k+1)`; at `r>k−r`, `e=100(k+1)`.
These statements are uniform in prime cutoff, dimension and coefficient height.

The approximation-rank and cardinality conclusions also hold with threshold
`max(Δ_r(H), rankDepthFloor(r,d,y,H))` when every prime is at most `y`.
Thus the elementary full-rank floor and scalar elimination in `d+1`
logarithms remain available.

## Proof

**Parameter growth.** Use the explicit parameters from
[CDG-SIM](../3-formalized/cdg-simultaneous-logarithm-bounds.md).
Write `B=1000Wk`, `A=h(k+1)`, `J=A+k`, and
`V=L+J+1`, where `L=2+A(floor(log₂B)+1)`.
Since `1≤h≤k`,

`V≤(B+3)(k+1)²≤U²`, `R+1≤V+2V²≤U⁶`.

Also `2^(floor(log₂B)+1)≤2B≤U` and
`2^(floor(log₂V)+1)≤2V≤U³`. Therefore

`2^R≤U^(1+A+6J)≤U^(19h(k+1))`,

using `J≤2A` and `A≥1`. The exponential step factor retains `h`; it is
not estimated by exponentiating the polynomial upper bound for `R`.

The remaining parameters obey

`E≤U⁷`, `q≤U^(13h)`, `Q=kq≤U^(14h)`, `M₀≤U^(15h)`,
`S≤U^(21h)`, `c≤U^(22h)`, `a≤U^(30h)`.

Thus every parameter, including `k−1` and `W`, is at most `v=U^(30h)`.
With `Z=2^R`, the exact coefficient from CDG-SIM satisfies
`C′≤200Zv³` by its polynomial majorant. Since `U≥10000`,

`C′+1≤U·U^(19h(k+1))·U^(90h)≤U^(100h(k+1))`.

**Uniform form floor.** Substitute this coefficient bound into the closed
simultaneous theorem. The factor `log(r!H^r)+2` is positive, so increasing
the exponent coefficient decreases the lower floor. No matrix-dependent
parameter remains in `Δ_r(H)`.

**Approximation rank.** Select a basis from the rational images of all near
relations. If its size were at least `r`, any `r` basis members would give
an independent integer matrix with every form strictly below `Δ_r(H)`,
contradicting the uniform form floor. An injective coordinate projection
of their rational span then bounds the whole coefficient-box count by
`(2H+1)^(r−1)`. The maximum threshold uses whichever of the collective or
scalar-elimination floors is larger.

**Rank dependence.** The integer quotient inequality gives `hr≤d+r=k`.
Multiplication by `100(k+1)` gives the asserted reciprocal-rank law.
For `d≤r`, `h≤2`; for `d<r`, `h=1`.

## Contribution and boundary

This makes the rank gain in the collective auxiliary method explicit and
uniform over every small-form family in the same prime-coordinate space.
At proportional rank the degree is linear in `k`, whereas scalar
elimination at proportional codimension retains a quadratic dimension
degree. The maximum-floor result preserves the useful near-full-rank
regimes of scalar elimination and integrality.

Gaudron remains the external benchmark recorded in CDG-SIM; no external
simultaneous-bound theorem is imported. These are approximation-rank and
coefficient-box counts, not counts of return heights. Constant phase
precision still limits the coefficient heights that can act on a return.
A breadth mechanism and the prime-degree RH producer remain open.

## Lean

Module: `CollectiveDiophantineGeometry/ReciprocalRankBounds.lean`.
Direct `lake --old env lean` verification passed. Transitive axiom audits of
`collectiveLambdaExponent_add_one_le`, `exists_large_collective_form`,
`nearRelationBox_finrank_le_collective`, `nearRelationBox_card_le_max_floor`,
`collectiveExponent_le_of_half_rank`, and
`collective_exponent_degree_mul_rank_le` use only `propext`,
`Classical.choice`, and `Quot.sound`.
