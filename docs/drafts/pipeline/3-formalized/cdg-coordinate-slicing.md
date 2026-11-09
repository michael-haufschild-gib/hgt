# Coordinate slicing separates counts from collective rank

- **ID:** CDG-SLICE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

Let `p₁,…,p_k≤y` be distinct primes, `k=n+s`, `s≥1`, and `H≥0`.
Write `B_s(y)=bakerExponent (s−1) ceil(s log y)` and

`σ_s(y,H)=½ exp(−B_s(y)(log(2sH)+2))`.

For `s=1`, use the stronger elementary threshold `σ₁=log 2/2`,
independent of `H`.

If `ε≤σ_s(y,H)`, projection onto the first `n` coordinates is injective on

`S={ν∈ℤ^k: |ν_j|≤H, |Σν_j log p_j|<ε}`.

Consequently `#S≤(2H+1)^n`. Relabelling the primes permits any retained
set of `n` coordinates. The conclusion does not use a collective rank bound.

## Proof

Suppose `e,f∈S` have the same retained coordinates. Their difference is
supported on the `s` omitted coordinates, each of absolute value at most
`2H`; its total coefficient height is at most `2sH`. If the difference is
nonzero, the existing scalar Baker bound and monotonicity in coefficient
height give

`|Σ(e_j−f_j)log p_j| ≥ exp(−B_s(y)(log(2sH)+2))`.

The triangle inequality instead gives a value strictly below `2ε`, hence
at most the same floor, a contradiction. The difference is zero.
The retained coordinates have `2H+1` choices each, proving the count.
For `H=0`, the same argument has no nonzero difference to consider.
For `s=1`, every nonzero difference has absolute logarithmic form at least
`log 2`: its coefficient is a nonzero integer and its prime is at least two.

## Exact comparison with the rank floor

For `r≥2` and `H≥1`, the collective threshold satisfies

`Δ(r,s−1,y,H)≤σ_s(y,H)`.

Put `D=r!H^(r−1)≥2`. The rank estimate uses total coefficient bound
`sr!H^r=sHD≥2sH`, so its exponential numerator is no larger than the
slicing numerator. Its denominator `D` is at least two. These two
inequalities prove the comparison. For `s=1`, both numerators are `log 2`
and only the denominator comparison is needed.

## Consequence for the programme

The count exponent `r−1` furnished by the rank-`r` theorem is already
available by omitting `s=k−r+1` coordinates and using a scalar bound.
For every `r≥2,H≥1`, the scalar threshold is at least as large.
Thus smooth-box counting alone does not expose the additional
content of the collective theorem. That content is the bound on the rational
span of **all** near relations, which projection injectivity does not imply.
At `s=1`, the count already holds at constant width, whereas full-rank
exclusion has a height-dependent floor.

Smooth-box mean squares obtained from this cardinal bound already follow
from scalar slicing and the existing Gallagher almost-diagonal theorem. A further
collective contribution must use span structure or arithmetic information
that survives the scalar slicing comparison. Constant-precision breadth
remains open.

## Lean status

Module: `CollectiveDiophantineGeometry/CollectiveRankDepth.lean`.

- `nearRelationBox_projection_injective`: coordinate slicing.
- `nearRelationBox_card_le_slice`: the resulting count.
- `rankDepthFloor_le_coordinateSliceFloor`: exact dominance for `r≥2,H≥1`.
- `coordinateSliceFloor_zero`: the elementary one-prime threshold.

The final direct repository-file Lean check passed. The three principal
proofs passed transitive axiom audits with only `propext`, `Classical.choice`,
and `Quot.sound`. The existing programme umbrella imports the module.
