# Explicit weighted cosine triple floor

- **Stage:** 1-in-progress
- **Type:** THEOREM / QUANTITATIVE PINCHING SOURCE
- **Parent:** [Positive cosine pinching](../3-formalized/trans-threshold-cosine-pinching-credit.md).

## Target

The compactness constant is replaced by an explicit all-frequency bound. For
`F_c(t)=ct sin t−cos t`, the theorem is

`max(|F_c(x)|, |F_c(y)|, |F_c(x+y)|) ≥ 1/10`

for every real c,x,y. The polynomial cosine-kernel identity would then give, for
`|x|,|y|,|x+y|≤S` and `A=θ sinθ≠0`,

`max(|Kθ(x)|,|Kθ(y)|,|Kθ(x+y)|) ≥ |A|/[10(π²S²+θ²)|aStar|]`.

Here K uses the corpus's normalized kernel and x,y are its frequency coordinates.
This would make the positive pinching constant explicit, with inverse fourth-power
bandwidth decay after squaring.

## Paper proof

Put X=cx, Y=cy, u=sin x, v=sin y, Q=1+X²+XY+Y² and A₀=Q|uv|.
Writing r=F_c(x), the circle identity and `(Xu+r)²≥0` give
`1≤2(1+X²)u²+2r²`. Thus `|r|≤1/10` implies
`(1+X²)u²≥2/5`; likewise for y.

The identities

`Q²−(1+X²)(1+Y²)=(X+Y)²(1+X²+Y²)≥0`,
`Q−3(1+Y²)/4=(X+Y/2)²+1/4≥0`

imply `A₀≥2/5` and `|Y|≤3Q|v|`; the symmetric inequality gives
`|X|≤3Q|u|`. Angle addition gives exactly

`F_c(x+y)=Q uv−Y u F_c(y)−X v F_c(x)−F_c(x)F_c(y)`.

If all three residuals have magnitude at most 1/10, then
`A₀≤1/10+(3/5)A₀+1/100`, so `A₀≤11/40<2/5`, a contradiction.
This proves the strict bound `max |F|>1/10`.

The polynomial kernel identity, including removable frequencies, transfers this
bound by multiplying the maximum kernel magnitude by
`(π²S²+θ²)|aStar|/|θ sinθ|`. Its zero-frequency identity is
`θ² aStar=θ sinθ`, so the normalized floor simplifies to

`θ²/[10(π²S²+θ²)]`.

For shape one, `θ²=1/2`, giving `1/(10+20π²S²)`.
The actual packing has nonnegative gaps with `x+y≤6λ`, so all three gaps
lie in `[-6λ,6λ]`. This yields `cλ=1/(10+720π²λ²)` and hence explicit
pair credit `δλ=cλ²/200`.
These bounds remain valid at removable frequencies; only `θ sinθ=0` is excluded.

## Corpus audit

Search found the existing shape-near-one, span-three floor and the new qualitative
compactness theorem. Neither supplies this all-frequency residual estimate or
explicit inverse-quadratic kernel floor. No claim of external novelty.
## Lean

`ExplicitCosineTripleFloor.lean` proves `cotangentLineResidual_triple_floor`,
`mtKernel_explicit_triple_floor`, and `mtKernel_shapeOne_explicit_triple_floor`.
`PositivePinchingEveryBandwidth.lean` now proves `zetaCosine_explicit_disjointPairs`
and `zetaCosine_explicit_rankTrace`, retaining its three previous positive-credit
statements as corollaries. All eight theorem audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. Direct final leaf checks are pending;
umbrella imports are present.
