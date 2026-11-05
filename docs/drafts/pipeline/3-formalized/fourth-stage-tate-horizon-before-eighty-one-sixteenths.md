# Fourth-stage Tate horizon before eighty-one sixteenths

- **ID:** fourth-stage-tate-horizon-before-eighty-one-sixteenths
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0411 §2.1, A6.

## Theorem

For `log 5<A≤log(81/16)`, let `T` be the twelve-vertex third-stage template.
The next template is `T ∪ {5/r:r∈T}`, with 24 vertices and spread `log 5`.
It is closed under ratio `2,3,4,5` neighbours in `[1,81/16)`.
The two copies of `T` meet through exactly one ratio-five edge, between `1` and `5`.

For `k≥0`, put `α=(2^k−1)/(2√2)`, `β=(3^k−1)/(2√3)`,
`χ=(4^k−2^k)/4`, `δ=(5^k−1)/(2√5)` and

`D=1−α²`, `z=χ−α²`, `v=D−β²/D`, `w=D−z²/v`,
`p=1−β²/w`, `q=1−α²/p`.

Exact positivity criterion: `D,v,w,p,q>0` and `w−δ−β²/q≥0`.
At `k=0`, all five strict pivots and the final pivot equal one.

## Paper reduction

Least-vertex block removal reduces every finite graph of span `<81/16`
to restrictions of the 24-vertex template. Conversely, its spread `log 5`
allows a smooth window realization throughout the stated interval.

Reflection `r↦5/r` reduces positivity to `Q₁₂(x)−δx₁²≥0`.
The even sector adds `2δx₁²`, so the odd sector decides the sign.
Eliminating both triangle centres and both outer arms gives the pivots `D,v`;
eight completed squares leave a four-vertex path with diagonal
`(w−δ,1,1,w)` and edge weights `(β,α,β)`.
Right-to-left elimination gives `w,p,q,w−δ−β²/q`.

For `k>0`, the couplings `α,β,z` are nonzero: `2α²≤χ` implies `z>0`.
A nonnegative binary form with nonzero cross coefficient has positive
diagonal entries. Applying this at each elimination proves strictness of
all intermediate pivots. Completing squares proves sufficiency.

## Lean theorem

`WindowTowerOfSpecZ.tateFunction_nonneg_iff_fourthStage_beforeEightyOneSixteenths`
in `TheTateHorizonBeforeEightyOneSixteenths.lean` proves both directions.
The final direct source check and four transitive axiom audits passed
(`propext`, `Classical.choice`, `Quot.sound`). The owning umbrella imports it.
The remainder of stage four and later stages remain open.
