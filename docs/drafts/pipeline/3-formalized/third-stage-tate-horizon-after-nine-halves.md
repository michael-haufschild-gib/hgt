# Third-stage Tate horizon after nine halves

- **ID:** third-stage-tate-horizon-after-nine-halves
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0411 §2.1, A6.

## Theorem

For `log(9/2)<A≤log 5`, use
`α=(2^k−1)/(2√2)`, `β=(3^k−1)/(2√3)`, `χ=(4^k−2^k)/4`, with `k≥0`.
Set `d=1−α²`, `z=χ−α²`,
`u=d−β²/(1−α)`, `v=d−β²/d`.

Exact positivity criterion: `χ≤1`, `u≥0`, `z²≤uv`.
At `A=log 5`, the ratio-five correlation vanishes by support.

## Paper reduction

The canonical twelve vertices are
`{1,2,4,3,3/2,4/3,8/3,9/2,9/4,9/8,27/8,27/16}`.
This set is closed under ratio `2,3,4` neighbours in `[1,81/16)`; the first
missing neighbour is `3·(27/16)=81/16`.
Its spread is `log(9/2)`. Least-vertex block removal and the rational-graph
converse therefore reduce the window form to this graph throughout the interval.

Reflection `r↦(9/2)/r` exchanges six pairs. The odd quadratic form is

`a²+b²+c²+(1−α)d₁²+e²+f²+2α(ab+bc+ef)+2β(ad₁+ce)+2χac`.

The even form adds `2αd₁²`, so the odd form decides positivity because `α≥0`.
The triangle forces `χ≤1`. Since `2α²≤χ` for these Tate weights,
`1−α>0` and `d>0` follow. Completing the four squares in `b,f,d₁,e`
leaves `ua²+2zac+vc²`. Also `u≤v`, since `1−α≤d`.
This last form is nonnegative exactly when `u≥0` and `z²≤uv`.

## Lean theorem

`WindowTowerOfSpecZ.tateFunction_nonneg_iff_thirdStage_afterNineHalves` in
`TheTateHorizonAfterNineHalves.lean` proves both directions, including the
ratio-five endpoint. The final direct source check and three transitive axiom
audits passed (`propext`, `Classical.choice`, `Quot.sound`). The owning umbrella
imports the module.
