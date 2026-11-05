# Third-stage Tate horizon before nine halves

- **ID:** third-stage-tate-horizon-before-nine-halves
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0411 §2.1, A6.

## Theorem

For `log 4 < A ≤ log(9/2)` and `k≥0`, set

`α=(2^k−1)/(2√2)`, `β=(3^k−1)/(2√3)`, `χ=(4^k−2^k)/4`.

Every Tate window test has nonnegative form iff

`χ≤1` and `(1−χ)(1−α²)≥β²`.

## Proof

The canonical rational graph has vertices
`{1,3/2,2,3,4,4/3,8/3}`. Its edges have ratios `2,3,4`.
Every finite graph of spread `<log(9/2)` decomposes into subgraphs of scaled
copies of this graph: take the least vertex `r`; the seven ratios form a set
closed under allowed neighbours in `[1,9/2)`. Remove that block and repeat.

Reflection `r↦4/r` splits the canonical quadratic form. Eliminating the two
outer vertices gives odd-sector determinant
`(1−χ)(1−α²)−β²`; the even sector has the larger endpoint diagonal
`1+χ−2α²`, since `χ−α²=(4^k−1)/8≥0`.
Since `2α²≤χ`, the condition `χ≤1` forces `α²≤1/2`.
The full graph fits every aperture above `log 4`, so its negative directions
are attained by rational bump tests. The graph-to-window converse supplies
the reverse implication.

## Lean theorem

`WindowTowerOfSpecZ.tateFunction_nonneg_iff_thirdStage_beforeNineHalves` in
`TheTateHorizonBeforeNineHalves.lean` proves the exact criterion, including
both aperture endpoints in the stated range. The final direct source check
and three transitive axiom audits passed (`propext`, `Classical.choice`,
`Quot.sound`). The owning umbrella imports the module.
