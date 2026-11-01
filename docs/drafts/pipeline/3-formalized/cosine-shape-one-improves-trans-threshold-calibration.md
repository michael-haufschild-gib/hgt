# Shape-one cosine calibration above bandwidth one

- **Stage:** 3-formalized
- **Type:** THEOREM / COSINE DIAGONAL COEFFICIENT
- **Parent:** [Positive cosine pinching](../3-formalized/trans-threshold-cosine-pinching-credit.md).

## Theorem

For the actual shape-one cosine window at bandwidth λ≥1, its
normalized diagonal coefficient converges to

`Hcos(λ)=2−[bStar(1)+λ² jStar(1)]/[λ aStar(1)²]`

and satisfies the strict improvement

`Hcos(λ) ≥ [2−1/λ−λ/3] + 43λ/7500`.

At λ=4/3 this gives `Hcos(4/3)≥3/4+79/1250` before adding the positive
pinching credit. The remaining signed prime surplus must use this same window.
This evaluates the coefficient; it is not a zero-proportion theorem.

## Paper proof

Write A=aStar(1), B=bStar(1), J=jStar(1). Integral variance on the unit interval
gives B≥A². The existing identity `cFun 1 (vStar 1)=cStar 1` and
`HD(1)≥1681/2500` give

`B+J≤(4/3−43/7500)A²`.

For λ≥1,

`B+λ²J = λ²(B+J)−(λ²−1)B`
`≤ [1+λ²/3−43λ²/7500]A²`.

Divide by λA² and subtract from two. The literal frozen-window moments have
errors at most `4w/L`, `4w/L`, `16w/L` from A,B,J. Since `L→∞`, `λ₁→λ`,
and A>0, their finite-height coefficient converges to the stated limit.

## Lean

`IncommensurableGaborPinching/CosineWindowCalibration.lean` proves:

- `aStar_sq_le_bStar`;
- `shapeOneCosineRate_ge_box`, `shapeOneCosineRate_fourThirds`;
- `cosineWindowRate_tendsto`, `cosineWindowRate_fourThirds_tendsto`;
- `cosineWindowRate_fourThirds_eventually`.

All six transitive axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. The exact production leaf passes `lake --old env lean`; umbrella import is present.

## Remaining

The [matched prime-Gram certificate](cosine-prime-certificate-with-explicit-pinching.md) is proved for `0<λ≤2`. The actual signed prime surplus still needs an upper bound.
