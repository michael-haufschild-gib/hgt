# Two generators strictly beat one

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## The question this answers

`single-generator-is-useless.md` shows each generator alone contributes only `O((log m)²/m)`, and
`uniform-distance-bound.md` freezes the best single-generator bound at a constant. Neither says whether
*combining* generators gains anything — and if it did not, the whole lane would be dead rather than open.

## What is proved

`RHTower/TwoGeneratorImprovement.lean`. With the rational coefficient pair `c = (2,1)` on the moduli `(2,4)`,
the quadratic form of `bdDist_sq_le_quadratic` evaluates — using all three entries of the `{2,4}` Gram matrix
(`bdGram_half`, `bdGram_half_quarter`, `bdGram_quarter`, the fourth by `bdGram_symm`) — to

**`bdDist_sq_le_two_generator` — `d² ≤ 1 − (3/8)·log 2 − (5/32)·π` for the family `{1/2, 1/4}`,**

and

**`two_generator_lt_single` — `1 − (3/8)log 2 − (5/32)π < 1 − log 2`.**

So the pair strictly beats the better of its members. The coefficients were chosen for arithmetic convenience,
not optimality: the optimal pair `G⁻¹v` does better still, and `bdGram_half_quarter_det_pos` guarantees it
exists.

## Why it matters

This is the first positive evidence in the development that combining moduli gains something. Together with the
negative results it gives the correct shape of the lane:

* no single modulus helps appreciably (`bdDist_single_ge`, gain `O((log m)²/m)`);
* every finite family is strictly obstructed (`bdDistDiscrete_pos`, factorial floor);
* but families *do* improve on their members (this card).

So `d_N → 0` is not excluded by anything proved here, and the collective mechanism is real at the smallest
scale — which is exactly the state one wants before attacking the open joint estimate. What is still missing is
any control on how the improvement accumulates as more moduli are added; two generators is not a trend.
