# Route R first wall: two-sided scale law and the bounded-depth no-go (2026-08-06, third pass)

Extends `mem:route_r/first_wall_scale_quantification_2026_08_06`. All unconditional, axioms
`[propext, Classical.choice, Quot.sound]`. Module
`RHTower/RouteRFirstWallScaleQuantification.lean`.

## Sandwich

For one stage `w` of a bounded unit prime profile carried inside `[q, Q]` (`q ≥ 3`):

  `(1 - q^(-2|t|))(1 - 3/q) ≤ ‖stageAverage w (W_t)‖ ≤ 1 - Q^(-2|t|)`

`stageAverage_criticalWall_sandwich`; the ceiling half is `norm_stageAverage_criticalWall_le`, proved
by the same termwise comparison as the floor but through `tsum_stageWeighted_le`, using `F(p) ≤ 1/p`
and `1 - p^(-2|t|) ≤ 1 - Q^(-2|t|)`.

## Bounded depth cannot decide — NO-GO

`1 - e^{-x} ≤ x` (`Real.add_one_le_exp`) with `t = r/(2 log Q)` gives `1 - Q^(-2|t|) ≤ r`. So:

- `exists_ne_zero_norm_stageAverage_le` — every stage with a depth ceiling `Q ≥ 2` and every
  tolerance `r > 0` admits a NONZERO grade whose average is within `r`.
- `exists_depthCeiling_of_finite_support` — finite support gives a ceiling (`Set.Finite.bddAbove` on
  the image in ℝ).
- `exists_isCofinalUnitProfile_no_single_stage_decides` — witnessed form: a bounded cofinal
  prime-harmonic profile exists all of whose stages are finitely supported, and every one of its
  stages is evaded by some nonzero grade.

Consequence: the unbounded-depth quantifier in `eq_zero_of_deepStage_norm_profileAverage_le` is
intrinsic. No single stage, no finite family of stages, and no finite certificate can separate
neutral grade. Do not look for a bounded-depth version of the criterion — it is false.

## HTGeometry additions

`unitWindowProfile_eq_zero_of_gt`, `finite_support_unitWindowProfile`,
`finite_support_comp_equiv`, and the strengthened existence theorems
`exists_isCofinalUnitProfile_finiteSupport`,
`exists_isCofinalUnitProfile_finiteSupport_of_equiv`,
`exists_isCofinalUnitProfile_finiteSupport_primeHarmonic`. The old plain-existence names are kept as
one-line corollaries so nothing downstream had to change.

## Interpretation

The reporter family is exactly a scale meter: its output is a function of `|t| · log(depth)` up to
the depth ratio `log Q / log q` and an `O(1/q)` Fisher correction. Neither the weights nor a finite
depth carry information. The whole remaining content of Route R's first-wall core is cancellation at
unboundedly deep scales — recorded on the parent card as
`ROUTE_R_FIRST_WALL_UNBOUNDED_DEPTH_CANCELLATION`.
