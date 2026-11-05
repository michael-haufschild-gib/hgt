# The third Tate stage distinguishes signed positivity from absolute edge costs

- **ID:** third-stage-tate-sign-frustration
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0411 §2.1, A6; WTZ README §4C.

At `k=1`, the seven-vertex Tate criterion has determinant margin `5/48>0`.
Reversing every edge sign gives value `−77` on

`(7√2√3, 7√3, 7√2√3, 8√2, 4, 8√2, 4)`.

Thus positive Tate forms can coexist with a negative all-cost graph form.
The negative graph has a smooth rational-bump realization with absolute
correlation costs exceeding the norm. Such a test rules out every bounded
positive Barta weight for these dimension-one weights once ratio four fits.
The ratio-four triangle's signs matter. This does not refute the separate
question relating balancing weights to the nonnegative adjacency spectral radius.

## Lean theorems

`WindowTowerOfSpecZ.tateFunction_one_nonneg_beforeNineHalves`,
`thirdStage_all_negative_edges_witness`,
`exists_thirdStage_absolute_cost_exceeds_norm` and
`no_thirdStage_absolute_cost_balancing_weight` in
`TheThirdTateStageDistinguishesEdgeSigns.lean` prove the positive survivor
and the absolute-cost obstruction. The final direct source check and all four
transitive axiom audits passed (`propext`, `Classical.choice`, `Quot.sound`).
The owning umbrella imports the module.
