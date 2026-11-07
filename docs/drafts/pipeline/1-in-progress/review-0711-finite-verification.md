# Review-0711 §2.1 finite verification (A1–A8)

- **ID:** review-0711-finite-verification
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), one per task
- **Source:** [Obstacles summary §2.1](../../../reports/review-0711/obstacles-summary.md)
- **Statement:** Each task A1–A8 gets a complete unconditional Lean theorem, easiest first. No computations.
- **Predecessor:** [review-0611 card](review-0611-finite-verification.md) (height 67, rank ten, templates below `27/5`).

## Status

| Task | Status | Lean |
|---|---|---|
| A8 | done: dimension one is Tate-positive iff `A ≤ log 5` | `WindowTowerOfSpecZ/TheFirstTateDimensionEndsAtFive.lean`: `tateFunction_one_nonneg_iff_le_log_five` |
| A1–A7 | open | |

## A8

At `k = 1`: `α² = 1/8`, `β² = 1/3`, `χ = 1/2`, `δ = 2/√5`. On `(log(9/2), log 5]` the late pivots are
`≥ 23/72` and `83/168`, and `9/64 ≤ (23/72)(83/168)`. Past `log 5` the pivots are `7/8, 83/168, 49/83,
64/147, 365/512`; the last is `49/83 − 2/√5 − 512/1095 < 0`. Antitonicity in `A` gives the horizon.
