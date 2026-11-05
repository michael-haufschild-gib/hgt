# Review-0511 §2.1 auxiliary tasks

- **ID:** review-0511-aux
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), one per task
- **Source:** [Obstacles summary §2.1](../../../reports/review-0511/obstacles-summary.md#21-auxiliary-tasks-difficulty-not-certified)
- **Statement:** Each task A* gets a complete unconditional Lean theorem, easiest first.

## Status

| Task | Status | Lean |
|---|---|---|
| A43 | done | `ArithmeticIncidencePositivity/TheWeilFloorTowerIsFrozen.lean`: `a_k < 0.3621`, `a_∞ − a₀ < 10^(−7800000)` |
| A28 | done | `WindowTowerOfSpecZ/TheAtomicLatticeHasTheSharpSchurBound.lean`: `Σ_{d≤N}Λ(d)/d ≤ log N`, atomic form `≤ ½ log N` |
| A52 | statement done, numeric `c` open | `RHTower/Heat/AHeatCoefficientGivesAZeroFreeStrip.lean`: ceiling `Λ_X log X ≤ κ` ⇒ depth `≤ √(κ/c)`; `κ < c/4` ⇒ `Re s ≤ σ < 1` |
| A7 | done as Schur complement; Gram expansion of the dual norm not done | `GrowingWindowsOfSpecZ/TheFirstStageComplementIsASchurComplement.lean`: `twoCollarForm_firstStage_eq` |
