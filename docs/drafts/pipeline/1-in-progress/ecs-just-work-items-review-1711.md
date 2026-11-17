# ECS just-work items of review 1711 (E-J10–E-J15)

- **ID:** ecs-just-work-1711
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper → Lean), one module per item
- **Source:** docs/reports/review-1711/route-ecs.md §4
- **Statement:** the six just-work items of the ECS route report, each as unconditional Lean theorems.

## Goal
Close the assembly-level gaps of the ECS route listed in §4 of the report: the ladder in Pick form, the Ω± sign law at the rate of the zeros, mean squares at the exact rate, the trace inequality of the ladder, the pointwise edge law at the wall, and the prime-side rows of stage 2. None of them is RH.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven (per item)
- [ ] 2 → 3  formalized (per item)

## Items (easiest first)

| Item | Module (ECS/) | Status |
|---|---|---|
| E-J15 prime-side rows of stage 2 | Index/StageTwoHasPrimeSideRows.lean | formalized: `stageTwo_primeSide_tfae` (B13 ⇔ finite layer ⇒ real-amplitude positivity above X ⇔ bounded confined index ⇒ no critical state ⇔ finite wave law ⇒ empty wave ⇔ finite wave law ⇒ positivity above X); `confinedIndexBounded_iff_exists_finiteWaveLaw`; `no_criticalState_iff_jasRealPositiveAbove_of_finiteOffLine`; `riemannHypothesis_iff_exists_finiteWaveLaw_empty` |
| E-J11 sign law at the rate of the zeros | Decay/TheSignLawHoldsAtTheRateOfTheZeros.lean | formalized: Landau against an exponential (`integrable_exp_of_tail_le_exp`); (a) `criticalState_re_le_of_tail_le_exp`, `criticalState_not_tail_le_exp`, Θ-form `criticalState_omega_pm` (both signs exceed e^{cu} for c > 17/2 − Θ, square moments finite for b < 17 − 2Θ); (b) `criticalState_unseen_of_beyondWall_le_exp`, `criticalState_beyondWall_not_tail_le_exp` (any seen zero, c < ½ − Re ρ), `criticalState_beyondWall_omega_pm`; dichotomy `riemannHypothesis_or_criticalState_omega_pm` |
| E-J12 mean squares at the exact rate | | not started |
| E-J13 trace inequality of the ladder | | not started |
| E-J10 ladder in Pick form | | not started |
| E-J14 pointwise edge law at the wall | | not started |

## Paper proofs

### E-J15
(a) B13 ⇒ row: FiniteOffLine ⇒ RH ⇒ real-amplitude positivity above some X (exists_jasRealPositiveAbove_one_of_riemannHypothesis). Row ⇒ B13: FiniteOffLine and positivity above X give RH (riemannHypothesis_iff_finiteOffLine_and_jasRealPositiveAbove). Under a finite layer: no critical state ⇔ RH (beyond-the-wall prime continuation) ⇔ positivity above some X.
(b) ConfinedIndexBounded ⇔ FiniteOffLine (confinedIndexBounded_tfae) ⇔ {Re ≠ ½} finite (Im of the spectral point is ½ − Re ρ) ⇔ finite wave law (finite_offLine_iff_exists_offLineWave). The empty wave law is RH (von Koch both ways). So B13 ⇔ (finite wave law ⇒ empty wave law) ⇔ (finite wave law ⇒ positivity above some X).

## Conjecture ledger

## Log
- 2026-11-17 — created in 1-in-progress
