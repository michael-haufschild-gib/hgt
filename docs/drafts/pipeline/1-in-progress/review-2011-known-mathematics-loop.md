# Review-2011 §2.1: work with known mathematics

- **ID:** R2011-KM
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) packages
- **Source:** docs/reports/review-2011/obstacles-summary.md §2.1
- **Statement:** formalize the eight §2.1 packages (5/6 faces, ECS↔PSM identity, Green transfer, pilot baselines, Λ_X pincer, verified height, twin suite, adversary bookkeeping), easiest first.

## Goal
Each package removes an obstacle without a new inequality. Order of work: 5/6 faces → ECS↔PSM identity → Green transfer → Λ_X pincer constant → pilot baselines → twin suite → adversary bookkeeping → verified height.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Packages
| # | Package | Lean module | Status |
|---|---|---|---|
| 1 | 5/6 faces (PSM, ECS, WD, MC, AAD) + unconditional faces at the 20999/24000 strip | SquareRootThreshold/TheFiveSixthsFacesOfTheZeroAbscissa (`fiveSixths_faces`, `fiveSixths_wd_face`, `unconditional_faces`, `unconditional_wd_face`) | formalized |
| 2 | ECS ↔ PSM identity with explicit constants | ExclusionOfTheCriticalState/Wall/TheTerminalJointHeightIsTheSquaredHalvingIncrement (`mul_terminalJointHeight`, `abs_terminalFlank_add_terminalOddHalf_le`: constant 95, `abs_mul_sum_terminalJointHeight_sub_sq_le`) | formalized |
| 3 | Green transfer D ↔ E(H)−E(H/2) | ExclusionOfTheCriticalState/Wall/TheMidpointAndTheHalvingIncrementShareOneSidedExponents (`error_le_of_terminalOddHalf_le`: coefficient 1/(1−2^(−b)), `midpoint_halving_joint_spectra`) | formalized |
| 4 | Pilot baselines (i)–(iii) | — | open |
| 5 | Λ_X pincer constant | ZeroConfigurationGeometry/HeatScaleRepulsion/TheLocalNewmanPincerCannotSeeTheStrip (`im_eq_zero_of_pairModelHeat_critical_eq_zero`, `pairModel_persistence_misses_pincer_threshold`) | formalized |
| 6 | Verified height beyond 67 | — | open |
| 7 | Twin test suite | — | open |
| 8 | Adversary bookkeeping | — | open |

## Findings
- WD module `ConjugateDiagonalGeometry/NearLineLogMean/SuperpolynomialMobiusOrder` did not compile against current Mathlib; repaired (5 API fixes) and wired.
- Green transfer: the kernels with symbols (1−2^(−s))/(2·3^s−2^s−4^s) and its reciprocal are signed, so D and ΔE exchange one-sided bounds only through Θ; at the level of exponents the exchange is lossless (both are exact meters).
- Λ_X pincer: excluding depth d needs c·d² > 6600/9991. The pair model (Lindelöf-size, RvM spacing) is real-rooted at its collision heat t* < δ/L, so any persistence constant valid for it has c·δ < 1, hence c·δ² < 1/2 < 6600/9991. At the strip depth the pincer needs c > 4.69, the pair-model ceiling is 24000/8999 ≈ 2.67. Answer: the pincer carries no strip information unless its lower law uses arithmetic absent from the pair model.

## Log
- 2026-11-20 — created; Θ ≤ 20999/24000 is a Lean theorem (`ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths`), so every face also has an unconditional reading.
