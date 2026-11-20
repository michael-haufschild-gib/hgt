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
| 1 | 5/6 faces (PSM, ECS, WD, MC, AAD) + unconditional faces at the 20999/24000 strip | SquareRootThreshold/TheFiveSixthsFacesOfTheZeroWidth | in progress |
| 2 | ECS ↔ PSM identity with explicit constants | — | open |
| 3 | Green transfer D ↔ E(H)−E(H/2) | — | open |
| 4 | Pilot baselines (i)–(iii) | — | open |
| 5 | Explicit Λ_X pincer constant | — | open |
| 6 | Verified height beyond 67 | — | open |
| 7 | Twin test suite | — | open |
| 8 | Adversary bookkeeping | — | open |

## Log
- 2026-11-20 — created; Θ ≤ 20999/24000 is a Lean theorem (`ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths`), so every face also has an unconditional reading.
