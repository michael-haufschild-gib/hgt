# Infinite-rank Weil theory over Spec ℤ (programme)

- **ID:** IRW
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — programme
- **Source:** docs/reports/review-0811/obstacles-summary.md §2.8b
- **Statement:** build the infinite-rank form of each step of the curve proof (crude count, self-improvement, reflection, count); answer Q1–Q6; build T1–T4.

## Goal
Folder `formal/GaloisForLFunctions/InfiniteRankWeilTheory/`, umbrella `InfiniteRankWeilTheory.lean`,
README in the folder. No computations; unconditional Lean only.

## Gates
- [x] 0 → 1  in-progress: README first draft written
- [ ] 1 → 2  paper proofs of each module
- [ ] 2 → 3  every module checked with `lake --old env lean`, wired into the umbrella

## Plan (modules)
| # | Module | Answers |
|---|---|---|
| 1 | WeilTowers — towers, level sums, reflection, curve and zeta instances | language |
| 2 | TuranWindows — one far window / thick sets self-improve; trace-norm tail | Q1, T1 |
| 3 | TheRankBarrier — roots of unity on density 1−1/k; Vandermonde hiding; cost | Q1 sharpness |
| 4 | WellFoundedElimination — crude ⇒ unitary at infinite rank; curve recovery | Q3 |
| 5 | ExceptionalLayers — ZAL/AAL/B13 for configurations; periodic ⇒ AAL; shifts | Q2 |
| 6 | ReflectionAdmitsEveryFiniteLayer — cosh models | Q4 |
| 7 | ZetaTowers — ¬AAL ⇒ isolated finite top in every tower; thick-set AAL producers | Q1–Q3 for ζ |
| 8 | LongMeanValues — band-limited mean value = diagonal + collision form | T3 |
| 9 | ReturnsFreezeSmoothPolynomials — forced vanishing at returns | T2, Q5 |
| 10 | CriticalWeight — damped / tilted kernels | T4, Q6 |

## Log
- 2026-11-08 — created; README draft
