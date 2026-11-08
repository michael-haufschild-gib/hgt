# Infinite-rank Weil theory over Spec ℤ (programme)

- **ID:** IRW
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — programme
- **Source:** docs/reports/review-0811/obstacles-summary.md §2.8b
- **Statement:** the infinite-rank form of each step of the curve proof (crude count, self-improvement,
  reflection, count); answers to Q1–Q6; tools T1–T4.

## Goal
Folder `formal/GaloisForLFunctions/InfiniteRankWeilTheory/`, umbrella `InfiniteRankWeilTheory.lean`
(wired into `MainTheorems.lean`), README in the folder. Unconditional Lean only, no computations.

## Gates
- [x] 0 → 1  in-progress: README draft
- [x] 1 → 2  paper proofs (module docstrings)
- [x] 2 → 3  every module checked with `lake --old env lean`; key `ζ` theorems audited: `propext`,
  `Classical.choice`, `Quot.sound` only

## Modules
| Module | Content | Answers |
|---|---|---|
| TheLevelSumsOfAWeilTower | towers, level sums, `S(−ν) = conj S(ν)`, outer/inner rank, curves | language, Q4 |
| TheExceptionalRankDecidesTheWindow | Vandermonde windows; isolated-top bound at infinite rank; syndetic excursions; thick sets; hiding cost | Q1, T1 |
| TheRankBarrier | roots-of-unity tower vanishes off `kℤ`; density `1 − 1/k`; infinite critical remainder; Vandermonde hiding; price | Q1 sharpness |
| WellFoundedTowersSelfImprove | elimination for well-founded towers on thick sets; reflection; curves from thick traces/point counts | Q3 |
| TheExceptionalCoordinate | RH = ZAL + AAL; ¬AAL ⇔ isolated top; eventual-to-global; tower dictionary; periodic ⇒ AAL; shifts | Q2 |
| TheFunctionalEquationAdmitsEveryFiniteLayer | cosh models: FE, reality, order one, any finite layer; ZAL, ¬AAL | Q4 |
| TheTowersOfZeta | `zetaTower`; lag = level sum; visibility; syndetic excursions; single top pair at base `π/γ`; AAL ⇐ thick lag bound; RH ⇔ ZAL + thick bounded lag; prime-side forms | Q1–Q3 for `ζ` |
| ReturnsFreezeSmoothPolynomials | freezing at returns; moment-annihilated polynomials; flatness; forced vanishing; one exact return | Q5, T2 |
| LongMeanValuesAreCollisionCounts | Fejér identity; kernel bounds; collision lower bounds; `Σ_{n≤N} n^{−it}` of exact order `N²` beyond the height; prime collisions | T3 |
| TheCriticalWeight | Kac–Murdock–Szegő; damping lossless; critical layers positive; renormalization no-go | Q6, T4 |
| TheCalibrationBattery | golden fake fails the crude count on thick sets; integer-norm one-off: ZAL, ¬AAL | Q2, calibration |

## Open core
1. A thick-set crude count for one tower of `ζ` at every exponent `½ + a` (AAL), at `½` with ZAL (RH).
2. Finite stratum: exclude a single top pair whose lag at base `π/γ` is large at every level.
3. Rouché precision of forced vanishing at constant precision (B97).
4. Main terms of prime collisions at length `T^{1+θ}`.
5. A damped arithmetic count over `ℤ` (B87, B88).

## Log
- 2026-11-08 — created; README draft; 11 modules formalized; card to 3-formalized
