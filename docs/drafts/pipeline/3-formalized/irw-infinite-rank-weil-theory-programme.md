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
| WellFoundednessIsNecessary | Wolff tower: positive weights, full symmetry, vanishing level sums, not well-founded | Q3 sharpness |
| TheCrudeStepAndTheCount | count of a ζ tower: positive under RH, positive ⇒ crude bound ⇒ AAL, with ZAL ⇔ RH; damping lossless; continuous levels ⇔ zero-free half-plane; B13 tower forms | Q6, T4, crude step, B13 |
| PrimeCollisionsHaveCollisionSize | Cauchy–Schwarz cells; prime mean value of order X² up to logs; diagonal bound | T3 for primes |
| ThePrecisionCostOfForcedVanishing | exponential tail; flatness; δ J! < (r log N)^J N^{2r}; J ≤ e² r log N + log(1/δ) | Q5, T2 |

## Open core
Each entry has its strength fixed by a theorem (README §9): the crude step along one tower (⇒ AAL,
with ZAL ⇔ RH); ZAL (tower well-foundedness); B13 (⇔ positive count / thick bounded lag of one tower in
the finite stratum); the Hardy–Littlewood pair constant (binary); B97 (beyond the auxiliary-function
route, whose order cap is proved).

## Log
- 2026-11-08 — created; 15 modules formalized; card to 3-formalized
