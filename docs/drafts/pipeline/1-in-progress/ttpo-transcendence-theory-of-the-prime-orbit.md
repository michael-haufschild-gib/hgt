# Transcendence theory of the prime orbit (TTPO)

- **ID:** ttpo
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0811/obstacles-summary.md §2.11
- **Statement:** develop the field: answer Q1–Q4, build T1–T4, test C1–C4, address M1–M5 of §2.11.

## Goal
Lean folder `formal/GaloisForLFunctions/TranscendenceTheoryOfThePrimeOrbit/`, umbrella
`TranscendenceTheoryOfThePrimeOrbit.lean` (wired into `MainTheorems.lean`), foundational `README.md`.
No sign, spectral or positivity input (C1). No computations.

## Gates
- [x] 0 → 1  agenda fixed from §2.11; README first draft
- [ ] 1 → 2  paper proofs of each module
- [ ] 2 → 3  each module checked with `lake --old env lean`, standard axioms only

## Modules
| # | Module | Agenda | Content | Status |
|---|---|---|---|---|
| 1 | TheReturnFormDuality | Q1, Q2 | return ⇒ forms near ℤ; windows; two-step depth form; Liouville `y^{−|ν|₁}`; rounded system matches height-`≤K` forms, exact return at `T ≥ 2πKy^K` | checked |
| 2 | LinearFormsWithExplicitDependenceOnTheirNumber | T1, M2, Q2 | explicit Fel'dman `R`; `C(k,W) ≤ (10⁴(W+1)(k+1)²)^{30(k+1)²}`; primes `≤ y` version; pigeonhole: no exponent `< k−1` | checked |
| 3 | TheDepthLawOfReturns | Q1, M1, C3 | any two primes `≤ y`: `t ≥ e^{−2}(2δ log y)^{−1/C(y)}/(2 log y)`; every set with two primes (heavy subsets); Dirichlet upper law | checked |
| 4 | SurvivalAtADeepReturn | Q3, T2 | jets at returns; multiples (approximate group); order 0 integrality; order 1 below Baker threshold; order 2 two primes (Gelfond–Schneider); no algebraic orbit point (six exponentials) | checked |
| 5 | TheReciprocityOfReturns | T4, Q1, Q4 | modulated explicit formula `P_φ(t) = π + Γ − Z`; localization `y^{depth}/(1+|γ−t|)²`; pole `O(t^{−2})`; Gamma `O(log t)`; finite-layer footprint → 0; pole imitation at returns | checked |
| 6 | TheFunctionFieldCase | C2 | rank one ⇒ exact returns, exact Frobenius (periodic frozen jets); rounded system is rank one; no exact return over ℤ | checked |
| 7 | ReturnBoundsAreLabelStatements | Q4, calibration | `MainConjecture` (B97) defined; `ζ(s−h)` Euler product over ℚ-primes, ¬ZAL; uniform route ⇒ ¬B97 | checked |
| 8 | TuranOnThickSetsOfLevels | T3, Q4 | explicit Turán window theorem with remainder at radius `R`; thick sets see the top part | checked |
| 9 | TheQuestionsOfTheField | all | bundle | open |

## Approach
Organizing principle: depth (precision at fixed primes) vs breadth (number of primes at fixed precision).
Transcendence controls depth; B97 is breadth at constant depth.

## Log
- 2026-11-09 — created; README draft written; modules 1–8 checked.
