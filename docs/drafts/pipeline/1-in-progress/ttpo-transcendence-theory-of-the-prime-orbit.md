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
| 1 | TheReturnFormDuality | Q1, Q2 | return ⇒ forms near ℤ; window exclusion; rounded system matches bounded-height forms and returns exactly (breadth cap) | open |
| 2 | LinearFormsWithExplicitDependenceOnTheirNumber | T1, M2, Q2 | explicit Fel'dman parameters; explicit `C(k, W)`; pigeonhole necessity `C ≥ k − 1` | open |
| 3 | TheDepthLawOfReturns | Q1, M1, M2, C3 | Baker ⇒ `R(P, δ) ≥ cδ^{−a}`, uniform over subsets of primes `≤ y` | open |
| 4 | SurvivalAtADeepReturn | Q3, T2 | jets at returns = jets at 0 up to `δ`; order one survives below explicit Baker threshold | open |
| 5 | Turán module | Q4, T3, M5 | window theorem for the finite-rank part; obstruction on the remainder | open |
| 6 | Reciprocity module | T4 | AFE / Estermann reflection along the orbit | open |
| 7 | TheQuestionsOfTheField | all | bundle | open |

## Approach
Organizing principle: depth (precision at fixed primes) vs breadth (number of primes at fixed precision).
Transcendence controls depth; B97 is breadth at constant depth.

## Log
- 2026-11-09 — created; README draft written.
