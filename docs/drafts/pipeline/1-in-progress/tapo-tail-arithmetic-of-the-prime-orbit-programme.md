# Tail arithmetic of the prime orbit (TAPO)

- **ID:** tapo
- **Stage:** 1-in-progress (programme core formalized; open topics remain)
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0711/obstacles-summary.md §2.8b
- **Statement:** the law of the tail phases `t log p`, `p > y`, at one height, conditionally on the head `p ≤ y`.

## Goal
Answer the six questions of §2.8b and build the six tools, in Lean, in
`formal/GaloisForLFunctions/TailArithmeticOfThePrimeOrbit/` (umbrella `TailArithmeticOfThePrimeOrbit.lean`,
wired into `MainTheorems.lean`). README is the foundational document.

## Module status

All modules check with `lake --old env lean`; oleans built; answer theorems depend only on the standard axioms.

| Module | Content | Answers |
|---|---|---|
| TheFirstReturn | `firstReturn`, Dirichlet bound, group laws, corners, rank one | Q1 |
| TheFirstReturnIsAnExtremeValue | harmonic defect = `log log N − log|ζ(1+1/log N+it)|` + O(1); Littlewood spike; pole price; escape | Q1 |
| ThePrecisionLawOfTheFirstReturn | PTT savings → `R > exp(√(y/48 log y))` at precision `y^{−9/2}`, `R > exp(y^{1/A})` | Q1 |
| ProportionalSavingIsAHeavyFirstReturn | B46 ⟺ no heavy return | T1 |
| TheFadeOfAReturn | forced fade, fade length `|ζ(1+iτ)|` | objects |
| TheTailDecouplesFromTheHead | smooth × rough mean value factorizes; conditional mean zero | Q2, T3 |
| TheConditionalMomentsOfTheTail | `‖B^k‖² ≤ k!‖b‖^{2k}`; Gaussian conditional moments and large deviations | Q2, T3 |
| TheHeadIsFrozenAtItsResolution | head moves by `|v|·Σ log p p^{−σ}/(1−p^{−σ})` | Q2 |
| TheTailOfAReturnCarriesTheZero | tail limit along bounded returns; returns at a zero tail-bad at every cut; density zero | Q5 |
| TheRecurrenceDichotomyOfTheTail | universality + zero targets tail-bad at every cut | Q5, T4 |
| TheJetOfTheLogarithm | dilation equivariance, step law, exotic isolation | Q3 |
| TheDepthAspect | exact `q`-differencing vs archimedean defect `t h h'/x²` | Q4 |
| EulerCoordinatesStopAtTheAbscissa | `Σ|1−E_p| < ∞ ⟺ Re s > 1`; head–tail certificates | Q6, T6 |
| TheCombOfAReturn | comb law, thin comb past `X ≍ t`, comb inequality | T5, T2 |
| TheQuestionsOfTheField | six answers and the tools | all |

## Open (README §10)
Constant-precision first-return exponent (needs a Lean VK bound for `|ζ(1+it)|`); tail law past the Kronecker scale
(tilted resonators); Bohr mean of `|ζ|²` (A23) with torus reading; B89; inverse theorem along the moving jet; exact
archimedean half depth; certificates at typical heights; smooth numbers on the comb below `X ≍ t`; heavy returns at the
size curve (B46).

## Gates
- [x] 0 → 1  in-progress: README, module plan
- [x] 1 → 2  paper proofs in module docstrings
- [x] 2 → 3  modules checked, wired into the umbrella (core); open topics stay on this card

## Log
- 2026-11-07 — created; core modules formalized
