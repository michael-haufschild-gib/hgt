# Arithmetic Lefschetz–Stepanov theory (ALST)

- **ID:** alst
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0811/obstacles-summary.md §2.9
- **Statement:** Over `ℤ`, Stepanov's three exact facts come apart: the exact Frobenius (Adams = Galois) lives on the torsion of the prime torus, inseparability only at finite places, the product formula counts the closed points of the prime circles at Chebyshev's price; exact order costs the degree at every point.

## Goal
Folder `formal/GaloisForLFunctions/ArithmeticLefschetzStepanovTheory/` (README), umbrella
`ArithmeticLefschetzStepanovTheory.lean` (wired in `MainTheorems`). Main conjecture (RH):
`c_B(log n²) ≥ −K` (`SurfaceOfSpecZ.riemannHypothesis_iff_bddBelow_squareDegrees`).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  paper proofs (module docstrings)
- [x] 2 → 3  Lean, every module checked with `lake --old env lean`

## Theorems
| # | Theorem | Module | Answers |
|---|---|---|---|
| 1 | Galois = Adams on torsion; `x^q = x` on `(q−1)`-torsion; Frobenius on the orbit = dilation; no common torsion return; torsion returns exist; norm amplifier on the torus and on Frobenius orbits of returns, precision `1/(4mL)`, threshold sharp | `TheFrobeniusOfTheTorsionIsGalois` | Q1, Q4, T3, C4 |
| 2 | Bézout at the common fixed point, two primes (Gelfond–Schneider + simplex unisolvence), sharp; orders 0, 1 exact for any `P` | `TheOrderAtTheCommonFixedPointCostsTheDegree` | Q3, Q4, M2 |
| 3 | No exact vanishing at generic heights (countable); every return window avoids it; repulsion at sign returns | `IntegralityActsOnlyOnTheTorsion` | Q4 |
| 4 | Stepanov count of the closed points of the prime circles `Π p^{φ(m)J} ≤ N`, sharp | `TheStepanovCountOfTheClosedPoints` | Q3, T5 |
| 5 | Siegel lemma on smooth numbers with torsion vanishing; small at every return | `SiegelAuxiliariesOnTheTorsion` | T1 |
| 6 | Zero estimate at returns uniform in the number of logarithms | `TheZeroEstimateAtTheReturns` | T2 |
| 7 | Order at any point ≤ total degree ≤ `log N/log 2`; amplifier order paid in length | `ExactVanishingCostsTheDegree` | C4, M2 |
| 8 | Excess orbit order at `0` is a homogeneous relation among `log p`, any `P` | `TheExcessOrderIsARelationAmongTheLogarithms` | Q4, M2 |
| 9 | Stepanov's construction on the torsion; `ψ_ℓ g ≡ g^ℓ`, `∂ψ_ℓ g ≡ 0 (mod ℓ)`; `ℓ`-adic amplifier with threshold `ℓ^{φ(m)}` | `StepanovsConstructionOnTheTorsion` | C1, S1+S2+S3 |
| 10 | Lefschetz = Stepanov: `Σ_{2≤n≤N}(Γ_1·Γ_n − 1 − 1/(n²−1)) = ψ(N) = log N(A_N)`, `N(A_N) = lcm(1..N)`, `A_N` minimal; RH ⇔ `log N(A_N) ≤ N + C√N log²N` (also squarefree, `θ`) | `TheLefschetzNumbersAreStepanovDegrees` | Q2, T4, M1, C2 |
| 11 | The Stepanov degree bound fails for the integer-norm one-off (every `C`), holds for the real one-off | `TheStepanovBoundSeparatesZetaFromTheOneOff` | C3 |

Corpus inputs: point count `pointCount_eq` (SOSZ), von Koch `riemannHypothesis_iff_chebyshevPsi_sub_isBigO` (RHTower), integer-norm one-off (APD), Stepanov over `𝔽_q` (RHTower, AKLT), precision cap (IRW), Gelfond–Schneider (RHTower).

## No-go closure
- **Exact killing theorem/mechanism:** exact vanishing of integer auxiliaries on the prime orbit occurs at countably many heights only; exact order at any point costs `log₂ N` per order; approximate copies at returns are Rouché-capped.
- **Strongest positive survivor:** the norm amplifier on closed torsion points (exact, any order, polynomial precision), its orbit form along Frobenius orbits of returns, and the repulsion at returns.
- **New insight:** the char-0 Frobenius exists (Adams = Galois on torsion) but is separable at the archimedean place; Stepanov's count needs an inseparable coupling of torsion to the orbit that uses the coefficients of `ζ`.
- **Status:** all eleven theorems in Lean.

## Log
- 2026-11-08 — created; eleven modules formalized; README written
