# Arithmetic Lefschetz–Stepanov theory (ALST)

- **ID:** alst
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0811/obstacles-summary.md §2.9
- **Statement:** Locate Stepanov's three exact facts (S1 Frobenius fixes the points, S2 inseparability, S3 product formula) over ℤ; answer Q1–Q4, build T1–T5, test criteria C1–C4.

## Goal
Programme folder `formal/GaloisForLFunctions/ArithmeticLefschetzStepanovTheory/`, umbrella
`ArithmeticLefschetzStepanovTheory.lean`, README in the folder. Main conjecture (RH): `c_B(log n²) ≥ −K`.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  paper proofs of the planned theorems
- [ ] 2 → 3  every theorem below in Lean, standard axioms

## Approach — planned theorems
| # | Theorem | Answers |
|---|---|---|
| 1 | Galois = Adams on torsion: `σ_a(F(ω)) = F(ω^a)`; `ψ_q F = F` on `(q−1)`-torsion; prime orbit ∩ torsion = {0} for two primes; dilates of a torsion return are returns to the conjugates | Q1, S1 |
| 2 | Norm amplifier: `Π_a |F(ω^a)| < 1 ⇒ F = 0` on `[ω]`; Hasse orders; via orbit values at the dilates; precision independent of order | Q4, T3, C4 |
| 3 | Cyclotomic Bézout/RR: vanishing at the closed torsion points of the prime circles ⇔ divisibility by `ΠΦ_m(p^{−s})^J`; `Σ φ(m)J log p ≤ deg` | Q3, T5 |
| 4 | Uniform order at a torus point `≤ deg/log 2`, sharp; orbit order at `s=0`: integrality gives order two exactly; order three ⇔ quadratic relation among `log p` (two primes: Gelfond–Schneider gives exactness at every order) | Q3, Q4 |
| 5 | Generic returns: the set of `t` where some nonzero integer auxiliary vanishes on the orbit is countable | Q4 no-go |
| 6 | Factorial auxiliaries: Legendre + Stirling ⇒ count = main + O(log x), blind | S2, C3 |
| 7 | Siegel lemma on `P`-smooth numbers with prescribed torsion vanishing and explicit height | T1 |
| 8 | Zero estimate for integer Dirichlet polynomials uniform in `|P|` | T2 |
| 9 | Arithmetic Stepanov bound in point-count form at square degrees ⇔ RH | Q2, T4 |
| 10 | Calibration: mechanisms 1–8 on the integer-norm one-off | C3 |

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** —
- **Strongest positive survivor:** —
- **New insight:** —
- **Status:** —

## Log
- 2026-11-08 — created in 1-in-progress; README draft written
