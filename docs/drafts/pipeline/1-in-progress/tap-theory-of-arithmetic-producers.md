# Theory of Arithmetic Producers (TAP)

- **ID:** TAP
- **Stage:** 1-in-progress
- **Type:** programme (CONJECTURE → THEOREM (Lean) loop)
- **Source:** docs/reports/review-2011/obstacles-summary.md §2.9
- **Statement:** develop the theory of arithmetic producers: which comparisons of sizes exist over ℤ, what they cost, at which place, and which twins they separate; answer Q1–Q8, build T1–T5.

## Goal
README: formal/GaloisForLFunctions/ArithmeticProducerTheory/README.md. Lean folder
formal/GaloisForLFunctions/ArithmeticProducerTheory/, umbrella ArithmeticProducerTheory.lean.
Non-circularity: no producer may compute its price from ψ, M or the zeros.

## Gates
- [x] 0 → 1  in-progress: README draft, questions, tools, criteria fixed
- [ ] 1 → 2  every pillar with a paper proof
- [ ] 2 → 3  every pillar formalized, wired, checked

## Conjecture table
| # | Conjecture | Status | Lean |
|---|---|---|---|
| C1 | (Q1) Every derivation of R[X_σ] compatible with expand a (D∘ψ_a = c·ψ_a∘D) is an Euler derivation Σ r_i X_i ∂_i, and c = a when D ≠ 0 and a is a non-zero-divisor; free multiplicity D^k(fψ_a g) = (D^k f)ψ_a g holds iff c = 0, i.e. iff a = 0 in R | open | — |
| C2 | (Q1) A nonzero ℚ-linear intertwiner of the Adams operations that preserves ℤ[X_σ] has integer scalars; inseparability to order k at p costs |λ| ≥ p^k at ∞ | open | — |
| C3 | (T5, Q8) positive Neumann transfer for dilation stencils | open | — |
| C4 | (Q4) Hasse–Weil for Kummer curves from the two pairings, positivity-free | open | — |
| C5 | (criterion 1) abstract Stepanov producer with the hyperelliptic instance | open | — |

## Approach
Order: C1, C2 (operator answer to Q1); C3 (transfer tool); C4, C5 (calibration); then Q2, Q5, Q7, T3, T4.

## Log
- 2026-11-20 — card created; README first draft written.
