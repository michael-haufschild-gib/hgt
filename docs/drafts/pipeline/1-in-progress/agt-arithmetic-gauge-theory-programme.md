# Arithmetic gauge theory of the ring ℤ (AGT programme)

- **ID:** agt-programme
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2910/obstacles-summary.md §2.5–2.6
- **Statement:** Develop the programme: gauge points, special-point rigidity, approximate ring
  endomorphisms (Frobenius gap), coherent divisor collapse, shells as successor correlations,
  bounded multiplicity of classical producers, gauge exponents.

## Goal
A Lean programme `formal/GaloisForLFunctions/ArithmeticGaugeTheory/` with umbrella
`ArithmeticGaugeTheory.lean` and a foundational README. It builds on ACG's `GaugeTorus`,
`gaugeHaar`, `twist`.

## Gates
- [x] 0 → 1  in-progress: README draft written
- [ ] 1 → 2  paper proofs of each pillar (in module docstrings)
- [ ] 2 → 3  each pillar formalized, checked with `lake --old env lean`, wired into the umbrella

## Approach
Pillar modules (planned order):
1. `TheAdditivelyInvariantPoint`: a nonvanishing completely multiplicative function that is
   eventually periodic, or convergent, is identically one; twist versions.
2. `ApproximateRingEndomorphisms`: completely multiplicative maps with bounded additive defect
   are the identity or bounded by one. The gauge torus is exactly the unimodular ones. Exact
   endomorphisms are the identity and zero. Frobenius over 𝔽_p[X] multiplies degree by p.
3. `TheDivisorCollapse`: `Σ_{k∣ℓ} Λ(k)χ_x(k)` equals `log ℓ` at `0` and for every ℓ only at `0`.
   It has a closed form at the Liouville twin, gauge mean `0`, gauge mean square
   `Σ_{k∣ℓ} Λ(k)²`, and coherence bounds.
4. `ShellsAreSuccessorCorrelations`: the non-ratio pairs `n = km + j` of the prime form equal
   the shift-`j` successor correlation of `Λ * x` against `x`; gauge mean zero for `j ≠ 0`.
5. `FactorialRatiosHaveBoundedMultiplicity`: above the square root, `v_p` of a balanced factorial
   ratio is bounded by the number of factorials.
6. `GaugeExponents`: the precision exponent of a gauge point. Its almost-sure value is `≤ 1/2`,
   it equals `1` at twin tails, and it equals `Θ` at `0` (if available).

## Log
- 2026-10-29 — created; README draft written.
