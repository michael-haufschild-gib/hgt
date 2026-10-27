# The least quadratic non-residue is at most p^{1/(4√e)+ε}

- **ID:** aet-least-nonresidue
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** card `burgess-bound-from-counting.md`
- **Statement:** for every `ε > 0` and every sufficiently large prime `p` there is a quadratic
  non-residue `1 ≤ n ≤ p^{1/(4√e)+ε}`.

## Proof
`β = 1/(4√e) + ε` (`ε ≤ 1/10`), `u = √e/(1 + 2√eε) ∈ (1, √e)`, `α = uβ = 1/4 + δ`, `r > 1/δ`.
If every `n ≤ y = ⌊p^β⌋` is a residue, every `n ≤ x = ⌊p^α⌋` without prime factors `> y` has
`χ(n) = 1`, and at most `x Σ_{y<q≤x} 1/q` others exist: `Σ_{n≤x} χ(n) ≥ x(1 − 2Σ 1/q)`. Mertens
on the window, `Σ_{X<q≤X^u} 1/q → log u < 1/2`, gives `≥ c x`; Burgess gives
`≤ K_r x^{1−1/r} p^{(r+1)/(4r²)}(1 + log p) = o(x)` since `α/r − (r+1)/(4r²) > 0`.

## Lean
`ArithmeticEffectivityTheory/TheLeastQuadraticNonresidue.lean`: `chiR_eq_one_of_smooth`,
`card_bad_le`, `sum_chiR_ge_vinogradov`, `tendsto_primeRecipSum_window` (from
`RHTower.tendsto_primeRecipSum_floor_sub_logLog`), `eventually_exists_nonresidue_le`.
Axioms: propext, choice, Quot.sound.

## Log
- 2026-10-27 — formalized.
