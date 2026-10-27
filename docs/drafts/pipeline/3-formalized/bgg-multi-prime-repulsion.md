# Multi-prime Diophantine repulsion of the Liouville vacuum

- **ID:** bgg-c8
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** BGG README open topic 3; Q1 open step.
- **Statement:** For distinct primes `p_1, …, p_N` (`N ≥ 2`), `L = Σ log p_j`,
  `τ = (N(|γ|L/π + 1))^{1/(N−1)}`, every `γ ∈ ℝ` satisfies
  `Σ_j (1 + cos(γ log p_j)) ≥ γ² e^{−2τL}/(32Nτ²)`.
  Corollary: for every `ε > 0` the first `⌈1/ε⌉ + 2` primes satisfy `Σ_j (1 + cos(γ log p_j)) ≥ exp(−|γ|^ε)`
  for all large `|γ|`.

## Paper proof
`γ log p_j = u_j π + δ_j`, `u_j` odd, `|u_j| ≤ |γ|L/π + 1`, `1 + cos(γ log p_j) ≥ δ_j²/8`. Siegel's lemma
for the `1 × N` system `(u_j)` gives `t ∈ ℤ^N \ {0}`, `Σ t_j u_j = 0`, `max|t_j| ≤ τ`. Then
`γ Σ t_j log p_j = Σ t_j δ_j`. With `A = Π p_j^{t_j⁺}`, `B = Π p_j^{t_j⁻}`: `A ≠ B` (a prime with `t_j ≠ 0`
divides exactly one side), so `|log A − log B| ≥ 1/(A + B) ≥ e^{−τL}/2`. Hence `|γ| e^{−τL}/2 ≤ τ Σ|δ_j|`;
Cauchy–Schwarz gives `Σ δ_j² ≥ (Σ|δ_j|)²/N`. Corollary: `τ ≤ K|γ|^a`, `a = 1/(N−1) < ε`, and
`|γ|^ε ≥ |γ|^a · |γ|^{ε−a}` dominates `2KL|γ|^a + log(32NK²)` eventually.

## Lean
`MultiPrimeDiophantineRepulsion.lean`: `prod_pow_toNat_ne`, `abs_sum_mul_log_prime_ge`, `repulsionScale`,
`multiPrime_repulsion`, `exists_primes_repulsion_ge_exp_neg_rpow`. Uses Mathlib `Int.Matrix.exists_ne_zero_int_vec_norm_le'`.
Axioms: propext, Classical.choice, Quot.sound.

## Log
- 2026-10-27 — formalized.
