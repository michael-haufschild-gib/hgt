import GaloisForLFunctions.RHTower.Sieve.DirichletLargeValues

/-!
# Counting the large values of a Dirichlet polynomial

If `|F| ≥ V` at each of `R + 1` points separated by `δ` inside `[δ/2, T - δ/2]`, then

`(R + 1) V² ≤ (T + 4N(1 + log N))(δ^{-1} + 2 log N) ∑_{n < N} |a_n|²`,

so the number of such points is at most that bound divided by `V²`.  This is the form in which a
large-values estimate is applied: a cap on how often a Dirichlet polynomial can be large.
-/

namespace RHTower.Sieve

open Finset

/-- **A cap on the number of large values.** -/
theorem card_largeValues_le (N : ℕ) (hN : 2 ≤ N) (a : Fin N → ℂ) {lam : ℕ → ℝ} {δ T V : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T) (hV : 0 < V)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0) (R : ℕ)
    (hhigh : lam R + δ / 2 ≤ T)
    (hbig : ∀ r ∈ Finset.range (R + 1), V ≤ ‖dirPoly N a (lam r)‖) :
    ((R : ℝ) + 1) * V ^ 2
      ≤ (T + 4 * (N : ℝ) * (1 + Real.log N)) * (1 / δ + 2 * Real.log N)
          * ∑ m : Fin N, ‖a m‖ ^ 2 := by
  have hterm : ∀ r ∈ Finset.range (R + 1), V ^ 2 ≤ ‖dirPoly N a (lam r)‖ ^ 2 := by
    intro r hr
    exact pow_le_pow_left₀ (le_of_lt hV) (hbig r hr) 2
  have hcount : ((R : ℝ) + 1) * V ^ 2
      ≤ ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖ ^ 2 := by
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hterm)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  exact le_trans hcount (largeValues_dirPoly N hN a hδ hT hgap hlow R hhigh)

end RHTower.Sieve
