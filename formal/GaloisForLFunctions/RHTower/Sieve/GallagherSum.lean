import GaloisForLFunctions.RHTower.Sieve.WindowDisjointness

/-!
# Gallagher's bound summed over separated points

Summing the local bound of `GallagherPointwise.lean` over points with consecutive gaps at least `δ`
and using the disjointness of their windows gives

`∑_{r ≤ R} |S(λ_r)|² ≤ δ^{-1} ∫_A^{λ_R + δ/2} |S|² + ∫_A^{λ_R + δ/2} 2|S||S'|`.

The right-hand side no longer refers to the points at all — only to the enclosing interval — which
is the whole point of the argument: no sum of reciprocal separations is ever formed, so the
logarithmic loss that `sum_inv_abs_dist_le` proves unavoidable for term-by-term bounds does not
arise.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- **Gallagher's bound over a separated family.** -/
theorem gallagher_sum (N : ℕ) (c : Fin N → ℂ) {lam : ℕ → ℝ} {δ A : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hA : A ≤ lam 0 - δ / 2) (R : ℕ) :
    ∑ r ∈ Finset.range (R + 1), ‖expSum N c (lam r)‖ ^ (2 : ℕ)
      ≤ (1 / δ) * (∫ t in A..(lam R + δ / 2), ‖expSum N c t‖ ^ (2 : ℕ))
        + (∫ t in A..(lam R + δ / 2),
            2 * ‖expSum N c t‖ * ‖expSum N (derivCoeff N c) t‖) := by
  have hcont1 : Continuous (fun t : ℝ => ‖expSum N c t‖ ^ (2 : ℕ)) :=
    ((continuous_expSum N c).norm).pow 2
  have hcont2 : Continuous (fun t : ℝ =>
      2 * ‖expSum N c t‖ * ‖expSum N (derivCoeff N c) t‖) :=
    (continuous_const.mul (continuous_expSum N c).norm).mul
      (continuous_expSum N (derivCoeff N c)).norm
  have hnn1 : ∀ t : ℝ, (0 : ℝ) ≤ ‖expSum N c t‖ ^ (2 : ℕ) := fun t => sq_nonneg _
  have hnn2 : ∀ t : ℝ, (0 : ℝ) ≤ 2 * ‖expSum N c t‖ * ‖expSum N (derivCoeff N c) t‖ := by
    intro t
    positivity
  have hterm : ∀ r ∈ Finset.range (R + 1),
      ‖expSum N c (lam r)‖ ^ (2 : ℕ)
        ≤ (1 / δ) * (∫ t in (lam r - δ / 2)..(lam r + δ / 2), ‖expSum N c t‖ ^ (2 : ℕ))
          + (∫ t in (lam r - δ / 2)..(lam r + δ / 2),
              2 * ‖expSum N c t‖ * ‖expSum N (derivCoeff N c) t‖) :=
    fun r _ => gallagher_at_point N c (lam r) hδ
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := sum_window_le hcont1 hnn1 hδ hgap hA R
  have h2 := sum_window_le hcont2 hnn2 hδ hgap hA R
  have hδinv : (0 : ℝ) ≤ 1 / δ := by positivity
  have h1' := mul_le_mul_of_nonneg_left h1 hδinv
  linarith

end RHTower.Sieve
