import GaloisForLFunctions.HTGeometry.SiegelIsometryColumns

/-!
# The exact column sum of a congruence

The diagonal entry of a congruate is the value of the original form at the corresponding column, so
in Jacobi coordinates it is an *exact* weighted sum:

`∑ₖ dₖ ((U γ)ₖᵢ)² = A'ᵢᵢ ≤ (1 + n tⁿ/4) d'ᵢ`.

The single-term form of this — `dₖ γₖᵢ² ≤ K d'ᵢ` — is what the entry bound records; the full sum is
strictly stronger, and it is the weights of `U γ`, not of `γ`, that appear.

* `siegel_col_sum_eq` : **the exact column sum.**
* `siegel_col_sum_bound` : **and its Siegel bound.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- **The exact column sum of a congruence.** -/
theorem siegel_col_sum_eq {J J' : JacobiData n} {γ : Matrix (Fin n) (Fin n) ℝ}
    (hγ : J'.form = γᵀ * J.form * γ) (i : Fin n) :
    (∑ k, J.d k * ((J.U *ᵥ (fun m => γ m i)) k) ^ (2 : ℕ)) = J'.form i i := by
  rw [hγ, congr_diag_eq_quadForm_col, J.quadForm_eq]

/-- **The Siegel bound on the exact column sum.** -/
theorem siegel_col_sum_bound {J J' : JacobiData n} {t u : ℝ} (ht : 1 ≤ t)
    (hS' : J'.IsSiegel t u) (hred' : ∀ a b : Fin n, a < b → |J'.U a b| ≤ 1 / 2)
    {γ : Matrix (Fin n) (Fin n) ℝ} (hγ : J'.form = γᵀ * J.form * γ) (i : Fin n) :
    (∑ k, J.d k * ((J.U *ᵥ (fun m => γ m i)) k) ^ (2 : ℕ))
      ≤ (1 + (n : ℝ) / 4 * t ^ n) * J'.d i := by
  rw [siegel_col_sum_eq hγ i]
  exact J'.form_diag_le_pow ht hS' hred' i

end GaloisForLFunctions.HTGeometry
