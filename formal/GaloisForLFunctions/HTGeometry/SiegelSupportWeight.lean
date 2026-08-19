import GaloisForLFunctions.HTGeometry.SiegelColumnSum

/-!
# The support weight of a column

Quasi-diagonality is exactly the bridge between the two structures of the previous file: the weights
attach to the columns of `U γ`, integrality attaches to `γ`, and quasi-diagonality transfers the
weighted bound from the former to the latter,

`c ∑ₖ dₖ γₖᵢ² ≤ (1 + n tⁿ/4) d'ᵢ`.

Since a nonzero integer entry has square at least one, the weights of the *support* of a column of
`γ` therefore already sum to at most a multiple of `d'ᵢ`.

* `siegel_col_weight_sum` : **the weighted column bound for `γ` itself.**
* `siegel_support_weight_sum` : **the support weights of a column sum to `≲ d'ᵢ`.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- **The weighted column bound, for `γ` itself.** -/
theorem siegel_col_weight_sum {J J' : JacobiData n} {t u c : ℝ} (ht : 1 ≤ t)
    (hS' : J'.IsSiegel t u) (hred' : ∀ a b : Fin n, a < b → |J'.U a b| ≤ 1 / 2)
    {γ : Matrix (Fin n) (Fin n) ℝ} (hγ : J'.form = γᵀ * J.form * γ)
    (hquasi : ∀ v : Fin n → ℝ, c * (∑ m, J.d m * (v m) ^ 2) ≤ v ⬝ᵥ (J.form *ᵥ v)) (i : Fin n) :
    c * (∑ k, J.d k * (γ k i) ^ 2) ≤ (1 + (n : ℝ) / 4 * t ^ n) * J'.d i := by
  have hcol : J'.form i i = (fun m => γ m i) ⬝ᵥ (J.form *ᵥ fun m => γ m i) := by
    rw [hγ]
    exact congr_diag_eq_quadForm_col _ _ i
  calc c * (∑ k, J.d k * (γ k i) ^ 2)
      = c * (∑ k, J.d k * ((fun m => γ m i) k) ^ 2) := rfl
    _ ≤ (fun m => γ m i) ⬝ᵥ (J.form *ᵥ fun m => γ m i) := hquasi _
    _ = J'.form i i := hcol.symm
    _ ≤ (1 + (n : ℝ) / 4 * t ^ n) * J'.d i := J'.form_diag_le_pow ht hS' hred' i

/-- **The support weights of a column of an integral `γ` sum to at most a multiple of `d'ᵢ`.** -/
theorem siegel_support_weight_sum {J J' : JacobiData n} {t u c : ℝ} (ht : 1 ≤ t) (hc : 0 < c)
    (hS' : J'.IsSiegel t u) (hred' : ∀ a b : Fin n, a < b → |J'.U a b| ≤ 1 / 2)
    {γ : Matrix (Fin n) (Fin n) ℝ} (hγ : J'.form = γᵀ * J.form * γ)
    (hquasi : ∀ v : Fin n → ℝ, c * (∑ m, J.d m * (v m) ^ 2) ≤ v ⬝ᵥ (J.form *ᵥ v))
    {g : Matrix (Fin n) (Fin n) ℤ} (hg : ∀ a b, γ a b = (g a b : ℝ)) (i : Fin n) :
    c * (∑ k ∈ Finset.univ.filter (fun k : Fin n => γ k i ≠ 0), J.d k)
      ≤ (1 + (n : ℝ) / 4 * t ^ n) * J'.d i := by
  classical
  refine le_trans ?_ (siegel_col_weight_sum ht hS' hred' hγ hquasi i)
  refine mul_le_mul_of_nonneg_left ?_ hc.le
  calc (∑ k ∈ Finset.univ.filter (fun k : Fin n => γ k i ≠ 0), J.d k)
      ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n => γ k i ≠ 0), J.d k * (γ k i) ^ 2 := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [Finset.mem_filter] at hk
        have hsq : (1 : ℝ) ≤ (γ k i) ^ 2 := one_le_sq_of_int_ne_zero (hg k i) hk.2
        nlinarith [hsq, (J.pos k).le]
    _ ≤ ∑ k, J.d k * (γ k i) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun k _ _ => mul_nonneg (J.pos k).le (sq_nonneg _))

end GaloisForLFunctions.HTGeometry
