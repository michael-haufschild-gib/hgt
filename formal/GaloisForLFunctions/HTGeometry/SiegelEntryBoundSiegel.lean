import GaloisForLFunctions.HTGeometry.SiegelMinorLowerBound

/-!
# The entry bound without size reduction

The Siegel bounds alone bound the diagonal of the form by its Jacobi diagonal: the column of the
unipotent factor above the diagonal entry has bounded entries and its weights are bounded by the
weight at the diagonal.  The entry bound for a congruence then needs no separate size-reduction
hypothesis.

* `JacobiData.form_diag_le_siegel` : the diagonal bound from the Siegel conditions alone.
* `siegel_entry_bound_of_siegel` : **the entry bound.**
* `d_le_of_entry_ne_zero_of_siegel` : a nonzero entry forces a comparison of diagonal entries.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- **The diagonal of a Siegel form is bounded by its Jacobi diagonal.** -/
theorem JacobiData.form_diag_le_siegel (J : JacobiData n) {t u : ℝ} (ht : 1 ≤ t)
    (hS : J.IsSiegel t u) (j : Fin n) :
    J.form j j ≤ (n : ℝ) * u ^ 2 * t ^ n * J.d j := by
  classical
  have hu : (0 : ℝ) ≤ u := le_trans (abs_nonneg _) (hS.2 j j)
  have htn : (0 : ℝ) < t ^ n := pow_pos (lt_of_lt_of_le zero_lt_one ht) n
  have hdj : (0 : ℝ) < J.d j := J.pos j
  rw [J.form_diag j]
  have hterm : ∀ m : Fin n, J.d m * (J.U m j) ^ 2 ≤ u ^ 2 * t ^ n * J.d j := by
    intro m
    by_cases hmj : j < m
    · rw [J.upper m j hmj]
      have : (0 : ℝ) ≤ u ^ 2 * t ^ n * J.d j := by positivity
      simpa using this
    · have hmle : (m : ℕ) ≤ (j : ℕ) := by
        have := not_lt.1 hmj
        exact Fin.le_def.1 this
      have h1 : J.d m ≤ t ^ n * J.d j := J.d_le_pow_n ht hS hmle
      have h2 : (J.U m j) ^ 2 ≤ u ^ 2 := by
        have habs := hS.2 m j
        nlinarith [abs_nonneg (J.U m j), sq_abs (J.U m j)]
      nlinarith [sq_nonneg (J.U m j), (J.pos m).le, htn.le, hdj.le]
  calc (∑ m, J.d m * (J.U m j) ^ 2) ≤ ∑ _m : Fin n, u ^ 2 * t ^ n * J.d j :=
        Finset.sum_le_sum fun m _ => hterm m
    _ = (n : ℝ) * u ^ 2 * t ^ n * J.d j := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The entry bound from the Siegel conditions alone.** -/
theorem siegel_entry_bound_of_siegel {J J' : JacobiData n} {t u c : ℝ} (ht : 1 ≤ t) (hc : 0 < c)
    (hS' : J'.IsSiegel t u) {γ : Matrix (Fin n) (Fin n) ℝ}
    (hγ : J'.form = γᵀ * J.form * γ)
    (hquasi : ∀ v : Fin n → ℝ, c * (∑ m, J.d m * (v m) ^ 2) ≤ v ⬝ᵥ (J.form *ᵥ v))
    (k i : Fin n) :
    c * (J.d k * (γ k i) ^ 2) ≤ (n : ℝ) * u ^ 2 * t ^ n * J'.d i := by
  classical
  set v : Fin n → ℝ := fun m => γ m i with hv
  have hcol : J'.form i i = v ⬝ᵥ (J.form *ᵥ v) := by
    rw [hγ]
    exact congr_diag_eq_quadForm_col _ _ i
  have hlow : c * (J.d k * (v k) ^ 2) ≤ c * (∑ m, J.d m * (v m) ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    exact Finset.single_le_sum (f := fun m => J.d m * (v m) ^ 2)
      (fun m _ => mul_nonneg (J.pos m).le (sq_nonneg _)) (Finset.mem_univ k)
  calc c * (J.d k * (γ k i) ^ 2) = c * (J.d k * (v k) ^ 2) := rfl
    _ ≤ c * (∑ m, J.d m * (v m) ^ 2) := hlow
    _ ≤ v ⬝ᵥ (J.form *ᵥ v) := hquasi v
    _ = J'.form i i := hcol.symm
    _ ≤ (n : ℝ) * u ^ 2 * t ^ n * J'.d i := J'.form_diag_le_siegel ht hS' i

/-- **A nonzero entry of the conjugating matrix forces a comparison of diagonal entries.** -/
theorem d_le_of_entry_ne_zero_of_siegel {J J' : JacobiData n} {t u c : ℝ} (ht : 1 ≤ t) (hc : 0 < c)
    (hS' : J'.IsSiegel t u) {γ : Matrix (Fin n) (Fin n) ℝ}
    (hγ : J'.form = γᵀ * J.form * γ)
    (hquasi : ∀ v : Fin n → ℝ, c * (∑ m, J.d m * (v m) ^ 2) ≤ v ⬝ᵥ (J.form *ᵥ v))
    {g : Matrix (Fin n) (Fin n) ℤ} (hg : ∀ a b, γ a b = (g a b : ℝ))
    {k i : Fin n} (hne : γ k i ≠ 0) :
    c * J.d k ≤ (n : ℝ) * u ^ 2 * t ^ n * J'.d i := by
  have hsq : (1 : ℝ) ≤ (γ k i) ^ 2 := one_le_sq_of_int_ne_zero (hg k i) hne
  have hbound := siegel_entry_bound_of_siegel ht hc hS' hγ hquasi k i
  have hdk : (0 : ℝ) < J.d k := J.pos k
  have h0 : (0 : ℝ) ≤ c * J.d k := (mul_pos hc hdk).le
  have hstep : c * J.d k ≤ c * (J.d k * (γ k i) ^ 2) := by nlinarith [hsq, h0]
  exact le_trans hstep hbound

end GaloisForLFunctions.HTGeometry
