import GaloisForLFunctions.HTGeometry.ComplexSiegelQuasiDiagonal
import GaloisForLFunctions.HTGeometry.ComplexCongruenceDiagonal

/-!
# Diagonal and congruence-entry bounds for Hermitian Siegel forms

The diagonal of a complex Jacobi form is an exact positive weighted column norm.  Siegel bounds
control it by the corresponding Jacobi weight, and quasi-diagonality then controls every entry of
a congruence carrying one Hermitian Siegel form to another.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- Exact diagonal of a Hermitian Jacobi form. -/
theorem ComplexJacobiData.form_diag (J : ComplexJacobiData n) (j : Fin n) :
    (J.form j j).re = ∑ m, J.d m * ‖J.U m j‖ ^ 2 := by
  have h := J.quadForm_eq (Pi.single j (1 : ℂ))
  rw [star_single_dot_mulVec_single] at h
  simpa [Matrix.mulVec_single] using h

/-- The diagonal of a Hermitian Siegel form is controlled by its corresponding Jacobi weight. -/
theorem ComplexJacobiData.form_diag_le_siegel (J : ComplexJacobiData n)
    {t u : ℝ} (ht : 1 ≤ t) (hS : J.IsSiegel t u) (j : Fin n) :
    (J.form j j).re ≤ (n : ℝ) * u ^ 2 * t ^ n * J.d j := by
  classical
  have hu : (0 : ℝ) ≤ u := le_trans (norm_nonneg _) (hS.2 j j)
  have htn : (0 : ℝ) < t ^ n := pow_pos (lt_of_lt_of_le zero_lt_one ht) n
  rw [J.form_diag j]
  have hterm : ∀ m : Fin n,
      J.d m * ‖J.U m j‖ ^ 2 ≤ u ^ 2 * t ^ n * J.d j := by
    intro m
    by_cases hmj : j < m
    · rw [J.upper m j hmj, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
      exact mul_nonneg (mul_nonneg (sq_nonneg u) htn.le) (J.pos j).le
    · have hmle : (m : ℕ) ≤ (j : ℕ) := Fin.le_def.1 (not_lt.1 hmj)
      have h1 : J.d m ≤ t ^ n * J.d j := J.d_le_pow_n ht hS hmle
      have h2 : ‖J.U m j‖ ^ 2 ≤ u ^ 2 := by
        nlinarith [hS.2 m j, norm_nonneg (J.U m j)]
      nlinarith [sq_nonneg ‖J.U m j‖, (J.pos m).le, htn.le, (J.pos j).le]
  calc
    ∑ m, J.d m * ‖J.U m j‖ ^ 2 ≤
        ∑ _m : Fin n, u ^ 2 * t ^ n * J.d j :=
      Finset.sum_le_sum fun m _ => hterm m
    _ = (n : ℝ) * u ^ 2 * t ^ n * J.d j := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Entry bound for a congruence between two Hermitian Siegel forms. -/
theorem complex_siegel_entry_bound
    {J J' : ComplexJacobiData n} {t u c : ℝ} (ht : 1 ≤ t) (hc : 0 < c)
    (hS' : J'.IsSiegel t u) {γ : Matrix (Fin n) (Fin n) ℂ}
    (hγ : J'.form = Matrix.conjTranspose γ * J.form * γ)
    (hquasi : ∀ v : Fin n → ℂ,
      c * (∑ m, J.d m * ‖v m‖ ^ 2) ≤ (star v ⬝ᵥ (J.form.mulVec v)).re)
    (k i : Fin n) :
    c * (J.d k * ‖γ k i‖ ^ 2) ≤
      (n : ℝ) * u ^ 2 * t ^ n * J'.d i := by
  let v : Fin n → ℂ := fun m => γ m i
  have hcol : (J'.form i i).re = (star v ⬝ᵥ (J.form.mulVec v)).re := by
    have hq := congrArg Complex.re
      (show J'.form i i = star v ⬝ᵥ (J.form.mulVec v) by
        rw [hγ]
        exact conjCongr_diag_eq_quadForm_col J.form γ i)
    exact hq
  have hlow : c * (J.d k * ‖v k‖ ^ 2) ≤
      c * ∑ m, J.d m * ‖v m‖ ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    exact Finset.single_le_sum
      (fun m _ => mul_nonneg (J.pos m).le (sq_nonneg ‖v m‖))
      (Finset.mem_univ k)
  calc
    c * (J.d k * ‖γ k i‖ ^ 2) = c * (J.d k * ‖v k‖ ^ 2) := rfl
    _ ≤ c * ∑ m, J.d m * ‖v m‖ ^ 2 := hlow
    _ ≤ (star v ⬝ᵥ (J.form.mulVec v)).re := hquasi v
    _ = (J'.form i i).re := hcol.symm
    _ ≤ (n : ℝ) * u ^ 2 * t ^ n * J'.d i := J'.form_diag_le_siegel ht hS' i

end GaloisForLFunctions.HTGeometry
