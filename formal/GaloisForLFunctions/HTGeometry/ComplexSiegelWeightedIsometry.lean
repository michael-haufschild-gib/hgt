import GaloisForLFunctions.HTGeometry.ComplexSiegelEntryBound

/-!
# Weighted isometries between Hermitian Siegel forms

Stripping the two upper-unipotent factors from a Hermitian congruence leaves a matrix carrying one
positive real diagonal exactly to the other.  Its columns therefore obey sharp weighted norm
bounds.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- Normal form of a congruence after removing its two complex Jacobi factors. -/
theorem complex_weightedIsometry_congr
    {J J' : ComplexJacobiData n} {γ : Matrix (Fin n) (Fin n) ℂ}
    (hform : J'.form = Matrix.conjTranspose γ * J.form * γ) :
    Matrix.conjTranspose (J.U * γ * J'.U⁻¹) *
        Matrix.diagonal (fun i => (J.d i : ℂ)) * (J.U * γ * J'.U⁻¹) =
      Matrix.diagonal (fun i => (J'.d i : ℂ)) := by
  have hU' : IsUnit J'.U.det := by rw [J'.det_eq_one]; exact isUnit_one
  have hU'H : IsUnit (Matrix.conjTranspose J'.U).det := by
    rw [Matrix.det_conjTranspose]
    exact hU'.star
  have hmid : Matrix.conjTranspose (J.U * γ) *
        Matrix.diagonal (fun i => (J.d i : ℂ)) * (J.U * γ) =
      Matrix.conjTranspose J'.U *
        Matrix.diagonal (fun i => (J'.d i : ℂ)) * J'.U := by
    have hA : Matrix.conjTranspose γ * J.form * γ =
        Matrix.conjTranspose (J.U * γ) *
          Matrix.diagonal (fun i => (J.d i : ℂ)) * (J.U * γ) := by
      rw [ComplexJacobiData.form, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have hB : J'.form = Matrix.conjTranspose J'.U *
        Matrix.diagonal (fun i => (J'.d i : ℂ)) * J'.U := rfl
    rw [← hA, ← hform, hB]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
  calc
    (Matrix.conjTranspose J'.U)⁻¹ * Matrix.conjTranspose (J.U * γ) *
          Matrix.diagonal (fun i => (J.d i : ℂ)) * (J.U * γ * J'.U⁻¹) =
        (Matrix.conjTranspose J'.U)⁻¹ *
          (Matrix.conjTranspose (J.U * γ) *
            Matrix.diagonal (fun i => (J.d i : ℂ)) * (J.U * γ)) * J'.U⁻¹ := by
      simp only [Matrix.mul_assoc]
    _ = (Matrix.conjTranspose J'.U)⁻¹ *
          (Matrix.conjTranspose J'.U *
            Matrix.diagonal (fun i => (J'.d i : ℂ)) * J'.U) * J'.U⁻¹ := by
      rw [hmid]
    _ = Matrix.diagonal (fun i => (J'.d i : ℂ)) := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv _ hU', Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hU'H, Matrix.one_mul]

/-- Each entry of a complex weighted isometry is controlled by its source and target weights. -/
theorem complex_weightedIsometry_entry_le
    {M : Matrix (Fin n) (Fin n) ℂ} {J J' : ComplexJacobiData n}
    (h : Matrix.conjTranspose M * Matrix.diagonal (fun i => (J.d i : ℂ)) * M =
      Matrix.diagonal (fun i => (J'.d i : ℂ))) (k i : Fin n) :
    J.d k * ‖M k i‖ ^ 2 ≤ J'.d i := by
  have hq := re_complex_jacobi_quadForm M J.d (Pi.single i (1 : ℂ))
  have hdiag :
      (star (Pi.single i (1 : ℂ)) ⬝ᵥ
        ((Matrix.conjTranspose M * Matrix.diagonal (fun j => (J.d j : ℂ)) * M).mulVec
          (Pi.single i (1 : ℂ)))).re = J'.d i := by
    rw [h, star_single_dot_mulVec_single]
    simp
  rw [hdiag] at hq
  have hq' : J'.d i = ∑ m, J.d m * ‖M m i‖ ^ 2 := by
    calc
      J'.d i = ∑ m, J.d m * ‖M.mulVec (Pi.single i (1 : ℂ)) m‖ ^ 2 := hq
      _ = ∑ m, J.d m * ‖M m i‖ ^ 2 := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Matrix.mulVec_single]
        simp
  rw [hq']
  exact Finset.single_le_sum
    (fun m _ => mul_nonneg (J.pos m).le (sq_nonneg ‖M m i‖))
    (Finset.mem_univ k)

end GaloisForLFunctions.HTGeometry
