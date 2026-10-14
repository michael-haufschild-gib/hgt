import GaloisForLFunctions.HTGeometry.FiniteBilateralWeightedShift

/-! # The Gram determinant of an actual finite bilateral weighted shift

The ordinary determinant of the shift is blind to every edge weight. Its Gram
operator is diagonal and its Fredholm determinant retains every squared modulus.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open HilbertSchmidt ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace

theorem finiteBilateralWeightedShift_gram_traceClass (N : ℕ) (w : ℤ → ℂ) :
    RHTower.MemSchattenClass 1
      ((finiteBilateralWeightedShift N w).adjoint ∘L finiteBilateralWeightedShift N w) :=
  RHTower.memSchattenClass_one_comp_left (finiteBilateralWeightedShift_traceClass N w) _

theorem coordMatrix_finiteBilateralWeightedShift_gram (N : ℕ) (w : ℤ → ℂ) (i j : ℤ) :
    RHTower.coordMatrix (lpBasis ℤ)
      ((finiteBilateralWeightedShift N w).adjoint ∘L finiteBilateralWeightedShift N w)
      (i, j) = if i = j ∧ j ∈ bilateralShiftEdges N then ((‖w j‖ ^ 2 : ℝ) : ℂ) else 0 := by
  rw [RHTower.coordMatrix_apply, comp_apply, adjoint_inner_right,
    lpBasis_apply, lpBasis_apply]
  change ⟪finiteBilateralWeightedShift N w (lpBasisVec i),
    finiteBilateralWeightedShift N w (lpBasisVec j)⟫_ℂ = _
  rw [finiteBilateralWeightedShift_basis, finiteBilateralWeightedShift_basis]
  by_cases hi : i ∈ bilateralShiftEdges N <;>
    by_cases hj : j ∈ bilateralShiftEdges N
  · simp only [if_pos hi, if_pos hj]
    by_cases hij : i = j
    · subst i
      simp [hj, inner_self_eq_norm_sq_to_K, norm_smul, lpBasisVec, lp.norm_single]
    · rw [inner_smul_left, inner_smul_right, inner_lpBasisVec]
      simp [hij, lpBasisVec, lp.single_apply]
  · simp [hi, hj]
  · have hij : i ≠ j := by intro h; subst i; exact hi hj
    simp [hi, hj, hij]
  · simp [hi, hj]

theorem finiteBilateralWeightedShift_gram_coordinate_support (N : ℕ) (w : ℤ → ℂ)
    (p : ℤ × ℤ) (hp : p ∉ bilateralShiftEdges N ×ˢ bilateralShiftEdges N) :
    RHTower.coordMatrix (lpBasis ℤ)
      ((finiteBilateralWeightedShift N w).adjoint ∘L finiteBilateralWeightedShift N w) p = 0 := by
  rcases p with ⟨i, j⟩
  rw [coordMatrix_finiteBilateralWeightedShift_gram]
  apply if_neg
  rintro ⟨rfl, hj⟩
  exact hp (Finset.mem_product.mpr ⟨hj, hj⟩)

theorem fredholmDetOp_finiteBilateralWeightedShift_gram (N : ℕ) (w : ℤ → ℂ) :
    RHTower.fredholmDetOp (lpBasis ℤ)
      ((finiteBilateralWeightedShift N w).adjoint ∘L finiteBilateralWeightedShift N w) =
      ∏ j ∈ bilateralShiftEdges N, (1 + (‖w j‖ ^ 2 : ℝ) : ℂ) := by
  rw [fredholmDetOp_eq_det_block_of_support (lpBasis ℤ)
    (finiteBilateralWeightedShift_gram_traceClass N w) (bilateralShiftEdges N)
    (finiteBilateralWeightedShift_gram_coordinate_support N w)]
  have heq : 1 + blockMatrix
      (RHTower.coordMatrix (lpBasis ℤ)
        ((finiteBilateralWeightedShift N w).adjoint ∘L finiteBilateralWeightedShift N w))
      (bilateralShiftEdges N) =
      Matrix.diagonal (fun j : bilateralShiftEdges N => (1 + (‖w j‖ ^ 2 : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst i
      simp [blockMatrix, coordMatrix_finiteBilateralWeightedShift_gram, j.property]
    · have hv : (i : ℤ) ≠ (j : ℤ) := fun he => h (Subtype.ext he)
      simp [Matrix.add_apply, blockMatrix,
        coordMatrix_finiteBilateralWeightedShift_gram, h, hv]
  rw [heq, Matrix.det_diagonal]
  exact Finset.prod_coe_sort (bilateralShiftEdges N) (fun j => (1 + (‖w j‖ ^ 2 : ℝ) : ℂ))

end
end GaloisForLFunctions.HTGeometry
