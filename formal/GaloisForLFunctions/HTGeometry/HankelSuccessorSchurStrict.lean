import GaloisForLFunctions.HTGeometry.HankelSuccessorSchur

/-! # Strict successor admission from the actual invertible Hankel head -/
open Matrix
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Exact determinant factorization at a strict finite Hankel head. -/
theorem finiteHankelMatrix_succ_det_eq_schur
    {m : ℕ → ℝ} {n : ℕ} (hhead : (finiteHankelMatrix m n).PosDef) :
    (finiteHankelMatrix m (n+1)).det =
      (finiteHankelMatrix m n).det * finiteHankelSuccessorSchur m n := by
  let A := finiteHankelMatrix m n
  let e : Fin n ⊕ Fin 1 ≃ Fin (n+1) := finSumFinEquiv
  let M := Matrix.reindex e.symm e.symm (finiteHankelMatrix m (n+1))
  let B : Matrix (Fin n) (Fin 1) ℝ := fun i _ => m (i.val+n)
  let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => m (2*n)
  have hA : A.PosDef := hhead
  letI : Invertible A := hA.isUnit.invertible
  let S := D-B.conjTranspose*A⁻¹*B
  have h11 : M.toBlocks₁₁ = A := by ext i j; rfl
  have h12 : M.toBlocks₁₂ = B := by ext i j; fin_cases j; rfl
  have h21 : M.toBlocks₂₁ = B.conjTranspose := by
    ext i j
    fin_cases i
    simp [M, B, Matrix.toBlocks₂₁, Matrix.reindex_apply, e,
      finiteHankelMatrix, add_comm]
  have h22 : M.toBlocks₂₂ = D := by
    ext i j
    fin_cases i
    fin_cases j
    change m (n+n) = m (2*n)
    congr 1
    omega
  have hblock : Matrix.fromBlocks A B B.conjTranspose D = M := by
    rw [← h11, ← h21, ← h12, ← h22]
    exact Matrix.fromBlocks_toBlocks _
  have hSval : S 0 0 = finiteHankelSuccessorSchur m n := by
    simp only [S, D, B, Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      star_trivial, finiteHankelSuccessorSchur, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdet : M.det = (finiteHankelMatrix m (n+1)).det := by
    simpa [M, Matrix.reindex_apply, Matrix.submatrix] using
      Matrix.det_submatrix_equiv_self e (finiteHankelMatrix m (n+1))
  rw [← hdet, ← hblock, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  change A.det * S.det = A.det * finiteHankelSuccessorSchur m n
  rw [Matrix.det_fin_one, hSval]

/-- Strict successor positivity is equivalent to strict positivity of its scalar Schur source. -/
theorem finiteHankelMatrix_succ_posDef_iff_schur_pos
    {m : ℕ → ℝ} {n : ℕ} (hhead : (finiteHankelMatrix m n).PosDef) :
    (finiteHankelMatrix m (n+1)).PosDef ↔ 0 < finiteHankelSuccessorSchur m n := by
  have hd := finiteHankelMatrix_succ_det_eq_schur hhead
  constructor
  · intro h
    have hp := h.det_pos
    rw [hd] at hp
    exact (mul_pos_iff_of_pos_left hhead.det_pos).mp hp
  · intro hs
    have hp := (finiteHankelMatrix_succ_posSemidef_iff_schur_nonneg hhead).mpr hs.le
    apply hp.posDef_iff_det_ne_zero.mpr
    rw [hd]
    exact (mul_pos hhead.det_pos hs).ne'

end
end GaloisForLFunctions.HTGeometry
