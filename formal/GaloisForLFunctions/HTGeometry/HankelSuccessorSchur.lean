import GaloisForLFunctions.HTGeometry.HankelTerminalFlux

/-! # Exact scalar admission for the successor of a strict finite Hankel head -/
open Matrix
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The exact successor Schur coordinate, using the inverse of the actual finite head. -/
def finiteHankelSuccessorSchur (m : ℕ → ℝ) (n : ℕ) : ℝ :=
  m (2*n) - ∑ i : Fin n, ∑ j : Fin n,
    m (i.val+n)*(finiteHankelMatrix m n)⁻¹ i j*m (j.val+n)

/-- Once its actual head is strict, successor positivity is exactly one explicit source scalar. -/
theorem finiteHankelMatrix_succ_posSemidef_iff_schur_nonneg
    {m : ℕ → ℝ} {n : ℕ} (hhead : (finiteHankelMatrix m n).PosDef) :
    (finiteHankelMatrix m (n+1)).PosSemidef ↔ 0 ≤ finiteHankelSuccessorSchur m n := by
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
  have hscalar : S.PosSemidef ↔ 0 ≤ finiteHankelSuccessorSchur m n := by
    constructor
    · intro hs
      have hd := hs.det_nonneg
      rw [Matrix.det_fin_one, hSval] at hd
      exact hd
    · intro hs
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      constructor
      · apply Matrix.IsHermitian.ext
        intro i j
        fin_cases i
        fin_cases j
        simp
      · intro v
        simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_one, hSval]
        nlinarith [sq_nonneg (v 0)]
  have hMiff : M.PosSemidef ↔ (finiteHankelMatrix m (n+1)).PosSemidef :=
    by simpa [M, Matrix.reindex_apply, Matrix.submatrix] using
      (Matrix.posSemidef_submatrix_equiv (M := finiteHankelMatrix m (n+1)) e)
  rw [← hMiff, ← hblock]
  exact (Matrix.PosDef.fromBlocks₁₁ B D hA).trans hscalar

end
end GaloisForLFunctions.HTGeometry
