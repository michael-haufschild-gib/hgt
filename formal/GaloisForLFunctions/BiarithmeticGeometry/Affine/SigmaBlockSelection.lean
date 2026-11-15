import GaloisForLFunctions.BiarithmeticGeometry.Affine.SigmaBlockDeterminant
import GaloisForLFunctions.HTGeometry.BlockDiagonalDeterminant

/-!
# Selecting coordinates within dependent diagonal blocks

Selecting original or transformed rows within each block commutes with
forming a block-diagonal matrix. Thus selected determinants multiply even
when the blocks have different sizes and their labels have no chosen order.
-/

open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

namespace GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix
noncomputable section
variable {ι : Type*} {κ : ι → Type*} [DecidableEq ι] [∀ i, DecidableEq (κ i)]

/-- Blockwise row selection commutes with a dependent block-diagonal sum. -/
theorem selectedMatrix_blockDiagonal (B : ∀ i, Matrix (κ i) (κ i) ℝ)
    (s : ∀ i, κ i → κ i ⊕ κ i) :
    selectedMatrix (Matrix.blockDiagonal' B) (blockSelector s) =
      Matrix.blockDiagonal' (fun i => selectedMatrix (B i) (s i)) := by
  ext ⟨i, x⟩ ⟨j, y⟩
  cases hs : s i x with
  | inl z =>
    by_cases hij : i = j
    · subst j
      simp [selectedMatrix, blockSelector, hs, Matrix.blockDiagonal'_apply_eq, Matrix.one_apply]
    · have hne : (Sigma.mk i z : Sigma κ) ≠ Sigma.mk j y := by
        intro h
        exact hij (congrArg (fun a : Sigma κ => a.1) h)
      simp [selectedMatrix, blockSelector, hs, Matrix.blockDiagonal'_apply, hij, Matrix.one_apply, hne]
  | inr z =>
    by_cases hij : i = j
    · subst j
      simp only [selectedMatrix, blockSelector, hs, Sum.elim_inr, Matrix.blockDiagonal'_apply_eq]
    · simp only [selectedMatrix, blockSelector, hs, Sum.elim_inr,
        Matrix.blockDiagonal'_apply, dif_neg hij]

/-- The selected determinant is the product of the selected block determinants. -/
theorem det_selectedMatrix_blockDiagonal [Fintype ι] [∀ i, Fintype (κ i)]
    (B : ∀ i, Matrix (κ i) (κ i) ℝ) (s : ∀ i, κ i → κ i ⊕ κ i) :
    (selectedMatrix (Matrix.blockDiagonal' B) (blockSelector s)).det =
      ∏ i, (selectedMatrix (B i) (s i)).det := by
  rw [selectedMatrix_blockDiagonal, GaloisForLFunctions.HTGeometry.det_blockDiagonal']

#print axioms selectedMatrix_blockDiagonal
#print axioms det_selectedMatrix_blockDiagonal

end
end GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix
