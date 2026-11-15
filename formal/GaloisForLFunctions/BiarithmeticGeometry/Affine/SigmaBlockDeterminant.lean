import GaloisForLFunctions.BiarithmeticGeometry.Affine.MixedMatrixOverlap
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Determinants of lower-triangular families of coordinate blocks

For a matrix indexed by a finite dependent sum, the determinant is the
product of the diagonal-block determinants when higher column blocks vanish.
Selecting original or transformed coordinates within each block preserves
this factorization. Lower-degree terms therefore do not affect the selected
determinant.
-/

open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

namespace GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix
noncomputable section
variable {ι : Type*} {κ : ι → Type*} {R : Type*}

/-- A diagonal block retains precisely the coordinates in a single fiber. -/
def diagonalBlock (M : Matrix (Sigma κ) (Sigma κ) R) (i : ι) : Matrix (κ i) (κ i) R :=
  fun x y => M ⟨i, x⟩ ⟨i, y⟩

private def fiberEquiv (i : ι) : κ i ≃ {x : Sigma κ // x.1 = i} where
  toFun x := ⟨⟨i, x⟩, rfl⟩
  invFun x := x.property ▸ x.val.2
  left_inv x := rfl
  right_inv := by
    rintro ⟨⟨j, x⟩, h⟩
    dsimp at h
    subst j
    rfl

variable [LinearOrder ι] [∀ i, DecidableEq (κ i)]

/-- Lower-triangular block matrices have the product of their diagonal-block determinants. -/
theorem det_of_lower [Fintype ι] [∀ i, Fintype (κ i)] [CommRing R]
    (M : Matrix (Sigma κ) (Sigma κ) R)
    (hM : ∀ a b, a.1 < b.1 → M a b = 0) :
    M.det = ∏ i, (diagonalBlock M i).det := by
  classical
  have ht : Matrix.BlockTriangular (α := OrderDual ι) M (fun a => a.1) := by
    intro a b hab
    exact hM a b hab
  rw [ht.det_fintype]
  apply Finset.prod_congr rfl
  intro i _
  exact (Matrix.det_submatrix_equiv_self (fiberEquiv (κ := κ) i)
    (M.toSquareBlock (fun a : Sigma κ => (a.1 : OrderDual ι)) i)).symm

/-- A blockwise selector embeds its original and transformed row choices into the full space. -/
def blockSelector (s : ∀ i, κ i → κ i ⊕ κ i) (a : Sigma κ) : Sigma κ ⊕ Sigma κ :=
  match s a.1 a.2 with
  | Sum.inl x => Sum.inl ⟨a.1, x⟩
  | Sum.inr x => Sum.inr ⟨a.1, x⟩

/-- Selection within a block agrees with selection from that diagonal block. -/
theorem diagonalBlock_selectedMatrix (M : Matrix (Sigma κ) (Sigma κ) ℝ)
    (s : ∀ i, κ i → κ i ⊕ κ i) (i : ι) :
    diagonalBlock (selectedMatrix M (blockSelector s)) i =
      selectedMatrix (diagonalBlock M i) (s i) := by
  ext x y
  cases hs : s i x with
  | inl z => simp [diagonalBlock, selectedMatrix, blockSelector, hs, Matrix.one_apply]
  | inr z => simp only [diagonalBlock, selectedMatrix, blockSelector, hs, Sum.elim_inr]

/-- Selection of original or transformed rows in the same degree preserves block triangularity. -/
theorem selectedMatrix_lower (M : Matrix (Sigma κ) (Sigma κ) ℝ)
    (hM : ∀ a b, a.1 < b.1 → M a b = 0) (s : ∀ i, κ i → κ i ⊕ κ i) :
    ∀ a b, a.1 < b.1 → selectedMatrix M (blockSelector s) a b = 0 := by
  rintro ⟨i, x⟩ ⟨j, y⟩ hij
  cases hs : s i x with
  | inl z =>
    have hne : (Sigma.mk i z : Sigma κ) ≠ Sigma.mk j y := by
      intro h
      have he : i = j := congrArg (fun a : Sigma κ => a.1) h
      exact (ne_of_lt hij) he
    simp only [selectedMatrix, blockSelector, hs, Sum.elim_inl, Matrix.one_apply, hne, ite_false]
  | inr z =>
    simpa only [selectedMatrix, blockSelector, hs, Sum.elim_inr] using hM ⟨i, z⟩ ⟨j, y⟩ hij

/-- The full selected determinant depends only on the diagonal blocks, not on lower terms. -/
theorem det_selectedMatrix_of_lower [Fintype ι] [∀ i, Fintype (κ i)]
    (M : Matrix (Sigma κ) (Sigma κ) ℝ)
    (hM : ∀ a b, a.1 < b.1 → M a b = 0) (s : ∀ i, κ i → κ i ⊕ κ i) :
    (selectedMatrix M (blockSelector s)).det =
      ∏ i, (selectedMatrix (diagonalBlock M i) (s i)).det := by
  rw [det_of_lower _ (selectedMatrix_lower M hM s)]
  simp only [diagonalBlock_selectedMatrix]

#print axioms det_of_lower
#print axioms diagonalBlock_selectedMatrix
#print axioms selectedMatrix_lower
#print axioms det_selectedMatrix_of_lower

end
end GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix
