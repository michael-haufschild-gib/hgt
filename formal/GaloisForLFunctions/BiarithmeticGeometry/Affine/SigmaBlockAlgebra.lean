import GaloisForLFunctions.BiarithmeticGeometry.Affine.SigmaBlockDeterminant

/-!
# Products with dependent block-diagonal matrices

Multiplication by a block-diagonal matrix uses only the coordinates in the
corresponding fiber. Diagonal blocks multiply separately, and multiplying on
the right preserves a lower-triangular degree pattern.
-/

open Matrix
open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix
noncomputable section
variable {ι : Type*} {κ : ι → Type*} {R : Type*}
variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (κ i)] [CommSemiring R]

/-- A block-diagonal matrix acts separately on each coordinate fiber. -/
theorem blockDiagonal_mulVec (B : ∀ i, Matrix (κ i) (κ i) R) (v : Sigma κ → R)
    (i : ι) (x : κ i) :
    (Matrix.blockDiagonal' B *ᵥ v) ⟨i, x⟩ = (B i *ᵥ (fun y => v ⟨i, y⟩)) x := by
  change (∑ b, Matrix.blockDiagonal' B ⟨i, x⟩ b * v b) = _
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp only [Matrix.blockDiagonal'_apply_eq]
    rfl
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro y _
    simp only [Matrix.blockDiagonal'_apply, dif_neg hji.symm, zero_mul]
  · simp

/-- Right multiplication by a block-diagonal matrix uses only the column's block. -/
theorem mul_blockDiagonal_apply (M : Matrix (Sigma κ) (Sigma κ) R)
    (B : ∀ i, Matrix (κ i) (κ i) R) (a : Sigma κ) (i : ι) (y : κ i) :
    (M * Matrix.blockDiagonal' B) a ⟨i, y⟩ = ∑ x, M a ⟨i, x⟩ * B i x y := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro x _
    simp only [Matrix.blockDiagonal'_apply, dif_neg hji, mul_zero]
  · simp

/-- Each diagonal block of the product is the product of the corresponding blocks. -/
theorem diagonalBlock_mul_blockDiagonal (M : Matrix (Sigma κ) (Sigma κ) R)
    (B : ∀ i, Matrix (κ i) (κ i) R) (i : ι) :
    diagonalBlock (M * Matrix.blockDiagonal' B) i = diagonalBlock M i * B i := by
  ext x y
  exact mul_blockDiagonal_apply M B ⟨i, x⟩ i y

/-- A block-diagonal right factor preserves the lower-triangular degree condition. -/
theorem mul_blockDiagonal_lower [LT ι] (M : Matrix (Sigma κ) (Sigma κ) R)
    (hM : ∀ a b, a.1 < b.1 → M a b = 0) (B : ∀ i, Matrix (κ i) (κ i) R) :
    ∀ a b, a.1 < b.1 → (M * Matrix.blockDiagonal' B) a b = 0 := by
  rintro a ⟨i, y⟩ hai
  rw [mul_blockDiagonal_apply]
  apply Finset.sum_eq_zero
  intro x _
  rw [hM a ⟨i, x⟩ hai, zero_mul]

#print axioms blockDiagonal_mulVec
#print axioms mul_blockDiagonal_apply
#print axioms diagonalBlock_mul_blockDiagonal
#print axioms mul_blockDiagonal_lower

end
end GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix
