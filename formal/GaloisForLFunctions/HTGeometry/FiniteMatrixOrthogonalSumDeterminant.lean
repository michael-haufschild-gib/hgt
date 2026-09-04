import GaloisForLFunctions.HTGeometry.BlockDiagonalDeterminant
import GaloisForLFunctions.HTGeometry.FiniteMatrixOrthogonalSum

/-!
# Determinants of finite real orthogonal block sums

The quadratic-form block constructors used by the number-field archimedean cone are connected to
the dependent block-diagonal determinant theorem.  This supplies determinant products for both the
indexed block family and the binary orthogonal sum.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped Classical Matrix

noncomputable section

variable {ι n m : Type*}
  [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

/-- Constant-fibre sigma indices are equivalent to product indices. -/
def sigmaConstProdEquiv : (Σ _ : ι, n) ≃ ι × n where
  toFun x := (x.1, x.2)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype ι] [Fintype n] [DecidableEq n] in
/-- The product-indexed block family is the reindexing of the dependent block diagonal. -/
theorem matrixFamilyBlockDiagonal_eq_reindex_blockDiagonal'
    (A : ι → Matrix n n ℝ) :
    matrixFamilyBlockDiagonal A =
      Matrix.reindex sigmaConstProdEquiv sigmaConstProdEquiv
        (Matrix.blockDiagonal' A) := by
  ext p q
  by_cases h : p.1 = q.1
  · simp [matrixFamilyBlockDiagonal, sigmaConstProdEquiv,
      Matrix.reindex_apply, Matrix.blockDiagonal'_apply_eq, h]
  · simp [matrixFamilyBlockDiagonal, sigmaConstProdEquiv,
      Matrix.reindex_apply, Matrix.blockDiagonal'_apply_ne, h]

/-- Determinant of a constant-size indexed block-diagonal family. -/
theorem det_matrixFamilyBlockDiagonal (A : ι → Matrix n n ℝ) :
    (matrixFamilyBlockDiagonal A).det = ∏ i, (A i).det := by
  rw [matrixFamilyBlockDiagonal_eq_reindex_blockDiagonal']
  rw [show (Matrix.reindex sigmaConstProdEquiv sigmaConstProdEquiv
      (Matrix.blockDiagonal' A)).det = (Matrix.blockDiagonal' A).det by
    exact Matrix.det_submatrix_equiv_self sigmaConstProdEquiv.symm
      (Matrix.blockDiagonal' A)]
  exact det_blockDiagonal' A

/-- Determinant is multiplicative across the binary real orthogonal sum. -/
theorem det_matrixOrthogonalSum (A : Matrix n n ℝ) (B : Matrix m m ℝ) :
    (matrixOrthogonalSum A B).det = A.det * B.det := by
  exact Matrix.det_fromBlocks_zero₁₂ A (0 : Matrix m n ℝ) B

end

end GaloisForLFunctions.HTGeometry
