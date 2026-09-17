import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Valuation.Basic

/-!
# Variable-size block-diagonal determinants

Mathlib's determinant theorem for `Matrix.blockDiagonal` uses one common block size. The k-server
minor argument needs blocks of different sizes. This module supplies the dependent-sum version and
its exact valuation factorization.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

variable {o : Type*} (m : o → Type*) (k : o)

/-- The fiber of a dependent sum over `k` is equivalent to the `k`-th summand. -/
def sigmaFiberEquiv : {x : Σ i, m i // x.1 = k} ≃ m k where
  toFun x := cast (congrArg m x.property) x.1.2
  invFun x := ⟨⟨k, x⟩, rfl⟩
  left_inv x := by
    rcases x with ⟨⟨i, x⟩, hi⟩
    cases hi
    rfl
  right_inv _ := rfl

variable {R : Type*} [CommRing R]

/-- Determinant of a dependently typed block-diagonal matrix. -/
theorem det_blockDiagonal'
    [Fintype o] [DecidableEq o]
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (M : ∀ i, Matrix (m i) (m i) R) :
    (Matrix.blockDiagonal' M).det = ∏ i, (M i).det := by
  classical
  letI : LinearOrder o := linearOrderOfSTO WellOrderingRel
  let B := Matrix.blockDiagonal' M
  have htri : B.BlockTriangular Sigma.fst := by
    intro i j hji
    apply Matrix.blockDiagonal'_apply_ne
    exact ne_of_gt hji
  rw [htri.det_fintype]
  apply Finset.prod_congr rfl
  intro i _
  let e := sigmaFiberEquiv m i
  have hblock : (Matrix.reindex e e) (B.toSquareBlock Sigma.fst i) = M i := by
    ext x y
    simp [e, sigmaFiberEquiv, B, Matrix.toSquareBlock_def, Matrix.reindex_apply]
  calc
    (B.toSquareBlock Sigma.fst i).det =
        ((Matrix.reindex e e) (B.toSquareBlock Sigma.fst i)).det := by
      symm
      exact Matrix.det_reindex_self e _
    _ = (M i).det := by rw [hblock]

/-- A valuation maps a variable-size block-diagonal determinant to the product of block
determinant values. -/
theorem valuation_det_blockDiagonal'
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    [Fintype o] [DecidableEq o]
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (val : Valuation K Γ) (M : ∀ i, Matrix (m i) (m i) K) :
    val (Matrix.blockDiagonal' M).det = ∏ i, val (M i).det := by
  rw [det_blockDiagonal' m M, map_prod]

end

end GaloisForLFunctions.HTGeometry
