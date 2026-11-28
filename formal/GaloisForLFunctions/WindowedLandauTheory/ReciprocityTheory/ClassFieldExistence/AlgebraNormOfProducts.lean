import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! The norm on a finite product is the product of the component norms.
Scalar extension takes the norm of a pure algebra tensor to the scalar
extension of the original norm. -/

noncomputable section

open Matrix Module
open scoped TensorProduct

namespace GlobalTheory.Reciprocity

private theorem det_dependent_blockDiagonal {α : Type*} [Fintype α] [DecidableEq α] {m : α → Type*}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {R : Type*} [CommRing R]
    (d : ∀ i, Matrix (m i) (m i) R) : (blockDiagonal' d).det = ∏ k, (d k).det := by
  classical
  let _ : LinearOrder α := LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  rw [(blockTriangular_blockDiagonal' d).det_fintype]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  have : (blockDiagonal' d).toSquareBlock Sigma.fst k =
      (d k).submatrix (Equiv.sigmaSubtype k) (Equiv.sigmaSubtype k) := by
    ext ⟨⟨i, a⟩, hi⟩ ⟨⟨j, b⟩, hj⟩
    dsimp only at hi hj
    subst hi hj
    simp [toSquareBlock_def, Equiv.sigmaSubtype]
  rw [this, det_submatrix_equiv_self]

variable {R : Type*} [Field R] {ι : Type*} [Fintype ι] {S : ι → Type*} [∀ i, CommRing (S i)]
  [∀ i, Algebra R (S i)] [∀ i, Module.Finite R (S i)]

omit [∀ i, Module.Finite R (S i)] in
private theorem leftMulMatrix_pi [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    [∀ i, DecidableEq (κ i)] (b : ∀ i, Basis (κ i) R (S i)) (x : ∀ i, S i) :
    Algebra.leftMulMatrix (Pi.basis b) x =
      blockDiagonal' fun i ↦ Algebra.leftMulMatrix (b i) (x i) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [Algebra.leftMulMatrix_eq_repr_mul, blockDiagonal'_apply', Pi.basis_repr, Pi.basis_apply]
  by_cases h : i = j
  · subst h
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  · simp [h]

theorem algebraNorm_pi (x : ∀ i, S i) : Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  classical
  let b := fun i ↦ Module.finBasis R (S i)
  rw [Algebra.norm_eq_matrix_det (Pi.basis b), leftMulMatrix_pi, det_dependent_blockDiagonal]
  exact Finset.prod_congr rfl fun i _ ↦ (Algebra.norm_eq_matrix_det (b i) (x i)).symm

theorem algebraNorm_one_tmul (K F L : Type*) [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [FiniteDimensional K L] (x : L) :
    Algebra.norm F ((1 : F) ⊗ₜ[K] x) = algebraMap K F (Algebra.norm K x) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange]

end GlobalTheory.Reciprocity
