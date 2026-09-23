import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Trace

/-!
# Symmetric-tensor character formula for Stokes resistance

This module formalizes the matrix mechanism behind Moreau,
*The Stokes resistance of an arbitrary particle: a classification of hydrodynamic symmetries*,
arXiv:2608.23907v1, equation (44).

The factor-swap involution on `V ⊗ V` commutes with `M ⊗ M`. Hence `(I + swap) / 2` is the
symmetric-tensor projector. Its trace after `M ⊗ M` is

`(trace(M)^(2 : ℕ) + trace(M^(2 : ℕ))) / 2`.

Unlike the coordinate formula in `SymmetricSquareMatrix`, this construction works in every finite
dimension. It can therefore count symmetry-compatible quadratic response tensors on all finite
representation spaces in the corpus.
-/

open scoped BigOperators Kronecker

noncomputable section

namespace GaloisForLFunctions.HTGeometry.StokesResistance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Factor-swap involution on the coordinate tensor square. -/
def tensorSwap : Matrix (ι × ι) (ι × ι) ℂ :=
  fun p q => if p = (q.2, q.1) then 1 else 0

/-- Left multiplication by factor swap exchanges the output indices. -/
@[simp] theorem tensorSwap_mul_apply
    (A : Matrix (ι × ι) (ι × ι) ℂ) (p q : ι × ι) :
    (tensorSwap (ι := ι) * A) p q = A (p.2, p.1) q := by
  classical
  simp only [Matrix.mul_apply, tensorSwap, ite_mul, one_mul, zero_mul,
    Prod.ext_iff, Fintype.sum_prod_type]
  simp_rw [ite_and]
  simp only [Fintype.sum_ite_eq]

/-- Factor swap is an involution. -/
@[simp] theorem tensorSwap_mul_self :
    tensorSwap (ι := ι) * tensorSwap (ι := ι) = 1 := by
  ext p q
  simp [tensorSwap, Matrix.one_apply, Prod.ext_iff, and_comm]

omit [Fintype ι] in
/-- Factor swap is symmetric. -/
@[simp] theorem tensorSwap_transpose :
    (tensorSwap (ι := ι)).transpose = tensorSwap (ι := ι) := by
  ext p q
  simp [tensorSwap, Prod.ext_iff, and_comm, eq_comm]

/-- Right multiplication by factor swap exchanges the input indices. -/
@[simp] theorem mul_tensorSwap_apply
    (A : Matrix (ι × ι) (ι × ι) ℂ) (p q : ι × ι) :
    (A * tensorSwap (ι := ι)) p q = A p (q.2, q.1) := by
  calc
    (A * tensorSwap (ι := ι)) p q =
        ((A * tensorSwap (ι := ι)).transpose) q p := rfl
    _ = ((tensorSwap (ι := ι)).transpose * A.transpose) q p := by
      rw [Matrix.transpose_mul]
    _ = (tensorSwap (ι := ι) * A.transpose) q p := by rw [tensorSwap_transpose]
    _ = A p (q.2, q.1) := by rw [tensorSwap_mul_apply]; rfl

/-- Projector from the tensor square onto its symmetric part. -/
def symmetricTensorProjection : Matrix (ι × ι) (ι × ι) ℂ :=
  (1 / 2 : ℂ) • (1 + tensorSwap)

/-- The symmetric-tensor projector is idempotent. -/
@[simp] theorem symmetricTensorProjection_mul_self :
    (symmetricTensorProjection : Matrix (ι × ι) (ι × ι) ℂ) *
        symmetricTensorProjection = symmetricTensorProjection := by
  rw [symmetricTensorProjection, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [mul_add, add_mul, Matrix.one_mul, Matrix.mul_one, tensorSwap_mul_self]
  module

/-- Factor swap commutes with the tensor-square action. -/
theorem tensorSwap_commutes_kronecker_self (M : Matrix ι ι ℂ) :
    tensorSwap (ι := ι) * (M ⊗ₖ M) = (M ⊗ₖ M) * tensorSwap (ι := ι) := by
  ext p q
  simp [Matrix.kroneckerMap_apply, mul_comm]

/-- Factor swap has one trace contribution for each diagonal tensor coordinate. -/
theorem trace_tensorSwap :
    Matrix.trace (tensorSwap (ι := ι)) = (Fintype.card ι : ℂ) := by
  rw [Matrix.trace, ← Finset.univ_product_univ]
  simp only [Matrix.diag, tensorSwap, Prod.ext_iff, Finset.sum_product]
  rw [show (Fintype.card ι : ℂ) = ∑ _ : ι, (1 : ℂ) by simp]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

/-- Dimension formula `dim Sym²(V) = dim(V)(dim(V)+1)/2`, expressed as projector trace. -/
theorem trace_symmetricTensorProjection :
    Matrix.trace (symmetricTensorProjection (ι := ι)) =
      ((Fintype.card ι : ℂ) ^ (2 : ℕ) + Fintype.card ι) / 2 := by
  rw [symmetricTensorProjection, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_one, trace_tensorSwap]
  simp [Fintype.card_prod]
  ring

/-- Swapping tensor factors inside the trace contracts the two factors into `M²`. -/
theorem trace_tensorSwap_mul_kronecker_self (M : Matrix ι ι ℂ) :
    Matrix.trace (tensorSwap * (M ⊗ₖ M)) = Matrix.trace (M * M) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, tensorSwap,
    Matrix.kroneckerMap_apply]
  rw [← Finset.univ_product_univ]
  simp only [Finset.sum_product]
  simp
  simp_rw [ite_and]
  simp only [Fintype.sum_ite_eq]
  simp only [mul_comm]

/-- Moreau equation (44) in arbitrary finite dimension: the symmetric-square character formula. -/
theorem trace_symmetricTensorProjection_mul_kronecker_self
    (M : Matrix ι ι ℂ) :
    Matrix.trace (symmetricTensorProjection * (M ⊗ₖ M)) =
      (Matrix.trace M ^ (2 : ℕ) + Matrix.trace (M * M)) / 2 := by
  rw [symmetricTensorProjection, Matrix.smul_mul, Matrix.add_mul,
    Matrix.one_mul, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_kronecker, trace_tensorSwap_mul_kronecker_self]
  ring

end GaloisForLFunctions.HTGeometry.StokesResistance
