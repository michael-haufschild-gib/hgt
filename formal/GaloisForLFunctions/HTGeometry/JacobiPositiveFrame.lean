import Mathlib.Analysis.InnerProductSpace.PiL2
import GaloisForLFunctions.HTGeometry.SiegelQuasiDiagonal

/-!
# Euclidean frames of positive-definite matrices

Jacobi decomposition writes a positive-definite real matrix as `Uᵀ diag(d) U`, with positive `d`.
The frame `diag(√d) U` is invertible, and its Euclidean norm-square is exactly the original quadratic
form.  This file packages that frame as a continuous linear equivalence.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

/-- Cholesky frame associated to Jacobi data. -/
def JacobiData.frameMatrix {n : ℕ} (J : JacobiData n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i ↦ Real.sqrt (J.d i)) * J.U

theorem JacobiData.frameMatrix_det_ne_zero {n : ℕ} (J : JacobiData n) :
    J.frameMatrix.det ≠ 0 := by
  rw [frameMatrix, Matrix.det_mul, Matrix.det_diagonal, J.det_eq_one, mul_one]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact (Real.sqrt_pos.2 (J.pos i)).ne'

theorem JacobiData.frameMatrix_isUnit_det {n : ℕ} (J : JacobiData n) :
    IsUnit J.frameMatrix.det :=
  isUnit_iff_ne_zero.mpr J.frameMatrix_det_ne_zero

/-- The Jacobi frame as a continuous real-linear equivalence into Euclidean coordinates. -/
noncomputable def JacobiData.frameContinuousLinearEquiv {n : ℕ} (J : JacobiData n) :
    (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  let hInv : Invertible J.frameMatrix :=
    Matrix.invertibleOfIsUnitDet J.frameMatrix J.frameMatrix_isUnit_det
  (J.frameMatrix.toLinearEquiv' hInv).toContinuousLinearEquiv.trans
    (EuclideanSpace.equiv (Fin n) ℝ).symm

theorem JacobiData.frameContinuousLinearEquiv_apply {n : ℕ} (J : JacobiData n)
    (v : Fin n → ℝ) :
    J.frameContinuousLinearEquiv v =
      (EuclideanSpace.equiv (Fin n) ℝ).symm (J.frameMatrix.mulVec v) := by
  rfl

/-- Exact frame identity: Euclidean norm-square equals the Jacobi quadratic form. -/
theorem JacobiData.norm_frameContinuousLinearEquiv_sq {n : ℕ} (J : JacobiData n)
    (v : Fin n → ℝ) :
    ‖J.frameContinuousLinearEquiv v‖ ^ 2 = v ⬝ᵥ J.form.mulVec v := by
  rw [J.frameContinuousLinearEquiv_apply, EuclideanSpace.real_norm_sq_eq,
    J.quadForm_eq]
  apply Finset.sum_congr rfl
  intro i hi
  change (((Matrix.diagonal fun i ↦ Real.sqrt (J.d i)) * J.U) *ᵥ v) i ^ 2 =
    J.d i * (J.U *ᵥ v) i ^ 2
  rw [← Matrix.mulVec_mulVec v (Matrix.diagonal fun i ↦ Real.sqrt (J.d i)) J.U]
  rw [Matrix.mulVec_diagonal, mul_pow, Real.sq_sqrt (J.pos i).le]

/-- Every positive-definite real matrix has an invertible Euclidean frame realizing its quadratic
form exactly. -/
theorem exists_posDefContinuousLinearEquiv
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ∃ e : (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ v, ‖e v‖ ^ 2 = v ⬝ᵥ A.mulVec v := by
  rcases exists_jacobiData hA with ⟨J, hJ⟩
  refine ⟨J.frameContinuousLinearEquiv, ?_⟩
  intro v
  rw [← hJ]
  exact J.norm_frameContinuousLinearEquiv_sq v

end

end GaloisForLFunctions.HTGeometry
