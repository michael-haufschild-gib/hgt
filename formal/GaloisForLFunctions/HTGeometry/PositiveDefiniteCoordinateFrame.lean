import GaloisForLFunctions.HTGeometry.JacobiPositiveFrame
import GaloisForLFunctions.HTGeometry.SiegelGramDomination

/-!
# Coordinate frames of positive-definite matrices

The Jacobi square-root frame is kept in the coordinate function space.  Its coordinate-square sum
is the original quadratic form, and the square of its determinant is the determinant of that form.
This is the determinant identity required by Hermite--Minkowski bounds.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Module
open scoped Classical

noncomputable section

/-- Jacobi's positive square-root frame as an automorphism of the coordinate function space. -/
def JacobiData.frameCoordinateContinuousLinearEquiv {n : ℕ} (J : JacobiData n) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  let hInv : Invertible J.frameMatrix :=
    Matrix.invertibleOfIsUnitDet J.frameMatrix J.frameMatrix_isUnit_det
  (J.frameMatrix.toLinearEquiv' hInv).toContinuousLinearEquiv

@[simp]
theorem JacobiData.frameCoordinateContinuousLinearEquiv_apply {n : ℕ}
    (J : JacobiData n) (v : Fin n → ℝ) :
    J.frameCoordinateContinuousLinearEquiv v = J.frameMatrix.mulVec v := by
  rfl

/-- The coordinate-square sum of the Jacobi frame is exactly its quadratic form. -/
theorem JacobiData.sum_sq_frameCoordinateContinuousLinearEquiv {n : ℕ}
    (J : JacobiData n) (v : Fin n → ℝ) :
    ∑ i, (J.frameCoordinateContinuousLinearEquiv v i) ^ 2 =
      v ⬝ᵥ J.form.mulVec v := by
  rw [J.frameCoordinateContinuousLinearEquiv_apply, J.quadForm_eq]
  apply Finset.sum_congr rfl
  intro i hi
  change (((Matrix.diagonal fun i ↦ Real.sqrt (J.d i)) * J.U) *ᵥ v) i ^ 2 =
    J.d i * (J.U *ᵥ v) i ^ 2
  rw [← Matrix.mulVec_mulVec v (Matrix.diagonal fun i ↦ Real.sqrt (J.d i)) J.U]
  rw [Matrix.mulVec_diagonal, mul_pow, Real.sq_sqrt (J.pos i).le]

/-- A real coordinate-square sum is bounded by dimension times the squared supremum norm. -/
theorem sum_sq_le_card_mul_pi_norm_sq {n : ℕ} (v : Fin n → ℝ) :
    ∑ i, (v i) ^ 2 ≤ (n : ℝ) * ‖v‖ ^ 2 := by
  have hcoord (i : Fin n) : (v i) ^ 2 ≤ ‖v‖ ^ 2 := by
    have hi : ‖v i‖ ≤ ‖v‖ := by
      rw [Pi.norm_def]
      exact NNReal.coe_le_coe.mpr
        (Finset.le_sup (f := fun j ↦ ‖v j‖₊) (Finset.mem_univ i))
    rw [Real.norm_eq_abs] at hi
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg (v i)) (norm_nonneg v)).2 hi
  calc
    ∑ i, (v i) ^ 2 ≤ ∑ i, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ ↦ hcoord i
    _ = (n : ℝ) * ‖v‖ ^ 2 := by simp [nsmul_eq_mul]

/-- Squaring the Jacobi-frame determinant gives the determinant of its positive form. -/
theorem JacobiData.frameMatrix_det_sq {n : ℕ} (J : JacobiData n) :
    J.frameMatrix.det ^ 2 = J.form.det := by
  rw [JacobiData.frameMatrix, Matrix.det_mul, Matrix.det_diagonal,
    J.det_eq_one, mul_one, J.det_form, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  exact Real.sq_sqrt (J.pos i).le

/-- The abstract determinant of the coordinate-frame automorphism is its matrix determinant. -/
theorem JacobiData.det_frameCoordinateContinuousLinearEquiv {n : ℕ}
    (J : JacobiData n) :
    LinearMap.det
      (J.frameCoordinateContinuousLinearEquiv :
        (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = J.frameMatrix.det := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin n))]
  congr 1
  ext i j
  simp [JacobiData.frameCoordinateContinuousLinearEquiv, Matrix.toLinearEquiv'_apply]

/-- Squaring any real power of the absolute frame determinant gives the same real power of the
positive-form determinant. -/
theorem JacobiData.rpow_abs_frameMatrix_det_sq {n : ℕ}
    (J : JacobiData n) (a : ℝ) :
    (Real.rpow |J.frameMatrix.det| a) ^ 2 = Real.rpow J.form.det a := by
  calc
    (Real.rpow |J.frameMatrix.det| a) ^ 2 =
        Real.rpow (Real.rpow |J.frameMatrix.det| a) (2 : ℝ) :=
      (Real.rpow_natCast _ 2).symm
    _ = Real.rpow |J.frameMatrix.det| (a * 2) :=
      (Real.rpow_mul (abs_nonneg J.frameMatrix.det) a 2).symm
    _ = Real.rpow |J.frameMatrix.det| (2 * a) := by rw [mul_comm a 2]
    _ = Real.rpow (Real.rpow |J.frameMatrix.det| 2) a :=
      Real.rpow_mul (abs_nonneg J.frameMatrix.det) 2 a
    _ = Real.rpow J.form.det a := by
      rw [show Real.rpow |J.frameMatrix.det| (2 : ℝ) =
        |J.frameMatrix.det| ^ 2 from Real.rpow_two _]
      rw [sq_abs, J.frameMatrix_det_sq]

end

end GaloisForLFunctions.HTGeometry
