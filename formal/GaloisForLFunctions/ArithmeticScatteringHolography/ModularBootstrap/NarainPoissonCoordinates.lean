import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMass
import GaloisForLFunctions.HTGeometry.GaussianThetaCharacteristics

/-!
# Momentum and dual-lattice coordinates for the Narain theta sum

The target quadratic form is the norm square of an explicit triangular
lattice map. Its determinant, inverse adjoint and integer pairing identify
the Gaussian characteristics of momentum Poisson summation.
-/

open Complex RHTower
open GaloisForLFunctions.HTGeometry.IntegerLatticePoisson
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The triangular lattice map realizing the target quadratic form. -/
def targetLatticeEquiv (σ : D4BMUpperHalfPlaneCoordinate) : E ≃L[ℝ] E where
  toLinearEquiv :=
    { toFun := fun v => WithLp.toLp 2 ![σ.y * v 0, v 1 - σ.x * v 0]
      invFun := fun v => WithLp.toLp 2 ![v 0 / σ.y, v 1 + σ.x * v 0 / σ.y]
      map_add' := by
        intro v w
        ext i
        fin_cases i <;> simp <;> ring
      map_smul' := by
        intro c v
        ext i
        fin_cases i <;> simp <;> ring
      left_inv := by
        intro v
        ext i
        fin_cases i
        · simp [σ.y_pos.ne']
        · simp
          field_simp [σ.y_pos.ne']
          ring
      right_inv := by
        intro v
        ext i
        fin_cases i
        · simp
          field_simp [σ.y_pos.ne']
        · simp
          field_simp [σ.y_pos.ne']
          ring }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem targetLatticeEquiv_apply (σ : D4BMUpperHalfPlaneCoordinate) (v : E) :
    targetLatticeEquiv σ v = WithLp.toLp 2 ![σ.y * v 0, v 1 - σ.x * v 0] := rfl

theorem targetLatticeEquiv_symm_apply (σ : D4BMUpperHalfPlaneCoordinate) (v : E) :
    (targetLatticeEquiv σ).symm v =
      WithLp.toLp 2 ![v 0 / σ.y, v 1 + σ.x * v 0 / σ.y] := rfl

theorem det_targetLatticeEquiv (σ : D4BMUpperHalfPlaneCoordinate) :
    LinearMap.det (targetLatticeEquiv σ : E →ₗ[ℝ] E) = σ.y := by
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 2)), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, targetLatticeEquiv, PiLp.basisFun_apply]

theorem latticeScale_targetLatticeEquiv (σ : D4BMUpperHalfPlaneCoordinate) :
    latticeScale (targetLatticeEquiv σ) = σ.y⁻¹ := by
  rw [latticeScale, det_targetLatticeEquiv, abs_of_pos σ.y_pos]

/-- The dual triangular map is the transpose of the explicit inverse. -/
theorem inverseAdjoint_targetLatticeEquiv (σ : D4BMUpperHalfPlaneCoordinate) (v : E) :
    inverseAdjoint (targetLatticeEquiv σ) v =
      WithLp.toLp 2 ![(v 0 + σ.x * v 1) / σ.y, v 1] := by
  apply ext_inner_left ℝ
  intro w
  rw [inverseAdjoint, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ ((targetLatticeEquiv σ).symm w) v = _
  rw [targetLatticeEquiv_symm_apply]
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem norm_targetLatticeEquiv_sq (σ : D4BMUpperHalfPlaneCoordinate) (v : E) :
    ‖targetLatticeEquiv σ v‖ ^ 2 = targetQuadratic σ (v 0, v 1) := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [targetLatticeEquiv_apply, Fin.sum_univ_two, targetQuadratic]

theorem norm_inverseAdjoint_targetLatticeEquiv_sq
    (σ : D4BMUpperHalfPlaneCoordinate) (v : E) :
    ‖inverseAdjoint (targetLatticeEquiv σ) v‖ ^ 2 =
      ((v 0 + σ.x * v 1) ^ 2 + σ.y ^ 2 * v 1 ^ 2) / σ.y ^ 2 := by
  rw [inverseAdjoint_targetLatticeEquiv, ← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [Fin.sum_univ_two]
  field_simp [σ.y_pos.ne']

/-- The Euclidean vector of an integer momentum or winding pair. -/
def integerPairVector (p : ℤ × ℤ) : E := WithLp.toLp 2 ![(p.1 : ℝ), (p.2 : ℝ)]

theorem integerPairVector_eq (p : ℤ × ℤ) :
    integerPairVector p = euclideanIntegerPoint ((finTwoArrowEquiv ℤ).symm p) := by
  ext i
  fin_cases i <;> simp [integerPairVector, euclideanIntegerPoint, integerPoint, finTwoArrowEquiv]

/-- Integer pairs and the standard rank-two lattice give the same theta sum. -/
theorem tsum_integerPairVector (f : E → ℂ) :
    (∑' p : ℤ × ℤ, f (integerPairVector p)) =
      ∑' k : Fin 2 → ℤ, f (euclideanIntegerPoint k) := by
  simpa only [← integerPairVector_eq] using
    (finTwoArrowEquiv ℤ).symm.tsum_eq (fun k => f (euclideanIntegerPoint k))

theorem inner_integerPairVector (p q : ℤ × ℤ) :
    inner ℝ (integerPairVector p) (integerPairVector q) =
      (p.1 : ℝ) * q.1 + (p.2 : ℝ) * q.2 := by
  simp [integerPairVector, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- The affine shift contributes the determinant phase in the dual sum. -/
theorem inner_target_shift_dual (σ : D4BMUpperHalfPlaneCoordinate)
    (B : ℝ) (m w : ℤ × ℤ) :
    inner ℝ (targetLatticeEquiv σ (B • integerPairVector (w.2, -w.1)))
      (inverseAdjoint (targetLatticeEquiv σ) (integerPairVector m)) =
      B * ((m.1 : ℝ) * w.2 - (m.2 : ℝ) * w.1) := by
  rw [inverseAdjoint, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ ((targetLatticeEquiv σ).symm
    (targetLatticeEquiv σ (B • integerPairVector (w.2, -w.1)))) (integerPairVector m) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, real_inner_smul_left, inner_integerPairVector]
  push_cast
  ring

/-- The affine shift has zero phase against the winding modulation. -/
theorem inner_target_shift_winding (σ : D4BMUpperHalfPlaneCoordinate)
    (B : ℝ) (w : ℤ × ℤ) :
    inner ℝ (targetLatticeEquiv σ (B • integerPairVector (w.2, -w.1)))
      (inverseAdjoint (targetLatticeEquiv σ) (integerPairVector w)) = 0 := by
  rw [inner_target_shift_dual]
  ring

#print axioms det_targetLatticeEquiv
#print axioms inverseAdjoint_targetLatticeEquiv
#print axioms norm_inverseAdjoint_targetLatticeEquiv_sq
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
