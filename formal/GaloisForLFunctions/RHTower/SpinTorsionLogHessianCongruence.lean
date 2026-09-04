import GaloisForLFunctions.HTGeometry.TwoModulusLogHessian
import GaloisForLFunctions.RHTower.LoewnerCongruenceNormalization

/-!
# Coordinate congruence for the spin-torsion log Hessian

The paper relates ordinary-radius and logarithmic-radius Hessians by a diagonal Jacobian
congruence at a stationary point.  Exponential diagonal entries make that Jacobian invertible
without side conditions.  Existing Loewner congruence machinery then proves that positive
semidefiniteness and positive definiteness are coordinate invariant.
-/

open Matrix
open scoped Matrix ComplexOrder

noncomputable section

namespace RHTower

/-- Complexification of the explicit real two-modulus logarithmic Hessian. -/
def complexTwoModulusLogHessian (A B C q m n family x y : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (GaloisForLFunctions.HTGeometry.twoModulusLogHessian
    A B C q m n family x y i j : ℂ)

/-- The complexified two-modulus log Hessian is Hermitian. -/
theorem complexTwoModulusLogHessian_isHermitian (A B C q m n family x y : ℝ) :
    (complexTwoModulusLogHessian A B C q m n family x y).IsHermitian := by
  unfold Matrix.IsHermitian complexTwoModulusLogHessian
  rw [GaloisForLFunctions.HTGeometry.twoModulusLogHessian_eq_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Positive diagonal Jacobian from logarithmic to ordinary radii. -/
def spinTorsionLogRadionJacobian (x y : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.exp x : ℂ), 0; 0, (Real.exp y : ℂ)]

/-- Exact determinant of the log-radion Jacobian. -/
theorem spinTorsionLogRadionJacobian_det (x y : ℝ) :
    (spinTorsionLogRadionJacobian x y).det = (Real.exp x * Real.exp y : ℝ) := by
  rw [spinTorsionLogRadionJacobian, Matrix.det_fin_two]
  norm_num

/-- Exponential radion coordinates give an invertible Jacobian for every real point. -/
theorem spinTorsionLogRadionJacobian_det_isUnit (x y : ℝ) :
    IsUnit (spinTorsionLogRadionJacobian x y).det := by
  rw [spinTorsionLogRadionJacobian_det]
  apply isUnit_iff_ne_zero.mpr
  exact_mod_cast mul_ne_zero (Real.exp_ne_zero x) (Real.exp_ne_zero y)

/-- Positive semidefiniteness of the exact spin-torsion Hessian survives radion congruence. -/
theorem spinTorsionLogHessian_congruence_posSemidef_iff
    (A B C q m n family x y : ℝ) :
    let H := complexTwoModulusLogHessian A B C q m n family x y
    let J := spinTorsionLogRadionJacobian x y
    (J * H * Jᴴ).PosSemidef ↔ H.PosSemidef := by
  dsimp only
  exact posSemidef_congruence_iff
    (complexTwoModulusLogHessian_isHermitian A B C q m n family x y)
    (spinTorsionLogRadionJacobian_det_isUnit x y)

/-- Positive definiteness of the exact spin-torsion Hessian survives radion congruence. -/
theorem spinTorsionLogHessian_congruence_posDef_iff
    (A B C q m n family x y : ℝ) :
    let H := complexTwoModulusLogHessian A B C q m n family x y
    let J := spinTorsionLogRadionJacobian x y
    (J * H * Jᴴ).PosDef ↔ H.PosDef := by
  dsimp only
  exact posDef_congruence_iff
    (complexTwoModulusLogHessian_isHermitian A B C q m n family x y)
    (spinTorsionLogRadionJacobian_det_isUnit x y)

end RHTower
