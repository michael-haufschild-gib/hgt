import GaloisForLFunctions.HTGeometry.FinitePowerCovarianceDeterminant
import GaloisForLFunctions.HTGeometry.PowerCovarianceMatrix
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltWeights
import GaloisForLFunctions.RHTower.WeilLogShiftTiltVarianceKernel

/-! # Exact maximal power-covariance determinant of every finite Weil tilt -/

namespace RHTower

open MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The exact determinant separates support geometry from positive tilted atom weights. -/
theorem finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_eq
    (r k : ℕ) (a b d : ℝ) :
    (powerCovarianceMatrix (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (fun z : E => z 0) r).det =
    (Matrix.vandermonde (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)).det ^ 2 *
      ∏ i, finiteWeilCanonicalJointQuadraticTiltWeight r k a b d i := by
  have hmatrix :
      powerCovarianceMatrix (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
        (fun z : E => z 0) r =
      fun i j : Fin r =>
        (∑ l, finiteWeilCanonicalJointQuadraticTiltWeight r k a b d l *
          (finiteWeilCanonicalFluctuationPoint r k l 0) ^ ((i.val + 1) + (j.val + 1))) -
        (∑ l, finiteWeilCanonicalJointQuadraticTiltWeight r k a b d l *
          (finiteWeilCanonicalFluctuationPoint r k l 0) ^ (i.val + 1)) *
        (∑ l, finiteWeilCanonicalJointQuadraticTiltWeight r k a b d l *
          (finiteWeilCanonicalFluctuationPoint r k l 0) ^ (j.val + 1)) := by
    ext i j
    rw [powerCovarianceMatrix, covariance_eq_sub
      (finiteWeilCanonicalJointQuadraticTilt_memLp_two r k a b d _)
      (finiteWeilCanonicalJointQuadraticTilt_memLp_two r k a b d _)]
    simp only [finiteWeilCanonicalJointQuadraticTilt_integral_sum, Pi.mul_apply, ← pow_add]
  rw [hmatrix]
  exact det_finite_power_covariance _ _
    (finiteWeilCanonicalJointQuadraticTiltWeight_sum r k a b d)

end RHTower
