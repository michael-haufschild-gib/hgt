import GaloisForLFunctions.HTGeometry.FinitePowerDifferenceMatrix
import GaloisForLFunctions.HTGeometry.PowerCovarianceKernel
import GaloisForLFunctions.RHTower.WeilLogShiftTiltVarianceKernel

/-! The exact finite power-covariance kernel depends on support nodes, not tilt weights. -/

open MeasureTheory ProbabilityTheory GaloisForLFunctions.HTGeometry
open scoped BigOperators
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_mulVec_eq_zero_iff_values
    (r k : ℕ) (a b d : ℝ) (n : ℕ) (c : Fin n → ℝ) :
    (powerCovarianceMatrix (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (fun z => z 0) n).mulVec c = 0 ↔
      ∀ i, (∑ j : Fin n, c j * (finiteWeilCanonicalFluctuationPoint r k i 0) ^
        ((j : ℕ) + 1)) = ∑ j : Fin n, c j *
          (finiteWeilCanonicalFluctuationPoint r k 0 0) ^ ((j : ℕ) + 1) := by
  constructor
  · intro hnull
    apply (finiteWeilCanonicalJointQuadraticTilt_variance_eq_zero_iff_values
      r k a b d (fun z : E => ∑ j : Fin n, c j * z 0 ^ ((j : ℕ) + 1))).mp
    rw [← powerCovarianceMatrix_quadraticForm
      (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) (fun z : E => z 0) n c
      (fun _ => finiteWeilCanonicalJointQuadraticTilt_memLp_two r k a b d _), hnull]
    simp
  · intro hvalues
    apply powerCovarianceMatrix_mulVec_eq_zero_of_ae_const
      (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) (fun z : E => z 0) n c
      (fun _ => finiteWeilCanonicalJointQuadraticTilt_memLp_two r k a b d _)
      (∑ j : Fin n, c j * (finiteWeilCanonicalFluctuationPoint r k 0 0) ^ ((j : ℕ) + 1))
    exact (finiteWeilCanonicalJointQuadraticTilt_ae_iff r k a b d _).mpr hvalues

theorem finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_ker_eq_difference
    (r k : ℕ) (a b d : ℝ) (n : ℕ) :
    LinearMap.ker (powerCovarianceMatrix
      (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) (fun z => z 0) n).mulVecLin =
      LinearMap.ker (finitePowerDifferenceMatrix r n
        (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)).mulVecLin := by
  ext c
  change (powerCovarianceMatrix
    (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) (fun z => z 0) n).mulVec c = 0 ↔
      (finitePowerDifferenceMatrix r n
        (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)).mulVec c = 0
  exact (finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_mulVec_eq_zero_iff_values
    r k a b d n c).trans (finitePowerDifferenceMatrix_mulVec_eq_zero_iff r n
      (fun i => finiteWeilCanonicalFluctuationPoint r k i 0) c).symm

theorem finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_ker_eq
    (r k : ℕ) (a b d A B D : ℝ) (n : ℕ) :
    LinearMap.ker (powerCovarianceMatrix
      (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) (fun z => z 0) n).mulVecLin =
      LinearMap.ker (powerCovarianceMatrix
        (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) (fun z => z 0) n).mulVecLin := by
  rw [finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_ker_eq_difference,
    finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_ker_eq_difference]

end RHTower
