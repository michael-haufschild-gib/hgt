import GaloisForLFunctions.HTGeometry.FinitePowerSumNodes
import GaloisForLFunctions.HTGeometry.PowerCovarianceKernel
import GaloisForLFunctions.RHTower.WeilLogShiftTiltVarianceKernel
import GaloisForLFunctions.RHTower.WeilLogShiftJointTransportGeometry

/-! Finite support gives positive power covariance up to its exact degree capacity and singularity above it. -/

open MeasureTheory ProbabilityTheory GaloisForLFunctions.HTGeometry
open scoped BigOperators
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem finiteWeilCanonicalJointQuadraticTilt_power_sum_variance_zero_iff
    (r k : ℕ) (a b d : ℝ) (n : ℕ) (hn : n ≤ r) (c : Fin n → ℝ) :
    variance (fun z : E => ∑ j : Fin n, c j * z 0 ^ ((j : ℕ) + 1))
      (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) = 0 ↔ c = 0 := by
  rw [finiteWeilCanonicalJointQuadraticTilt_variance_eq_zero_iff_values]
  exact finite_power_sum_succ_constant_iff r n
    (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
    (finiteWeilCanonicalFluctuationPoint_fst_injective r k) hn c

theorem finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_posDef_of_le
    (r k : ℕ) (a b d : ℝ) (n : ℕ) (hn : n ≤ r) :
    (powerCovarianceMatrix (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (fun z => z 0) n).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (powerCovarianceMatrix_isHermitian _ _ _)
  intro c hc
  rw [powerCovarianceMatrix_quadraticForm
    (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) (fun z : E => z 0) n c
    (fun _ => finiteWeilCanonicalJointQuadraticTilt_memLp_two r k a b d _)]
  have hne : variance (fun z : E => ∑ j : Fin n, c j * z 0 ^ ((j : ℕ) + 1))
      (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) ≠ 0 := by
    intro h
    exact hc ((finiteWeilCanonicalJointQuadraticTilt_power_sum_variance_zero_iff
      r k a b d n hn c).mp h)
  exact lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hne)

theorem finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_zero_of_lt
    (r k : ℕ) (a b d : ℝ) (n : ℕ) (hn : r < n) :
    (powerCovarianceMatrix (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (fun z => z 0) n).det = 0 := by
  let x : Fin (r + 1) → ℝ := fun i => finiteWeilCanonicalFluctuationPoint r k i 0
  obtain ⟨c, hc, hvalues⟩ := exists_ne_zero_finite_power_sum_constant r n x hn
  apply powerCovarianceMatrix_det_eq_zero_of_ae_const
    (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) (fun z : E => z 0) n c
    (fun _ => finiteWeilCanonicalJointQuadraticTilt_memLp_two r k a b d _)
    (∑ j : Fin n, c j * x 0 ^ ((j : ℕ) + 1)) hc
  exact (finiteWeilCanonicalJointQuadraticTilt_ae_iff r k a b d _).mpr hvalues

end RHTower
