import GaloisForLFunctions.HTGeometry.GaussianPowerVariance
import GaloisForLFunctions.HTGeometry.PowerCovarianceMatrix
import Mathlib.Analysis.Matrix.PosDef

/-! Every finite Gaussian power covariance matrix is positive definite at nonzero variance. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

theorem gaussianZero_powerCovarianceMatrix_posDef (v : NNReal) (hv : v ≠ 0) (n : ℕ) :
    (powerCovarianceMatrix (gaussianReal 0 v) id n).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (powerCovarianceMatrix_isHermitian _ _ _)
  intro c hc
  rw [powerCovarianceMatrix_quadraticForm (gaussianReal 0 v) id n c
    (fun i => gaussianZero_memLp_two_nat_pow v ((i : ℕ) + 1))]
  have hne : variance (fun x : ℝ => ∑ i : Fin n, c i * x ^ ((i : ℕ) + 1))
      (gaussianReal 0 v) ≠ 0 := by
    intro h
    exact hc ((gaussianZero_variance_power_sum_zero_iff v hv n c).mp h)
  exact lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hne)

theorem gaussianZero_powerCovarianceMatrix_det_pos (v : NNReal) (hv : v ≠ 0) (n : ℕ) :
    0 < (powerCovarianceMatrix (gaussianReal 0 v) id n).det :=
  (gaussianZero_powerCovarianceMatrix_posDef v hv n).det_pos

end GaloisForLFunctions.HTGeometry
