import GaloisForLFunctions.HTGeometry.GaussianPowerCovariance
import GaloisForLFunctions.RHTower.WeilLogShiftPolynomialCovarianceLimit
import Mathlib.Topology.Instances.Matrix

/-! Each fixed power covariance determinant is eventually positive for actual subcritical Weil tilts. -/

open MeasureTheory ProbabilityTheory Filter Topology GaloisForLFunctions.HTGeometry
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (n : ℕ) :
    Tendsto (fun r => powerCovarianceMatrix
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E)
      (fun z => z 0) n) atTop
      (𝓝 (powerCovarianceMatrix (gaussianReal 0
        (finiteWeilQuadraticTiltVariance ⟨a + 2 * b + d.val, d.property⟩)) id n)) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  have hlim := tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_covariance t a b d
    ((MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) ^ ((i : ℕ) + 1))
    ((MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) ^ ((j : ℕ) + 1))
  simpa only [powerCovarianceMatrix, MvPolynomial.eval_pow, MvPolynomial.eval_X, id_eq] using hlim

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (n : ℕ) :
    Tendsto (fun r => (powerCovarianceMatrix
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E)
      (fun z => z 0) n).det) atTop
      (𝓝 ((powerCovarianceMatrix (gaussianReal 0
        (finiteWeilQuadraticTiltVariance ⟨a + 2 * b + d.val, d.property⟩)) id n).det)) := by
  have hc : Continuous (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) := continuous_id.matrix_det
  exact hc.continuousAt.tendsto.comp
    (tendsto_finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix t a b d n)

theorem eventually_finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_pos
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (n : ℕ) :
    ∀ᶠ r in atTop, 0 < (powerCovarianceMatrix
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E)
      (fun z => z 0) n).det := by
  have hv : finiteWeilQuadraticTiltVariance ⟨a + 2 * b + d.val, d.property⟩ ≠ 0 := by
    apply ne_of_gt
    change (0 : ℝ) < 1 / (4 - 2 * (a + 2 * b + d.val))
    exact one_div_pos.mpr (by linarith only [d.property])
  exact (tendsto_order.mp
    (tendsto_finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det t a b d n)).1 0
      (gaussianZero_powerCovarianceMatrix_det_pos _ hv n)

end RHTower
