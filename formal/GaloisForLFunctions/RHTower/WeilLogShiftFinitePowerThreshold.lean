import GaloisForLFunctions.RHTower.WeilLogShiftFinitePowerCovariance
import Mathlib.Analysis.Matrix.PosDef

/-! Exact finite covariance threshold, with no depth growth or subcriticality requirement. -/

open MeasureTheory ProbabilityTheory Filter Topology GaloisForLFunctions.HTGeometry
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_pos_iff
    (r k : ℕ) (a b d : ℝ) (n : ℕ) :
    0 < (powerCovarianceMatrix (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (fun z => z 0) n).det ↔ n ≤ r := by
  constructor
  · intro hpos
    by_contra h
    have hzero := finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_zero_of_lt
      r k a b d n (Nat.lt_of_not_ge h)
    exact (ne_of_gt hpos) hzero
  · intro hn
    exact (finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_posDef_of_le
      r k a b d n hn).det_pos

theorem finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_posDef_iff
    (r k : ℕ) (a b d : ℝ) (n : ℕ) :
    (powerCovarianceMatrix (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (fun z => z 0) n).PosDef ↔ n ≤ r := by
  constructor
  · intro h
    exact (finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_pos_iff
      r k a b d n).mp h.det_pos
  · exact finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_posDef_of_le r k a b d n

theorem finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_zero_iff
    (r k : ℕ) (a b d : ℝ) (n : ℕ) :
    (powerCovarianceMatrix (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (fun z => z 0) n).det = 0 ↔ r < n := by
  constructor
  · intro hzero
    by_contra h
    have hpos := (finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_pos_iff
      r k a b d n).mpr (Nat.le_of_not_gt h)
    exact (ne_of_gt hpos) hzero
  · exact finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_zero_of_lt r k a b d n

theorem eventually_finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_pos_arbitrary
    (k : ℕ → ℕ) (a b d : ℕ → ℝ) (n : ℕ) :
    ∀ᶠ r in atTop, 0 < (powerCovarianceMatrix
      (finiteWeilCanonicalJointQuadraticTilt r (k r) (a r) (b r) (d r) : Measure E)
      (fun z => z 0) n).det := by
  filter_upwards [eventually_ge_atTop n] with r hr
  exact (finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_pos_iff
    r (k r) (a r) (b r) (d r) n).mpr hr

end RHTower
