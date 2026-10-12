import GaloisForLFunctions.RHTower.WeilLogShiftTiltVarianceKernel
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltEquality

/-! Any finite probe tilt detects equality of two quadratic laws through a single variance. -/

open MeasureTheory ProbabilityTheory
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem finiteWeilCanonicalJointQuadraticTilt_eq_iff_variance_eq_zero
    (r k : ℕ) (a b d A B D u v w : ℝ) :
    (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) =
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) ↔
        variance (finiteWeilJointQuadratic (a - A) (b - B) (d - D))
          (finiteWeilCanonicalJointQuadraticTilt r k u v w : Measure E) = 0 :=
  (finiteWeilCanonicalJointQuadraticTilt_eq_iff_values r k a b d A B D).trans
    (finiteWeilCanonicalJointQuadraticTilt_variance_eq_zero_iff_values r k u v w
      (finiteWeilJointQuadratic (a - A) (b - B) (d - D))).symm

theorem finiteWeilCanonicalJointQuadraticTilt_ne_iff_variance_pos
    (r k : ℕ) (a b d A B D u v w : ℝ) :
    (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) ≠
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) ↔
        0 < variance (finiteWeilJointQuadratic (a - A) (b - B) (d - D))
          (finiteWeilCanonicalJointQuadraticTilt r k u v w : Measure E) := by
  have heq := finiteWeilCanonicalJointQuadraticTilt_eq_iff_variance_eq_zero r k a b d A B D u v w
  constructor
  · intro hne
    apply lt_of_le_of_ne (variance_nonneg _ _)
    intro hzero
    exact hne (heq.mpr hzero.symm)
  · intro hpos h
    exact (ne_of_gt hpos) (heq.mp h)

end RHTower
