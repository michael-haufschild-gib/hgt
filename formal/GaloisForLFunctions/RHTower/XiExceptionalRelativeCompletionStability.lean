import GaloisForLFunctions.RHTower.Deninger.DeningerExponentExceptionalTameGreenBridge
import GaloisForLFunctions.RHTower.XiRelativeCompletionStabilityWall

/-!
# Exceptional-divisor realization of the Xi stability wall

The marked-pole displacement on the exponent-deformation exceptional fibre is exactly twice the
relative-completion slope. Thus exceptional-pole collision, semistability, and zero HN radius are
the same condition; strict pole ordering gives the two stability chambers.
-/

open Complex

namespace RHTower

noncomputable section

/-- Exceptional normal displacement is exactly twice the relative-completion slope. -/
theorem deningerExponentExceptionalPole_displacement_eq_twice_relativeCompletionSlope
    (q : XiZeroCopy) :
    deningerExponentExceptionalReflectedPole q -
        deningerExponentExceptionalSourcePole q =
      ((2 * xiRelativeCompletionSlope q : ℝ) : ℂ) := by
  rw [deningerExponentExceptionalPole_displacement_eq_greenFracture,
    xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  congr 2

/-- Relative-completion semistability is coincidence of the two marked exceptional poles. -/
theorem xiRelativeCompletionSemistable_iff_exceptionalPoles_coincide
    (q : XiZeroCopy) :
    XiRelativeCompletionSemistable q ↔
      deningerExponentExceptionalReflectedPole q =
        deningerExponentExceptionalSourcePole q := by
  rw [xiRelativeCompletionSemistable_iff_re_eq_half,
    ← xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff,
    ← deningerExponentExceptionalPole_displacement_eq_greenFracture,
    sub_eq_zero]

/-- HN radius is half the metric separation of the marked exceptional poles. -/
theorem abs_xiRelativeCompletionSlope_eq_half_norm_exceptionalPoleDisplacement
    (q : XiZeroCopy) :
    |xiRelativeCompletionSlope q| =
      (1 / 2 : ℝ) * ‖deningerExponentExceptionalReflectedPole q -
        deningerExponentExceptionalSourcePole q‖ := by
  rw [deningerExponentExceptionalPole_displacement_eq_twice_relativeCompletionSlope]
  simp only [norm_real, Real.norm_eq_abs, abs_mul]
  norm_num
  ring

/-- Positive stability chamber is positive real exceptional-pole displacement. -/
theorem xiRelativeCompletionStable_iff_exceptionalPoleDisplacement_re_pos
    (q : XiZeroCopy) :
    XiRelativeCompletionStable q ↔
      0 < (deningerExponentExceptionalReflectedPole q -
        deningerExponentExceptionalSourcePole q).re := by
  rw [xiRelativeCompletionStable_iff_re_gt_half,
    deningerExponentExceptionalPole_displacement_eq_twice_relativeCompletionSlope]
  simp only [ofReal_re, xiRelativeCompletionSlope,
    deningerMeyerHalfDensityXiHorizontalRate]
  constructor <;> intro h <;> linarith

/-- Negative stability chamber is negative real exceptional-pole displacement. -/
theorem xiRelativeCompletionUnstable_iff_exceptionalPoleDisplacement_re_neg
    (q : XiZeroCopy) :
    XiRelativeCompletionUnstable q ↔
      (deningerExponentExceptionalReflectedPole q -
        deningerExponentExceptionalSourcePole q).re < 0 := by
  rw [xiRelativeCompletionUnstable_iff_re_lt_half,
    deningerExponentExceptionalPole_displacement_eq_twice_relativeCompletionSlope]
  simp only [ofReal_re, xiRelativeCompletionSlope,
    deningerMeyerHalfDensityXiHorizontalRate]
  constructor <;> intro h <;> linarith

end

end RHTower
