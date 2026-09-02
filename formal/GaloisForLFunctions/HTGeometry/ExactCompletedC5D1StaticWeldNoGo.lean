import GaloisForLFunctions.HTGeometry.ExactCompletedC5SeamSlopeChamberNoGo

/-!
# Strict D1 does not orient the completed C5 first crossing

The source-positive seam state at squared scale `100` has strict rank-three reflected `D1`, lies
on the exact completed C5 orientation wall, and crosses that wall in the negative direction.  Thus
even adjoining strict `D1` to the known static source-positive chamber cannot turn the completed
C5 first-crossing problem into a static minor-extension argument.  Any common D1--C5 producer
must use actual theta-orbit dynamics rather than pointwise positivity of the two adjacent Hankel
levels.
-/

open Complex Real

namespace HTGeometry

noncomputable section

/-- At the C5 counterstate of squared seam scale `100`, source-positive rank-three `D1` is
strictly positive. -/
theorem eval_modularThetaSourcePositiveReflectedEighthPolynomial_hundred_re_pos :
    0 < (MvPolynomial.eval (modularThetaSourcePositiveSeamState 100)
      modularThetaSourcePositiveReflectedEighthPolynomial).re := by
  rw [← modularThetaSourcePositiveChart_reflectedEighthPolynomial,
    show modularThetaSourcePositiveSeamState 100 =
      modularThetaSourcePositiveSeamState ((10 : ℝ) ^ 2) by norm_num,
    eval_modularThetaSourcePositiveChartPullback_seam,
    eval_modularThetaLyapunovReflectedEighthPolynomial_seam]
  norm_num [modularThetaReflectedEighthSeamPolynomial]

/-- **Static D1--C5 weld no-go.** Strict source-positive `D1` can coexist with zero completed C5
orientation and strictly negative physical C5 Lie derivative. -/
theorem exists_sourcePositive_D1_pos_c5Orientation_zero_c5Slope_neg :
    ∃ v : ModularThetaSourcePositiveState → ℂ,
      0 < (MvPolynomial.eval v
          modularThetaSourcePositiveReflectedEighthPolynomial).re ∧
      MvPolynomial.eval v
          modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial = 0 ∧
      (MvPolynomial.eval v
          (modularThetaSourcePositiveLie
            modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial)).re < 0 := by
  refine ⟨modularThetaSourcePositiveSeamState 100,
    eval_modularThetaSourcePositiveReflectedEighthPolynomial_hundred_re_pos,
    eval_modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial_hundred_eq_zero,
    eval_modularThetaSourcePositiveLie_c5ExactCompletedSeamOrientation_hundred_re_neg⟩

end

end HTGeometry
