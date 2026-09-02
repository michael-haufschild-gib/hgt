import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixPositiveStarUntwisting
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixRelativeReflectionFraming

/-!
# Integral relative-reflection complex fusion

The integral Laurent source, functional-equation inversion, and Gamma-six curved reflection are
one two-periodic rank-two object. Its off-diagonal arrows are `T - 1` and `T⁻¹ - 1`; its square is
the quadratic Laurent ghost times the identity; and physical Gamma evaluation is exactly the
curved suspension between bare and transported reflections.
-/

open Complex Matrix

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Universal integral odd differential comparing bare reflection with its Laurent transport. -/
def deningerIntegralRelativeReflectionDifferential :
    Matrix (Fin 2) (Fin 2) DeningerIntegralCartierSourceRing :=
  !![0, deningerIntegralCartierSourceGenerator;
    inversion ℤ deningerIntegralCartierSourceGenerator, 0]

/-- Complex-valued physical Gamma evaluation of the integral Laurent source. -/
def deningerIntegralGammaEvaluationComplex (a : ℝ) :
    DeningerIntegralCartierSourceRing →+* ℂ :=
  (algebraMap ℝ ℂ).comp (deningerIntegralGammaEvaluation a)

/-- Physical evaluation of the universal integral differential is exactly the Gamma-six curved
suspension, hence transported reflection minus bare reflection. -/
theorem deningerIntegralRelativeReflectionDifferential_evaluation (a : ℝ) :
    deningerIntegralRelativeReflectionDifferential.map
        (deningerIntegralGammaEvaluationComplex a) =
      sourceHorizontalGammaSixCurvedSuspension a := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [deningerIntegralRelativeReflectionDifferential,
      deningerIntegralGammaEvaluationComplex,
      sourceHorizontalGammaSixCurvedSuspension,
      sourceHorizontalGammaSixForwardSuspensionLeg,
      sourceHorizontalGammaSixReflectedSuspensionLeg]
  · simp [deningerIntegralRelativeReflectionDifferential,
      deningerIntegralGammaEvaluationComplex,
      sourceHorizontalGammaSixCurvedSuspension,
      sourceHorizontalGammaSixForwardSuspensionLeg,
      sourceHorizontalGammaSixReflectedSuspensionLeg,
      deningerIntegralGammaEvaluation_generator]
  · simp [deningerIntegralRelativeReflectionDifferential,
      deningerIntegralGammaEvaluationComplex,
      sourceHorizontalGammaSixCurvedSuspension,
      sourceHorizontalGammaSixForwardSuspensionLeg,
      sourceHorizontalGammaSixReflectedSuspensionLeg,
      deningerIntegralGammaEvaluation_inverseGenerator]
  · simp [deningerIntegralRelativeReflectionDifferential,
      deningerIntegralGammaEvaluationComplex,
      sourceHorizontalGammaSixCurvedSuspension,
      sourceHorizontalGammaSixForwardSuspensionLeg,
      sourceHorizontalGammaSixReflectedSuspensionLeg]

/-- Determinant of the universal relative-reflection differential is minus the one-copy integral
quadratic ghost. -/
theorem det_deningerIntegralRelativeReflectionDifferential :
    Matrix.det deningerIntegralRelativeReflectionDifferential =
      -sourceHorizontalGammaSixIntegralHermitianSquare := by
  rw [Matrix.det_fin_two]
  simp [deningerIntegralRelativeReflectionDifferential,
    sourceHorizontalGammaSixIntegralHermitianSquare]

/-- Exact source Clifford law: the odd differential squares to the quadratic ghost times the
identity. -/
theorem deningerIntegralRelativeReflectionDifferential_sq :
    deningerIntegralRelativeReflectionDifferential *
        deningerIntegralRelativeReflectionDifferential =
      sourceHorizontalGammaSixIntegralHermitianSquare •
        (1 : Matrix (Fin 2) (Fin 2) DeningerIntegralCartierSourceRing) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [deningerIntegralRelativeReflectionDifferential,
      sourceHorizontalGammaSixIntegralHermitianSquare, Matrix.mul_apply]
  all_goals ring_nf

/-- Determinant transgression: evaluating the integral source determinant gives exactly positive
paired Gamma curvature. -/
theorem deningerIntegralRelativeReflection_determinant_evaluation (a : ℝ) :
    deningerIntegralGammaEvaluationComplex a
        (Matrix.det deningerIntegralRelativeReflectionDifferential) =
      (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a : ℂ) := by
  rw [det_deningerIntegralRelativeReflectionDifferential, map_neg,
    deningerIntegralGammaEvaluationComplex,
    RingHom.comp_apply,
    deningerIntegralGammaEvaluation_hermitianSquare_eq_neg_curvature]
  norm_num

end


end RHTower
