import GaloisForLFunctions.RHTower.IntegralCofinalTateRelativeReflectionAssembly

/-!
# Global Gamma base change of the integral cofinal Tate operator

Coefficientwise physical Gamma evaluation intertwines the globally assembled integral curved Tate
operator with the complex curved-suspension operator on every cofinal stage. This is the global
source-to-completion Beck--Chevalley square; no Xi divisor is selected.
-/

open Complex Matrix

namespace RHTower

noncomputable section

/-- Complex reciprocal-orientation packets over all cofinal Tate stages. -/
abbrev DeningerPhysicalCofinalTateOrientationPacket :=
  ℕ →₀ (Fin 2 → ℂ)

/-- Coefficientwise Gamma physicalization of the global integral cofinal Tate packet. -/
def deningerIntegralCofinalTateGammaPhysicalization
    (a : ℝ) (x : DeningerIntegralCofinalTateOrientationPacket) :
    DeningerPhysicalCofinalTateOrientationPacket :=
  x.mapRange
    (fun v i => deningerIntegralGammaEvaluationComplex a (v i))
    (by funext i; simp)

@[simp] theorem deningerIntegralCofinalTateGammaPhysicalization_apply
    (a : ℝ) (x : DeningerIntegralCofinalTateOrientationPacket)
    (m : ℕ) (i : Fin 2) :
    deningerIntegralCofinalTateGammaPhysicalization a x m i =
      deningerIntegralGammaEvaluationComplex a (x m i) := by
  simp [deningerIntegralCofinalTateGammaPhysicalization]

/-- Global physical completion operator, acting by the curved suspension at every stage. -/
def deningerPhysicalCofinalRelativeReflectionOperator (a : ℝ) :
    DeningerPhysicalCofinalTateOrientationPacket →ₗ[ℂ]
      DeningerPhysicalCofinalTateOrientationPacket :=
  Finsupp.mapRange.linearMap
    (Matrix.mulVecLin (sourceHorizontalGammaSixCurvedSuspension a))

@[simp] theorem deningerPhysicalCofinalRelativeReflectionOperator_apply
    (a : ℝ) (x : DeningerPhysicalCofinalTateOrientationPacket) (m : ℕ) :
    deningerPhysicalCofinalRelativeReflectionOperator a x m =
      (sourceHorizontalGammaSixCurvedSuspension a).mulVec (x m) := by
  simp [deningerPhysicalCofinalRelativeReflectionOperator]

/-- Matrix-vector Gamma naturality on one reciprocal orientation fibre. -/
theorem deningerIntegralGammaEvaluationComplex_mulVec
    (a : ℝ) (v : Fin 2 → DeningerIntegralTateRing) (i : Fin 2) :
    deningerIntegralGammaEvaluationComplex a
        (deningerIntegralRelativeReflectionDifferential.mulVec v i) =
      (sourceHorizontalGammaSixCurvedSuspension a).mulVec
        (fun j => deningerIntegralGammaEvaluationComplex a (v j)) i := by
  fin_cases i <;>
    simp [deningerIntegralRelativeReflectionDifferential,
      sourceHorizontalGammaSixCurvedSuspension,
      sourceHorizontalGammaSixForwardSuspensionLeg,
      sourceHorizontalGammaSixReflectedSuspensionLeg,
      Matrix.mulVec, deningerIntegralGammaEvaluation_generator,
      deningerIntegralGammaEvaluation_inverseGenerator,
      deningerIntegralGammaEvaluationComplex,
      sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq,
      sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq]
  all_goals left; congr

/-- Global Gamma base-change square: physicalization intertwines the source integral operator and
the physical curved completion operator on the entire cofinal direct sum. -/
theorem deningerIntegralCofinalRelativeReflectionOperator_gamma_natural
    (a : ℝ) (x : DeningerIntegralCofinalTateOrientationPacket) :
    deningerIntegralCofinalTateGammaPhysicalization a
        (deningerIntegralCofinalRelativeReflectionOperator x) =
      deningerPhysicalCofinalRelativeReflectionOperator a
        (deningerIntegralCofinalTateGammaPhysicalization a x) := by
  apply Finsupp.ext
  intro m
  funext i
  rw [deningerIntegralCofinalTateGammaPhysicalization_apply,
    deningerIntegralCofinalRelativeReflectionOperator_apply,
    deningerPhysicalCofinalRelativeReflectionOperator_apply]
  exact deningerIntegralGammaEvaluationComplex_mulVec a (x m) i

/-- Global physical curved-completion law after Gamma base change. -/
theorem deningerPhysicalCofinalRelativeReflectionOperator_sq (a : ℝ) :
    (deningerPhysicalCofinalRelativeReflectionOperator a).comp
        (deningerPhysicalCofinalRelativeReflectionOperator a) =
      -(sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a : ℂ) • LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Finsupp.ext
  intro m
  funext i
  rw [LinearMap.comp_apply,
    deningerPhysicalCofinalRelativeReflectionOperator_apply,
    deningerPhysicalCofinalRelativeReflectionOperator_apply,
    Matrix.mulVec_mulVec,
    sourceHorizontalGammaSixCurvedSuspension_sq]
  fin_cases i <;> simp [Matrix.mulVec]

end


end RHTower
