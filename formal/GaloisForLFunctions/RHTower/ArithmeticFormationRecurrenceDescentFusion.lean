import GaloisForLFunctions.RHTower.ArithmeticFormationCompletionBoundaryFusion
import GaloisForLFunctions.RHTower.HedenmalmThetaSourcePrimeModularCompactRecurrenceDescent

/-!
# Arithmetic formation--recurrence descent fusion

The singular Meyer--Tate completion and the faithful compact prime-circle recurrence formation
detect the same Xi obstruction in complementary directions.  A completed Xi boundary is born
beyond finite arithmetic formation exactly when its recovered real prime-history character fails
continuous compact descent.  Globally, boundary freedom and compact descent are the same law.
-/

open Complex

namespace RHTower

open HedenmalmThetaSource

noncomputable section

/-- **Pointwise formation--recurrence complementarity.**  Arithmetic completion birth is exactly
failure of information-neutral compact recurrence descent for the recovered source character. -/
theorem deningerGammaSixCofinalXiGreenVerticalBoundary_mem_formationCompletionBoundary_iff_not_compactRecurrenceDescent
    (q : XiZeroCopy) :
    deningerGammaSixCofinalXiGreenVerticalBoundary q ∈
        deningerGammaSixArithmeticFormationCompletionBoundary ↔
      ¬ ThetaXiPrimeModularCompactRecurrenceDescent q := by
  rw [deningerGammaSixCofinalXiGreenVerticalBoundary_mem_formationCompletionBoundary_iff,
    thetaXiPrimeModularCompactRecurrenceDescent_iff]

/-- **Global formation--recurrence fusion.**  Universal finite arithmetic effectivity and
universal faithful compact descent are the same source law. -/
theorem xiArithmeticFormationCompletionBoundaryFree_iff_compactRecurrenceDescent :
    XiArithmeticFormationCompletionBoundaryFree ↔
      ∀ q : XiZeroCopy, ThetaXiPrimeModularCompactRecurrenceDescent q := by
  rw [xiArithmeticFormationCompletionBoundaryFree_iff_riemannHypothesis,
    forall_thetaXiPrimeModularCompactRecurrenceDescent_iff_riemannHypothesis]

/-- Closed certificate joining the pointwise complementarity, its global source law, and RH. -/
def ArithmeticFormationRecurrenceDescentFusionLaw : Prop :=
  (∀ q : XiZeroCopy,
    deningerGammaSixCofinalXiGreenVerticalBoundary q ∈
        deningerGammaSixArithmeticFormationCompletionBoundary ↔
      ¬ ThetaXiPrimeModularCompactRecurrenceDescent q) ∧
  (XiArithmeticFormationCompletionBoundaryFree ↔
    ∀ q : XiZeroCopy, ThetaXiPrimeModularCompactRecurrenceDescent q) ∧
  ((∀ q : XiZeroCopy, ThetaXiPrimeModularCompactRecurrenceDescent q) ↔
    RiemannHypothesis)

/-- Arithmetic formation--recurrence descent fusion law, without external hypotheses. -/
theorem arithmeticFormationRecurrenceDescentFusion_law :
    ArithmeticFormationRecurrenceDescentFusionLaw := by
  exact
    ⟨deningerGammaSixCofinalXiGreenVerticalBoundary_mem_formationCompletionBoundary_iff_not_compactRecurrenceDescent,
      xiArithmeticFormationCompletionBoundaryFree_iff_compactRecurrenceDescent,
      forall_thetaXiPrimeModularCompactRecurrenceDescent_iff_riemannHypothesis⟩

end

end RHTower
