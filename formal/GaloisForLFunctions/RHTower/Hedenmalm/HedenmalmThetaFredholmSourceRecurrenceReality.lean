import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaFredholmEigenmodeGreenIsotropy
import GaloisForLFunctions.RHTower.ArithmeticAsymptoticHullTemperedness

/-!
# Fixed theta Fredholm spectrum and arithmetic source recurrence

The requested reality statement for every nonzero eigenvalue of the fixed theta source operator
is isolated as a target-free proposition.  Compact Fredholm theory identifies it exactly with
real nonzero source spectrum and hence with RH.  The literal first CCM clock then removes Xi from
both sides of the final source bridge: eigenvalue reality is equivalent to asymptotic Bohr
recurrence of a function defined directly from the completed prime--Gamma source.

This is an unconditional classification theorem, not a proof of source recurrence.  Reflection,
finite arithmetic stages, positivity, and Calkin control do not supply that cofinal recurrence.
-/

open Complex MeasureTheory

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry
open Module.End

namespace HedenmalmThetaSource

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-- Every nonzero eigenvalue of the fixed theta source operator is real. -/
def ThetaKernelOperatorNonzeroEigenvaluesReal : Prop :=
  ∀ (mu : ℂ) (f : ThetaH), f ≠ 0 → mu ≠ 0 →
    thetaKernelOperator f = mu • f → ∃ t : ℝ, mu = (t : ℂ)

/-- The requested fixed-source eigenvalue reality statement is exactly RH. -/
theorem thetaKernelOperatorNonzeroEigenvaluesReal_iff_riemannHypothesis :
    ThetaKernelOperatorNonzeroEigenvaluesReal ↔ RiemannHypothesis := by
  constructor
  · intro hreal
    rw [riemannHypothesis_iff_thetaKernelOperator_nonzero_spectrum_real]
    intro mu hspec hmu
    have heigen : HasEigenvalue
        (thetaKernelOperator : Module.End ℂ ThetaH) mu :=
      (isCompactOperator_thetaKernelOperator.hasEigenvalue_iff_mem_spectrum hmu).2 hspec
    obtain ⟨f, hf⟩ := heigen.exists_hasUnifEigenvector
    exact hreal mu f hf.2 hmu hf.apply_eq_smul
  · intro hRH mu f hf hmu heigen
    have hevec : Module.End.HasEigenvector
        (thetaKernelOperator : Module.End ℂ ThetaH) mu f :=
      ⟨Module.End.mem_eigenspace_iff.mpr heigen, hf⟩
    have hspec : mu ∈ spectrum ℂ thetaKernelOperator :=
      (isCompactOperator_thetaKernelOperator.hasEigenvalue_iff_mem_spectrum hmu).1
        hevec.hasUnifEigenvalue
    exact
      (riemannHypothesis_iff_thetaKernelOperator_nonzero_spectrum_real.mp hRH)
        mu hspec hmu

/-- Target-free source bridge: real nonzero theta spectrum is equivalent to asymptotic recurrence
of the literal aperture-scaled first CCM clock. -/
theorem thetaKernelOperatorNonzeroEigenvaluesReal_iff_firstClockSourceRecurrence :
    ThetaKernelOperatorNonzeroEigenvaluesReal ↔
      CCMFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic := by
  rw [thetaKernelOperatorNonzeroEigenvaluesReal_iff_riemannHypothesis,
    ccmFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic_iff_rh]

end HedenmalmThetaSource
end
end RHTower
