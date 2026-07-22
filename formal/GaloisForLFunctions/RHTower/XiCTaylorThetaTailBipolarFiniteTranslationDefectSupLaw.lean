import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSignedFiniteTranslationDefectSup
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailUniformFiniteTranslationDefectSup

/-!
# Bipolar continuum-uniform finite translation defect

The signed diagonal estimate controls the positive theta-tail phase throughout the symmetric
logarithmic displacement chamber.  Applying it to the negated Xi-centered path and using the exact
negative/positive phase identity gives one eventual stage controlling both phase channels
simultaneously on that full chamber.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- **Bipolar signed-chamber law.**  Scheduled positive and negative theta-tail translation
defects vanish uniformly together, at twice local Xi order, for every signed displacement below
the logarithmic horizon. -/
theorem eventually_forall_scheduled_thetaCuspTail_bipolarFullDefect_localOrder_of_abs_le
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ a : ℝ,
      |a| ≤ xiCTaylorLogarithmicHaarDisplacement A n →
        (|thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent
            (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
            (xiCTaylorAnisotropicCenteredPoint sigma n) a| *
          (((n + 1 : ℕ) : ℝ) ^
            (2 * (analyticOrderAt xi sigma).toNat)) < epsilon) ∧
        (|thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent
            (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
            (xiCTaylorAnisotropicCenteredPoint sigma n) a| *
          (((n + 1 : ℕ) : ℝ) ^
            (2 * (analyticOrderAt xi sigma).toNat)) < epsilon) := by
  obtain ⟨R, hR, hz⟩ :=
    exists_eventually_xiCTaylorAnisotropicCenteredPoint_norm_le_nat sigma
  have hzneg : ∀ᶠ n : ℕ in atTop,
      ‖-xiCTaylorAnisotropicCenteredPoint sigma n‖ ≤ R := by
    simpa only [norm_neg] using hz
  have hpositive :=
    eventually_forall_scheduled_thetaCuspTailPhaseTranslationFullDefect_localOrder_of_abs_le
      hD A sigma hepsilon
  have hnegative :=
    eventually_forall_thetaCuspTailPhaseTranslationFullDefect_mul_pow_lt_of_abs_le
      A (2 * (analyticOrderAt xi sigma).toNat) R hR
        (fun n => D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
        (le_xiCTaylorScheduledThetaTailDepth hD sigma)
        (fun n => -xiCTaylorAnisotropicCenteredPoint sigma n) hzneg hepsilon
  filter_upwards [hpositive, hnegative] with n hnpositive hnnegative
  intro a ha
  refine ⟨hnpositive a ha, ?_⟩
  rw [thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent_eq_neg_positive_neg,
    abs_neg]
  exact hnnegative a ha

end

end RHTower
