import GaloisForLFunctions.RHTower.XiCTaylorThetaTailBipolarFiniteTranslationDefectSupLaw
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedProuhetCurrentBound

/-!
# Synchronized bipolar theta-tail and Prouhet control

The bipolar continuum-uniform translation estimate and the phase-adapted Prouhet cross estimate
run on the same anisotropic Taylor center and superaccurate odd schedule.  Intersecting their
cofinal stages gives one index range on which both mechanisms hold simultaneously.
-/

open Complex Real Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- **Xi Taylor bipolar--Prouhet synchronization law.**  Eventually, every signed displacement
below the logarithmic horizon has small positive and negative theta-tail full defect, while an
arbitrary scheduled phase-adapted Prouhet cross is simultaneously dominated by the scaled squared
final Taylor value. -/
theorem eventually_bipolarFullDefect_and_phaseAdaptedProuhetCross_lt
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ)
    (F F' E E' : ℕ → ℂ) (m : ℕ → ℕ)
    (q r tau a L : ℕ → ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      (∀ displacement : ℝ,
        |displacement| ≤ xiCTaylorLogarithmicHaarDisplacement A n →
        (|thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent
            (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
            (xiCTaylorAnisotropicCenteredPoint sigma n) displacement| *
          (((n + 1 : ℕ) : ℝ) ^
            (2 * (analyticOrderAt xi sigma).toNat)) < epsilon) ∧
        (|thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent
            (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
            (xiCTaylorAnisotropicCenteredPoint sigma n) displacement| *
          (((n + 1 : ℕ) : ℝ) ^
            (2 * (analyticOrderAt xi sigma).toNat)) < epsilon)) ∧
      phaseAdaptedProuhetOneSidedTranslationHermitianCrossPacket
          (F n) (F' n) (E n) (E' n) (m n)
          (q n) (r n) (tau n) (a n) (L n)
          (xiCTaylorAnisotropicCenteredPoint sigma n) <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  exact (eventually_forall_scheduled_thetaCuspTail_bipolarFullDefect_localOrder_of_abs_le
    hD A sigma hepsilon).and
      (eventually_phaseAdaptedProuhetOneSidedTranslationHermitianCrossPacket_lt_scaled_normSq
        hD sigma F F' E E' m q r tau a L hepsilon)

end

end RHTower
