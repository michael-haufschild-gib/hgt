import GaloisForLFunctions.RHTower.Suzuki.SuzukiTransitionCoreAlignedGammaCompletion
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiGammaBinetCofinalBridge

/-!
# The literal pole and Gamma completion of the Suzuki energy

The finite prime amplitude is corrected by the integral of
`2 cosh(t/2) − Γ(t)` against the same reporter before it is squared.
The aligned energy is comparable to this literal completed square, with
the explicit condition-number constant `1889568 (log 4 + 4)²`.
-/

noncomputable section
open Real MeasureTheory Filter Set
open scoped Topology
open _root_.RHTower GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.BiScaleUncertainty

/-- Finite-prime amplitude with its actual pole and Gamma integral restored. -/
def suzukiPrimePolarGammaAmplitude (N : ℕ) : ℝ :=
  unitRieszCoherentPrimeOutgoingCharge N -
    ∫ t in unitRieszSuzukiBase..Real.log N,
      unitRieszSuzukiReporter (Real.log N) t *
        (2 * Real.cosh (t / 2) - ccmGammaTranslationDensity t)

/-- The literal source correction is exactly the completed lower-Hardy amplitude. -/
theorem suzukiPrimePolarGammaAmplitude_eq {N : ℕ} (hN : 2 ≤ N) :
    suzukiPrimePolarGammaAmplitude N = suzukiNaturalApertureCompletedLowerHardyAmplitude N := by
  rw [suzukiNaturalApertureCompletedLowerHardyAmplitude,
    suzukiNaturalApertureLowerHardyAmplitude_eq_primeOutgoingCharge hN]
  unfold suzukiPrimePolarGammaAmplitude suzukiUnitRieszRegularWardMass
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < N by omega))
  have ht0 : 0 < t := (lt_min unitRieszSuzukiBase_pos hlog).trans_le ht.1
  rw [screwRegularKernel_eq_polar_sub_ccmGammaTranslationDensity ht0]

/-- Both sides of the aligned-energy comparison retain the full arithmetic completion. -/
theorem eventually_suzukiAlignedEnergy_literal_bounds :
    ∀ᶠ N : ℕ in atTop,
      suzukiPrimePolarGammaAmplitude N ^ 2 ≤ suzukiTransitionCoreAlignedGammaCompletedEnergy N ∧
      suzukiTransitionCoreAlignedGammaCompletedEnergy N ≤
        (1889568 * (Real.log 4 + 4) ^ 2) * suzukiPrimePolarGammaAmplitude N ^ 2 := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    eventually_completedAnchor_sq_le_suzukiTransitionCoreAlignedEnergy,
    eventually_suzukiAlignedEnergy_le_condition_mul_completedAnchor_sq] with N hN hlo hup
  rw [suzukiPrimePolarGammaAmplitude_eq hN]
  exact ⟨hlo, hup⟩

/-- The completed-source criterion with the pole and Gamma terms written literally. -/
theorem riemannHypothesis_iff_suzukiPrimePolarGammaAmplitude_bounded :
    RiemannHypothesis ↔ ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      |suzukiPrimePolarGammaAmplitude (N + 2)| ≤ B := by
  rw [riemannHypothesis_iff_suzukiNaturalCauchyCompletedAnchorBounded]
  have he (N : ℕ) : suzukiPrimePolarGammaAmplitude (N + 2) =
      suzukiNaturalApertureCompletedLowerHardyAmplitude (N + 2) :=
    suzukiPrimePolarGammaAmplitude_eq (by omega)
  simp only [SuzukiNaturalCauchyCompletedAnchorBounded, he]

#print axioms suzukiPrimePolarGammaAmplitude_eq
#print axioms eventually_suzukiAlignedEnergy_literal_bounds
#print axioms riemannHypothesis_iff_suzukiPrimePolarGammaAmplitude_bounded

end GaloisForLFunctions.BiScaleUncertainty
