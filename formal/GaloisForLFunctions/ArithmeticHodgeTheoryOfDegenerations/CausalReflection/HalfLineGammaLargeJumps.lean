import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineGammaCutoffKernel
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineGammaMixedEnergy
import GaloisForLFunctions.HTGeometry.HardyBoundary.TranslationKernelPairing

/-!
# Large Gamma jumps as bounded convolution pairings

A positive cutoff makes the Lévy density integrable and square integrable.
The resulting translated mixed terms are bounded by the ordinary mass of
a nonnegative test, without a pointwise bound on the other profile.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- The positive-lag Gamma density with its singular endpoint removed. -/
def halfLineGammaCutoffKernel (δ : ℝ) : ℝ → ℝ := (Ioi δ).indicator archLevyDensity

theorem measurable_halfLineGammaCutoffKernel (δ : ℝ) :
    Measurable (halfLineGammaCutoffKernel δ) :=
  measurable_archLevyDensity.indicator measurableSet_Ioi

theorem halfLineGammaCutoffKernel_nonneg {δ : ℝ} (hδ : 0 < δ) (h : ℝ) :
    0 ≤ halfLineGammaCutoffKernel δ h := by
  by_cases hh : h ∈ Ioi δ
  · rw [halfLineGammaCutoffKernel, indicator_of_mem hh]
    exact (archLevyDensity_pos (hδ.trans hh)).le
  · rw [halfLineGammaCutoffKernel, indicator_of_notMem hh]

theorem integrable_halfLineGammaCutoffKernel {δ : ℝ} (hδ : 0 < δ) :
    Integrable (halfLineGammaCutoffKernel δ) :=
  (WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hδ).integrable_indicator measurableSet_Ioi

private theorem halfLineGammaCutoffKernel_sq (δ : ℝ) :
    (fun h => halfLineGammaCutoffKernel δ h ^ 2) =
      (Ioi δ).indicator (fun h => archLevyDensity h ^ 2) := by
  funext h
  by_cases hh : h ∈ Ioi δ
  · simp only [halfLineGammaCutoffKernel, indicator_of_mem hh]
  · simp only [halfLineGammaCutoffKernel, indicator_of_notMem hh, zero_pow two_ne_zero]

theorem integrable_sq_halfLineGammaCutoffKernel {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun h => halfLineGammaCutoffKernel δ h ^ 2) := by
  rw [halfLineGammaCutoffKernel_sq]
  exact (integrableOn_sq_archLevyDensity hδ).integrable_indicator measurableSet_Ioi

theorem integral_sq_halfLineGammaCutoffKernel (δ : ℝ) :
    (∫ h, halfLineGammaCutoffKernel δ h ^ 2) = ∫ h in Ioi δ, archLevyDensity h ^ 2 := by
  rw [halfLineGammaCutoffKernel_sq, integral_indicator measurableSet_Ioi]

theorem integral_halfLineGammaCutoffKernel_mul (δ : ℝ) (f : ℝ → ℝ) :
    (∫ h, halfLineGammaCutoffKernel δ h * f h) =
      ∫ h in Ioi δ, archLevyDensity h * f h := by
  calc
    _ = ∫ h, (Ioi δ).indicator (fun h => archLevyDensity h * f h) h := by
      apply integral_congr_ae
      exact Eventually.of_forall fun h => by
        by_cases hh : h ∈ Ioi δ
        · simp only [halfLineGammaCutoffKernel, indicator_of_mem hh]
        · simp only [halfLineGammaCutoffKernel, indicator_of_notMem hh, zero_mul]
    _ = _ := integral_indicator measurableSet_Ioi

/-- One cutoff Gamma row is bounded by the ordinary mass of a nonnegative actual-domain test. -/
theorem halfLineGamma_cutoff_backward_le {δ : ℝ} (hδ : 0 < δ) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    (hG0 : ∀ u, 0 ≤ G u) :
    (∫ h in Ioi δ, archLevyDensity h * ∫ u, F (u - h) * G u) ≤
      Real.sqrt ((∫ h in Ioi δ, archLevyDensity h ^ 2) * ∫ u, F u ^ 2) * ∫ u, G u := by
  have hh := HTGeometry.integral_weighted_translation_pairing_le
    (integrable_halfLineGammaCutoffKernel hδ) (measurable_halfLineGammaCutoffKernel δ)
    (halfLineGammaCutoffKernel_nonneg hδ) (integrable_sq_halfLineGammaCutoffKernel hδ)
    hF.meas hG.meas hF.sq hG.sq hG.integrable hG0
  rw [integral_halfLineGammaCutoffKernel_mul, integral_sq_halfLineGammaCutoffKernel] at hh
  exact hh

/-- Reflection of the two profiles supplies the matching forward-row bound. -/
theorem halfLineGamma_cutoff_forward_le {δ : ℝ} (hδ : 0 < δ) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    (hG0 : ∀ u, 0 ≤ G u) :
    (∫ h in Ioi δ, archLevyDensity h * ∫ u, F (u + h) * G u) ≤
      Real.sqrt ((∫ h in Ioi δ, archLevyDensity h ^ 2) * ∫ u, F u ^ 2) * ∫ u, G u := by
  have hh := HTGeometry.integral_weighted_forward_pairing_le
    (integrable_halfLineGammaCutoffKernel hδ) (measurable_halfLineGammaCutoffKernel δ)
    (halfLineGammaCutoffKernel_nonneg hδ) (integrable_sq_halfLineGammaCutoffKernel hδ)
    hF.meas hG.meas hF.sq hG.sq hG.integrable hG0
  rw [integral_halfLineGammaCutoffKernel_mul, integral_sq_halfLineGammaCutoffKernel] at hh
  exact hh

#print axioms halfLineGamma_cutoff_backward_le
#print axioms halfLineGamma_cutoff_forward_le
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
