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

private theorem integrableOn_cutoff_backward_pairing {δ : ℝ} (hδ : 0 < δ) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    IntegrableOn (fun h => archLevyDensity h * ∫ u, F (u - h) * G u) (Ioi δ) := by
  have hj := HTGeometry.integrable_weighted_translation_pairing
    (integrable_halfLineGammaCutoffKernel hδ) (measurable_halfLineGammaCutoffKernel δ)
    (halfLineGammaCutoffKernel_nonneg hδ) hF.meas hG.meas hF.sq hG.sq
  have hi : Integrable (fun h => halfLineGammaCutoffKernel δ h * ∫ u, F (u - h) * G u) := by
    apply hj.integral_prod_left.congr
    exact Eventually.of_forall fun h => by
      dsimp only
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun u => mul_assoc _ _ _
  apply hi.integrableOn.congr_fun _ measurableSet_Ioi
  intro h hh
  dsimp only
  rw [halfLineGammaCutoffKernel, indicator_of_mem hh]

private theorem integrableOn_cutoff_forward_pairing {δ : ℝ} (hδ : 0 < δ) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    IntegrableOn (fun h => archLevyDensity h * ∫ u, F (u + h) * G u) (Ioi δ) := by
  apply (integrableOn_cutoff_backward_pairing hδ hG hF).congr_fun _ measurableSet_Ioi
  intro h _
  dsimp only
  congr 1
  calc
    _ = ∫ u, G (u + h - h) * F (u + h) :=
      (integral_add_right_eq_self (fun u => G (u - h) * F u) h).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun u => by
        dsimp only
        rw [add_sub_cancel_right, mul_comm]

/-- Translation invariance identifies the two mixed cross terms of a Gamma jump. -/
theorem halfLineGammaMixedJump_eq_rows {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) (h : ℝ) :
    halfLineGammaMixedJump F G h = archLevyDensity h *
      (2 * (∫ u, F u * G u) - (∫ u, F (u - h) * G u) - ∫ u, F (u + h) * G u) := by
  have hf := hF.memLp_real.comp_measurePreserving (measurePreserving_add_right volume h)
  have hg := hG.memLp_real.comp_measurePreserving (measurePreserving_add_right volume h)
  have hFG : Integrable (fun u => F u * G u) := hF.memLp_real.integrable_mul hG.memLp_real
  have hs : Integrable (fun u => F (u + h) * G (u + h)) :=
    hFG.comp_measurePreserving (measurePreserving_add_right volume h)
  have hc : Integrable (fun u => F u * G (u + h)) := hF.memLp_real.integrable_mul hg
  have hd : Integrable (fun u => F (u + h) * G u) := hf.integrable_mul hG.memLp_real
  have hec : (∫ u, F u * G (u + h)) = ∫ u, F (u - h) * G u := by
    calc
      _ = ∫ u, F (u + h - h) * G (u + h) := by simp only [add_sub_cancel_right]
      _ = _ := integral_add_right_eq_self (fun u => F (u - h) * G u) h
  have hes : (∫ u, F (u + h) * G (u + h)) = ∫ u, F u * G u :=
    integral_add_right_eq_self (fun u => F u * G u) h
  have hea : (∫ u, F u * G u + F (u + h) * G (u + h)) =
      (∫ u, F u * G u) + ∫ u, F (u + h) * G (u + h) := integral_add hFG hs
  unfold halfLineGammaMixedJump
  congr 1
  calc
    _ = ∫ u, (F u * G u + F (u + h) * G (u + h) - F u * G (u + h)) -
        F (u + h) * G u := by
      apply integral_congr_ae
      exact Eventually.of_forall fun u => by dsimp only; ring
    _ = (∫ u, F u * G u + F (u + h) * G (u + h) - F u * G (u + h)) -
        ∫ u, F (u + h) * G u := integral_sub ((hFG.add hs).sub hc) hd
    _ = ((∫ u, F u * G u + F (u + h) * G (u + h)) -
        ∫ u, F u * G (u + h)) - ∫ u, F (u + h) * G u :=
      congrArg (fun z => z - ∫ u, F (u + h) * G u) (integral_sub (hFG.add hs) hc)
    _ = _ := by rw [hea, hes, hec]; ring

/-- Large Gamma jumps are the diagonal row mass minus the two bounded convolution pairings. -/
theorem integral_halfLineGammaMixedJump_cutoff {δ : ℝ} (hδ : 0 < δ) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    (∫ h in Ioi δ, halfLineGammaMixedJump F G h) =
      (2 * ∫ h in Ioi δ, archLevyDensity h) * (∫ u, F u * G u) -
        (∫ h in Ioi δ, archLevyDensity h * ∫ u, F (u - h) * G u) -
        ∫ h in Ioi δ, archLevyDensity h * ∫ u, F (u + h) * G u := by
  have hb := integrableOn_cutoff_backward_pairing hδ hF hG
  have hf := integrableOn_cutoff_forward_pairing hδ hF hG
  have hm := (WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hδ).mul_const
    (2 * ∫ u, F u * G u)
  calc
    _ = ∫ h in Ioi δ, (archLevyDensity h * (2 * ∫ u, F u * G u) -
        archLevyDensity h * (∫ u, F (u - h) * G u)) -
        archLevyDensity h * (∫ u, F (u + h) * G u) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun h => by
        dsimp only
        rw [halfLineGammaMixedJump_eq_rows hF hG]
        ring
    _ = (∫ h in Ioi δ, archLevyDensity h * (2 * ∫ u, F u * G u) -
        archLevyDensity h * (∫ u, F (u - h) * G u)) -
        ∫ h in Ioi δ, archLevyDensity h * (∫ u, F (u + h) * G u) :=
      integral_sub (hm.sub hb) hf
    _ = ((∫ h in Ioi δ, archLevyDensity h * (2 * ∫ u, F u * G u)) -
        ∫ h in Ioi δ, archLevyDensity h * (∫ u, F (u - h) * G u)) -
        ∫ h in Ioi δ, archLevyDensity h * (∫ u, F (u + h) * G u) :=
      congrArg (fun z => z - ∫ h in Ioi δ, archLevyDensity h * (∫ u, F (u + h) * G u))
        (integral_sub hm hb)
    _ = _ := by rw [integral_mul_const]; ring

/-- The large-jump loss is controlled by the ordinary mass of the nonnegative test. -/
theorem halfLineGamma_largeJump_lower {δ : ℝ} (hδ : 0 < δ) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    (hG0 : ∀ u, 0 ≤ G u) :
    (2 * ∫ h in Ioi δ, archLevyDensity h) * (∫ u, F u * G u) -
      2 * Real.sqrt ((∫ h in Ioi δ, archLevyDensity h ^ 2) * ∫ u, F u ^ 2) * (∫ u, G u) ≤
      ∫ h in Ioi δ, halfLineGammaMixedJump F G h := by
  have hb := halfLineGamma_cutoff_backward_le hδ hF hG hG0
  have hf := halfLineGamma_cutoff_forward_le hδ hF hG hG0
  rw [integral_halfLineGammaMixedJump_cutoff hδ hF hG]
  linarith only [hb, hf]

#print axioms halfLineGamma_cutoff_backward_le
#print axioms halfLineGamma_cutoff_forward_le
#print axioms integral_halfLineGammaMixedJump_cutoff
#print axioms halfLineGamma_largeJump_lower
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
