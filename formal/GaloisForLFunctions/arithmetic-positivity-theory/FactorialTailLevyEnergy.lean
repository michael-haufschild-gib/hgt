import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailLogTranslation
import GaloisForLFunctions.RHTower.WeilLevyHarmonicDoublingPairCoupling
import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover

/-! The actual tail's arithmetic-scale translation bound controls the complete
positive Gamma jump energy, including its singularity at zero. -/

open MeasureTheory Set
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- The fixed, finite mass of the Gamma jump kernel beyond unit displacement. -/
def factorialTailLevyFarMass : ℝ := ∫ h : ℝ in Ioi 1, archLevyDensity h

private theorem levy_far_mass_nonneg : 0 ≤ factorialTailLevyFarMass := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact (archLevyDensity_pos (lt_trans (by norm_num : (0 : ℝ) < 1) hh)).le

/-- A constant independent of the arithmetic scale and Mellin weight. -/
def factorialTailLevyConstant : ℝ :=
  factorialTailTranslationConstant+384*factorialTailLevyFarMass

theorem factorialTailLevyConstant_pos : 0 < factorialTailLevyConstant :=
  add_pos_of_pos_of_nonneg factorialTailTranslationConstant_pos
    (mul_nonneg (by norm_num) levy_far_mass_nonneg)

private theorem levy_near_le {h : ℝ} (hh : h ∈ Ioc (0 : ℝ) 1) :
    archLevyDensity h ≤ 1/h := by
  have hk := WeilLevyHarmonicDoubling.two_mul_archLevyDensity_le_inv_add_half hh.1
  have hi : (1 : ℝ) ≤ 1/h := (le_div_iff₀ hh.1).mpr (by simpa using hh.2)
  linarith

private theorem levy_near_integrable (n : ℕ) (σ : FactorialSamplingAbscissa) :
    IntegrableOn (fun h : ℝ => archLevyDensity h*factorialTailTranslationEnergy n σ h)
      (Ioc 0 1) := by
  apply (factorialTailTranslationRatio_integrable n σ).mono'
    ((measurable_archLevyDensity.mul
      (factorialTailTranslationEnergy_measurable n σ)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
  change ‖archLevyDensity h*factorialTailTranslationEnergy n σ h‖ ≤
    factorialTailTranslationEnergy n σ h/h
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (archLevyDensity_pos hh.1).le
    (factorialTailTranslationEnergy_nonneg n σ h))]
  calc
    _ ≤ (1/h)*factorialTailTranslationEnergy n σ h :=
      mul_le_mul_of_nonneg_right (levy_near_le hh)
        (factorialTailTranslationEnergy_nonneg n σ h)
    _ = _ := by ring

private theorem levy_far_integrable (n : ℕ) (σ : FactorialSamplingAbscissa) :
    IntegrableOn (fun h : ℝ => archLevyDensity h*factorialTailTranslationEnergy n σ h)
      (Ioi 1) := by
  apply ((WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi
    (by norm_num : (0 : ℝ) < 1)).mul_const (384/((n+1 : ℕ) : ℝ))).mono'
    ((measurable_archLevyDensity.mul
      (factorialTailTranslationEnergy_measurable n σ)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  have hk := (archLevyDensity_pos (lt_trans (by norm_num : (0 : ℝ) < 1) hh)).le
  change ‖archLevyDensity h*factorialTailTranslationEnergy n σ h‖ ≤
    archLevyDensity h*(384/((n+1 : ℕ) : ℝ))
  rw [Real.norm_eq_abs,abs_of_nonneg
    (mul_nonneg hk (factorialTailTranslationEnergy_nonneg n σ h))]
  exact mul_le_mul_of_nonneg_left (factorialTailTranslationEnergy_le_mass n σ h) hk

/-- Integrability is established by actual source bounds before taking the energy. -/
theorem factorialTailLevy_integrable (n : ℕ) (σ : FactorialSamplingAbscissa) :
    IntegrableOn (fun h : ℝ => archLevyDensity h*factorialTailTranslationEnergy n σ h)
      (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  exact (levy_near_integrable n σ).union (levy_far_integrable n σ)

/-- The positive Gamma jump energy of the literal weighted source. -/
def factorialTailLevyEnergy (n : ℕ) (σ : ℝ) : ℝ :=
  ∫ h : ℝ in Ioi 0, archLevyDensity h*factorialTailTranslationEnergy n σ h

theorem factorialTailLevyEnergy_nonneg (n : ℕ) (σ : ℝ) :
    0 ≤ factorialTailLevyEnergy n σ := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact mul_nonneg (archLevyDensity_pos hh).le (factorialTailTranslationEnergy_nonneg n σ h)

/-- Both displacement ranges retain the logarithmic arithmetic-scale budget. -/
theorem factorialTailLevyEnergy_le (n : ℕ) (σ : FactorialSamplingAbscissa) :
    factorialTailLevyEnergy n σ ≤
      factorialTailLevyConstant*(1+Real.log ((n+1 : ℕ) : ℝ))/((n+1 : ℕ) : ℝ) := by
  let f : ℝ → ℝ := fun h => archLevyDensity h*factorialTailTranslationEnergy n σ h
  have hN : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hlog : 0 ≤ Real.log ((n+1 : ℕ) : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ n+1 by omega))
  have hnear : (∫ h : ℝ in Ioc 0 1, f h) ≤ factorialTailLogTranslationEnergy n σ := by
    apply setIntegral_mono_on (levy_near_integrable n σ)
      (factorialTailTranslationRatio_integrable n σ) measurableSet_Ioc
    intro h hh
    calc
      f h ≤ (1/h)*factorialTailTranslationEnergy n σ h :=
        mul_le_mul_of_nonneg_right (levy_near_le hh)
          (factorialTailTranslationEnergy_nonneg n σ h)
      _ = _ := by ring
  have hfar : (∫ h : ℝ in Ioi 1, f h) ≤
      384*factorialTailLevyFarMass/((n+1 : ℕ) : ℝ) := by
    calc
      _ ≤ ∫ h : ℝ in Ioi 1, archLevyDensity h*(384/((n+1 : ℕ) : ℝ)) := by
        apply setIntegral_mono_on (levy_far_integrable n σ)
          ((WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi
            (by norm_num : (0 : ℝ) < 1)).mul_const _) measurableSet_Ioi
        intro h hh
        exact mul_le_mul_of_nonneg_left (factorialTailTranslationEnergy_le_mass n σ h)
          (archLevyDensity_pos (lt_trans (by norm_num : (0 : ℝ) < 1) hh)).le
      _ = _ := by
        rw [integral_mul_const]
        change factorialTailLevyFarMass*(384/((n+1 : ℕ) : ℝ)) = _
        ring
  have hsplit : factorialTailLevyEnergy n σ =
      (∫ h : ℝ in Ioc 0 1, f h)+(∫ h : ℝ in Ioi 1, f h) := by
    unfold factorialTailLevyEnergy
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
    exact setIntegral_union (disjoint_left.mpr (fun h hh0 hh1 => not_lt_of_ge hh0.2 hh1))
      measurableSet_Ioi (levy_near_integrable n σ) (levy_far_integrable n σ)
  have hfar' : 384*factorialTailLevyFarMass/((n+1 : ℕ) : ℝ) ≤
      384*factorialTailLevyFarMass*(1+Real.log ((n+1 : ℕ) : ℝ))/((n+1 : ℕ) : ℝ) := by
    apply div_le_div_of_nonneg_right _ hN.le
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 384)
      levy_far_mass_nonneg) hlog
    nlinarith only [this]
  calc
    _ ≤ factorialTailLogTranslationEnergy n σ+
        384*factorialTailLevyFarMass/((n+1 : ℕ) : ℝ) := by
      rw [hsplit]
      exact add_le_add hnear hfar
    _ ≤ factorialTailTranslationConstant*(1+Real.log ((n+1 : ℕ) : ℝ))/((n+1 : ℕ) : ℝ)+
        384*factorialTailLevyFarMass*(1+Real.log ((n+1 : ℕ) : ℝ))/((n+1 : ℕ) : ℝ) :=
      add_le_add (factorialTailLogTranslationEnergy_le n σ) hfar'
    _ = _ := by unfold factorialTailLevyConstant; ring

end
end GaloisForLFunctions.ArithmeticPositivityTheory
