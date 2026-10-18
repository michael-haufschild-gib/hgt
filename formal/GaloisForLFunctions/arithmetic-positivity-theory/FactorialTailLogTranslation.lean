import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailTranslation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Integrating the literal tail's two translation regimes produces a logarithmic
energy budget. The endpoint at zero is controlled by the linear displacement
bound, so finiteness is proved before using the integral. -/

open MeasureTheory Set

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- The logarithmic translation energy of the actual weighted factorial tail. -/
def factorialTailLogTranslationEnergy (n : ℕ) (σ : ℝ) : ℝ :=
  ∫ h : ℝ in Ioc 0 1, factorialTailTranslationEnergy n σ h/h

/-- The linear increment bound pays for the apparent singularity of `dh/h`. -/
theorem factorialTailTranslationRatio_integrable (n : ℕ) (σ : FactorialSamplingAbscissa) :
    IntegrableOn (fun h : ℝ => factorialTailTranslationEnergy n σ h/h) (Ioc 0 1) := by
  have hi : IntegrableOn (fun _ : ℝ => factorialTailTranslationConstant) (Ioc 0 1) :=
    integrableOn_const (by simp)
  apply hi.mono'
    ((factorialTailTranslationEnergy_measurable n σ).div measurable_id).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
  change ‖factorialTailTranslationEnergy n σ h/h‖ ≤ factorialTailTranslationConstant
  rw [Real.norm_eq_abs,abs_of_nonneg
    (div_nonneg (factorialTailTranslationEnergy_nonneg n σ h) hh.1.le)]
  exact (div_le_iff₀ hh.1).mpr
    (factorialTailTranslationEnergy_le_linear n σ ⟨h,hh.1.le,hh.2⟩)

theorem factorialTailLogTranslationEnergy_nonneg (n : ℕ) (σ : ℝ) :
    0 ≤ factorialTailLogTranslationEnergy n σ := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
  exact div_nonneg (factorialTailTranslationEnergy_nonneg n σ h) hh.1.le

/-- A uniform logarithmic budget, with the split exactly at the arithmetic scale. -/
theorem factorialTailLogTranslationEnergy_le (n : ℕ) (σ : FactorialSamplingAbscissa) :
    factorialTailLogTranslationEnergy n σ ≤
      factorialTailTranslationConstant*(1+Real.log ((n+1 : ℕ) : ℝ))/((n+1 : ℕ) : ℝ) := by
  let a : ℝ := 1/((n+1 : ℕ) : ℝ)
  let C : ℝ := factorialTailTranslationConstant
  let f : ℝ → ℝ := fun h => factorialTailTranslationEnergy n σ h/h
  have hN : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ n+1 by omega)
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := (div_le_one hN).mpr hN1
  have hC : 0 ≤ C := factorialTailTranslationConstant_pos.le
  have hi : IntegrableOn f (Ioc 0 1) := factorialTailTranslationRatio_integrable n σ
  have hlo : IntegrableOn f (Ioc 0 a) := hi.mono_set
    (fun _ hh => ⟨hh.1,hh.2.trans ha1⟩)
  have hhi : IntegrableOn f (Ioc a 1) := hi.mono_set
    (fun _ hh => ⟨ha0.trans hh.1,hh.2⟩)
  have hconst : IntegrableOn (fun _ : ℝ => C) (Ioc 0 a) := integrableOn_const (by simp)
  have hlower : (∫ h : ℝ in Ioc 0 a, f h) ≤ C*a := by
    calc
      _ ≤ ∫ _ : ℝ in Ioc 0 a, C := by
        apply setIntegral_mono_on hlo hconst measurableSet_Ioc
        intro h hh
        exact (div_le_iff₀ hh.1).mpr
          (factorialTailTranslationEnergy_le_linear n σ ⟨h,hh.1.le,hh.2.trans ha1⟩)
      _ = _ := by
        rw [setIntegral_const,Real.volume_real_Ioc_of_le ha0.le,smul_eq_mul]
        ring
  have hcontinuous : ContinuousOn (fun h : ℝ => 1/h) (Icc a 1) :=
    continuousOn_const.div continuousOn_id (fun _ hh => ne_of_gt (ha0.trans_le hh.1))
  have hinv : IntegrableOn (fun h : ℝ => 1/h) (Ioc a 1) :=
    hcontinuous.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hinva : 1/a = ((n+1 : ℕ) : ℝ) := by
    dsimp only [a]
    simp only [one_div,inv_inv]
  have hupper : (∫ h : ℝ in Ioc a 1, f h) ≤ C*a*Real.log ((n+1 : ℕ) : ℝ) := by
    calc
      _ ≤ ∫ h : ℝ in Ioc a 1, C*a*(1/h) := by
        apply setIntegral_mono_on hhi (hinv.const_mul _) measurableSet_Ioc
        intro h hh
        have hh0 : 0 < h := ha0.trans hh.1
        have hD := factorialTailTranslationEnergy_le_min n σ ⟨h,hh0.le,hh.2⟩
        change factorialTailTranslationEnergy n σ h ≤ C*min a h at hD
        rw [min_eq_left hh.1.le] at hD
        calc
          f h ≤ (C*a)/h := div_le_div_of_nonneg_right hD hh0.le
          _ = _ := by ring
      _ = _ := by
        rw [integral_const_mul,← intervalIntegral.integral_of_le ha1,
          integral_one_div_of_pos ha0 (by norm_num),hinva]
  have hsplit : (∫ h : ℝ in Ioc 0 1, f h) =
      (∫ h : ℝ in Ioc 0 a, f h)+(∫ h : ℝ in Ioc a 1, f h) := by
    rw [← Ioc_union_Ioc_eq_Ioc ha0.le ha1]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hlo hhi
  calc
    factorialTailLogTranslationEnergy n σ =
        (∫ h : ℝ in Ioc 0 a, f h)+(∫ h : ℝ in Ioc a 1, f h) := hsplit
    _ ≤ C*a+C*a*Real.log ((n+1 : ℕ) : ℝ) := add_le_add hlower hupper
    _ = _ := by dsimp only [a,C]; ring

end
end GaloisForLFunctions.ArithmeticPositivityTheory
