import GaloisForLFunctions.HTGeometry.FourierTailSup
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Absolute logarithmic Fourier energy

The L¹ Fourier bound controls the integrable logarithmic singularity at
zero. On the complement, comparison with a logarithmically growing symbol
transfers absolute integrability in both directions.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped FourierTransform
namespace GaloisForLFunctions.HTGeometry

/-- The Fourier L¹ bound makes the logarithmic singularity at zero integrable. -/
theorem integrableOn_abs_log_fourier_sq {f : ℝ → ℂ} (hf : Integrable f) :
    IntegrableOn (fun ξ => |Real.log (|ξ|)| * ‖𝓕 f ξ‖ ^ 2) (Ioo (-1) 1) := by
  have hl : IntegrableOn Real.log (Ioo (-1) 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (intervalIntegral.intervalIntegrable_log' (a := -1) (b := 1))).mono_set Ioo_subset_Ioc_self
  have hlabs : IntegrableOn (fun ξ : ℝ => |Real.log (|ξ|)|) (Ioo (-1) 1) := by
    change Integrable (fun ξ : ℝ => |Real.log (|ξ|)|) (volume.restrict (Ioo (-1) 1))
    simpa only [Real.log_abs] using hl.abs
  have hFourier := RHTower.continuous_fourier_of_integrable hf
  have hm : Measurable (fun ξ : ℝ => |Real.log (|ξ|)| * ‖𝓕 f ξ‖ ^ 2) := by fun_prop
  apply (hlabs.mul_const ((∫ u, ‖f u‖) ^ 2)).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_fourierIntegral_le_mass f ξ) 2) (abs_nonneg _)

/-- A logarithmic upper bound gives symbol integrability on the absolute logarithmic domain. -/
theorem integrable_symbol_fourier_sq_of_log {f : ℝ → ℂ} (hf1 : Integrable f)
    (hf2 : MemLp f 2 volume) {σ : ℝ → ℝ} (hσ : Continuous σ) {C : ℝ}
    (hbound : ∀ ξ, |σ ξ| ≤ C + |Real.log (|ξ|)|)
    (hlog : Integrable (fun ξ => |Real.log (|ξ|)| * ‖𝓕 f ξ‖ ^ 2)) :
    Integrable (fun ξ => σ ξ * ‖𝓕 f ξ‖ ^ 2) := by
  have hm := RHTower.integrable_norm_sq_fourier hf1 hf2
  have hFourier := RHTower.continuous_fourier_of_integrable hf1
  have hmeas : Measurable (fun ξ => σ ξ * ‖𝓕 f ξ‖ ^ 2) := by fun_prop
  apply ((hm.const_mul C).add hlog).mono' hmeas.aestronglyMeasurable
  exact Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖𝓕 f ξ‖)]
    have h := mul_le_mul_of_nonneg_right (hbound ξ) (sq_nonneg ‖𝓕 f ξ‖)
    simpa only [add_mul, Pi.add_apply] using h

/-- High-frequency symbol control and local L¹ Fourier bounds recover absolute logarithmic energy. -/
theorem integrable_log_fourier_sq_of_symbol {f : ℝ → ℂ} (hf1 : Integrable f)
    (hf2 : MemLp f 2 volume) {σ : ℝ → ℝ} {C : ℝ}
    (hbound : ∀ ξ, 1 ≤ |ξ| → |Real.log (|ξ|)| ≤ C + |σ ξ|)
    (hσ : Integrable (fun ξ => σ ξ * ‖𝓕 f ξ‖ ^ 2)) :
    Integrable (fun ξ => |Real.log (|ξ|)| * ‖𝓕 f ξ‖ ^ 2) := by
  have hm := RHTower.integrable_norm_sq_fourier hf1 hf2
  have hFourier := RHTower.continuous_fourier_of_integrable hf1
  have hmeas : Measurable (fun ξ => |Real.log (|ξ|)| * ‖𝓕 f ξ‖ ^ 2) := by fun_prop
  have hσabs : Integrable (fun ξ => |σ ξ| * ‖𝓕 f ξ‖ ^ 2) := by
    apply hσ.abs.congr
    exact Eventually.of_forall fun ξ => by
      change |σ ξ * ‖𝓕 f ξ‖ ^ 2| = _
      rw [abs_mul, abs_of_nonneg (sq_nonneg ‖𝓕 f ξ‖)]
  have hfar : IntegrableOn (fun ξ => |Real.log (|ξ|)| * ‖𝓕 f ξ‖ ^ 2) (Ioo (-1) 1)ᶜ := by
    apply ((hm.const_mul C).add hσabs).integrableOn.mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo.compl] with ξ hξ
    have hξ1 : 1 ≤ |ξ| := by
      by_contra hh
      exact hξ (abs_lt.mp (lt_of_not_ge hh))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    have h := mul_le_mul_of_nonneg_right (hbound ξ hξ1) (sq_nonneg ‖𝓕 f ξ‖)
    simpa only [add_mul, Pi.add_apply] using h
  rw [← integrableOn_univ, ← union_compl_self (Ioo (-1 : ℝ) 1)]
  exact (integrableOn_abs_log_fourier_sq hf1).union hfar

#print axioms integrableOn_abs_log_fourier_sq
#print axioms integrable_symbol_fourier_sq_of_log
#print axioms integrable_log_fourier_sq_of_symbol
end GaloisForLFunctions.HTGeometry
