import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.SoftLogarithmicTrialScaling
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Compact profiles in the soft logarithmic trial domain

Compact support supplies absolute integrability and exponential square
moments. Finite positive Fourier logarithmic energy then gives the full
trial domain, using the local integrability of the logarithmic singularity.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open _root_.RHTower
open scoped FourierTransform
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open HTGeometry CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri


/-- Compact half-line L² profiles with finite positive logarithmic energy are trials.
Compact support supplies L¹ and every required exponential moment; the
local Fourier bound controls the negative logarithmic singularity. -/
theorem softLogarithmicHalfLineDomain_of_compact_positiveLogarithm
    {F : ℝ → ℝ} (hmeas : Measurable F) (hsq : Integrable (fun u => F u ^ 2))
    {H : ℝ}
    (hleft : ∀ u, u ≤ -H → F u = 0) (hright : ∀ u, 0 ≤ u → F u = 0)
    (hpositive : Integrable (fun ξ : ℝ => max (Real.log |ξ|) 0 * ‖𝓕 (cx F) ξ‖ ^ 2)) :
    SoftLogarithmicHalfLineDomain F := by
  have hF2 : MemLp F 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).mpr
    simpa only [Real.norm_eq_abs, sq_abs] using hsq
  have hsupport : Function.support F ⊆ Icc (-H) 0 := by
    intro u hu
    by_contra hn
    by_cases hl : -H ≤ u
    · have hp : 0 < u := lt_of_not_ge fun h => hn ⟨hl, h⟩
      exact hu (hright u hp.le)
    · exact hu (hleft u (lt_of_not_ge hl).le)
  have hF1 : Integrable F := by
    have hi : IntegrableOn F (Icc (-H) 0) :=
      (hF2.locallyIntegrable (by norm_num)).integrableOn_isCompact isCompact_Icc
    exact (integrableOn_iff_integrable_of_support_subset hsupport).mp hi
  have hc2 : MemLp (cx F) 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm (hF1.ofReal (𝕜 := ℂ)).aestronglyMeasurable).mpr
    simpa only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hsq
  refine ⟨hmeas, hF1, hsq, hright, ⟨1, zero_lt_one, ?_⟩, ?_⟩
  · have hm : Measurable (fun u => F u ^ 2 * Real.exp (-(1 * u))) := by fun_prop
    apply (hsq.const_mul (Real.exp H)).mono' hm.aestronglyMeasurable
    exact Eventually.of_forall fun u => by
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
      by_cases hu : u ≤ -H
      · rw [hleft u hu, zero_pow two_ne_zero, zero_mul, mul_zero]
      · have he : Real.exp (-(1 * u)) ≤ Real.exp H :=
          Real.exp_le_exp.mpr (by linarith only [lt_of_not_ge hu])
        simpa only [mul_comm (F u ^ 2)] using mul_le_mul_of_nonneg_left he (sq_nonneg (F u))
  · apply integrable_log_fourier_sq_of_symbol (hF1.ofReal (𝕜 := ℂ)) hc2
      (σ := fun ξ : ℝ => max (Real.log |ξ|) 0) (C := 0) ?_ hpositive
    intro ξ hξ
    have hl := Real.log_nonneg hξ
    simp only [max_eq_left hl, abs_of_nonneg hl, zero_add, le_refl]

#print axioms softLogarithmicHalfLineDomain_of_compact_positiveLogarithm
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

