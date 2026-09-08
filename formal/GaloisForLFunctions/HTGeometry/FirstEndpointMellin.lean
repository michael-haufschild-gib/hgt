import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! A source-faithful first endpoint subtraction for a frequency-dependent Mellin integral. -/
namespace GaloisForLFunctions.HTGeometry
open Complex Filter Topology MeasureTheory Set Metric
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def firstEndpointMellinRemainder (F : ℂ → ℝ → ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  ∫ t in Ioc (0:ℝ) b, (t:ℂ)^w*(F w t-F w 0)

def firstEndpointMellin (F : ℂ → ℝ → ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  F w 0*(b:ℂ)^(w+1)/(w+1)+firstEndpointMellinRemainder F b w

/-- The actual endpoint difference gains one full power of absolute integrability. -/
theorem firstEndpointMellinRemainder_integrable {F : ℂ → ℝ → ℂ} {w : ℂ} {b C : ℝ}
    (hb : 0 ≤ b) (hw : -2 < w.re) (hm : Measurable (F w))
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-F w 0‖ ≤ C*t) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^w*(F w t-F w 0)) (Ioc 0 b) := by
  have hp : IntegrableOn (fun t : ℝ => t^(w.re+1)) (Ioc 0 b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  refine (hp.const_mul C).mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht.1,Real.rpow_add ht.1,Real.rpow_one]
  calc
    _ ≤ t^w.re*(C*t) := mul_le_mul_of_nonneg_left (hC t ht) (Real.rpow_nonneg ht.1.le _)
    _ = _ := by ring

/-- In the original chamber, the restored endpoint term equals the genuine integral. -/
theorem firstEndpointMellin_eq_integral {F : ℂ → ℝ → ℂ} {w : ℂ} {b C : ℝ}
    (hb : 0 ≤ b) (hw : -1 < w.re) (hm : Measurable (F w))
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖F w t-F w 0‖ ≤ C*t) :
    firstEndpointMellin F b w = ∫ t in Ioc (0:ℝ) b, (t:ℂ)^w*F w t := by
  have hr := firstEndpointMellinRemainder_integrable hb (by linarith : -2 < w.re) hm hC
  have hp : IntegrableOn (fun t : ℝ => (t:ℂ)^w) (Ioc 0 b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp (intervalIntegral.intervalIntegrable_cpow' hw)
  have he : (∫ t in Ioc (0:ℝ) b, (t:ℂ)^w*F w t) =
      (∫ t in Ioc (0:ℝ) b, (t:ℂ)^w*F w 0)+firstEndpointMellinRemainder F b w := by
    rw [firstEndpointMellinRemainder,← integral_add (hp.mul_const _) hr]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    ring
  have hv : (∫ t in Ioc (0:ℝ) b, (t:ℂ)^w) = (b:ℂ)^(w+1)/(w+1) := by
    rw [← intervalIntegral.integral_of_le hb,integral_cpow (Or.inl hw),Complex.ofReal_zero]
    have hn : w+1 ≠ 0 := by intro h; have hh := congrArg Complex.re h; simp at hh; linarith
    rw [Complex.zero_cpow hn,sub_zero]
  rw [he,integral_mul_const,hv,firstEndpointMellin]
  ring

/-- Uniform first-remainder bounds prove frequency holomorphy after endpoint subtraction. -/
theorem firstEndpointMellinRemainder_differentiableAt
    {F : ℂ → ℝ → ℂ} {w : ℂ} {b R C β : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hR : 0 < R) (hC0 : 0 ≤ C) (hβ : -2 < β)
    (hreal : ∀ u ∈ ball w R, β ≤ u.re)
    (hm : ∀ u ∈ ball w R, Measurable (F u))
    (hd : ∀ t ∈ Icc (0:ℝ) b, ∀ u ∈ ball w R, DifferentiableAt ℂ (fun v => F v t) u)
    (hC : ∀ u ∈ ball w R, ∀ t ∈ Ioc (0:ℝ) b, ‖F u t-F u 0‖ ≤ C*t) :
    DifferentiableAt ℂ (firstEndpointMellinRemainder F b) w := by
  let G (u : ℂ) : ℝ → ℂ := (Ioc (0:ℝ) b).indicator (fun t => (t:ℂ)^u*(F u t-F u 0))
  let bound : ℝ → ℝ := (Ioc (0:ℝ) b).indicator (fun t => C*t^(β+1))
  have hmeas (u : ℂ) (hu : u ∈ ball w R) : AEStronglyMeasurable (G u) volume := by
    have hFu := hm u hu
    exact ((show Measurable (fun t : ℝ => (t:ℂ)^u*(F u t-F u 0)) by fun_prop).indicator
      measurableSet_Ioc).aestronglyMeasurable
  have hdiff (t : ℝ) : DifferentiableOn ℂ (fun u => G u t) (ball w R) := by
    intro u hu
    by_cases ht : t ∈ Ioc (0:ℝ) b
    · simp only [G,indicator_of_mem ht]
      exact ((differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt ht.1)))).mul
        ((hd t ⟨ht.1.le,ht.2⟩ u hu).sub (hd 0 ⟨le_rfl,hb⟩ u hu))).differentiableWithinAt
    · simp only [G,indicator_of_notMem ht]
      fun_prop
  have hbound (t : ℝ) (u : ℂ) (hu : u ∈ ball w R) : ‖G u t‖ ≤ bound t := by
    by_cases ht : t ∈ Ioc (0:ℝ) b
    · simp only [G,bound,indicator_of_mem ht,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
      calc
        _ ≤ t^u.re*(C*t) := mul_le_mul_of_nonneg_left (hC u hu t ht) (Real.rpow_nonneg ht.1.le _)
        _ ≤ t^β*(C*t) := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge ht.1 (ht.2.trans hb1) (hreal u hu)) (mul_nonneg hC0 ht.1.le)
        _ = C*t^(β+1) := by rw [Real.rpow_add ht.1,Real.rpow_one]; ring
    · simp only [G,bound,indicator_of_notMem ht,norm_zero,le_refl]
  have hi : Integrable bound volume := by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < β+1))).const_mul C
  have hg := differentiableAt_integral_of_cauchy_dominated hR hmeas hdiff hbound hi
  change DifferentiableAt ℂ (fun u => ∫ t in Ioc (0:ℝ) b, (t:ℂ)^u*(F u t-F u 0)) w
  simpa only [G,integral_indicator measurableSet_Ioc] using hg

end
end GaloisForLFunctions.HTGeometry
