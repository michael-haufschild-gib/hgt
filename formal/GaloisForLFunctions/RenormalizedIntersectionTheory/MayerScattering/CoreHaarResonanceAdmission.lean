import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.CoreCauchyAnalyticContinuation
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.WholeHaarHeckeWindowAdmission
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.GaussianCoreMellinSynthesis

/-!
# Physical Haar admission detects Mayer resonance

The actual Cauchy core has lower trace `−ζ(2s)`. Whole-Haar square
integrability therefore detects the Mayer fixed-state equation throughout
the upper open strip.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter Topology
open scoped FourierTransform
open GaloisForLFunctions RenormalizedIntersectionTheory MayerScatteringCore
open MayerCauchyMellinSymbol

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

private theorem cauchy_haar_mass {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ℝ, mayerCauchyHaarKernel s x) = (Gammaℝ (2 * s))⁻¹ := by
  have hw : 0 < (2 * s).re := by simp; linarith only [hs]
  have hsym : symbol (2 * s) 0 = 1 :=
    (cauchyKernel_hasMellin hw (u := 0) (by norm_num)
      (by simp; linarith only [hs])).2.symm.trans (cauchyKernel_mellin_zero hw).2
  have hf := fourier_mayerCauchyHaarKernel s hs 0
  have hz : 𝓕 (mayerCauchyHaarKernel s) 0 = ∫ x : ℝ, mayerCauchyHaarKernel s x := by
    rw [Real.fourier_real_eq]
    simp
  rw [hz] at hf
  simpa only [mul_zero, mayerCoreMellinFactor, Complex.ofReal_zero, zero_mul, hsym, one_div] using hf

private theorem remainder_tendsto_zero {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (him : 0 < s.im) :
    Tendsto (mayerFieldLogRemainder s) atTop (𝓝 0) := by
  obtain ⟨C, ε, hC, hε, hb⟩ := mayerFieldLogRemainder_exponential_bound hs hs1 him
  have he : Tendsto (fun x : ℝ => C * Real.exp (-(ε * x))) atTop (𝓝 0) := by
    have ht : Tendsto (fun x : ℝ => ε * x) atTop atTop :=
      tendsto_id.const_mul_atTop hε
    simpa only [mul_zero, Function.comp_apply] using
      (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ht)).const_mul C
  have he' : Tendsto (fun x : ℝ => C * Real.exp (-(ε * |x|))) atTop (𝓝 0) := by
    apply he.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [abs_of_nonneg hx]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun x => norm_nonneg _) hb he')

private theorem remainder_cauchy_tendsto_zero {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (him : 0 < s.im) :
    Tendsto (fun x : ℝ => ∫ z : ℝ,
      mayerCauchyHaarKernel s z * mayerFieldLogRemainder s (x - z)) atTop (𝓝 0) := by
  have hk := integrable_mayerCauchyHaarKernel s hs
  have hh := (mayerFieldLogRemainder_integrable_memLp hs hs1 him).1
  obtain ⟨C, ε, hC, hε, hb⟩ := mayerFieldLogRemainder_exponential_bound hs hs1 him
  have hbound (x : ℝ) : ‖mayerFieldLogRemainder s x‖ ≤ C :=
    (hb x).trans ((mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hε.le (abs_nonneg x)))) hC).trans_eq
        (mul_one C))
  have hlim (z : ℝ) : Tendsto (fun x : ℝ => mayerFieldLogRemainder s (x - z))
      atTop (𝓝 0) :=
    (remainder_tendsto_zero hs hs1 him).comp (by
      rw [tendsto_atTop]
      intro b
      filter_upwards [eventually_ge_atTop (b + z)] with x hx
      linarith only [hx])
  have hsub (x : ℝ) : MeasurePreserving (fun z : ℝ => x - z) volume volume := by
    have hn : MeasurePreserving (fun z : ℝ => -z) volume volume := ⟨measurable_neg, by simp⟩
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_left volume x).comp hn
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun z : ℝ => ‖mayerCauchyHaarKernel s z‖ * C)
    (F := fun x z : ℝ => mayerCauchyHaarKernel s z * mayerFieldLogRemainder s (x - z))
    (f := fun _ : ℝ => (0 : ℂ))
    (Eventually.of_forall fun x => hk.aestronglyMeasurable.mul
      (((hsub x).integrable_comp hh.aestronglyMeasurable).mpr hh).aestronglyMeasurable)
    (Eventually.of_forall fun x => Eventually.of_forall fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _))
    (hk.norm.mul_const C)
    (Eventually.of_forall fun z => by simpa only [mul_zero] using (hlim z).const_mul _)
  simpa only [integral_zero] using h

private theorem cauchy_cumulative_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun x : ℝ => ∫ z in Iic x, mayerCauchyHaarKernel s z) atTop
      (𝓝 ((Gammaℝ (2 * s))⁻¹)) := by
  have hk := integrable_mayerCauchyHaarKernel s hs
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun z : ℝ => ‖mayerCauchyHaarKernel s z‖)
    (F := fun x : ℝ => (Iic x).indicator (mayerCauchyHaarKernel s))
    (f := mayerCauchyHaarKernel s)
    (Eventually.of_forall fun x => (hk.indicator measurableSet_Iic).aestronglyMeasurable)
    (Eventually.of_forall fun x => Eventually.of_forall fun z => by
      by_cases hz : z ≤ x
      · rw [indicator_of_mem (show z ∈ Iic x from hz)]
      · rw [indicator_of_notMem (show z ∉ Iic x from hz), norm_zero]; exact norm_nonneg _)
    hk.norm
    (Eventually.of_forall fun z => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop z] with x hx
      rw [indicator_of_mem (show z ∈ Iic x from hx)])
  simpa only [integral_indicator measurableSet_Iic, cauchy_haar_mass hs] using h

/-- The lower trace of the literal PM core is exactly its negative zeta charge,
including nonresonant parameters. -/
theorem mayerPeriodCore_lower_trace {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (him : 0 < s.im) :
    Tendsto (mayerPeriodCore s) (𝓝[>] 0) (𝓝 (-riemannZeta (2 * s))) := by
  have hg : Gammaℝ (2 * s) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith only [hs])
  have h := (remainder_cauchy_tendsto_zero hs hs1 him).sub
    ((cauchy_cumulative_tendsto hs).const_mul (Gammaℝ (2 * s) * riemannZeta (2 * s)))
  have he : 0 - Gammaℝ (2 * s) * riemannZeta (2 * s) * (Gammaℝ (2 * s))⁻¹ =
      -riemannZeta (2 * s) := by
    rw [mul_right_comm (Gammaℝ (2 * s)), mul_inv_cancel₀ hg, one_mul, zero_sub]
  rw [he] at h
  have hl : Tendsto (fun x : ℝ => mayerPeriodCore s (Real.exp (-x))) atTop
      (𝓝 (-riemannZeta (2 * s))) := by
    apply h.congr
    intro x
    exact (mayerPeriodCore_log_boundary_decomposition hs hs1 him x).symm
  have ht : Tendsto (fun a : ℝ => -Real.log a) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [Function.comp_def, Real.log_inv] using
      Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  apply (hl.comp ht).congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  simp only [Function.comp_apply, neg_neg, Real.exp_log ha]

/-- The actual core has finite whole-Haar square energy exactly at zeta zeros. -/
theorem mayerPeriodCore_finite_whole_haar_iff_zeta_zero {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (him : 0 < s.im) :
    IntegrableOn (fun a : ℝ => ‖mayerPeriodCore s a‖ ^ 2 / a) (Ioi 0) ↔
      riemannZeta (2 * s) = 0 := by
  constructor
  · intro hi
    have hz := haarSquareIntegrable_zero_trace (mayerPeriodCore_lower_trace hs hs1 him)
      zero_lt_one (hi.mono_set (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun a ha => ha.1))
    exact neg_eq_zero.mp hz
  · intro hz
    have hr : s ∈ upperMayerResonances :=
      ⟨him, (isMayerScatteringResonance_iff_zeta_zero hs hs1).mpr hz⟩
    exact upperMayerCore_finite_whole_haar_energy ⟨s, hr⟩

/-- A physical square-integrability condition detects the actual Mayer fixed-state
resonance on the upper open strip. -/
theorem mayerPeriodCore_finite_whole_haar_iff_resonance {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (him : 0 < s.im) :
    IntegrableOn (fun a : ℝ => ‖mayerPeriodCore s a‖ ^ 2 / a) (Ioi 0) ↔
      IsMayerScatteringResonance s :=
  (mayerPeriodCore_finite_whole_haar_iff_zeta_zero hs hs1 him).trans
    (isMayerScatteringResonance_iff_zeta_zero hs hs1).symm

#print axioms mayerPeriodCore_lower_trace
#print axioms mayerPeriodCore_finite_whole_haar_iff_zeta_zero
#print axioms mayerPeriodCore_finite_whole_haar_iff_resonance

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
