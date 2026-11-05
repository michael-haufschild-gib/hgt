import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicCausalKernelIsAPositiveProbabilityDensity
import GaloisForLFunctions.RHTower.StripSourceHardyTransfer

/-!
# The Fourier multiplier of the logarithmic causal density

The literal Laplace integral is holomorphic on the right half-plane. Analytic
uniqueness and dominated boundary convergence identify its Fourier transform
with the reciprocal factor at every frequency. The exact boundary modulus
recovers the positive logarithmic symbol, including at zero.
-/

open MeasureTheory Set Filter Topology Complex Metric
open scoped FourierTransform
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

/-- The explicit zero extension is measurable despite its singular endpoint. -/
theorem measurable_logarithmicCausalKernel : Measurable logarithmicCausalKernel := by
  classical
  have hm := continuousOn_logarithmicCausalKernel.measurable_piecewise
    (g := fun _ => (0 : ℝ)) continuousOn_const measurableSet_Ioi
  have he : (Ioi (0 : ℝ)).piecewise logarithmicCausalKernel (fun _ => 0) =
      logarithmicCausalKernel := by
    funext x
    by_cases hx : 0 < x
    · exact piecewise_eq_of_mem _ _ _ hx
    · have hxm : x ∉ Ioi (0 : ℝ) := hx
      rw [piecewise_eq_of_notMem _ _ _ hxm, logarithmicCausalKernel_of_nonpos (le_of_not_gt hx)]
  rwa [he] at hm

/-- The literal complex Laplace integral of the positive causal density. -/
def logarithmicCausalLaplace (z : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-z * (x : ℂ)) * (logarithmicCausalKernel x : ℂ)

theorem integrable_complex_logarithmicCausalKernel :
    Integrable (fun x : ℝ => (logarithmicCausalKernel x : ℂ)) :=
  Complex.ofRealCLM.integrable_comp logarithmicCausalKernel_mass_one.1

private theorem aestronglyMeasurable_logarithmicCausalLaplace_integrand (z : ℂ) :
    AEStronglyMeasurable (fun x : ℝ => Complex.exp (-z * (x : ℂ)) *
      (logarithmicCausalKernel x : ℂ)) := by
  have hc : Continuous (fun x : ℝ => Complex.exp (-z * (x : ℂ))) := by fun_prop
  exact hc.aestronglyMeasurable.mul integrable_complex_logarithmicCausalKernel.aestronglyMeasurable

private theorem norm_logarithmicCausalLaplace_integrand_le {z : ℂ} (hz : 0 ≤ z.re) (x : ℝ) :
    ‖Complex.exp (-z * (x : ℂ)) * (logarithmicCausalKernel x : ℂ)‖ ≤ logarithmicCausalKernel x := by
  by_cases hx : 0 < x
  · have he : ‖Complex.exp (-z * (x : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      apply Real.exp_le_one_iff.mpr
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) hx.le
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (logarithmicCausalKernel_nonneg x)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he (logarithmicCausalKernel_nonneg x)
  · rw [logarithmicCausalKernel_of_nonpos (le_of_not_gt hx), Complex.ofReal_zero, mul_zero, norm_zero]

theorem integrable_logarithmicCausalLaplace_integrand {z : ℂ} (hz : 0 ≤ z.re) :
    Integrable (fun x : ℝ => Complex.exp (-z * (x : ℂ)) * (logarithmicCausalKernel x : ℂ)) :=
  logarithmicCausalKernel_mass_one.1.mono'
    (aestronglyMeasurable_logarithmicCausalLaplace_integrand z)
    (Eventually.of_forall (norm_logarithmicCausalLaplace_integrand_le hz))

/-- Integrability of the actual density supplies a uniform local holomorphic majorant. -/
theorem differentiableOn_logarithmicCausalLaplace :
    DifferentiableOn ℂ logarithmicCausalLaplace {z : ℂ | 0 < z.re} := by
  intro z hz
  change 0 < z.re at hz
  have hR : 0 < z.re / 2 := by linarith only [hz]
  have hr : ∀ w ∈ ball z (z.re / 2), 0 ≤ w.re := by
    intro w hw
    have hd : ‖w - z‖ < z.re / 2 := by simpa only [mem_ball, dist_eq_norm] using hw
    have ha := Complex.abs_re_le_norm (w - z)
    have hn := neg_le_abs ((w - z).re)
    rw [Complex.sub_re] at ha hn
    linarith only [hd, ha, hn, hz]
  have hdiff : DifferentiableAt ℂ logarithmicCausalLaplace z := by
    apply HTGeometry.differentiableAt_integral_of_cauchy_dominated
      (bound := logarithmicCausalKernel) hR
    · intro w _
      exact aestronglyMeasurable_logarithmicCausalLaplace_integrand w
    · intro x w _
      have hc : DifferentiableAt ℂ (fun v : ℂ =>
          Complex.exp (-v * (x : ℂ)) * (logarithmicCausalKernel x : ℂ)) w := by fun_prop
      exact hc.differentiableWithinAt
    · intro x w hw
      exact norm_logarithmicCausalLaplace_integrand_le (hr w hw) x
    · exact logarithmicCausalKernel_mass_one.1
  exact hdiff.differentiableWithinAt

/-- The complex integral agrees with the proved real Laplace transform. -/
theorem logarithmicCausalLaplace_ofReal {s : ℝ} (hs : 0 < s) :
    logarithmicCausalLaplace (s : ℂ) = (continuedLogReferenceFactor (s : ℂ))⁻¹ := by
  have hi : (Ioi (0 : ℝ)).indicator (fun x : ℝ => Real.exp (-s * x) * logarithmicCausalKernel x) =
      fun x : ℝ => Real.exp (-s * x) * logarithmicCausalKernel x := by
    funext x
    by_cases hx : 0 < x
    · exact indicator_of_mem (s := Ioi (0 : ℝ)) hx _
    · rw [indicator_of_notMem (s := Ioi (0 : ℝ)) hx,
        logarithmicCausalKernel_of_nonpos (le_of_not_gt hx), mul_zero]
  calc
    _ = ∫ x : ℝ, ((Real.exp (-s * x) * logarithmicCausalKernel x : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]
    _ = ((∫ x : ℝ, Real.exp (-s * x) * logarithmicCausalKernel x : ℝ) : ℂ) := integral_complex_ofReal
    _ = ((∫ x in Ioi (0 : ℝ), Real.exp (-s * x) * logarithmicCausalKernel x : ℝ) : ℂ) := by
      rw [← integral_indicator measurableSet_Ioi, hi]
    _ = (((logReferenceFactor s)⁻¹ : ℝ) : ℂ) := congrArg Complex.ofReal (logarithmicCausalKernel_laplace hs).2
    _ = _ := by rw [continuedLogReferenceFactor_ofReal hs, Complex.ofReal_inv]

/-- Analytic uniqueness extends the actual Laplace identity throughout the right half-plane. -/
theorem logarithmicCausalLaplace_eq_factor_inv {z : ℂ} (hz : 0 < z.re) :
    logarithmicCausalLaplace z = (continuedLogReferenceFactor z)⁻¹ := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ logarithmicCausalLaplace U :=
    differentiableOn_logarithmicCausalLaplace.analyticOnNhd hUo
  have hg : AnalyticOnNhd ℂ (fun z => (continuedLogReferenceFactor z)⁻¹) U := by
    intro w hw
    change 0 < w.re at hw
    have hn : continuedLogReferenceFactor w ≠ 0 := by
      rw [continuedLogReferenceFactor_eq (Or.inl hw)]
      exact complexLogReferenceFactor_ne_zero w
    exact (analyticOnNhd_continuedLogReferenceFactor w (Or.inl (by linarith only [hw]))).inv hn
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ),
      logarithmicCausalLaplace w = (continuedLogReferenceFactor w)⁻¹ := by
    let u : ℕ → ℂ := fun k => ((1 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ)
    have hlim : Tendsto u atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
        rw [add_zero] at h
        have hc := (Complex.continuous_ofReal.tendsto 1).comp h
        rw [Complex.ofReal_one] at hc
        exact hc
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, u]
        intro h
        have he : (1 + 1 / ((k : ℝ) + 1) : ℝ) = 1 := by exact_mod_cast h
        have hp : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith only [he, hp]
    apply hlim.frequently
    exact Frequently.of_forall fun k => logarithmicCausalLaplace_ofReal (by positivity)
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (convex_halfSpace_re_gt 0).isPreconnected
    (by simp [U]) hfreq hz

/-- Dominated boundary convergence retains every real Fourier frequency. -/
theorem tendsto_logarithmicCausalLaplace_boundary (y : ℝ) :
    Tendsto (fun e : ℝ => logarithmicCausalLaplace ((e : ℂ) + (y : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (nhds (logarithmicCausalLaplace ((y : ℂ) * Complex.I))) := by
  apply tendsto_integral_filter_of_dominated_convergence logarithmicCausalKernel
  · exact Eventually.of_forall fun e => aestronglyMeasurable_logarithmicCausalLaplace_integrand _
  · filter_upwards [self_mem_nhdsWithin] with e he
    filter_upwards with x
    apply norm_logarithmicCausalLaplace_integrand_le
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, add_zero] using he.le
  · exact logarithmicCausalKernel_mass_one.1
  · filter_upwards with x
    have hc : ContinuousAt (fun e : ℝ => Complex.exp (-((e : ℂ) + (y : ℂ) * Complex.I) * (x : ℂ)) *
        (logarithmicCausalKernel x : ℂ)) 0 := by fun_prop
    simpa only [Complex.ofReal_zero, zero_add] using! hc.tendsto.mono_left nhdsWithin_le_nhds

/-- The reciprocal factor is the actual boundary Laplace transform, including frequency zero. -/
theorem logarithmicCausalLaplace_imaginary (y : ℝ) :
    logarithmicCausalLaplace ((y : ℂ) * Complex.I) =
      (continuedLogReferenceFactor ((y : ℂ) * Complex.I))⁻¹ := by
  have hz : (y : ℂ) * Complex.I ∈ logarithmicFactorContinuationDomain :=
    Or.inl (by simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero]; norm_num)
  have hn : continuedLogReferenceFactor ((y : ℂ) * Complex.I) ≠ 0 := by
    intro he
    have h := congrArg Complex.re ((continuedLogReferenceFactor_eq_zero_iff _).mp he)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, zero_mul, sub_zero, Complex.neg_re] at h
    linarith only [h, logarithmicFactorZeroRadius_pos]
  have hpath : Tendsto (fun e : ℝ => (e : ℂ) + (y : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ)) (nhds ((y : ℂ) * Complex.I)) := by
    have hc : ContinuousAt (fun e : ℝ => (e : ℂ) + (y : ℂ) * Complex.I) 0 := by fun_prop
    simpa only [Complex.ofReal_zero, zero_add] using! hc.tendsto.mono_left nhdsWithin_le_nhds
  have hK := (((analyticOnNhd_continuedLogReferenceFactor _ hz).continuousAt.inv₀ hn).tendsto).comp hpath
  have hL : Tendsto (fun e : ℝ => logarithmicCausalLaplace ((e : ℂ) + (y : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (nhds ((continuedLogReferenceFactor ((y : ℂ) * Complex.I))⁻¹)) := by
    apply hK.congr'
    filter_upwards [self_mem_nhdsWithin] with e he
    change (0 : ℝ) < e at he
    exact (logarithmicCausalLaplace_eq_factor_inv
      (by simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, add_zero] using he)).symm
  exact tendsto_nhds_unique (tendsto_logarithmicCausalLaplace_boundary y) hL

/-- The actual Fourier transform of the positive density is the reciprocal factor. -/
theorem fourier_logarithmicCausalKernel (ξ : ℝ) :
    𝓕 (fun x : ℝ => (logarithmicCausalKernel x : ℂ)) ξ =
      (continuedLogReferenceFactor (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I))⁻¹ := by
  rw [RHTower.fourier_real_eq_integral_exp]
  calc
    _ = logarithmicCausalLaplace (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) := by
      apply integral_congr_ae
      filter_upwards with x
      congr 2
      push_cast
      ring
    _ = _ := logarithmicCausalLaplace_imaginary (2 * Real.pi * ξ)

/-- The continued boundary factor has the exact logarithmic modulus, also at the origin. -/
theorem continuedLogReferenceFactor_imaginary_norm_sq (y : ℝ) :
    ‖continuedLogReferenceFactor ((y : ℂ) * Complex.I)‖ ^ 2 = positiveLogarithmicSymbol y := by
  by_cases hy : y = 0
  · simp only [hy, Complex.ofReal_zero, zero_mul, continuedLogReferenceFactor_zero,
      norm_one, one_pow, positiveLogarithmicSymbol, zero_pow (by norm_num : 2 ≠ 0),
      add_zero, Real.log_one, mul_zero]
  · rw [continuedLogReferenceFactor_eq
      (Or.inr (by simpa only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] using hy))]
    exact complexLogReferenceFactor_imaginary_norm_sq hy

theorem one_le_norm_continuedLogReferenceFactor_imaginary (y : ℝ) :
    1 ≤ ‖continuedLogReferenceFactor ((y : ℂ) * Complex.I)‖ := by
  have h := continuedLogReferenceFactor_imaginary_norm_sq y
  have hp := one_le_positiveLogarithmicSymbol y
  have hn := norm_nonneg (continuedLogReferenceFactor ((y : ℂ) * Complex.I))
  nlinarith only [h, hp, hn]

#print axioms logarithmicCausalLaplace_eq_factor_inv
#print axioms fourier_logarithmicCausalKernel
#print axioms continuedLogReferenceFactor_imaginary_norm_sq

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
