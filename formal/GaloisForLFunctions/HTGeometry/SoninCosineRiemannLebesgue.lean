import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Riemann--Lebesgue for real cosine modulation

The oscillatory integral of a continuous compactly supported real function against
`cos (2 π x w)` is the real part of the Fourier transform of its complexification, so it tends to
zero as the frequency grows.  This is the single analytic input behind the normalisation and weak
escape estimates for the annular wavepacket.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter Complex
open scoped FourierTransform Topology Real

/-- Pointwise: the real part of the Fourier integrand is the cosine-modulated function. -/
theorem re_fourierChar_smul_ofReal (g : ℝ → ℝ) (w x : ℝ) :
    ((Real.fourierChar (-(inner ℝ x w : ℝ)) : ℂ) • (g x : ℂ)).re =
      g x * Real.cos (2 * Real.pi * x * w) := by
  rw [Real.fourierChar_apply]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    RCLike.inner_apply, conj_trivial]
  rw [show (2 * Real.pi * -(w * x)) = -(2 * Real.pi * x * w) by ring, Real.cos_neg]
  ring

/-- **Riemann--Lebesgue, cosine form.**  The cosine-modulated integral of a continuous compactly
supported function vanishes at high frequency. -/
theorem tendsto_integral_mul_cos_atTop {g : ℝ → ℝ} (hg : Integrable g) :
    Tendsto (fun w : ℝ => ∫ x : ℝ, g x * Real.cos (2 * Real.pi * x * w)) atTop (𝓝 0) := by
  have hG : Integrable (fun x : ℝ => (g x : ℂ)) := hg.ofReal
  have hkey : ∀ w : ℝ, (∫ x : ℝ, g x * Real.cos (2 * Real.pi * x * w)) =
      (𝓕 (fun x : ℝ => (g x : ℂ)) w).re := by
    intro w
    have hFint : Integrable (fun x : ℝ =>
        ((Real.fourierChar (-(inner ℝ x w : ℝ)) : ℂ)) • (g x : ℂ)) :=
      ((Real.fourierIntegral_convergent_iff w).mpr hG).congr
        (Filter.Eventually.of_forall fun x => rfl)
    have hrew : (∫ v : ℝ, (Real.fourierChar (-(inner ℝ v w : ℝ))) • (g v : ℂ)) =
        ∫ v : ℝ, ((Real.fourierChar (-(inner ℝ v w : ℝ)) : ℂ)) • (g v : ℂ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      rfl
    rw [Real.fourier_eq, hrew, ← RCLike.re_to_complex, ← integral_re hFint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simpa [RCLike.re_to_complex] using (re_fourierChar_smul_ofReal g w x).symm
  have hRL : Tendsto (fun w : ℝ => 𝓕 (fun x : ℝ => (g x : ℂ)) w) atTop (𝓝 0) :=
    (Real.zero_at_infty_fourier (fun x : ℝ => (g x : ℂ))).mono_left atTop_le_cocompact
  have hre : Tendsto (fun w : ℝ => (𝓕 (fun x : ℝ => (g x : ℂ)) w).re) atTop (𝓝 0) := by
    have h := (Complex.continuous_re.tendsto (0 : ℂ)).comp hRL
    simpa [Function.comp_def] using h
  exact hre.congr fun w => (hkey w).symm

/-- Multiplying an integrable function by a cosine keeps it integrable. -/
theorem integrable_mul_cos {f : ℝ → ℝ} (hf : Integrable f) (a : ℝ) :
    Integrable (fun x : ℝ => f x * Real.cos (a * x)) := by
  refine Integrable.mono' hf.norm
    (hf.aestronglyMeasurable.mul (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [norm_mul, Real.norm_eq_abs (Real.cos (a * x))]
  calc ‖f x‖ * |Real.cos (a * x)| ≤ ‖f x‖ * 1 := by
        gcongr
        exact Real.abs_cos_le_one _
    _ = ‖f x‖ := mul_one _

/-- The same with the frequency written as in the Fourier convention. -/
theorem integrable_mul_cos_freq {f : ℝ → ℝ} (hf : Integrable f) (w : ℝ) :
    Integrable (fun x : ℝ => f x * Real.cos (2 * Real.pi * x * w)) := by
  refine Integrable.mono' hf.norm
    (hf.aestronglyMeasurable.mul (Real.continuous_cos.comp (by fun_prop)).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [norm_mul, Real.norm_eq_abs (Real.cos (2 * Real.pi * x * w))]
  calc ‖f x‖ * |Real.cos (2 * Real.pi * x * w)| ≤ ‖f x‖ * 1 := by
        gcongr
        exact Real.abs_cos_le_one _
    _ = ‖f x‖ := mul_one _

/-- **Riemann--Lebesgue, complex cosine form.** -/
theorem tendsto_integral_complex_mul_cos_atTop {h : ℝ → ℂ} (hh : Integrable h) :
    Tendsto (fun w : ℝ => ∫ x : ℝ, h x * (Real.cos (2 * Real.pi * x * w) : ℂ))
      atTop (𝓝 0) := by
  have hre : Integrable (fun x : ℝ => (h x).re) := hh.re
  have him : Integrable (fun x : ℝ => (h x).im) := hh.im
  have h1 := tendsto_integral_mul_cos_atTop hre
  have h2 := tendsto_integral_mul_cos_atTop him
  have hsplit : ∀ w : ℝ, (∫ x : ℝ, h x * (Real.cos (2 * Real.pi * x * w) : ℂ)) =
      ((∫ x : ℝ, (h x).re * Real.cos (2 * Real.pi * x * w) : ℝ) : ℂ) +
        Complex.I * ((∫ x : ℝ, (h x).im * Real.cos (2 * Real.pi * x * w) : ℝ) : ℂ) := by
    intro w
    have hA : Integrable (fun x : ℝ =>
        (((h x).re * Real.cos (2 * Real.pi * x * w) : ℝ) : ℂ)) :=
      (integrable_mul_cos_freq hre w).ofReal
    have hB : Integrable (fun x : ℝ =>
        Complex.I * (((h x).im * Real.cos (2 * Real.pi * x * w) : ℝ) : ℂ)) :=
      ((integrable_mul_cos_freq him w).ofReal).const_mul _
    have hpt : ∀ x : ℝ, h x * (Real.cos (2 * Real.pi * x * w) : ℂ) =
        (((h x).re * Real.cos (2 * Real.pi * x * w) : ℝ) : ℂ) +
          Complex.I * (((h x).im * Real.cos (2 * Real.pi * x * w) : ℝ) : ℂ) := by
      intro x
      conv_lhs => rw [← Complex.re_add_im (h x)]
      push_cast
      ring
    calc (∫ x : ℝ, h x * (Real.cos (2 * Real.pi * x * w) : ℂ))
        = ∫ x : ℝ, ((((h x).re * Real.cos (2 * Real.pi * x * w) : ℝ) : ℂ) +
            Complex.I * (((h x).im * Real.cos (2 * Real.pi * x * w) : ℝ) : ℂ)) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = (∫ x : ℝ, (((h x).re * Real.cos (2 * Real.pi * x * w) : ℝ) : ℂ)) +
            ∫ x : ℝ, Complex.I * (((h x).im * Real.cos (2 * Real.pi * x * w) : ℝ) : ℂ) :=
          integral_add hA hB
      _ = _ := by
          rw [integral_complex_ofReal, integral_const_mul, integral_complex_ofReal]
  have hlim : Tendsto (fun w : ℝ =>
      ((∫ x : ℝ, (h x).re * Real.cos (2 * Real.pi * x * w) : ℝ) : ℂ) +
        Complex.I * ((∫ x : ℝ, (h x).im * Real.cos (2 * Real.pi * x * w) : ℝ) : ℂ))
      atTop (𝓝 0) := by
    have hc1 : Tendsto (fun w : ℝ =>
        ((∫ x : ℝ, (h x).re * Real.cos (2 * Real.pi * x * w) : ℝ) : ℂ)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h1
    have hc2 : Tendsto (fun w : ℝ =>
        ((∫ x : ℝ, (h x).im * Real.cos (2 * Real.pi * x * w) : ℝ) : ℂ)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h2
    simpa using hc1.add (hc2.const_mul Complex.I)
  exact hlim.congr fun w => (hsplit w).symm

end RHTower
