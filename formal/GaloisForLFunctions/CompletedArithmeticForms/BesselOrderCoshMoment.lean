import GaloisForLFunctions.RHTower.BesselKImaginaryOrderUniformBound
import GaloisForLFunctions.RHTower.StripSourceHardyTransfer

/-!
# Cosh moments in imaginary Bessel order

Fourier inversion on the Schläfli strip gives the exact positive frequency
average `∫ cosh(ητ) Re K_(iτ)(x) dτ = π exp(-x cos η)` for
`0 ≤ η < π/2`, including absolute convergence.
-/

set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
open RHTower
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms

private theorem bessel_source_strip_decay {x : ℝ} (hx : 0 < x)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ β →
      ‖besselOrderEntireKernel x 0 z‖ ≤ C * Real.exp (-|z.re|) := by
  have hcos : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ⟩
  have hq : 0 < x * Real.cos β := mul_pos hx hcos
  refine ⟨Real.exp (2 / (x * Real.cos β)), (Real.exp_pos _).le, ?_⟩
  intro z hz
  have hc : Real.cos β ≤ Real.cos z.im := by
    rw [← Real.cos_abs z.im]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hz
  have hn := norm_besselOrderEntireKernel x 0 z.re z.im
  simp only [Complex.re_add_im, Complex.zero_re, Complex.zero_im, zero_mul, sub_zero,
    add_zero] at hn
  rw [hn, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he := bessel_exponent_bound (x * Real.cos β) 1 hq (abs_nonneg z.re)
  rw [Real.cosh_abs] at he
  norm_num only [one_pow, mul_one, one_mul] at he
  have hp := mul_le_mul_of_nonneg_left hc (mul_pos hx (Real.cosh_pos z.re)).le
  have hs := mul_nonneg (show 0 ≤ (x * Real.cos β) / 8 by positivity) (sq_nonneg |z.re|)
  nlinarith only [he, hp, hs]

private theorem bessel_source_even (x t : ℝ) :
    besselOrderEntireKernel x 0 (-(t : ℂ)) = besselOrderEntireKernel x 0 (t : ℂ) := by
  simp only [besselOrderEntireKernel, Complex.cosh_neg, zero_mul]

private theorem bessel_source_real (x t : ℝ) :
    (besselOrderEntireKernel x 0 (t : ℂ)).im = 0 := by
  simp only [besselOrderEntireKernel, zero_mul, add_zero, ← Complex.ofReal_cosh,
    ← Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.ofReal_im]

private theorem fourier_bessel_source {x : ℝ} (hx : 0 < x) (ξ : ℝ) :
    𝓕 (fun t : ℝ => besselOrderEntireKernel x 0 (t : ℂ)) ξ =
      2 * modifiedBesselKOrder x (((2 * Real.pi * ξ : ℝ) : ℂ) * I) := by
  rw [fourier_real_eq_integral_exp]
  have he : (fun t : ℝ =>
      Complex.exp (-(2 * Real.pi * I * t * ξ)) * besselOrderEntireKernel x 0 (t : ℂ)) =
      fun t : ℝ => besselOrderExpKernel x (-(((2 * Real.pi * ξ : ℝ) : ℂ) * I)) t := by
    funext t
    simp only [besselOrderEntireKernel, besselOrderExpKernel, zero_mul, add_zero,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he, integral_besselOrderExpKernel_eq_two_mul hx, modifiedBesselKOrder_neg]

/-- Positive cosh weighting of the imaginary-order Bessel carrier equals its exact imaginary-axis value. -/
theorem integral_cosh_besselOrder_scaled {x η : ℝ} (hx : 0 < x)
    (hη0 : 0 ≤ η) (hη : η < Real.pi / 2) :
    (∫ ξ : ℝ, Real.cosh (2 * Real.pi * η * ξ) *
      (2 * (modifiedBesselKOrder x (((2 * Real.pi * ξ : ℝ) : ℂ) * I)).re)) =
      Real.exp (-x * Real.cos η) := by
  have hholo : ∀ z : ℂ, |z.im| < Real.pi / 2 →
      DifferentiableAt ℂ (besselOrderEntireKernel x 0) z :=
    fun z _ => differentiable_besselOrderEntireKernel x 0 z
  have hs := strip_axis_eq_ofReal hholo (bessel_source_strip_decay hx)
    (bessel_source_even x) (bessel_source_real x) hη0 hη
  rw [integral_cosh_stripDensity hholo (bessel_source_strip_decay hx)
    (bessel_source_even x) (bessel_source_real x) (by rwa [abs_of_nonneg hη0])] at hs
  have hsr := congrArg Complex.re hs
  simp only [Complex.ofReal_re] at hsr
  have hd (ξ : ℝ) : stripDensity (besselOrderEntireKernel x 0) ξ =
      2 * (modifiedBesselKOrder x (((2 * Real.pi * ξ : ℝ) : ℂ) * I)).re := by
    rw [stripDensity, fourier_bessel_source hx]
    norm_num [Complex.mul_re]
  simp_rw [hd] at hsr
  rw [← hsr]
  simp only [besselOrderEntireKernel, zero_mul, add_zero, Complex.cosh_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_mul, ← Complex.ofReal_neg,
    ← Complex.ofReal_exp, Complex.ofReal_re]

/-- The unscaled positive frequency average of the Schläfli carrier. -/
theorem integral_cosh_besselOrder {x η : ℝ} (hx : 0 < x)
    (hη0 : 0 ≤ η) (hη : η < Real.pi / 2) :
    (∫ τ : ℝ, Real.cosh (η * τ) *
      (modifiedBesselKOrder x ((τ : ℂ) * I)).re) =
      Real.pi * Real.exp (-x * Real.cos η) := by
  let f : ℝ → ℝ := fun τ => Real.cosh (η * τ) *
    (modifiedBesselKOrder x ((τ : ℂ) * I)).re
  have h := integral_cosh_besselOrder_scaled hx hη0 hη
  have hp : (∫ ξ : ℝ, Real.cosh (2 * Real.pi * η * ξ) *
      (2 * (modifiedBesselKOrder x (((2 * Real.pi * ξ : ℝ) : ℂ) * I)).re)) =
      2 * ∫ ξ : ℝ, f (2 * Real.pi * ξ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ξ
    dsimp only [f]
    rw [show 2 * Real.pi * η * ξ = η * (2 * Real.pi * ξ) by ring]
    ring
  rw [hp] at h
  have hs := MeasureTheory.Measure.integral_comp_mul_left f (2 * Real.pi)
  rw [abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))] at hs
  change (∫ ξ : ℝ, f (2 * Real.pi * ξ)) = (2 * Real.pi)⁻¹ * ∫ τ : ℝ, f τ at hs
  rw [hs] at h
  change (∫ τ : ℝ, f τ) = _
  have hpi := Real.pi_ne_zero
  field_simp at h
  simpa only [neg_mul] using h

/-- Every subcritical cosh moment converges absolutely. -/
theorem integrable_cosh_besselOrder {x η : ℝ} (hx : 0 < x)
    (hη0 : 0 ≤ η) (hη : η < Real.pi / 2) :
    Integrable (fun τ : ℝ => Real.cosh (η * τ) *
      (modifiedBesselKOrder x ((τ : ℂ) * I)).re) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_cosh_besselOrder hx hη0 hη]
  exact (mul_pos Real.pi_pos (Real.exp_pos _)).ne'

end GaloisForLFunctions.CompletedArithmeticForms
