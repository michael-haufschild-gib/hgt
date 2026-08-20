import GaloisForLFunctions.HTGeometry.HalfPlanePoissonKernel
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The Poisson average of a Cauchy kernel

The half-plane Cauchy kernel `u ↦ (A - i u)⁻¹` is, in real and imaginary parts, exactly the pair
`π (P_{Re A} + i Q_{Re A})` centred at `Im A`.  Averaging it against the Poisson kernel at height
`c` therefore adds the heights in both channels, and the result is the Cauchy kernel with `A`
replaced by `A + c`:

`∫ P_c (u) (A - i u)⁻¹ du = (A + c)⁻¹`   for `Re A > 0`, `c > 0`.

This is the analytic step that turns the Poisson divisor expansion of a boundary density into the
value of the function inside the half plane.
-/

noncomputable section

open Complex MeasureTheory
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

theorem normSq_sub_I_mul_real (A : ℂ) (u : ℝ) :
    Complex.normSq (A - Complex.I * (u : ℂ)) = A.re ^ 2 + (u - A.im) ^ 2 := by
  have hre : (A - Complex.I * (u : ℂ)).re = A.re := by
    simp
  have him : (A - Complex.I * (u : ℂ)).im = A.im - u := by
    simp
  rw [Complex.normSq_apply, hre, him]
  ring

theorem re_inv_sub_I_mul_real (A : ℂ) (u : ℝ) :
    ((A - Complex.I * (u : ℂ))⁻¹).re = Real.pi * halfPlanePoisson A.re (u - A.im) := by
  have hre : (A - Complex.I * (u : ℂ)).re = A.re := by
    simp
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [Complex.inv_re, hre, normSq_sub_I_mul_real, halfPlanePoisson]
  rcases eq_or_ne (A.re ^ 2 + (u - A.im) ^ 2) 0 with h0 | h0
  · rw [h0]
    simp
  · field_simp

theorem im_inv_sub_I_mul_real (A : ℂ) (u : ℝ) :
    ((A - Complex.I * (u : ℂ))⁻¹).im = Real.pi * conjugatePoisson A.re (u - A.im) := by
  have him : (A - Complex.I * (u : ℂ)).im = A.im - u := by
    simp
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [Complex.inv_im, him, normSq_sub_I_mul_real, conjugatePoisson]
  rcases eq_or_ne (A.re ^ 2 + (u - A.im) ^ 2) 0 with h0 | h0
  · rw [h0]
    simp
  · field_simp
    ring

theorem inv_sub_I_mul_real_eq (A : ℂ) (u : ℝ) :
    (A - Complex.I * (u : ℂ))⁻¹
      = ((Real.pi * halfPlanePoisson A.re (u - A.im) : ℝ) : ℂ)
        + Complex.I * ((Real.pi * conjugatePoisson A.re (u - A.im) : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [re_inv_sub_I_mul_real]
    simp
  · rw [im_inv_sub_I_mul_real]
    simp

theorem norm_inv_sub_I_mul_real_le {A : ℂ} (hA : 0 < A.re) (u : ℝ) :
    ‖(A - Complex.I * (u : ℂ))⁻¹‖ ≤ 1 / A.re := by
  have hre : (A - Complex.I * (u : ℂ)).re = A.re := by
    simp
  have hge : A.re ≤ ‖A - Complex.I * (u : ℂ)‖ := by
    have := Complex.re_le_norm (A - Complex.I * (u : ℂ))
    rwa [hre] at this
  rw [norm_inv, inv_eq_one_div]
  exact one_div_le_one_div_of_le hA hge

theorem integrable_poisson_cauchy {c : ℝ} (hc : 0 < c) {A : ℂ} (hA : 0 < A.re) :
    Integrable fun u : ℝ => ((halfPlanePoisson c u : ℝ) : ℂ) * (A - Complex.I * (u : ℂ))⁻¹ := by
  have hcont : Continuous fun u : ℝ =>
      ((halfPlanePoisson c u : ℝ) : ℂ) * (A - Complex.I * (u : ℂ))⁻¹ := by
    refine Continuous.mul (Complex.continuous_ofReal.comp (continuous_halfPlanePoisson hc))
      (Continuous.inv₀ (by fun_prop) fun u => ?_)
    intro h
    have hre : (A - Complex.I * (u : ℂ)).re = A.re := by
      simp
    rw [h, Complex.zero_re] at hre
    exact absurd hre.symm (ne_of_gt hA)
  refine ((integrable_halfPlanePoisson hc).const_mul (1 / A.re)).mono'
    hcont.aestronglyMeasurable ?_
  filter_upwards with u
  have hp := halfPlanePoisson_pos hc u
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp, mul_comm (1 / A.re)]
  exact mul_le_mul_of_nonneg_left (norm_inv_sub_I_mul_real_le hA u) (le_of_lt hp)

/-- **The Poisson average of a Cauchy kernel raises the height.** -/
theorem integral_poisson_cauchy {c : ℝ} (hc : 0 < c) {A : ℂ} (hA : 0 < A.re) :
    (∫ u : ℝ, ((halfPlanePoisson c u : ℝ) : ℂ) * (A - Complex.I * (u : ℂ))⁻¹)
      = (A + (c : ℂ))⁻¹ := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hcongr : ∀ u : ℝ, ((halfPlanePoisson c u : ℝ) : ℂ) * (A - Complex.I * (u : ℂ))⁻¹
      = ((Real.pi * (halfPlanePoisson c (0 - u) * halfPlanePoisson A.re (u - A.im)) : ℝ) : ℂ)
        + Complex.I
          * ((Real.pi * (halfPlanePoisson c (0 - u) * conjugatePoisson A.re (u - A.im)) : ℝ)
            : ℂ) := by
    intro u
    have heven : halfPlanePoisson c (0 - u) = halfPlanePoisson c u := by
      rw [halfPlanePoisson, halfPlanePoisson]
      congr 2
      ring
    rw [inv_sub_I_mul_real_eq, heven]
    push_cast
    ring
  have hi1 : Integrable fun u : ℝ =>
      ((Real.pi * (halfPlanePoisson c (0 - u) * halfPlanePoisson A.re (u - A.im)) : ℝ) : ℂ) := by
    have hbase := integrable_poisson_shift_product hc hA (0 : ℝ) A.im
    exact ((hbase.const_mul Real.pi).ofReal)
  have hi2 : Integrable fun u : ℝ =>
      Complex.I
        * ((Real.pi * (halfPlanePoisson c (0 - u) * conjugatePoisson A.re (u - A.im)) : ℝ)
          : ℂ) := by
    have hbase : Integrable fun u : ℝ =>
        halfPlanePoisson c (0 - u) * conjugatePoisson A.re (u - A.im) := by
      have hcont : Continuous fun u : ℝ =>
          halfPlanePoisson c (0 - u) * conjugatePoisson A.re (u - A.im) := by
        refine ((continuous_halfPlanePoisson hc).comp (by fun_prop)).mul ?_
        unfold conjugatePoisson
        refine Continuous.div (by fun_prop) (by fun_prop) fun u => ?_
        have := Real.pi_pos
        positivity
      have hpi2 := Real.pi_pos
      refine ((integrable_halfPlanePoisson hc).comp_neg.const_mul
        (1 / (2 * Real.pi * A.re))).mono' hcont.aestronglyMeasurable ?_
      filter_upwards with u
      have h1 := halfPlanePoisson_pos hc (0 - u)
      have h2 : (0 : ℝ) < A.re ^ 2 + (u - A.im) ^ 2 := by positivity
      have h2p : (0 : ℝ) < 2 * Real.pi * A.re := by positivity
      have hposden : (0 : ℝ) < Real.pi * (A.re ^ 2 + (u - A.im) ^ 2) := by positivity
      have hQ : |conjugatePoisson A.re (u - A.im)| ≤ 1 / (2 * Real.pi * A.re) := by
        rw [conjugatePoisson, abs_div, abs_of_pos hposden,
          div_le_div_iff₀ hposden h2p]
        nlinarith [sq_nonneg (|u - A.im| - A.re), abs_nonneg (u - A.im), sq_abs (u - A.im),
          hpi2, hA]
      have hnegeq : halfPlanePoisson c (0 - u) = halfPlanePoisson c (-u) := by
        congr 1
        ring
      have h1' : (0 : ℝ) < halfPlanePoisson c (-u) := by rwa [← hnegeq]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos h1, hnegeq,
        mul_comm (1 / (2 * Real.pi * A.re))]
      exact mul_le_mul_of_nonneg_left hQ (le_of_lt h1')
    exact ((hbase.const_mul Real.pi).ofReal).const_mul _
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_add hi1 hi2]
  rw [integral_complex_ofReal, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, integral_complex_ofReal,
    MeasureTheory.integral_const_mul,
    integral_poisson_shift_product hc hA 0 A.im, conjugatePoisson_convolution hc hA 0 A.im]
  have hs : (0 : ℝ) - A.im = -A.im := by ring
  rw [hs]
  have hden : ((c + A.re) ^ 2 + A.im ^ 2) ≠ 0 := by positivity
  have hpip : (0 : ℝ) < Real.pi := Real.pi_pos
  apply Complex.ext
  · rw [halfPlanePoisson, conjugatePoisson, Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.add_im]
    field_simp
    ring
  · rw [halfPlanePoisson, conjugatePoisson, Complex.inv_im, Complex.normSq_apply]
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add, one_mul, Complex.add_re]
    field_simp
    ring

end GaloisForLFunctions.HTGeometry
