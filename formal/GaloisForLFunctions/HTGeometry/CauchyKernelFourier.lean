import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import GaloisForLFunctions.HTGeometry.PoissonKernelIntegrals

/-!
# The Fourier transform of the Cauchy kernel

The two-sided exponential `e^{-a|t|}` has the elementary Fourier transform `2a/(a² + 4π²ξ²)`,
computed by splitting the line at the origin.  Both are integrable and the exponential is
continuous, so Fourier inversion applies and, after the scaling `ξ = x/2π`, returns

`∫_ℝ e^{i x t}/(a² + x²) dx = (π/a)·e^{-a|t|}`.

This is the archimedean half-density seen from the frequency side: a rational kernel of mass `a`
has exponential frequency decay of rate `a`.
-/

open MeasureTheory Set Complex
open scoped FourierTransform RealInnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable def twoSidedExp (a t : ℝ) : ℂ := ((Real.exp (-(a * |t|)) : ℝ) : ℂ)

theorem integrable_twoSidedExpReal {a : ℝ} (ha : 0 < a) :
    Integrable fun t : ℝ => Real.exp (-(a * |t|)) := by
  have hIic : IntegrableOn (fun t : ℝ => Real.exp (-(a * |t|))) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic (a := a) ha 0).congr_fun ?_ measurableSet_Iic
    intro t ht
    simp only [mem_Iic] at ht
    show Real.exp (a * t) = Real.exp (-(a * |t|))
    rw [abs_of_nonpos ht]
    congr 1
    ring
  have hIoi : IntegrableOn (fun t : ℝ => Real.exp (-(a * |t|))) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0).congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [mem_Ioi] at ht
    show Real.exp (-a * t) = Real.exp (-(a * |t|))
    rw [abs_of_pos ht]
    congr 1
    ring
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hIoi

theorem integrable_twoSidedExp {a : ℝ} (ha : 0 < a) : Integrable (twoSidedExp a) :=
  (integrable_twoSidedExpReal ha).ofReal

theorem continuous_twoSidedExp (a : ℝ) : Continuous (twoSidedExp a) := by
  unfold twoSidedExp
  fun_prop

theorem fourier_twoSidedExp {a : ℝ} (ha : 0 < a) (w : ℝ) :
    𝓕 (twoSidedExp a) w = ((2 * a / (a ^ 2 + (2 * Real.pi * w) ^ 2) : ℝ) : ℂ) := by
  set b : ℝ := 2 * Real.pi * w with hb
  set c₁ : ℂ := -(a : ℂ) - (b : ℂ) * I with hc1
  set c₂ : ℂ := (a : ℂ) - (b : ℂ) * I with hc2
  have hc1re : c₁.re = -a := by
    rw [hc1]
    simp [Complex.sub_re, Complex.mul_re]
  have hc2re : c₂.re = a := by
    rw [hc2]
    simp [Complex.sub_re, Complex.mul_re]
  have hIic : ∀ v ∈ Iic (0 : ℝ),
      cexp ((↑(-2 * Real.pi * (w * v)) : ℂ) * I) * twoSidedExp a v = cexp (c₂ * v) := by
    intro v hv
    simp only [mem_Iic] at hv
    rw [twoSidedExp, abs_of_nonpos hv, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    rw [hc2, hb]
    push_cast
    ring
  have hIoi : ∀ v ∈ Ioi (0 : ℝ),
      cexp ((↑(-2 * Real.pi * (w * v)) : ℂ) * I) * twoSidedExp a v = cexp (c₁ * v) := by
    intro v hv
    simp only [mem_Ioi] at hv
    rw [twoSidedExp, abs_of_pos hv, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    rw [hc1, hb]
    push_cast
    ring
  have hint1 : IntegrableOn
      (fun v : ℝ => cexp ((↑(-2 * Real.pi * (w * v)) : ℂ) * I) * twoSidedExp a v) (Iic 0) := by
    refine (integrableOn_exp_mul_complex_Iic (a := c₂) (by rw [hc2re]; exact ha) 0).congr_fun
      (fun v hv => (hIic v hv).symm) measurableSet_Iic
  have hint2 : IntegrableOn
      (fun v : ℝ => cexp ((↑(-2 * Real.pi * (w * v)) : ℂ) * I) * twoSidedExp a v) (Ioi 0) := by
    refine (integrableOn_exp_mul_complex_Ioi (a := c₁) (by rw [hc1re]; linarith) 0).congr_fun
      (fun v hv => (hIoi v hv).symm) measurableSet_Ioi
  rw [Real.fourier_eq']
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hint1 hint2,
    setIntegral_congr_fun measurableSet_Iic hIic,
    setIntegral_congr_fun measurableSet_Ioi hIoi,
    integral_exp_mul_complex_Iic (by rw [hc2re]; exact ha) 0,
    integral_exp_mul_complex_Ioi (by rw [hc1re]; linarith) 0]
  have hden2 : ((a : ℂ) - (b : ℂ) * I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, Complex.zero_re] at hre
    linarith
  have hden1 : (-(a : ℂ) - (b : ℂ) * I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, Complex.zero_re] at hre
    linarith
  have hdensum : ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.zero_re] at hre
    nlinarith [sq_nonneg b, sq_nonneg a]
  have e2 : (1 : ℂ) / ((a : ℂ) - (b : ℂ) * I)
      = ((a : ℂ) + (b : ℂ) * I) / ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) := by
    rw [div_eq_div_iff hden2 hdensum]
    linear_combination ((b : ℂ) ^ 2) * Complex.I_sq
  have e1 : (1 : ℂ) / (-(a : ℂ) - (b : ℂ) * I)
      = (-(a : ℂ) + (b : ℂ) * I) / ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) := by
    rw [div_eq_div_iff hden1 hdensum]
    linear_combination ((b : ℂ) ^ 2) * Complex.I_sq
  have key : (1 : ℂ) / ((a : ℂ) - (b : ℂ) * I) - 1 / (-(a : ℂ) - (b : ℂ) * I)
      = ((2 * a / (a ^ 2 + b ^ 2) : ℝ) : ℂ) := by
    rw [e2, e1, div_sub_div_same, Complex.ofReal_div]
    push_cast
    congr 1
    ring
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, hc1, hc2]
  rw [← key]
  ring

theorem integrable_fourier_twoSidedExp {a : ℝ} (ha : 0 < a) :
    Integrable (𝓕 (twoSidedExp a)) := by
  have hbase : Integrable fun w : ℝ => (a ^ 2 + (2 * Real.pi * w) ^ 2)⁻¹ := by
    have h := (GaloisForLFunctions.HTGeometry.integrable_inv_sq_add_sq ha).comp_mul_left'
      (R := 2 * Real.pi) (by positivity)
    exact h
  have h2 : Integrable fun w : ℝ => ((2 * a / (a ^ 2 + (2 * Real.pi * w) ^ 2) : ℝ) : ℂ) := by
    refine (Integrable.ofReal (𝕜 := ℂ) ?_)
    refine (hbase.const_mul (2 * a)).congr ?_
    filter_upwards with w
    exact (div_eq_mul_inv (2 * a) (a ^ 2 + (2 * Real.pi * w) ^ 2)).symm
  refine h2.congr ?_
  filter_upwards with w
  exact (fourier_twoSidedExp ha w).symm

theorem integral_cexp_mul_inv_sq_add_sq {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (∫ x : ℝ, Complex.exp (((x * t : ℝ) : ℂ) * I) * ((a ^ 2 + x ^ 2 : ℝ) : ℂ)⁻¹)
      = ((Real.pi / a * Real.exp (-(a * |t|)) : ℝ) : ℂ) := by
  have hinv := (integrable_twoSidedExp ha).fourierInv_fourier_eq
    (integrable_fourier_twoSidedExp ha) (v := t) (continuous_twoSidedExp a).continuousAt
  rw [Real.fourierInv_eq'] at hinv
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul] at hinv
  have hTS : twoSidedExp a t = ((Real.exp (-(a * |t|)) : ℝ) : ℂ) := rfl
  rw [hTS] at hinv
  have hinv2 : (∫ v : ℝ, cexp ((↑(2 * Real.pi * (t * v)) : ℂ) * I)
      * ((2 * a / (a ^ 2 + (2 * Real.pi * v) ^ 2) : ℝ) : ℂ))
      = ((Real.exp (-(a * |t|)) : ℝ) : ℂ) := by
    rw [← hinv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show cexp ((↑(2 * Real.pi * (t * v)) : ℂ) * I)
        * ((2 * a / (a ^ 2 + (2 * Real.pi * v) ^ 2) : ℝ) : ℂ)
      = cexp ((↑(2 * Real.pi * (t * v)) : ℂ) * I) * 𝓕 (twoSidedExp a) v
    rw [fourier_twoSidedExp ha v]
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hscale := MeasureTheory.Measure.integral_comp_div
    (fun v : ℝ => cexp ((↑(2 * Real.pi * (t * v)) : ℂ) * I)
      * ((2 * a / (a ^ 2 + (2 * Real.pi * v) ^ 2) : ℝ) : ℂ)) (2 * Real.pi)
  have hgdiv : ∀ x : ℝ, cexp ((↑(2 * Real.pi * (t * (x / (2 * Real.pi)))) : ℂ) * I)
      * ((2 * a / (a ^ 2 + (2 * Real.pi * (x / (2 * Real.pi))) ^ 2) : ℝ) : ℂ)
      = ((2 * a : ℝ) : ℂ) * (cexp ((↑(x * t) : ℂ) * I) * ((a ^ 2 + x ^ 2 : ℝ) : ℂ)⁻¹) := by
    intro x
    have h1 : 2 * Real.pi * (t * (x / (2 * Real.pi))) = x * t := by
      field_simp
    have h2 : 2 * Real.pi * (x / (2 * Real.pi)) = x := by
      field_simp
    rw [h1, h2]
    rw [show ((2 * a / (a ^ 2 + x ^ 2) : ℝ) : ℂ)
        = ((2 * a : ℝ) : ℂ) * ((a ^ 2 + x ^ 2 : ℝ) : ℂ)⁻¹ by
      rw [Complex.ofReal_div, div_eq_mul_inv]]
    ring
  rw [hinv2, Complex.real_smul] at hscale
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hgdiv),
    MeasureTheory.integral_const_mul] at hscale
  have habs : |2 * Real.pi| = 2 * Real.pi := abs_of_pos (by positivity)
  rw [habs] at hscale
  have hane : ((2 * a : ℝ) : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.2 ?_
    positivity
  have hfinal : (∫ x : ℝ, cexp ((↑(x * t) : ℂ) * I) * ((a ^ 2 + x ^ 2 : ℝ) : ℂ)⁻¹)
      = ((2 * Real.pi : ℝ) : ℂ) * ((Real.exp (-(a * |t|)) : ℝ) : ℂ) / ((2 * a : ℝ) : ℂ) := by
    rw [eq_div_iff hane]
    rw [← hscale]
    ring
  rw [hfinal]
  have hane2 : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt ha)
  push_cast
  field_simp

/-- **The Cauchy kernel against a frequency**, in the sign convention of the completed source. -/
theorem integral_inv_sq_add_sq_mul_cexp_neg {a : ℝ} (ha : 0 < a) (L : ℝ) :
    (∫ x : ℝ, ((a ^ 2 + x ^ 2 : ℝ) : ℂ)⁻¹ * Complex.exp (((-(L * x) : ℝ) : ℂ) * I))
      = ((Real.pi / a * Real.exp (-(a * |L|)) : ℝ) : ℂ) := by
  have h := integral_cexp_mul_inv_sq_add_sq ha (-L)
  rw [abs_neg] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ((a ^ 2 + x ^ 2 : ℝ) : ℂ)⁻¹ * Complex.exp (((-(L * x) : ℝ) : ℂ) * I)
      = Complex.exp (((x * -L : ℝ) : ℂ) * I) * ((a ^ 2 + x ^ 2 : ℝ) : ℂ)⁻¹
  rw [show (x * -L : ℝ) = -(L * x) by ring]
  ring

end GaloisForLFunctions.HTGeometry
