import GaloisForLFunctions.RHTower.ChiRamanujanMovingCofactorLimit
import GaloisForLFunctions.RHTower.HalfPlaneDecayVerticalIntegral
import GaloisForLFunctions.HTGeometry.VerticalStripContourShift
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
/-!
# Exact signed cancellation of the BAG mixed-frequency candidate profile

Write `P(u) = integral_0^1 (exp(ut)-1)/t`, `E(u) = integral_0^1 exp(ut)`, and
`F(u) = exp(P(u))`, with removable values understood. The entire continuation
of `G(u) = F(u)*(1-E(u))^2/u` is absolutely integrable on every positive vertical
line and its full signed integral vanishes.

The exact differential identity `(u*F(u))' = exp(u)*F(u)` bounds `u*F(u)` on
left half-planes by the corpus exponential half-plane primitive theorem.
This gives inverse-square decay for `G`, paying every hypothesis of the
vertical contour shift and of the final limit toward the left.

Identification with the actual growing labelled source in a mixed-frequency
sector, uniform remainders and physical frequency tails remain separate open
problems. This module asserts no physical signed saving or RH conclusion.
-/

noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace RHTower.BAGTrace

/-- Entire exponential divided difference, equal to the compact exponential mean. -/
def criticalExponentialMean (u : ℂ) : ℂ := dslope Complex.exp 0 u

/-- Compact integral of the actual critical Euler deformation profile. -/
def criticalEulerExponent (u : ℂ) : ℂ := ∫ t in (0 : ℝ)..1,criticalEulerProfile u t

/-- Exponential carrier of the critical Euler deformation. -/
def criticalEulerCarrier (u : ℂ) : ℂ := Complex.exp (criticalEulerExponent u)

private theorem entire_dslope {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    Differentiable ℂ (dslope f c) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (s := univ) (by simp)).mpr hf.differentiableOn

private theorem mean_entire : Differentiable ℂ criticalExponentialMean :=
  entire_dslope Complex.differentiable_exp 0

private theorem mean_zero : criticalExponentialMean 0=1 := by
  simp [criticalExponentialMean,dslope_same,Complex.deriv_exp]

private theorem mean_mul (u : ℂ) : u*criticalExponentialMean u=Complex.exp u-1 := by
  have h := sub_smul_dslope Complex.exp 0 u
  simpa [criticalExponentialMean,smul_eq_mul] using h

theorem criticalExponentialMean_eq_integral (u : ℂ) :
    criticalExponentialMean u=∫ t in (0 : ℝ)..1,Complex.exp (u*(t : ℂ)) := by
  by_cases hu : u=0
  · subst u
    simp [mean_zero]
  · rw [integral_exp_mul_complex hu]
    simp only [ofReal_one,mul_one,ofReal_zero,mul_zero,Complex.exp_zero]
    exact (eq_div_iff hu).mpr (by simpa [mul_comm] using mean_mul u)

private theorem profile_eq_div (u : ℂ) {t : ℝ} (ht : t ≠ 0) :
    criticalEulerProfile u t=(Complex.exp (u*(t : ℂ))-1)/(t : ℂ) := by
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr ht)).mpr
  simpa [mul_comm] using criticalEulerProfile_mul u t

private theorem profile_deriv (u : ℂ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun w : ℂ => criticalEulerProfile w t) (Complex.exp (u*(t : ℂ))) u := by
  have h := ((((hasDerivAt_id u).mul_const (t : ℂ)).cexp).sub_const 1).div_const (t : ℂ)
  simp only [one_mul,mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr ht)] at h
  exact h.congr_of_eventuallyEq (Eventually.of_forall (fun w => profile_eq_div w ht))

theorem criticalEulerExponent_hasDerivAt (u : ℂ) :
    HasDerivAt criticalEulerExponent (criticalExponentialMean u) u := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  have hbound : ∀ᵐ t : ℝ ∂μ, ∀ w ∈ Metric.ball u 1,
      ‖Complex.exp (w*(t : ℂ))‖ ≤ Real.exp (‖u‖+1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro w hw
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hn : ‖w‖ < ‖u‖+1 := by
      have h := norm_lt_of_mem_ball hw
      linarith
    have hr : w.re*(t : ℝ) ≤ ‖w‖ := by
      calc _ ≤ ‖w‖*t := mul_le_mul_of_nonneg_right (Complex.re_le_norm w) ht.1.le
        _ ≤ ‖w‖*1 := mul_le_mul_of_nonneg_left ht.2 (norm_nonneg w)
        _ = _ := mul_one _
    simpa using hr.trans hn.le
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun w t => criticalEulerProfile w t)
    (F' := fun w t => Complex.exp (w*(t : ℂ)))
    (bound := fun _ => Real.exp (‖u‖+1)) (s := Metric.ball u 1)
    (Metric.ball_mem_nhds u (by norm_num : (0 : ℝ)<1))
    (Eventually.of_forall (fun w => (criticalEulerProfile_continuous w).aestronglyMeasurable))
    ((criticalEulerProfile_continuous u).intervalIntegrable 0 1).1
    (by fun_prop) hbound (integrable_const _) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      intro w _
      exact profile_deriv w ht.1.ne')
  change HasDerivAt (fun w => ∫ t in (0 : ℝ)..1,criticalEulerProfile w t) _ u
  rw [criticalExponentialMean_eq_integral]
  simpa only [intervalIntegral.integral_of_le zero_le_one,μ] using h.2

private theorem exponent_entire : Differentiable ℂ criticalEulerExponent :=
  fun u => (criticalEulerExponent_hasDerivAt u).differentiableAt

private theorem carrier_deriv (u : ℂ) :
    HasDerivAt criticalEulerCarrier (criticalEulerCarrier u*criticalExponentialMean u) u :=
  (criticalEulerExponent_hasDerivAt u).cexp

private theorem carrier_entire : Differentiable ℂ criticalEulerCarrier :=
  fun u => (carrier_deriv u).differentiableAt

/-- Exact primitive identity driving signed cancellation in the mixed-frequency profile. -/
theorem criticalEulerCarrier_primitive_deriv (u : ℂ) :
    HasDerivAt (fun w : ℂ => w*criticalEulerCarrier w)
      (Complex.exp u*criticalEulerCarrier u) u := by
  apply ((hasDerivAt_id u).mul (carrier_deriv u)).congr_deriv
  calc
    _ = criticalEulerCarrier u*(1+u*criticalExponentialMean u) := by simp only [id_eq]; ring
    _ = _ := by rw [mean_mul]; ring

/-- Entire continuation of the candidate mixed-frequency source profile. -/
def criticalMixedProfile (u : ℂ) : ℂ := criticalEulerCarrier u*
  (criticalExponentialMean u-1)*dslope criticalExponentialMean 0 u

/-- The removable mixed-frequency profile is entire. -/
theorem criticalMixedProfile_differentiable : Differentiable ℂ criticalMixedProfile :=
  (carrier_entire.mul (mean_entire.sub_const 1)).mul (entire_dslope mean_entire 0)

private theorem mixed_formula {u : ℂ} (hu : u ≠ 0) :
    criticalMixedProfile u=criticalEulerCarrier u*(1-criticalExponentialMean u)^2/u := by
  have h := sub_smul_dslope criticalExponentialMean 0 u
  simp only [sub_zero,smul_eq_mul,mean_zero] at h
  unfold criticalMixedProfile
  field_simp
  linear_combination criticalEulerCarrier u*(criticalExponentialMean u-1)*h


/-- The entire continuation vanishes at its apparent pole. -/
theorem criticalMixedProfile_zero : criticalMixedProfile 0 = 0 := by
  simp [criticalMixedProfile,mean_zero]

/-- The continuation equals the complete candidate mixed profile away from zero. -/
theorem criticalMixedProfile_eq (u : ℂˣ) :
    criticalMixedProfile u = criticalEulerCarrier u*(1-criticalExponentialMean u)^2/(u : ℂ) :=
  mixed_formula u.ne_zero


private theorem exponent_re_le (c : ℝ) {u : ℂ} (hu : u.re ≤ c) :
    (criticalEulerExponent u).re ≤ (criticalEulerExponent (c : ℂ)).re := by
  have hi (w : ℂ) : IntervalIntegrable (criticalEulerProfile w) volume 0 1 :=
    (criticalEulerProfile_continuous w).intervalIntegrable 0 1
  change (∫ t in (0 : ℝ)..1,criticalEulerProfile u t).re ≤
    (∫ t in (0 : ℝ)..1,criticalEulerProfile (c : ℂ) t).re
  have hr (w : ℂ) : (∫ t in (0 : ℝ)..1,criticalEulerProfile w t).re =
      ∫ t in (0 : ℝ)..1,(criticalEulerProfile w t).re := by
    simpa using (intervalIntegral.intervalIntegral_re (hi w)).symm
  rw [hr,hr]
  apply intervalIntegral.integral_mono_on zero_le_one
    ((Complex.continuous_re.comp (criticalEulerProfile_continuous u)).intervalIntegrable 0 1)
    ((Complex.continuous_re.comp (criticalEulerProfile_continuous (c : ℂ))).intervalIntegrable 0 1)
  intro t ht
  simp only [Function.comp_def]
  rcases ht.1.eq_or_lt with rfl | ht0
  · simpa [criticalEulerProfile_zero] using hu
  · have he : (Complex.exp (u*(t : ℂ))).re ≤ (Complex.exp ((c : ℂ)*(t : ℂ))).re := by
      calc
        _ ≤ ‖Complex.exp (u*(t : ℂ))‖ := Complex.re_le_norm _
        _ = Real.exp (u.re*t) := by rw [Complex.norm_exp]; simp
        _ ≤ Real.exp (c*t) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hu ht0.le)
        _ = _ := by simp [Complex.exp_re]
    rw [profile_eq_div u ht0.ne',profile_eq_div (c : ℂ) ht0.ne']
    simp only [div_eq_mul_inv,Complex.mul_re,Complex.sub_re,Complex.one_re,
      ← Complex.ofReal_inv,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_le_mul_of_nonneg_right (sub_le_sub_right he 1) (inv_nonneg.mpr ht0.le)

private def carrierBound (c : ℝ) : ℝ := Real.exp (criticalEulerExponent (c : ℂ)).re

private theorem carrier_norm_le (c : ℝ) {u : ℂ} (hu : u.re ≤ c) :
    ‖criticalEulerCarrier u‖ ≤ carrierBound c := by
  rw [criticalEulerCarrier,Complex.norm_exp]
  exact Real.exp_le_exp.mpr (exponent_re_le c hu)

private theorem mean_norm_le (c : ℝ) {u : ℂ} (hu : u.re ≤ c) :
    ‖criticalExponentialMean u‖ ≤ Real.exp (max c 0) := by
  rw [criticalExponentialMean_eq_integral]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := Real.exp (max c 0)) (f := fun t : ℝ => Complex.exp (u*(t : ℂ))) (by
      intro t ht
      rw [uIoc_of_le zero_le_one] at ht
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have he : u.re*t ≤ max c 0 := by
        calc _ ≤ max c 0*t := mul_le_mul_of_nonneg_right (hu.trans (le_max_left _ _)) ht.1.le
          _ ≤ max c 0*1 := mul_le_mul_of_nonneg_left ht.2 (le_max_right _ _)
          _ = _ := mul_one _
      simpa using he)
  simpa using h


private def carrierPrimitive (u : ℂ) : ℂ := u*criticalEulerCarrier u
private def carrierDerivative (u : ℂ) : ℂ := Complex.exp u*criticalEulerCarrier u

private theorem derivative_entire : Differentiable ℂ carrierDerivative :=
  Complex.differentiable_exp.mul carrier_entire

private theorem derivative_bound (c : ℝ) {u : ℂ} (hu : u.re ≤ c) :
    ‖carrierDerivative u‖ ≤ carrierBound c*Real.exp u.re := by
  rw [carrierDerivative,norm_mul,Complex.norm_exp,mul_comm]
  exact mul_le_mul_of_nonneg_right (carrier_norm_le c hu) (Real.exp_nonneg _)

private theorem primitive_real_difference (c x : ℝ) (hx : x ≤ c) :
    ‖carrierPrimitive (x : ℂ)-carrierPrimitive (c : ℂ)‖ ≤ carrierBound c*Real.exp c := by
  have hder (t : ℝ) : HasDerivAt (fun r : ℝ => carrierPrimitive (r : ℂ))
      (carrierDerivative (t : ℂ)) t := (criticalEulerCarrier_primitive_deriv (t : ℂ)).comp_ofReal
  have hi : IntervalIntegrable (fun t : ℝ => carrierDerivative (t : ℂ)) volume x c :=
    (derivative_entire.continuous.comp Complex.continuous_ofReal).intervalIntegrable x c
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) hi
  rw [norm_sub_rev,← he]
  have hb : ∀ t ∈ Icc x c, ‖carrierDerivative (t : ℂ)‖ ≤ carrierBound c*Real.exp t :=
    fun t ht => derivative_bound c ht.2
  calc
    _ ≤ ∫ t in x..c, carrierBound c*Real.exp t :=
      intervalIntegral.norm_integral_le_of_norm_le hx
        (Eventually.of_forall (fun t ht => hb t ⟨ht.1.le,ht.2⟩))
        ((by fun_prop : Continuous (fun t : ℝ => carrierBound c*Real.exp t)).intervalIntegrable x c)
    _ = carrierBound c*(Real.exp c-Real.exp x) := by rw [intervalIntegral.integral_const_mul,integral_exp]
    _ ≤ _ := by have hC : 0 ≤ carrierBound c := Real.exp_nonneg _; nlinarith [Real.exp_pos x]

private theorem derivative_vertical_bound (c x a b : ℝ) (hx : x ≤ c) :
    ‖∫ t in a..b, carrierDerivative (-((-x : ℝ) : ℂ)-(t : ℂ)*Complex.I)‖ ≤
      2*(carrierBound c*Real.exp x) := by
  have hf : Differentiable ℂ (fun z : ℂ => carrierDerivative (-z)) :=
    derivative_entire.comp differentiable_id.neg
  have hbd (z : ℂ) (hz : -x ≤ z.re) :
      ‖carrierDerivative (-z)‖ ≤ carrierBound c*Real.exp (-1*z.re) := by
    have h := derivative_bound c (u := -z) (by simp only [Complex.neg_re]; linarith)
    simpa only [Complex.neg_re,neg_mul,one_mul] using h
  have he (t : ℝ) : carrierDerivative (-((-x : ℝ) : ℂ)-(t : ℂ)*Complex.I)=
      carrierDerivative (-(((-x : ℝ) : ℂ)+(t : ℂ)*Complex.I)) := by congr 1; ring
  simp_rw [he]
  by_cases hab : a ≤ b
  · have h := norm_integral_vertical_le_of_halfPlane_decay (F := fun z => carrierDerivative (-z))
      (d := -x) (T₁ := a) (T₂ := b) (K := carrierBound c) (α := 1) hab (by norm_num)
      (Real.exp_nonneg _) (fun z _ => hf.analyticAt z) hbd
    simpa using h
  · rw [intervalIntegral.integral_symm,norm_neg]
    have h := norm_integral_vertical_le_of_halfPlane_decay (F := fun z => carrierDerivative (-z))
      (d := -x) (T₁ := b) (T₂ := a) (K := carrierBound c) (α := 1) (le_of_not_ge hab) (by norm_num)
      (Real.exp_nonneg _) (fun z _ => hf.analyticAt z) hbd
    simpa using h

private theorem primitive_vertical_difference (c x y : ℝ) (hx : x ≤ c) :
    ‖carrierPrimitive ((x : ℂ)+(y : ℂ)*Complex.I)-carrierPrimitive (x : ℂ)‖ ≤
      2*(carrierBound c*Real.exp x) := by
  let z (t : ℂ) : ℂ := -((-x : ℝ) : ℂ)-t*Complex.I
  have hz (t : ℂ) : HasDerivAt z (-Complex.I) t := by
    simpa only [z,id_eq,neg_mul,one_mul] using! ((hasDerivAt_id t).mul_const Complex.I).const_sub (-((-x : ℝ) : ℂ))
  have hd (t : ℝ) : HasDerivAt (fun r : ℝ => carrierPrimitive (z (r : ℂ)))
      (carrierDerivative (z (t : ℂ))*(-Complex.I)) t :=
    ((criticalEulerCarrier_primitive_deriv (z (t : ℂ))).comp (t : ℂ) (hz (t : ℂ))).comp_ofReal
  have hi : IntervalIntegrable (fun t : ℝ => carrierDerivative (z (t : ℂ))*(-Complex.I)) volume 0 (-y) := by
    apply Continuous.intervalIntegrable
    exact (derivative_entire.continuous.comp (by dsimp [z]; fun_prop)).mul continuous_const
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  have hz0 : z (0 : ℂ)=(x : ℂ) := by simp [z]
  have hzy : z ((-y : ℝ) : ℂ)=(x : ℂ)+(y : ℂ)*Complex.I := by simp [z]
  rw [Complex.ofReal_zero,hz0,hzy,intervalIntegral.integral_mul_const] at he
  have hn := congrArg norm he
  simp only [norm_mul,norm_neg,Complex.norm_I,mul_one] at hn
  rw [← hn]
  exact derivative_vertical_bound c x 0 (-y) hx

private def primitiveBound (c : ℝ) : ℝ :=
  ‖carrierPrimitive (c : ℂ)‖+3*(carrierBound c*Real.exp c)

private theorem primitive_bound (c : ℝ) {u : ℂ} (hu : u.re ≤ c) :
    ‖carrierPrimitive u‖ ≤ primitiveBound c := by
  have hr := primitive_real_difference c u.re hu
  have hv := primitive_vertical_difference c u.re u.im hu
  rw [Complex.re_add_im] at hv
  have hC : 0 ≤ carrierBound c := Real.exp_nonneg _
  have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu) hC
  have hn := norm_sub_le (carrierPrimitive u) (carrierPrimitive (u.re : ℂ))
  have ht := norm_add_le (carrierPrimitive u-carrierPrimitive (u.re : ℂ))
    (carrierPrimitive (u.re : ℂ)-carrierPrimitive (c : ℂ))
  rw [sub_add_sub_cancel] at ht
  have hf := norm_add_le (carrierPrimitive u-carrierPrimitive (c : ℂ)) (carrierPrimitive (c : ℂ))
  rw [sub_add_cancel] at hf
  dsimp only [primitiveBound]
  linarith


private theorem primitiveBound_nonneg (c : ℝ) : 0 ≤ primitiveBound c := by
  unfold primitiveBound carrierBound
  positivity

private def mixedBound (c : ℝ) : ℝ := primitiveBound c*(1+Real.exp (max c 0))^2

private theorem mixedBound_nonneg (c : ℝ) : 0 ≤ mixedBound c :=
  mul_nonneg (primitiveBound_nonneg c) (sq_nonneg _)

private theorem mixed_quadratic_bound (c : ℝ) {u : ℂ} (hu : u.re ≤ c) (hu0 : u ≠ 0) :
    ‖criticalMixedProfile u‖ ≤ mixedBound c/‖u‖^2 := by
  have hn : ‖1-criticalExponentialMean u‖ ≤ 1+Real.exp (max c 0) := by
    have h := norm_sub_le (1 : ℂ) (criticalExponentialMean u)
    simp only [norm_one] at h
    linarith [mean_norm_le c hu]
  have he : ‖u‖^2*‖criticalMixedProfile u‖ =
      ‖carrierPrimitive u‖*‖1-criticalExponentialMean u‖^2 := by
    rw [mixed_formula hu0,norm_div,norm_mul,norm_pow,carrierPrimitive,norm_mul]
    field_simp
  apply (le_div_iff₀ (pow_pos (norm_pos_iff.mpr hu0) 2)).mpr
  rw [mul_comm,he]
  exact mul_le_mul (primitive_bound c hu) (pow_le_pow_left₀ (norm_nonneg _) hn 2)
    (sq_nonneg _) (primitiveBound_nonneg c)

private theorem lorentz_scale {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    (a^2+t^2)⁻¹=(a^2)⁻¹*(1+(t/a)^2)⁻¹ := by
  have ha2 : a^2+t^2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg t))
  have ht : 1+(t/a)^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp

private theorem lorentz_integrable {a : ℝ} (ha : a ≠ 0) :
    Integrable (fun t : ℝ => (a^2+t^2)⁻¹) := by
  simp_rw [lorentz_scale ha]
  apply Integrable.const_mul
  exact (integrable_comp_div_iff _ ha).mpr integrable_inv_one_add_sq

private theorem lorentz_integral {a : ℝ} (ha : a ≠ 0) :
    (∫ t : ℝ, (a^2+t^2)⁻¹)=Real.pi/|a| := by
  simp_rw [lorentz_scale ha]
  rw [integral_const_mul]
  have h : (∫ t : ℝ, (1+(t/a)^2)⁻¹) = |a| * Real.pi := by
    calc
      _ = |a| • ∫ t : ℝ, (1+t^2)⁻¹ := Measure.integral_comp_div _ a
      _ = _ := by rw [integral_univ_inv_one_add_sq,smul_eq_mul]
  rw [h]
  rw [← sq_abs a]
  field_simp

private theorem line_norm_sq (a t : ℝ) :
    ‖(a : ℂ)+(t : ℂ)*Complex.I‖^2=a^2+t^2 := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply,pow_two]

private theorem line_ne_zero {a t : ℝ} (ha : a ≠ 0) : (a : ℂ)+(t : ℂ)*Complex.I ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_self,add_zero,Complex.zero_re] at hr
  exact ha hr

private theorem mixed_line_bound (c a t : ℝ) (ha : a ≤ c) (ha0 : a ≠ 0) :
    ‖criticalMixedProfile ((a : ℂ)+(t : ℂ)*Complex.I)‖ ≤ mixedBound c*(a^2+t^2)⁻¹ := by
  have h := mixed_quadratic_bound c (u := (a : ℂ)+(t : ℂ)*Complex.I)
    (by simpa using ha) (line_ne_zero ha0)
  simpa only [line_norm_sq,div_eq_mul_inv] using h

private theorem mixed_vertical_integrable (c a : ℝ) (ha : a ≤ c) (ha0 : a ≠ 0) :
    Integrable (fun t : ℝ => criticalMixedProfile ((a : ℂ)+(t : ℂ)*Complex.I)) := by
  apply ((lorentz_integrable ha0).const_mul (mixedBound c)).mono'
    (criticalMixedProfile_differentiable.continuous.comp (by fun_prop)).aestronglyMeasurable
  exact Eventually.of_forall (fun t => mixed_line_bound c a t ha ha0)

private theorem mixed_vertical_norm (c a : ℝ) (ha : a ≤ c) (ha0 : a ≠ 0) :
    ‖∫ t : ℝ, criticalMixedProfile ((a : ℂ)+(t : ℂ)*Complex.I)‖ ≤
      mixedBound c*Real.pi/|a| := by
  calc
    _ ≤ ∫ t : ℝ, mixedBound c*(a^2+t^2)⁻¹ :=
      norm_integral_le_of_norm_le ((lorentz_integrable ha0).const_mul (mixedBound c))
        (Eventually.of_forall (fun t => mixed_line_bound c a t ha ha0))
    _ = _ := by rw [integral_const_mul,lorentz_integral ha0]; ring

private theorem mixed_horizontal_bound (c x t : ℝ) (hx : x ≤ c) (ht : t ≠ 0) :
    ‖criticalMixedProfile ((x : ℂ)+(t : ℂ)*Complex.I)‖ ≤ mixedBound c/t^2 := by
  have hz : (x : ℂ)+(t : ℂ)*Complex.I ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    simp at h'
    exact ht h'
  have h := mixed_quadratic_bound c (u := (x : ℂ)+(t : ℂ)*Complex.I) (by simpa using hx) hz
  rw [line_norm_sq] at h
  exact h.trans (div_le_div_of_nonneg_left (mixedBound_nonneg c) (sq_pos_of_ne_zero ht)
    (le_add_of_nonneg_left (sq_nonneg x)))


private theorem horizontal_edges_zero (c a : ℝ) (ha : a ≤ c) (neg : Bool) :
    Tendsto (fun T : ℝ => ∫ x in a..c,
      criticalMixedProfile ((x : ℂ)+((if neg then -T else T : ℝ) : ℂ)*Complex.I))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => mixedBound c/T^2) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.pow 2).const_mul (mixedBound c)
    simpa only [zero_pow (by omega : 2 ≠ 0),mul_zero,div_eq_mul_inv,inv_pow] using h
  apply GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
    (M := fun T => mixedBound c/T^2) _ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  intro x hx
  rw [uIoc_of_le ha] at hx
  cases neg with
  | false => simpa using mixed_horizontal_bound c x T hx.2 hT.ne'
  | true => simpa using mixed_horizontal_bound c x (-T) hx.2 (neg_ne_zero.mpr hT.ne')

private theorem mixed_shift_left (c X : ℝ) (hc : 0 < c) (hX : 0 < X) :
    (∫ t : ℝ, criticalMixedProfile ((c : ℂ)+(t : ℂ)*Complex.I)) =
      ∫ t : ℝ, criticalMixedProfile (((-X : ℝ) : ℂ)+(t : ℂ)*Complex.I) := by
  have hxc : -X ≤ c := by linarith
  apply GaloisForLFunctions.HTGeometry.integral_vertical_line_eq_of_horizontal_tendsto hxc
    criticalMixedProfile_differentiable.differentiableOn
    (mixed_vertical_integrable c (-X) hxc (neg_ne_zero.mpr hX.ne'))
    (mixed_vertical_integrable c c le_rfl hc.ne')
  · simpa using horizontal_edges_zero c (-X) hxc true
  · simpa using horizontal_edges_zero c (-X) hxc false

/-- The complete candidate mixed-frequency profile is absolutely integrable and
has exactly zero signed integral on every positive vertical line. -/
theorem criticalMixedProfile_vertical_integral_zero (c : {r : ℝ // 0 < r}) :
    Integrable (fun t : ℝ => criticalMixedProfile ((c : ℂ)+(t : ℂ)*Complex.I)) ∧
      (∫ t : ℝ, criticalMixedProfile ((c : ℂ)+(t : ℂ)*Complex.I))=0 := by
  refine ⟨mixed_vertical_integrable c c le_rfl c.property.ne',?_⟩
  have hlim : Tendsto (fun X : ℝ => mixedBound c*Real.pi/X) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      tendsto_inv_atTop_zero.const_mul (mixedBound c*Real.pi)
  have hzero : Tendsto (fun _ : ℝ =>
      ‖∫ t : ℝ, criticalMixedProfile ((c : ℂ)+(t : ℂ)*Complex.I)‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    rw [mixed_shift_left c X c.property hX]
    have h := mixed_vertical_norm c (-X) (by linarith [c.property]) (neg_ne_zero.mpr hX.ne')
    simpa only [abs_neg,abs_of_pos hX] using h
  exact norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hzero)

end RHTower.BAGTrace
