import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.WeightedCausalExponentialReflection
import GaloisForLFunctions.HTGeometry.FourierUniquenessL1

/-!
# Both Laplace representations of exponential reflection

At a zero total Laplace coefficient, the causal convolution equals a negative
anti-causal convolution. After exponential weighting one of these two kernels
is integrable on either side of the resonant rate. This supplies the pole
moment identity without differentiating the input profile.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Convolution

namespace GaloisForLFunctions.HTGeometry
open _root_.RHTower

/-- Reflection of the causal kernel integrates the upper Laplace tail. -/
theorem reflectedCausalConvolution_eq_partial_laplace (b y : ℝ) (f : ℝ → ℂ) :
    ((fun t => causalFourierExponential b (-t)) ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y =
      ((Real.pi : ℂ) * Complex.exp ((Real.pi * b * y : ℝ) : ℂ)) *
        ∫ u in Ioi y, Complex.exp (-(Real.pi * b * u : ℝ)) * f u := by
  have hr : ((fun t => causalFourierExponential b (-t)) ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y =
      ∫ u, causalFourierExponential b (u - y) * f u := by
    rw [convolution_def]
    have hh := integral_sub_left_eq_self (μ := volume)
      (fun u => causalFourierExponential b (u - y) * f u) y
    convert hh using 1
    congr 1
    funext u
    dsimp only [ContinuousLinearMap.mul_apply']
    congr 1
    congr 1
    ring
  rw [hr, ← integral_indicator measurableSet_Ioi, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  by_cases hu : u ∈ Ioi y
  · have huy : u - y ∈ Ioi (0 : ℝ) := by
      change (0 : ℝ) < u - y
      exact sub_pos.mpr hu
    rw [causalFourierExponential, indicator_of_mem huy, indicator_of_mem hu]
    have he : Complex.exp (-((Real.pi * b : ℝ) : ℂ) * ((u - y : ℝ) : ℂ)) =
        Complex.exp ((Real.pi * b * y : ℝ) : ℂ) * Complex.exp (-(Real.pi * b * u : ℝ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  · have huy : u - y ∉ Ioi (0 : ℝ) := by
      change ¬ (0 : ℝ) < u - y
      exact not_lt.mpr (sub_nonpos.mpr (le_of_not_gt hu))
    rw [causalFourierExponential, indicator_of_notMem huy, indicator_of_notMem hu,
      zero_mul, mul_zero]

/-- A vanishing total Laplace coefficient converts the causal resolvent into
its anti-causal representation. -/
theorem causalConvolution_eq_neg_reflected_of_laplace_zero (a : ℝ) {f : ℝ → ℂ}
    (hi : Integrable (fun u => Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u))
    (hz : (∫ u, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u) = 0) :
    causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f =
      fun y => -(((fun t => causalFourierExponential (-a) (-t)) ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y) := by
  funext y
  rw [causalExponentialConvolution_eq_upper_laplace_of_zero a hi hz y,
    reflectedCausalConvolution_eq_partial_laplace]
  simp only [mul_neg, neg_mul, neg_neg, Complex.ofReal_neg]

/-- Exponential weighting shifts an anti-causal kernel in the opposite direction. -/
theorem exp_mul_reflectedCausalFourierExponential (b x y : ℝ) :
    Complex.exp (-(Real.pi * x * y : ℝ)) * causalFourierExponential b (-y) =
      causalFourierExponential (b - x) (-y) := by
  have hh := exp_mul_causalFourierExponential b (-x) (-y)
  simpa only [mul_neg, neg_mul, neg_neg, sub_eq_add_neg] using hh

/-- The exact weighting identity for the reflected convolution. -/
theorem causalLaplaceWeighted_reflectedCausalConvolution (b x : ℝ) (f : ℝ → ℂ) :
    causalLaplaceWeighted x ((fun t => causalFourierExponential b (-t)) ⋆[ContinuousLinearMap.mul ℂ ℂ] f) =
      (fun t => causalFourierExponential (b - x) (-t)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        causalLaplaceWeighted x f := by
  rw [causalLaplaceWeighted_convolution]
  congr 1
  funext y
  exact exp_mul_reflectedCausalFourierExponential b x y

/-- The causal kernel's total mass in the Fourier normalization. -/
theorem integral_causalFourierExponential {b : ℝ} (hb : 0 < b) :
    (∫ u, causalFourierExponential b u) = (b : ℂ)⁻¹ := by
  have hh := causalLaplaceIntegral_causalFourierExponential (a := b) (x := 0) hb le_rfl
  simpa only [causalLaplaceIntegral, causalLaplaceWeighted, mul_zero, Complex.ofReal_zero,
    zero_mul, neg_zero, Complex.exp_zero, one_mul, add_zero] using hh

/-- The reflected kernel has the same total mass. -/
theorem integral_reflectedCausalFourierExponential {b : ℝ} (hb : 0 < b) :
    (∫ u, causalFourierExponential b (-u)) = (b : ℂ)⁻¹ := by
  calc
    _ = ∫ u, causalFourierExponential b u := by
      simpa only [zero_sub] using integral_sub_left_eq_self (μ := volume) (causalFourierExponential b) 0
    _ = _ := integral_causalFourierExponential hb

/-- The Laplace-resolvent law on the side with an integrable causal kernel. -/
theorem causalLaplaceIntegral_causalConvolution_of_pos {a x : ℝ} (hb : 0 < a + x)
    {f : ℝ → ℂ} (hf : Integrable (causalLaplaceWeighted x f)) :
    causalLaplaceIntegral x (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) =
      (((a + x : ℝ) : ℂ)⁻¹) * causalLaplaceIntegral x f := by
  unfold causalLaplaceIntegral
  rw [causalLaplaceWeighted_causalExponentialConvolution,
    integral_convolution (ContinuousLinearMap.mul ℂ ℂ) (causalFourierExponential_integrable hb) hf,
    integral_causalFourierExponential hb]
  rfl

/-- Beyond the resonant rate, the anti-causal representation gives the same law. -/
theorem causalLaplaceIntegral_causalConvolution_of_neg {a x : ℝ} (hb : a + x < 0)
    {f : ℝ → ℂ} (hi : Integrable (fun u => Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u))
    (hz : (∫ u, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u) = 0)
    (hf : Integrable (causalLaplaceWeighted x f)) :
    causalLaplaceIntegral x (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) =
      (((a + x : ℝ) : ℂ)⁻¹) * causalLaplaceIntegral x f := by
  have hb' : 0 < -a - x := by linarith only [hb]
  have hfun : causalLaplaceWeighted x (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) =
      fun y => -(((fun t => causalFourierExponential (-a - x) (-t)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        causalLaplaceWeighted x f) y) := by
    rw [causalConvolution_eq_neg_reflected_of_laplace_zero a hi hz]
    have hh := causalLaplaceWeighted_reflectedCausalConvolution (-a) x f
    calc
      _ = fun y => -causalLaplaceWeighted x
          ((fun t => causalFourierExponential (-a) (-t)) ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y := by
        funext y
        unfold causalLaplaceWeighted
        ring
      _ = _ := by rw [hh]
  rw [causalLaplaceIntegral, hfun, integral_neg,
    integral_convolution (ContinuousLinearMap.mul ℂ ℂ)
      (causalFourierExponential_integrable hb').comp_neg hf,
    integral_reflectedCausalFourierExponential hb']
  have he : -a - x = -(a + x) := by ring
  rw [he, Complex.ofReal_neg, inv_neg]
  change -(-(((a + x : ℝ) : ℂ)⁻¹) * causalLaplaceIntegral x f) = _
  ring

/-- The resonance-inclusive linear Laplace law, using both kernel representations. -/
theorem causalLaplaceIntegral_causalConvolution_mul {a x : ℝ} {f : ℝ → ℂ}
    (hi : Integrable (causalLaplaceWeighted (-a) f))
    (hz : causalLaplaceIntegral (-a) f = 0)
    (hf : Integrable (causalLaplaceWeighted x f)) :
    ((a + x : ℝ) : ℂ) *
      causalLaplaceIntegral x (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) =
      causalLaplaceIntegral x f := by
  by_cases hax : a + x = 0
  · have hx : x = -a := by linarith only [hax]
    rw [hax, Complex.ofReal_zero, zero_mul, hx, hz]
  · have hi' : Integrable (fun u => Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u) := by
      change Integrable (fun u => Complex.exp (-(Real.pi * (-a) * u : ℝ)) * f u) at hi
      simpa only [mul_neg, neg_mul, neg_neg, Complex.ofReal_neg] using hi
    have hz' : (∫ u, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * f u) = 0 := by
      simpa only [causalLaplaceIntegral, causalLaplaceWeighted, mul_neg, neg_mul, neg_neg, Complex.ofReal_neg] using hz
    have hl : causalLaplaceIntegral x (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) =
        (((a + x : ℝ) : ℂ)⁻¹) * causalLaplaceIntegral x f := by
      rcases lt_or_gt_of_ne hax with hn | hp
      · exact causalLaplaceIntegral_causalConvolution_of_neg hn hi' hz' hf
      · exact causalLaplaceIntegral_causalConvolution_of_pos hp hf
    have hc : ((a + x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hax
    rw [hl, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- The reflected Laplace value has the opposite linear factor. -/
theorem causalLaplaceIntegral_reflection_linear {a x : ℝ} {f : ℝ → ℂ}
    (hi : Integrable (causalLaplaceWeighted (-a) f))
    (hz : causalLaplaceIntegral (-a) f = 0)
    (hf : Integrable (causalLaplaceWeighted x f))
    (hc : Integrable (causalLaplaceWeighted x
      (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f))) :
    causalLaplaceIntegral x (causalBlaschkeStep a f) =
      ((a - x : ℝ) : ℂ) *
        causalLaplaceIntegral x (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) := by
  have hs : causalLaplaceWeighted x (causalBlaschkeStep a f) = fun y =>
      -causalLaplaceWeighted x f y + (2 * a : ℂ) * causalLaplaceWeighted x
        (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y := by
    funext y
    unfold causalLaplaceWeighted causalBlaschkeStep
    ring
  rw [causalLaplaceIntegral, hs]
  dsimp only
  have hadd : (∫ y, -causalLaplaceWeighted x f y + (2 * a : ℂ) *
      causalLaplaceWeighted x (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y) =
      (∫ y, -causalLaplaceWeighted x f y) +
        ∫ y, (2 * a : ℂ) * causalLaplaceWeighted x
          (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y :=
    integral_add hf.neg (hc.const_mul (2 * a : ℂ))
  rw [hadd, integral_neg, integral_const_mul]
  change -causalLaplaceIntegral x f + (2 * a : ℂ) *
    causalLaplaceIntegral x (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) = _
  rw [← causalLaplaceIntegral_causalConvolution_mul hi hz hf]
  push_cast
  ring

/-- The paired opposite Laplace moments are exactly invariant, including resonance. -/
theorem causalLaplaceIntegral_reflection_pair {a x : ℝ} {f : ℝ → ℂ}
    (hi : Integrable (causalLaplaceWeighted (-a) f))
    (hz : causalLaplaceIntegral (-a) f = 0)
    (hp : Integrable (causalLaplaceWeighted x f))
    (hm : Integrable (causalLaplaceWeighted (-x) f))
    (hcp : Integrable (causalLaplaceWeighted x
      (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f)))
    (hcm : Integrable (causalLaplaceWeighted (-x)
      (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f))) :
    causalLaplaceIntegral x (causalBlaschkeStep a f) * causalLaplaceIntegral (-x) (causalBlaschkeStep a f) =
      causalLaplaceIntegral x f * causalLaplaceIntegral (-x) f := by
  rw [causalLaplaceIntegral_reflection_linear hi hz hp hcp,
    causalLaplaceIntegral_reflection_linear hi hz hm hcm,
    ← causalLaplaceIntegral_causalConvolution_mul hi hz hp,
    ← causalLaplaceIntegral_causalConvolution_mul hi hz hm]
  push_cast
  ring

/-- The causal resolvent is injective on actual integrable profiles. -/
theorem ae_eq_zero_of_causalExponentialConvolution_ae_zero {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : Integrable f)
    (hz : (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) =ᵐ[volume] 0) :
    f =ᵐ[volume] 0 := by
  apply _root_.HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero hf
  intro ξ
  have hh := Real.fourier_congr_ae hz ξ
  have hzero : FourierTransform.fourier (0 : ℝ → ℂ) ξ = 0 := by
    rw [Real.fourier_real_eq]
    simp
  rw [hzero, fourier_mul_convolution_eq_of_integrable (causalFourierExponential_integrable ha) hf,
    fourier_causalFourierExponential ha] at hh
  have hd : (a : ℂ) + 2 * Complex.I * ξ ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    exact ha.ne' hre
  exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero hd)

end GaloisForLFunctions.HTGeometry
