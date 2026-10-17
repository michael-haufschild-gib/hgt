import GaloisForLFunctions.RHTower.ThetaRenewalCausalModes
import GaloisForLFunctions.HTGeometry.PositiveSchurKernel
import GaloisForLFunctions.HTGeometry.StrictlyCausalFredholm

/-! # Exact positive theta transport response and its entire determinant -/

noncomputable section
open MeasureTheory Set Complex Filter
open scoped ComplexOrder

namespace RHTower
open GaloisForLFunctions.HTGeometry

local notation "μ₊" => Measure.restrict (volume : Measure ℝ) (Ioi 0)

theorem thetaRenewalCausalKernel_nonneg (t a : ℝ) : 0 ≤ thetaRenewalCausalKernel t a := by
  unfold thetaRenewalCausalKernel
  split
  · exact Complex.zero_le_real.mpr
      (div_pos (thetaRenewalHalfDensity_pos t) (thetaRenewalHalfDensity_pos a)).le
  · exact le_rfl

theorem thetaRenewalCausalOperator_nonneg {f : ThetaRenewalL2} (hf : 0 ≤ f) :
    0 ≤ thetaRenewalCausalOperator f :=
  thetaRenewalSchurKernel.op_nonneg thetaRenewalCausalKernel_nonneg hf

theorem thetaRenewalCausalAdjoint_nonneg {f : ThetaRenewalL2} (hf : 0 ≤ f) :
    0 ≤ ContinuousLinearMap.adjoint thetaRenewalCausalOperator f :=
  thetaRenewalSchurKernel.adjoint_op_nonneg thetaRenewalCausalKernel_nonneg hf

theorem thetaRenewalCausalKernel_mode_integral (z : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ a, thetaRenewalCausalKernel t a * thetaRenewalModeFn z a ∂μ₊) =
      (thetaRenewalHalfDensity t : ℂ) *
        ∫ a in (0 : ℝ)..t, Complex.exp (-(z * (a : ℂ))) := by
  have he : (fun a => thetaRenewalCausalKernel t a * thetaRenewalModeFn z a) =
      (Ioo 0 t).indicator (fun a => (thetaRenewalHalfDensity t : ℂ) *
        Complex.exp (-(z * (a : ℂ)))) := by
    funext a
    by_cases h : 0 < a ∧ a < t
    · rw [thetaRenewalCausalKernel, if_pos h,
        Set.indicator_of_mem (show a ∈ Ioo 0 t from h), thetaRenewalModeFn,
        Complex.ofReal_div, ← mul_assoc]
      have hga : (thetaRenewalHalfDensity a : ℂ) ≠ 0 := by
        exact_mod_cast (thetaRenewalHalfDensity_pos a).ne'
      rw [div_mul_cancel₀ _ hga]
    · rw [thetaRenewalCausalKernel, if_neg h, zero_mul,
        Set.indicator_of_notMem (show a ∉ Ioo 0 t from h)]
  have hset : Ioo (0 : ℝ) t ∩ Ioi 0 = Ioo 0 t :=
    inter_eq_left.mpr fun _ ha => ha.1
  rw [he, integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    hset, integral_const_mul, intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]

theorem thetaRenewalCausalOperator_mode_ae (z : ℂ) :
    (thetaRenewalCausalOperator (thetaRenewalMode z) : ℝ → ℂ) =ᵐ[μ₊]
      fun t => (thetaRenewalHalfDensity t : ℂ) *
        ∫ a in (0 : ℝ)..t, Complex.exp (-(z * (a : ℂ))) := by
  filter_upwards [thetaRenewalSchurKernel.op_coeFn (thetaRenewalMode z),
    ae_restrict_mem measurableSet_Ioi] with t ht htpos
  change thetaRenewalSchurKernel.op (thetaRenewalMode z) t = _
  rw [ht]
  change (∫ a, thetaRenewalCausalKernel t a * thetaRenewalMode z a ∂μ₊) = _
  calc (∫ a, thetaRenewalCausalKernel t a * thetaRenewalMode z a ∂μ₊) =
      ∫ a, thetaRenewalCausalKernel t a * thetaRenewalModeFn z a ∂μ₊ := by
        apply integral_congr_ae
        filter_upwards [thetaRenewalMode_ae z] with a ha
        rw [ha]
    _ = _ := thetaRenewalCausalKernel_mode_integral z htpos.le

theorem exp_add_mul_causal_integral (z : ℂ) (t : ℝ) :
    Complex.exp (-(z * (t : ℂ))) +
      z * (∫ a in (0 : ℝ)..t, Complex.exp (-(z * (a : ℂ)))) = 1 := by
  have hd (a : ℝ) : HasDerivAt (fun a : ℝ => Complex.exp (-(z * (a : ℂ))))
      (-z * Complex.exp (-(z * (a : ℂ)))) a := by
    have hb : HasDerivAt (fun a : ℝ => -(z * (a : ℂ))) (-z) a := by
      simpa using! ((hasDerivAt_id a).ofReal_comp.const_mul z).neg
    exact hb.cexp.congr_deriv (by ring)
  have hc : Continuous (fun a : ℝ => -z * Complex.exp (-(z * (a : ℂ)))) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun a _ => hd a) (hc.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_const_mul] at h
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero] at h
  linear_combination -h

/-- This exact response holds at every complex parameter, including zero. -/
theorem thetaRenewalMode_add_smul_causal (z : ℂ) :
    thetaRenewalMode z + z • thetaRenewalCausalOperator (thetaRenewalMode z) =
      thetaRenewalMode 0 := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (thetaRenewalMode z)
      (z • thetaRenewalCausalOperator (thetaRenewalMode z)),
    Lp.coeFn_smul z (thetaRenewalCausalOperator (thetaRenewalMode z)),
    thetaRenewalMode_ae z, thetaRenewalMode_ae 0,
    thetaRenewalCausalOperator_mode_ae z] with t hadd hsmul hz h0 hV
  rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, hz, h0, hV,
    thetaRenewalModeFn, thetaRenewalModeFn_zero]
  calc (thetaRenewalHalfDensity t : ℂ) * Complex.exp (-(z * (t : ℂ))) +
      z * ((thetaRenewalHalfDensity t : ℂ) *
        ∫ a in (0 : ℝ)..t, Complex.exp (-(z * (a : ℂ)))) =
      (thetaRenewalHalfDensity t : ℂ) * (Complex.exp (-(z * (t : ℂ))) +
        z * ∫ a in (0 : ℝ)..t, Complex.exp (-(z * (a : ℂ)))) := by ring
    _ = _ := by rw [exp_add_mul_causal_integral, mul_one]

theorem thetaRenewalCausalOperator_zero_ae :
    (thetaRenewalCausalOperator (thetaRenewalMode 0) : ℝ → ℂ) =ᵐ[μ₊]
      fun t => (thetaRenewalHalfDensity t : ℂ) * (t : ℂ) := by
  filter_upwards [thetaRenewalCausalOperator_mode_ae 0] with t ht
  simpa using ht

theorem mul_inner_thetaRenewalCausalAdjoint_mode (z : ℂ) :
    z * inner ℂ (ContinuousLinearMap.adjoint thetaRenewalCausalOperator (thetaRenewalMode 0))
      (thetaRenewalMode z) = thetaRenewalLaplace 0 - thetaRenewalLaplace z := by
  have h := congrArg (fun u => inner ℂ (thetaRenewalMode 0) u)
    (thetaRenewalMode_add_smul_causal z)
  rw [inner_add_right, inner_smul_right, inner_thetaRenewalMode_zero,
    inner_thetaRenewalMode_zero] at h
  rw [ContinuousLinearMap.adjoint_inner_left]
  linear_combination h

theorem inner_thetaRenewalCausalAdjoint_zero :
    inner ℂ (ContinuousLinearMap.adjoint thetaRenewalCausalOperator (thetaRenewalMode 0))
      (thetaRenewalMode 0) = ((∫ t in Ioi (0 : ℝ), t * thetaRenewalIncrement t : ℝ) : ℂ) := by
  rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [thetaRenewalMode_ae 0, thetaRenewalCausalOperator_zero_ae] with t hg hV
  rw [hg, hV, thetaRenewalModeFn_zero, RCLike.inner_apply]
  simp only [Complex.conj_ofReal, Complex.ofReal_mul]
  calc (thetaRenewalHalfDensity t : ℂ) * (t : ℂ) * (thetaRenewalHalfDensity t : ℂ) =
      (t : ℂ) * (thetaRenewalHalfDensity t : ℂ) ^ 2 := by ring
    _ = _ := by rw [← Complex.ofReal_pow, thetaRenewalHalfDensity_sq]

theorem thetaRenewalCausalOperator_det2
    {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ ThetaRenewalL2) (z : ℂ) :
    det2Op b (z • thetaRenewalCausalOperator) = 1 := by
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have he := SchurKernel.entireDet2_eq_one_of_strictlyCausal b
    (k := thetaRenewalSchurKernel)
    (fun t a hta => thetaRenewalCausalKernel_eq_zero hta)
    thetaRenewalSqIntKernel.energy_lt_top
  rw [det2Op, coordMatrix_smul,
    entireDet2_smul (isHS_coordMatrix b thetaRenewalCausalOperator_isHilbertSchmidt)]
  exact congrFun he (z * -1)

end RHTower
