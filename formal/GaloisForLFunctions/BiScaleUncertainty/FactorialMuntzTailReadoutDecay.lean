import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTailPrimitive

/-! Integration by parts for the literal correction tail, with both improper
endpoint obligations discharged. -/

open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

private def primitiveTilt (n : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (z*(x : ℂ))*(factorialMuntzTailPrimitive n x : ℂ)

private theorem primitiveTilt_continuous (n : ℕ) (z : ℂ) :
    Continuous (primitiveTilt n z) := by
  unfold primitiveTilt
  have he : Continuous (fun x : ℝ => Complex.exp (z*(x : ℂ))) := by fun_prop
  exact he.mul
    (Complex.continuous_ofReal.comp (factorialMuntzTailPrimitive_continuous n))

private theorem primitiveTilt_norm_le (n : ℕ) (z : ℂ) (x : ℝ) :
    ‖primitiveTilt n z x‖ ≤ 12*Real.exp (z.re*x) := by
  simp only [primitiveTilt, norm_mul, Complex.norm_exp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (factorialMuntzTailPrimitive_abs_le n x)
    (Real.exp_pos (z.re*x)).le).trans_eq (mul_comm _ _)

private theorem primitiveTilt_integrable (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (primitiveTilt n z) (Iic (0 : ℝ)) := by
  exact ((integrableOn_exp_mul_Iic hz 0).const_mul (12 : ℝ)).mono'
    (primitiveTilt_continuous n z).aestronglyMeasurable
    (Eventually.of_forall (primitiveTilt_norm_le n z))

private theorem primitiveTilt_integral_norm_le (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    ‖∫ x in Iic (0 : ℝ), primitiveTilt n z x‖ ≤ 12/z.re := by
  calc
    _ ≤ ∫ x in Iic (0 : ℝ), 12*Real.exp (z.re*x) :=
      norm_integral_le_of_norm_le ((integrableOn_exp_mul_Iic hz 0).const_mul (12 : ℝ))
        (Eventually.of_forall (primitiveTilt_norm_le n z))
    _ = _ := by rw [integral_const_mul, integral_exp_mul_Iic hz]; simp [div_eq_mul_inv]

private theorem primitiveTilt_atBot (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    Tendsto (primitiveTilt n z) atBot (𝓝 0) := by
  have he : Tendsto (fun x : ℝ => 12*Real.exp (z.re*x)) atBot (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hz)).const_mul 12
  exact squeeze_zero_norm (fun x => primitiveTilt_norm_le n z x) he

theorem factorialMuntzCorrectedTail_tilt_eq_primitive_deriv (n : ℕ) (s : ℂ)
    {x : ℝ} (hx : x ≤ 0) :
    Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ) =
      -(factorialMuntzTailPrimitiveScale n : ℂ)*Complex.exp ((s+2)*(x : ℂ))*
        ((deriv (factorialMuntzTailPrimitive n) x : ℝ) : ℂ) := by
  have he : Complex.exp ((s-1/2)*(x : ℂ))*(Real.exp (5*x/2) : ℂ) =
      Complex.exp ((s+2)*(x : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [factorialMuntzCorrectedTail_eq_primitive_deriv n hx]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg]
  calc
    _ =
      -(factorialMuntzTailPrimitiveScale n : ℂ)*
        (Complex.exp ((s-1/2)*(x : ℂ))*(Real.exp (5*x/2) : ℂ))*
        ((deriv (factorialMuntzTailPrimitive n) x : ℝ) : ℂ) := by ring
    _ = _ := by rw [he]

/-- The endpoint term is retained; the improper endpoint vanishes by a
uniform bound on the actual primitive. -/
theorem factorialMuntzCorrectedTail_readout_eq_primitive (n : ℕ) (s : ℂ)
    (hs : -1 < s.re) :
    (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ)) =
      (factorialMuntzTailPrimitiveScale n : ℂ)*
        ((s+2)*(∫ x in Iic (0 : ℝ), Complex.exp ((s+2)*(x : ℂ))*
          (factorialMuntzTailPrimitive n x : ℂ))-(factorialMuntzTailPrimitive n 0 : ℂ)) := by
  have hz : 0 < (s+2).re := by change 0 < s.re+2; linarith
  have hA : (factorialMuntzTailPrimitiveScale n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (factorialMuntzTailPrimitiveScale_pos n).ne'
  have hi : IntegrableOn (fun x : ℝ => Complex.exp ((s+2)*(x : ℂ))*
      ((deriv (factorialMuntzTailPrimitive n) x : ℝ) : ℂ)) (Iic (0 : ℝ)) := by
    refine ((factorialMuntzCorrectedTail_readout_integrable n s hs).integrableOn.const_mul
      (-(factorialMuntzTailPrimitiveScale n : ℂ))⁻¹).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    rw [factorialMuntzCorrectedTail_tilt_eq_primitive_deriv n s hx]
    field_simp
  have hu (x : ℝ) (_ : x ∈ Iio (0 : ℝ)) :
      HasDerivAt (fun x : ℝ => Complex.exp ((s+2)*(x : ℂ)))
        ((s+2)*Complex.exp ((s+2)*(x : ℂ))) x := by
    simpa only [id_eq, Complex.ofReal_one, mul_one, one_mul, mul_comm]
      using! (((hasDerivAt_id x).ofReal_comp.const_mul (s+2)).cexp)
  have hv (x : ℝ) (_ : x ∈ Iio (0 : ℝ)) :
      HasDerivAt (fun x : ℝ => (factorialMuntzTailPrimitive n x : ℂ))
        ((deriv (factorialMuntzTailPrimitive n) x : ℝ) : ℂ) x := by
    rw [(factorialMuntzTailPrimitive_hasDerivAt n x).deriv]
    exact (factorialMuntzTailPrimitive_hasDerivAt n x).ofReal_comp
  have hip : IntegrableOn (fun x : ℝ => ((s+2)*Complex.exp ((s+2)*(x : ℂ)))*
      (factorialMuntzTailPrimitive n x : ℂ)) (Iic (0 : ℝ)) := by
    simpa only [primitiveTilt, IntegrableOn, mul_assoc]
      using! (primitiveTilt_integrable n hz).const_mul (s+2)
  have hzero : Tendsto (primitiveTilt n (s+2)) (𝓝[<] (0 : ℝ))
      (𝓝 (factorialMuntzTailPrimitive n 0 : ℂ)) := by
    have hc : ContinuousAt (primitiveTilt n (s+2)) (0 : ℝ) :=
      (primitiveTilt_continuous n (s+2)).continuousAt
    simpa only [primitiveTilt, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
      using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))
  have hibp := integral_Iic_mul_deriv_eq_deriv_mul hu hv hi hip hzero (primitiveTilt_atBot n hz)
  have hrestrict : (∫ x in Iic (0 : ℝ),
      Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ)) =
      ∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp only [factorialMuntzCorrectedTail, indicator_of_notMem hx, Complex.ofReal_zero, mul_zero]
  rw [← hrestrict]
  calc
    _ = ∫ x in Iic (0 : ℝ), -(factorialMuntzTailPrimitiveScale n : ℂ)*
        (Complex.exp ((s+2)*(x : ℂ))*((deriv (factorialMuntzTailPrimitive n) x : ℝ) : ℂ)) := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro x hx
      simpa only [mul_assoc] using factorialMuntzCorrectedTail_tilt_eq_primitive_deriv n s hx
    _ = -(factorialMuntzTailPrimitiveScale n : ℂ)*
        (∫ x in Iic (0 : ℝ), Complex.exp ((s+2)*(x : ℂ))*
          ((deriv (factorialMuntzTailPrimitive n) x : ℝ) : ℂ)) := integral_const_mul _ _
    _ = _ := by
      rw [hibp]
      simp only [sub_zero, mul_assoc, integral_const_mul]
      ring

theorem factorialMuntzCorrectedTail_readout_decay (n : ℕ) (s : ℂ) (hs : -1 < s.re) :
    ‖∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ)‖ ≤
      180/(((n+1 : ℕ) : ℝ)*Real.sqrt ((n+1 : ℕ) : ℝ))*(1+‖s+2‖/(s.re+2)) := by
  have hz : 0 < (s+2).re := by change 0 < s.re+2; linarith
  have hj := primitiveTilt_integral_norm_le n hz
  have hv : ‖(factorialMuntzTailPrimitive n 0 : ℂ)‖ ≤ 12 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using factorialMuntzTailPrimitive_abs_le n 0
  rw [factorialMuntzCorrectedTail_readout_eq_primitive n s hs, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (factorialMuntzTailPrimitiveScale_pos n)]
  calc
    _ ≤ factorialMuntzTailPrimitiveScale n*
        (‖s+2‖*(12/(s.re+2))+12) := by
      apply mul_le_mul_of_nonneg_left _ (factorialMuntzTailPrimitiveScale_pos n).le
      refine (norm_sub_le _ _).trans (add_le_add ?_ hv)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (by simpa [primitiveTilt] using hj) (norm_nonneg _)
    _ ≤ (15/(((n+1 : ℕ) : ℝ)*Real.sqrt ((n+1 : ℕ) : ℝ)))*
        (‖s+2‖*(12/(s.re+2))+12) := by
      apply mul_le_mul_of_nonneg_right (factorialMuntzTailPrimitiveScale_le n)
      have : 0 < s.re+2 := by linarith
      positivity
    _ = _ := by ring

theorem factorialMuntzCorrectedTail_readout_decay_of_nonneg_re (n : ℕ) (s : ℂ)
    (hs : 0 ≤ s.re) :
    ‖∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ)‖ ≤
      360*(1+|s.im|)/(((n+1 : ℕ) : ℝ)*Real.sqrt ((n+1 : ℕ) : ℝ)) := by
  have hd : 0 < s.re+2 := by linarith
  have hn : ‖s+2‖ ≤ s.re+2+|s.im| := by
    simpa [abs_of_pos hd] using Complex.norm_le_abs_re_add_abs_im (s+2)
  have hr : ‖s+2‖/(s.re+2) ≤ 1+|s.im| := by
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg hs (abs_nonneg s.im), abs_nonneg s.im]
  calc
    _ ≤ 180/(((n+1 : ℕ) : ℝ)*Real.sqrt ((n+1 : ℕ) : ℝ))*
        (1+‖s+2‖/(s.re+2)) := factorialMuntzCorrectedTail_readout_decay n s (by linarith)
    _ ≤ 180/(((n+1 : ℕ) : ℝ)*Real.sqrt ((n+1 : ℕ) : ℝ))*(2*(1+|s.im|)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [abs_nonneg s.im]
    _ = _ := by ring

private theorem real_paperFT_eq_readout (f : ℝ → ℝ) (τ : ℝ) :
    _root_.Zeta23.paperFT (fun x => (f x : ℂ)) (τ : ℂ) =
      ∫ x : ℝ, Complex.exp (((1/2 : ℂ)+Complex.I*(τ : ℂ)-1/2)*(x : ℂ))*(f x : ℂ) := by
  simp only [_root_.Zeta23.paperFT, add_sub_cancel_left, mul_comm]

theorem factorialMuntzCorrectedTail_paperFT_decay (n : ℕ) (τ : ℝ) :
    ‖_root_.Zeta23.paperFT (fun x => (factorialMuntzCorrectedTail n x : ℂ)) (τ : ℂ)‖ ≤
      360*(1+|τ|)/(((n+1 : ℕ) : ℝ)*Real.sqrt ((n+1 : ℕ) : ℝ)) := by
  rw [real_paperFT_eq_readout]
  simpa using factorialMuntzCorrectedTail_readout_decay_of_nonneg_re n
    ((1/2 : ℂ)+Complex.I*(τ : ℂ)) (by simp)

theorem factorialMuntzSmoothedTail_paperFT_decay (n k : ℕ) (τ : ℝ) :
    ‖_root_.Zeta23.paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (τ : ℂ)‖ ≤
      360*Real.exp 1*(1+|τ|)/(((n+1 : ℕ) : ℝ)*Real.sqrt ((n+1 : ℕ) : ℝ)) := by
  let s : ℂ := (1/2 : ℂ)+Complex.I*(τ : ℂ)
  have hs0 : 0 ≤ s.re := by dsimp [s]; norm_num
  have hs1 : s.re ≤ 1 := by dsimp [s]; norm_num
  have hb := factorialMuntzCorrectedTail_readout_decay_of_nonneg_re n s hs0
  rw [real_paperFT_eq_readout, (factorialMuntzSmoothedTail_readout n k s (by linarith)).2,
    norm_mul]
  calc
    _ ≤ Real.exp 1*(360*(1+|s.im|)/
        (((n+1 : ℕ) : ℝ)*Real.sqrt ((n+1 : ℕ) : ℝ))) :=
      mul_le_mul (factorialMuntzKernelReadout_bound k hs0 hs1) hb
        (norm_nonneg _) (Real.exp_pos 1).le
    _ = _ := by
      have hi : s.im = τ := by simp [s]
      rw [hi]
      ring

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
