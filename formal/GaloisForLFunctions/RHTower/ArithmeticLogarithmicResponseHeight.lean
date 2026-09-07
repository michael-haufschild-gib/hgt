import GaloisForLFunctions.RHTower.ArithmeticFullReflectionResponse
import GaloisForLFunctions.RHTower.ArithmeticClockFirstVariation

/-!
# Full logarithmic source flux and height decay

Right differentiation of the literal periodic Bernoulli kernel retains every
integer join. Integration by parts against the unchanged logarithmic height
character expresses the entire critical response through its signed arithmetic
flux. Both boundaries vanish, and exact logarithmic moments bound the flux mass
by 19/9. The full response consequently has inverse-height decay. This is norm
control; no signed separation from the exact off-line-zero target is asserted.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Complex Real
open scoped BigOperators
namespace RHTower.DeletionMixedRefinement

/-- Sharp uniform absolute bound on the full centered arithmetic kernel. -/
theorem abs_centeredBernoulliKernel_le (x : ℝ) : |RHTower.bernoulliPeriodic x+1/12| ≤ 1/12 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  rw [RHTower.bernoulliPeriodic,abs_le]
  constructor <;> nlinarith [sq_nonneg (Int.fract x-1/2)]

/-- The centered arithmetic kernel is continuous across all integer joins. -/
theorem continuous_centeredBernoulliKernel : Continuous (fun x : ℝ => RHTower.bernoulliPeriodic x+1/12) := by
  have hc : Continuous (fun x : ℝ => (x^2-x)/2+1/12) := by fun_prop
  exact hc.continuousOn.comp_fract'' (by norm_num)

/-- Primitive amplitude for integration by parts against the height character. -/
def criticalLogPrimitiveKernel (x : ℝ) : ℝ :=
  (RHTower.bernoulliPeriodic x+1/12)*x^(-(3/2:ℝ))*Real.log x

/-- Literal right derivative, retaining the arithmetic slope at integer joins. -/
def criticalLogDerivativeKernel (x : ℝ) : ℝ :=
  (Int.fract x-1/2)*x^(-(3/2:ℝ))*Real.log x+
    (RHTower.bernoulliPeriodic x+1/12)*x^(-(5/2:ℝ))*(1-(3/2)*Real.log x)

/-- Positive integrable majorant for the complete signed derivative. -/
def criticalLogDerivativeMajorant (x : ℝ) : ℝ :=
  (1/2)*x^(-(3/2:ℝ))*Real.log x+
    (1/12)*x^(-(5/2:ℝ))*(1+(3/2)*Real.log x)

/-- Actual full logarithmic density. -/
def criticalLogSourceDensity (t x : ℝ) : ℂ :=
  (((RHTower.bernoulliPeriodic x+1/12)*x^(-(5/2:ℝ))*Real.log x:ℝ):ℂ)*
    Complex.exp (((t*Real.log x:ℝ):ℂ)*Complex.I)

/-- Oscillatory arithmetic derivative; its sign is retained. -/
def criticalLogFluxDensity (t x : ℝ) : ℂ :=
  (criticalLogDerivativeKernel x:ℂ)*Complex.exp (((t*Real.log x:ℝ):ℂ)*Complex.I)

/-- The primitive amplitude vanishes at the unit endpoint. -/
theorem criticalLogPrimitiveKernel_one : criticalLogPrimitiveKernel 1=0 := by
  simp [criticalLogPrimitiveKernel]

/-- Right differentiation of the amplitude keeps every arithmetic join. -/
theorem hasDerivWithinAt_criticalLogPrimitiveKernel {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt criticalLogPrimitiveKernel (criticalLogDerivativeKernel x) (Ioi x) x := by
  have hp := ((bernoulliPeriodic_hasDerivWithinAt_right x).add_const (1/12)).mono Ioi_subset_Ici_self
  have hw := Real.hasDerivAt_rpow_const (p := -(3/2:ℝ)) (Or.inl hx.ne')
  have hl := Real.hasDerivAt_log hx.ne'
  have he : x^(-(3/2:ℝ))=x^(-(5/2:ℝ))*x := by
    calc
      _ = x^((-(5/2:ℝ))+1) := by norm_num
      _ = _ := by rw [Real.rpow_add hx,Real.rpow_one]
  convert! (hp.mul hw.hasDerivWithinAt).mul hl.hasDerivWithinAt using 1
  unfold criticalLogDerivativeKernel
  simp only [Pi.mul_apply]
  norm_num only
  rw [he]
  field_simp
  ring

/-- The complete derivative is bounded by explicit positive logarithmic moments. -/
theorem abs_criticalLogDerivativeKernel_le {x : ℝ} (hx : 1 ≤ x) :
    |criticalLogDerivativeKernel x| ≤ criticalLogDerivativeMajorant x := by
  have hl := Real.log_nonneg hx
  have hp : 0 ≤ x^(-(5/2:ℝ)) := Real.rpow_nonneg (zero_lt_one.trans_le hx).le _
  have hq : 0 ≤ x^(-(3/2:ℝ)) := Real.rpow_nonneg (zero_lt_one.trans_le hx).le _
  have hf : |Int.fract x-1/2| ≤ 1/2 := by
    have h0 := Int.fract_nonneg x
    have h1 := Int.fract_lt_one x
    rw [abs_le]; constructor <;> linarith
  have hlog : |1-(3/2)*Real.log x| ≤ 1+(3/2)*Real.log x := by
    exact (abs_sub _ _).trans_eq (by rw [abs_of_pos zero_lt_one,abs_of_nonneg (by positivity)])
  unfold criticalLogDerivativeKernel criticalLogDerivativeMajorant
  calc
    _ ≤ |(Int.fract x-1/2)*x^(-(3/2:ℝ))*Real.log x|+
      |(RHTower.bernoulliPeriodic x+1/12)*x^(-(5/2:ℝ))*(1-(3/2)*Real.log x)| := abs_add_le _ _
    _ = |Int.fract x-1/2| *x^(-(3/2:ℝ))*Real.log x+
      |RHTower.bernoulliPeriodic x+1/12| *x^(-(5/2:ℝ))*|1-(3/2)*Real.log x| := by
      simp only [abs_mul,abs_of_nonneg hq,abs_of_nonneg hp,abs_of_nonneg hl]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf hq) hl)
      (mul_le_mul (mul_le_mul_of_nonneg_right (abs_centeredBernoulliKernel_le x) hp) hlog
        (abs_nonneg _) (by positivity))

/-- The derivative majorant is integrable on the entire half-line. -/
theorem integrable_criticalLogDerivativeMajorant : IntegrableOn criticalLogDerivativeMajorant (Ioi (1:ℝ)) := by
  have h1 : IntegrableOn (fun x : ℝ => x^(-(3/2:ℝ))*Real.log x) (Ioi (1:ℝ)) := by
    convert RHTower.integrableOn_rpow_mul_log_Ioi_one (by norm_num : (0:ℝ)<1/2) using 1
    norm_num
  have h2 : IntegrableOn (fun x : ℝ => x^(-(5/2:ℝ))*Real.log x) (Ioi (1:ℝ)) := by
    convert RHTower.integrableOn_rpow_mul_log_Ioi_one (by norm_num : (0:ℝ)<3/2) using 1
    norm_num
  have h0 := integrableOn_Ioi_rpow_of_lt (by norm_num : -(5/2:ℝ)< -1) zero_lt_one
  have he : criticalLogDerivativeMajorant = fun x : ℝ =>
      (1/2)*(x^(-(3/2:ℝ))*Real.log x)+(1/12)*(x^(-(5/2:ℝ))+(3/2)*(x^(-(5/2:ℝ))*Real.log x)) := by
    funext x; unfold criticalLogDerivativeMajorant; ring
  rw [he]
  exact (h1.const_mul (1/2)).add ((h0.add (h2.const_mul (3/2))).const_mul (1/12))

/-- Exact total mass of the source derivative majorant. -/
theorem integral_criticalLogDerivativeMajorant : (∫ x in Ioi (1:ℝ), criticalLogDerivativeMajorant x)=19/9 := by
  have h1 : IntegrableOn (fun x : ℝ => x^(-(3/2:ℝ))*Real.log x) (Ioi (1:ℝ)) := by
    convert RHTower.integrableOn_rpow_mul_log_Ioi_one (by norm_num : (0:ℝ)<1/2) using 1
    norm_num
  have h2 : IntegrableOn (fun x : ℝ => x^(-(5/2:ℝ))*Real.log x) (Ioi (1:ℝ)) := by
    convert RHTower.integrableOn_rpow_mul_log_Ioi_one (by norm_num : (0:ℝ)<3/2) using 1
    norm_num
  have h0 := integrableOn_Ioi_rpow_of_lt (by norm_num : -(5/2:ℝ)< -1) zero_lt_one
  have he : criticalLogDerivativeMajorant = fun x : ℝ =>
      (1/2)*(x^(-(3/2:ℝ))*Real.log x)+(1/12)*(x^(-(5/2:ℝ))+(3/2)*(x^(-(5/2:ℝ))*Real.log x)) := by
    funext x; unfold criticalLogDerivativeMajorant; ring
  have hsum : IntegrableOn (fun x : ℝ => x^(-(5/2:ℝ))+(3/2)*(x^(-(5/2:ℝ))*Real.log x)) (Ioi (1:ℝ)) :=
    h0.add (h2.const_mul (3/2))
  rw [he,integral_add (h1.const_mul (1/2)) (hsum.const_mul (1/12)),
    integral_const_mul,integral_const_mul,integral_add h0 (h2.const_mul (3/2)),integral_const_mul]
  have hm1 : (∫ x in Ioi (1:ℝ), x^(-(3/2:ℝ))*Real.log x)=4 := by
    convert RHTower.integral_rpow_mul_log_Ioi_one (by norm_num : (0:ℝ)<1/2) using 1 <;> norm_num
  have hm2 : (∫ x in Ioi (1:ℝ), x^(-(5/2:ℝ))*Real.log x)=4/9 := by
    convert RHTower.integral_rpow_mul_log_Ioi_one (by norm_num : (0:ℝ)<3/2) using 1 <;> norm_num
  rw [hm1,hm2,integral_Ioi_rpow_of_lt (by norm_num : -(5/2:ℝ)< -1) zero_lt_one]
  norm_num

/-- The signed arithmetic derivative is measurable despite its slope jumps. -/
theorem measurable_criticalLogDerivativeKernel : Measurable criticalLogDerivativeKernel := by
  unfold criticalLogDerivativeKernel RHTower.bernoulliPeriodic
  fun_prop

/-- The full signed flux is integrable; no frequency sector has been dropped. -/
theorem integrable_criticalLogFluxDensity (t : ℝ) : IntegrableOn (criticalLogFluxDensity t) (Ioi (1:ℝ)) := by
  apply Integrable.mono integrable_criticalLogDerivativeMajorant
  · have hm := measurable_criticalLogDerivativeKernel
    unfold criticalLogFluxDensity
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [criticalLogFluxDensity,norm_mul]
    simp only [Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,Real.exp_zero,mul_one]
    exact (abs_criticalLogDerivativeKernel_le hx.le).trans (le_abs_self _)

/-- The literal source density has the existing full response as its integral. -/
theorem integral_criticalLogSourceDensity (t : ℝ) :
    (∫ x in Ioi (1:ℝ), criticalLogSourceDensity t x)=criticalFullLogResponse t := by
  unfold criticalLogSourceDensity criticalFullLogResponse
  apply integral_congr_ae
  filter_upwards with x
  push_cast
  ring

/-- Absolute integrability of the full critical source density. -/
theorem integrable_criticalLogSourceDensity (t : ℝ) : IntegrableOn (criticalLogSourceDensity t) (Ioi (1:ℝ)) := by
  have hm : IntegrableOn (fun x : ℝ => x^(-(5/2:ℝ))*Real.log x) (Ioi (1:ℝ)) := by
    convert RHTower.integrableOn_rpow_mul_log_Ioi_one (by norm_num : (0:ℝ)<3/2) using 1
    norm_num
  apply Integrable.mono (hm.const_mul (1/12))
  · unfold criticalLogSourceDensity RHTower.bernoulliPeriodic
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hp := Real.rpow_nonneg (zero_lt_one.trans hx).le (-(5/2:ℝ))
    have hl := Real.log_nonneg hx.le
    simp only [criticalLogSourceDensity,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,
      Real.exp_zero,mul_one,abs_of_nonneg hp,abs_of_nonneg hl]
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (abs_centeredBernoulliKernel_le x) hp) hl
    simpa only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/12),mul_assoc] using h

/-- Boundary primitive carrying the unchanged logarithmic height character. -/
def criticalLogBoundaryTerm (t x : ℝ) : ℂ :=
  (criticalLogPrimitiveKernel x:ℂ)*Complex.exp (((t*Real.log x:ℝ):ℂ)*Complex.I)

/-- Exact derivative of the logarithmic height character. -/
theorem hasDerivAt_logHeightCharacter (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Complex.exp (((t*Real.log y:ℝ):ℂ)*Complex.I))
      (Complex.exp (((t*Real.log x:ℝ):ℂ)*Complex.I)*((t/x:ℝ):ℂ)*Complex.I) x := by
  convert! ((((Real.hasDerivAt_log hx.ne').const_mul t).ofReal_comp).mul_const Complex.I).cexp using 1
  push_cast
  ring

/-- The full boundary primitive is continuous on the positive half-line. -/
theorem continuousAt_criticalLogBoundaryTerm (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (criticalLogBoundaryTerm t) x := by
  have hp := (Real.hasDerivAt_rpow_const (p := -(3/2:ℝ)) (Or.inl hx.ne')).continuousAt
  have hl := (Real.hasDerivAt_log hx.ne').continuousAt
  have ha : ContinuousAt criticalLogPrimitiveKernel x :=
    (continuous_centeredBernoulliKernel.continuousAt.mul hp).mul hl
  exact (Complex.continuous_ofReal.continuousAt.comp ha).mul (hasDerivAt_logHeightCharacter t hx).continuousAt

/-- The right derivative consists of the signed flux and the complete source response. -/
theorem hasDerivWithinAt_criticalLogBoundaryTerm (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt (criticalLogBoundaryTerm t)
      (criticalLogFluxDensity t x+(t:ℂ)*Complex.I*criticalLogSourceDensity t x) (Ioi x) x := by
  have he : x^(-(3/2:ℝ))=x^(-(5/2:ℝ))*x := by
    calc
      _ = x^((-(5/2:ℝ))+1) := by norm_num
      _ = _ := by rw [Real.rpow_add hx,Real.rpow_one]
  convert! (hasDerivWithinAt_criticalLogPrimitiveKernel hx).ofReal_comp.mul
    (hasDerivAt_logHeightCharacter t hx).hasDerivWithinAt using 1
  unfold criticalLogFluxDensity criticalLogPrimitiveKernel criticalLogSourceDensity
  have hxC : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [he]
  push_cast
  field_simp [hxC]

/-- The source primitive vanishes at infinity with its full oscillatory phase retained. -/
theorem tendsto_criticalLogBoundaryTerm_zero (t : ℝ) :
    Tendsto (criticalLogBoundaryTerm t) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => x^(-(3/2:ℝ))*Real.log x) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<3/2)).tendsto_div_nhds_zero
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [Real.rpow_neg hx.le]
    ring
  have ht' : Tendsto (fun x : ℝ => (1/12)*(x^(-(3/2:ℝ))*Real.log x)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ht.const_mul (1/12:ℝ)
  apply squeeze_zero_norm' ?_ ht'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  have hp := Real.rpow_nonneg (zero_lt_one.trans_le hx).le (-(3/2:ℝ))
  have hl := Real.log_nonneg hx
  simp only [criticalLogBoundaryTerm,criticalLogPrimitiveKernel,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,sub_zero,Real.exp_zero,mul_one,abs_of_nonneg hp,abs_of_nonneg hl]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (abs_centeredBernoulliKernel_le x) hp) hl

/-- Exact full-source integration by parts; every integer join and both boundaries are accounted for. -/
theorem criticalFullLogResponse_flux_identity (t : ℝ) :
    (t:ℂ)*Complex.I*criticalFullLogResponse t = -(∫ x in Ioi (1:ℝ), criticalLogFluxDensity t x) := by
  let D : ℝ → ℂ := fun x => criticalLogFluxDensity t x+(t:ℂ)*Complex.I*criticalLogSourceDensity t x
  have hD : IntegrableOn D (Ioi (1:ℝ)) := (integrable_criticalLogFluxDensity t).add
    ((integrable_criticalLogSourceDensity t).const_mul ((t:ℂ)*Complex.I))
  have hi := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (1:ℝ) hD tendsto_id
  have he : ∀ᶠ b : ℝ in atTop, (∫ x in (1:ℝ)..b, D x)=criticalLogBoundaryTerm t b := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with b hb
    have hc : ContinuousOn (criticalLogBoundaryTerm t) (uIcc (1:ℝ) b) := by
      intro x hx
      exact (continuousAt_criticalLogBoundaryTerm t
        (zero_lt_one.trans_le ((uIcc_of_le hb ▸ hx).1))).continuousWithinAt
    have hd : ∀ x ∈ Ioo (min (1:ℝ) b) (max (1:ℝ) b),
        HasDerivWithinAt (criticalLogBoundaryTerm t) (D x) (Ioi x) x := by
      intro x hx
      rw [min_eq_left hb,max_eq_right hb] at hx
      exact hasDerivWithinAt_criticalLogBoundaryTerm t (zero_lt_one.trans hx.1)
    have hint : IntervalIntegrable D volume 1 b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mpr (hD.mono_set Ioc_subset_Ioi_self)
    have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right hc hd hint
    simpa only [criticalLogBoundaryTerm,criticalLogPrimitiveKernel_one,Complex.ofReal_zero,zero_mul,sub_zero] using h
  have hzero : (∫ x in Ioi (1:ℝ), D x)=0 :=
    tendsto_nhds_unique hi ((tendsto_criticalLogBoundaryTerm_zero t).congr' (he.mono (fun _ h => h.symm)))
  dsimp only [D] at hzero
  rw [integral_add (integrable_criticalLogFluxDensity t) ((integrable_criticalLogSourceDensity t).const_mul ((t:ℂ)*Complex.I)),
    integral_const_mul,integral_criticalLogSourceDensity] at hzero
  rw [add_comm] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

/-- Height times the norm of the whole critical response has an absolute arithmetic ceiling. -/
theorem height_mul_norm_criticalFullLogResponse_le (t : ℝ) : |t| * ‖criticalFullLogResponse t‖ ≤ 19/9 := by
  have hn : ‖∫ x in Ioi (1:ℝ), criticalLogFluxDensity t x‖ ≤ 19/9 := by
    rw [←integral_criticalLogDerivativeMajorant]
    apply norm_integral_le_of_norm_le integrable_criticalLogDerivativeMajorant
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [criticalLogFluxDensity,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,
      Real.exp_zero,mul_one]
    exact abs_criticalLogDerivativeKernel_le hx.le
  have h := congrArg norm (criticalFullLogResponse_flux_identity t)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,norm_neg] at h
  exact h ▸ hn

/-- Inverse-height decay of the actual complete critical logarithmic source. -/
theorem norm_criticalFullLogResponse_le_inverse_height {t : ℝ} (ht : t≠0) :
    ‖criticalFullLogResponse t‖ ≤ 19/(9*|t|) := by
  have h := height_mul_norm_criticalFullLogResponse_le t
  have ht' := abs_pos.mpr ht
  apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<9) ht')).mpr
  nlinarith

end RHTower.DeletionMixedRefinement
