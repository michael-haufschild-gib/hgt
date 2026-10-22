import GaloisForLFunctions.RHTower.ThetaQuantileResistanceNetwork
import GaloisForLFunctions.RHTower.ThetaQuantileHalfPowerThreshold
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspNativeOddSchurFarTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullDerivativeExponentialMoments
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltFluxSourceWeld
import GaloisForLFunctions.RHTower.ThetaDerivativePacketDivisor
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmClosedWeightedDerivative

/-!
# The theta quotient as an oblique Stein-score projection

Put `q = Q' = 1/h`, `s = −h' = −H(Q)` (`H = k'/k` the log-hazard of the theta source).  The theta
tails give `|H(x)| ≤ C e^{2|x|}`, hence finite Fisher information `∫ k'²/k < ∞` and `s ∈ L²(0,1)`;
the endpoint products `Q h` vanish.  Then

* `∫₀¹ Q s = 1`, `V s = −h`, `A s = −i P h`;
* `Π f = f − (∫ Q f) s` is a projection with range `Q^⊥` and kernel `ℂ s`;
* `T D = A Π` on `H₀` (the one-port pencil with the input port written through the score);
* `ker D ∩ H₀ = ℂ s`: the coupled frequencies have the exact zero vector `s`, although every
  isolated `{n, −n}` block of `D` is invertible.
-/

namespace RHTower

open MeasureTheory Filter Topology Set HedenmalmThetaSource HedenmalmQuantile GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace

noncomputable section

local notation "ThetaL2" => Lp ℂ 2 unitIntervalMeasure

/-! ## The theta score and its Fisher information -/

/-- **The hazard bound** `|H(x)| ≤ C e^{2|x|}`. -/
theorem exists_abs_thetaLogHazard_le : ∃ C : ℝ, 0 < C ∧ ∀ x, |thetaLogHazard x| ≤ C * Real.exp (2 * |x|) := by
  obtain ⟨X, hX⟩ := eventually_atTop.1 ((thetaCuspFullSource_deriv_div_firstAtom_scale_tendsto.eventually
    (Ioo_mem_nhds (show (-3 : ℝ) < -2 by norm_num) (show (-2 : ℝ) < -1 by norm_num))))
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := max X 0)).exists_bound_of_continuousOn
    continuous_thetaLogHazard.continuousOn
  set C : ℝ := max C₀ (3 * Real.pi) + 1
  have hC : 0 < C := by have := le_max_right C₀ (3 * Real.pi); positivity
  have hpos : ∀ x, 0 ≤ x → |thetaLogHazard x| ≤ C * Real.exp (2 * x) := by
    intro x hx
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    rcases le_or_gt x (max X 0) with hxX | hxX
    · have h1 := hC₀ x ⟨hx, hxX⟩
      rw [Real.norm_eq_abs] at h1
      calc |thetaLogHazard x| ≤ C₀ := h1
        _ ≤ C := by have := le_max_left C₀ (3 * Real.pi); linarith
        _ ≤ C * Real.exp (2 * x) := le_mul_of_one_le_right hC.le he
    have hx0 : 0 < x := lt_of_le_of_lt (le_max_right X 0) hxX
    have hr := hX x (le_of_lt (lt_of_le_of_lt (le_max_left X 0) hxX))
    set r := deriv thetaCuspFullSource x / (thetaCuspSourceTerm x 1 * thetaCuspSingleAtomReflectionScale 1 x)
    have hterm : 0 < thetaCuspSourceTerm x 1 :=
      lt_of_lt_of_le (mul_pos thetaEnvelopeLower_pos (thetaEnvelope_pos x)) (thetaCuspSourceTerm_one_ge hx)
    have hscale : thetaCuspSingleAtomReflectionScale 1 x = Real.pi * Real.exp (2 * x) := by
      simp [thetaCuspSingleAtomReflectionScale]
    have hden : 0 < thetaCuspSourceTerm x 1 * thetaCuspSingleAtomReflectionScale 1 x := by
      rw [hscale]; positivity
    have hk : thetaCuspSourceTerm x 1 ≤ thetaCuspFullSource x := by
      rw [thetaCuspFullSource]
      exact (summable_thetaCuspSourceTerm x).le_tsum 1 (fun j _ => thetaCuspSourceTerm_nonneg_of_pos hx0 j)
    have hkpos := thetaCuspFullSource_pos x
    have hd : deriv thetaCuspFullSource x = r * (thetaCuspSourceTerm x 1 * thetaCuspSingleAtomReflectionScale 1 x) := by
      simp only [r]; rw [div_mul_cancel₀ _ hden.ne']
    have hrabs : |r| ≤ 3 := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
    rw [thetaLogHazard, abs_div, abs_of_pos hkpos, div_le_iff₀ hkpos, hd, abs_mul, abs_of_pos hden, hscale]
    calc |r| * (thetaCuspSourceTerm x 1 * (Real.pi * Real.exp (2 * x)))
        ≤ 3 * (thetaCuspFullSource x * (Real.pi * Real.exp (2 * x))) := by
          gcongr
      _ = (3 * Real.pi) * Real.exp (2 * x) * thetaCuspFullSource x := by ring
      _ ≤ C * Real.exp (2 * x) * thetaCuspFullSource x := by
          gcongr
          have := le_max_right C₀ (3 * Real.pi); linarith
  refine ⟨C, hC, fun x => ?_⟩
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact hpos x hx
  · have := hpos (-x) (by linarith)
    rwa [thetaLogHazard_neg, abs_neg, ← abs_of_neg hx] at this

/-- `H ρ = k'/M`. -/
theorem thetaLogHazard_mul_normalized (x : ℝ) :
    thetaLogHazard x * thetaSource.normalized x = deriv thetaCuspFullSource x / thetaSource.mass := by
  have hk := thetaCuspFullSource_pos x
  rw [thetaLogHazard, PositiveDensitySource.normalized]
  change deriv thetaCuspFullSource x / thetaCuspFullSource x * (thetaCuspFullSource x / thetaSource.mass) = _
  field_simp

/-- **Finite Fisher information of the theta score**: `∫ H² ρ < ∞`. -/
theorem integrable_thetaLogHazard_sq_mul_normalized :
    Integrable fun x => thetaLogHazard x ^ 2 * thetaSource.normalized x := by
  obtain ⟨C, hC, hH⟩ := exists_abs_thetaLogHazard_le
  have hM := thetaSource.mass_pos
  have hbound := (integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource 1 2).const_mul (C / thetaSource.mass)
  refine hbound.mono' ((continuous_thetaLogHazard.pow 2).mul
    continuous_normalized_theta).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hρ := thetaSource.normalized_pos x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq, mul_assoc, thetaLogHazard_mul_normalized,
    iteratedDeriv_one]
  calc thetaLogHazard x * (deriv thetaCuspFullSource x / thetaSource.mass)
      ≤ |thetaLogHazard x| * (|deriv thetaCuspFullSource x| / thetaSource.mass) := by
        rw [← abs_of_pos hM, ← abs_div, ← abs_mul, abs_of_pos hM]
        exact le_abs_self _
    _ ≤ C * Real.exp (2 * |x|) * (|deriv thetaCuspFullSource x| / thetaSource.mass) :=
        mul_le_mul_of_nonneg_right (hH x) (by positivity)
    _ = C / thetaSource.mass * (Real.exp (2 * |x|) * |deriv thetaCuspFullSource x|) := by ring

/-- **Finite Fisher information** `∫ k'²/k < ∞`. -/
theorem integrable_thetaFisherInformation :
    Integrable fun x => deriv thetaCuspFullSource x ^ 2 / thetaCuspFullSource x := by
  refine (integrable_thetaLogHazard_sq_mul_normalized.const_mul thetaSource.mass).congr
    (Eventually.of_forall fun x => ?_)
  have hk := thetaCuspFullSource_pos x
  have hM := thetaSource.mass_pos
  simp only [thetaLogHazard, PositiveDensitySource.normalized]
  change thetaSource.mass * ((deriv thetaCuspFullSource x / thetaCuspFullSource x) ^ 2 *
    (thetaCuspFullSource x / thetaSource.mass)) = _
  field_simp

/-- The location score `s = −H(Q) = −h'`. -/
def thetaScoreFun (t : ℝ) : ℝ := -thetaLogHazard (thetaQuantile t)

theorem measurable_thetaScoreFun : Measurable thetaScoreFun :=
  (continuous_thetaLogHazard.measurable.comp thetaSource.measurable_quantileFun).neg

theorem thetaScoreFun_cdfFun (x : ℝ) : thetaScoreFun (thetaSource.cdfFun x) = -thetaLogHazard x := by
  rw [thetaScoreFun, thetaQuantile, thetaSource.quantile_cdfFun]

/-- **`s ∈ L²(0,1)`**: `∫₀¹ s² = ∫ H² ρ`. -/
theorem memLp_thetaScore : MemLp (fun t => (thetaScoreFun t : ℂ)) 2 unitIntervalMeasure := by
  have hm : AEStronglyMeasurable (fun t => (thetaScoreFun t : ℂ)) unitIntervalMeasure :=
    (Complex.continuous_ofReal.measurable.comp measurable_thetaScoreFun).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm).2 ((integrable_unitInterval_iff_cdf
    (hm.norm.pow 2)).2 ?_)
  refine integrable_thetaLogHazard_sq_mul_normalized.congr (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, Pi.pow_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs, thetaScoreFun_cdfFun,
    neg_sq]
  ring

/-- The score vector `s ∈ L²(0,1)`. -/
def thetaScoreVec : ThetaL2 := memLp_thetaScore.toLp _

theorem thetaScoreVec_ae : (thetaScoreVec : ℝ → ℂ) =ᵐ[unitIntervalMeasure] fun t => (thetaScoreFun t : ℂ) :=
  MemLp.coeFn_toLp _

theorem integrableOn_thetaScoreFun : IntegrableOn thetaScoreFun (Icc 0 1) := by
  have h := (memLp_thetaScore.integrable one_le_two).norm
  refine (h.congr (Eventually.of_forall fun t => ?_) : Integrable (fun t => |thetaScoreFun t|) _) |>.mono'
    measurable_thetaScoreFun.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  · simp only [Complex.norm_real, Real.norm_eq_abs]
  · rw [Real.norm_eq_abs]

/-! ## The endpoint products and the score moment -/

theorem exists_norm_mul_thetaCuspFullSource_le :
    ∃ C : ℝ, ∀ x, ‖x * thetaCuspFullSource x‖ ≤ C * Real.exp (-|x|) := by
  obtain ⟨C, hC, hk⟩ := thetaCuspFullSource_superexponential_envelope 2
  refine ⟨C, fun x => ?_⟩
  have hkx := hk x
  have hk0 := (thetaCuspFullSource_pos x).le
  have hx : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hk0]
  calc |x| * thetaCuspFullSource x ≤ Real.exp |x| * (C * Real.exp (-(2 * |x|))) :=
        mul_le_mul hx hkx hk0 (Real.exp_pos _).le
    _ = C * Real.exp (-|x|) := by rw [mul_left_comm, ← Real.exp_add]; ring_nf

theorem tendsto_mul_thetaCuspFullSource_atBot :
    Tendsto (fun x => x * thetaCuspFullSource x) atBot (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_norm_mul_thetaCuspFullSource_le
  have hexp : Tendsto (fun x : ℝ => C * Real.exp x) atBot (𝓝 0) := by
    simpa using Real.tendsto_exp_atBot.const_mul C
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [eventually_le_atBot 0] with x hx
  have := hC x
  rwa [abs_of_nonpos hx, neg_neg] at this

theorem tendsto_mul_thetaCuspFullSource_atTop :
    Tendsto (fun x => x * thetaCuspFullSource x) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_norm_mul_thetaCuspFullSource_le
  have hexp : Tendsto (fun x : ℝ => C * Real.exp (-x)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [eventually_ge_atTop 0] with x hx
  have := hC x
  rwa [abs_of_nonneg hx] at this

theorem tendsto_thetaQuantile_nhdsLT_one : Tendsto thetaQuantile (𝓝[<] 1) atTop := by
  have hc : Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 0) := by
    have := (tendsto_const_nhds (x := (1 : ℝ)) (f := 𝓝 (1 : ℝ))).sub (tendsto_id (x := 𝓝 (1 : ℝ)))
    simpa using this
  have h1 : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hc.mono_left nhdsWithin_le_nhds)
      (by filter_upwards [self_mem_nhdsWithin] with t ht; exact sub_pos.2 (mem_Iio.1 ht))
  have h2 := tendsto_neg_atBot_atTop.comp (tendsto_thetaQuantile_nhdsGT_zero.comp h1)
  refine h2.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have ht' : 1 - t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simp only [Function.comp_apply]
  rw [← quantileFun_one_sub ht', sub_sub_cancel]

/-- **The endpoint product `Q h` vanishes at `0`.** -/
theorem tendsto_thetaQuantile_mul_profile_nhdsGT_zero :
    Tendsto (fun t => thetaQuantile t * thetaQuantileProfile t) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_mul_thetaCuspFullSource_atBot.comp tendsto_thetaQuantile_nhdsGT_zero).div_const
    thetaSource.mass
  rw [zero_div] at h
  refine h.congr fun t => ?_
  simp only [Function.comp_apply, thetaQuantileProfile_eq]
  ring

/-- **The endpoint product `Q h` vanishes at `1`.** -/
theorem tendsto_thetaQuantile_mul_profile_nhdsLT_one :
    Tendsto (fun t => thetaQuantile t * thetaQuantileProfile t) (𝓝[<] 1) (𝓝 0) := by
  have h := (tendsto_mul_thetaCuspFullSource_atTop.comp tendsto_thetaQuantile_nhdsLT_one).div_const
    thetaSource.mass
  rw [zero_div] at h
  refine h.congr fun t => ?_
  simp only [Function.comp_apply, thetaQuantileProfile_eq]
  ring

/-- **The score moment** `∫₀¹ Q s = 1`. -/
theorem integral_thetaQuantile_mul_score :
    ∫ t, thetaSource.quantileFun t * thetaScoreFun t ∂unitIntervalMeasure = 1 := by
  rw [integral_unitInterval_eq_cdf (g := fun t => thetaSource.quantileFun t * thetaScoreFun t)
    (thetaSource.measurable_quantileFun.mul measurable_thetaScoreFun).aestronglyMeasurable]
  have hM := thetaSource.mass_pos
  have hpt : ∀ x, thetaSource.normalized x • (thetaSource.quantileFun (thetaSource.cdfFun x) *
      thetaScoreFun (thetaSource.cdfFun x)) = -(1 / thetaSource.mass) * (x ^ 1 * iteratedDeriv 1 thetaCuspFullSource x) := by
    intro x
    rw [smul_eq_mul, thetaSource.quantile_cdfFun, thetaScoreFun_cdfFun, iteratedDeriv_one, pow_one,
      show thetaSource.normalized x * (x * -thetaLogHazard x) =
        -x * (thetaLogHazard x * thetaSource.normalized x) by ring, thetaLogHazard_mul_normalized]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, show (1 : ℕ) = 0 + 1 from rfl, integral_pow_mul_iteratedDeriv_succ_thetaCuspFullSource]
  simp only [Nat.cast_one, zero_add, pow_zero, one_mul, iteratedDeriv_zero, Nat.sub_self]
  have hmass : ∫ x, thetaCuspFullSource x = thetaSource.mass := rfl
  rw [hmass]
  field_simp

/-! ## The score is the pinned primitive of the profile -/

theorem hasDerivAt_thetaNetworkProfile {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt thetaNetworkProfile (thetaLogHazard (thetaQuantile t)) t :=
  (hasDerivAt_thetaQuantileProfile ht).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) fun _ hs => thetaNetworkProfile_of_mem hs)

/-- `∫₀ᵗ s = −h(t)` on `[0,1]`. -/
theorem integral_thetaScoreFun {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∫ u in (0 : ℝ)..t, thetaScoreFun u = -thetaNetworkProfile t := by
  have hint : IntervalIntegrable (fun u => thetaLogHazard (thetaQuantile u)) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1]
    exact (integrableOn_thetaScoreFun.mono_set (Icc_subset_Icc le_rfl ht.2)).neg.congr_fun
      (fun u _ => by simp [thetaScoreFun]) measurableSet_Icc
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (continuousOn_thetaNetworkProfile.mono (Icc_subset_Icc le_rfl ht.2))
    (fun u hu => hasDerivAt_thetaNetworkProfile ⟨hu.1, lt_of_lt_of_le hu.2 ht.2⟩) hint
  have h0 : thetaNetworkProfile 0 = 0 := if_neg (by simp)
  simp only [thetaScoreFun, intervalIntegral.integral_neg, h, h0, sub_zero]

theorem pinnedPrefix_thetaScoreVec {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pinnedPrefix thetaScoreVec t = -(thetaNetworkProfile t : ℂ) := by
  rw [pinnedPrefix]
  have hae : (Iic t).indicator (fun u => (thetaScoreVec : ℝ → ℂ) u) =ᵐ[unitIntervalMeasure]
      (Iic t).indicator fun u => (thetaScoreFun u : ℂ) :=
    thetaScoreVec_ae.indicator
  rw [integral_congr_ae hae, integral_unitInterval_Iic_eq ht, intervalIntegral.integral_ofReal,
    integral_thetaScoreFun ht, Complex.ofReal_neg]

/-- **`s ∈ H₀`**: `∫₀¹ s = h(0) − h(1) = 0`. -/
theorem pinnedMean_thetaScoreVec : pinnedMean thetaScoreVec = 0 := by
  have h := pinnedPrefix_thetaScoreVec (t := 1) ⟨zero_le_one, le_rfl⟩
  have h1 : thetaNetworkProfile 1 = 0 := if_neg (by simp)
  rw [h1, Complex.ofReal_zero, neg_zero] at h
  rw [← h, pinnedPrefix, pinnedMean]
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_Icc_unitInterval] with u hu
  rw [indicator_of_mem (mem_Iic.2 hu.2)]

theorem thetaScoreVec_mem : thetaScoreVec ∈ meanZeroSpace := by
  rw [mem_meanZeroSpace_iff, inner_constMode_eq_pinnedMean, pinnedMean_thetaScoreVec]

/-- The profile vector `h = M_h 1 ∈ L²(0,1)`. -/
theorem coeFn_profileVector :
    (thetaMetricOperator constMode : ℝ → ℂ) =ᵐ[unitIntervalMeasure] fun t => (thetaQuantileProfile t : ℂ) := by
  filter_upwards [coeFn_thetaMetricOperator constMode, coeFn_unitFourierBasis 0] with t h1 h2
  rw [h1, show (constMode : ThetaL2) = unitFourierBasis 0 from rfl, h2, fourierMode_zero, mul_one,
    metricSymbol, thetaQuantileProfile_eq]
  rfl

/-- **`V s = −h`.** -/
theorem pinnedVolterraCLM_thetaScoreVec : pinnedVolterraCLM thetaScoreVec = -thetaMetricOperator constMode := by
  apply Lp.ext
  filter_upwards [pinnedVolterra_coeFn thetaScoreVec, Lp.coeFn_neg (thetaMetricOperator constMode),
    coeFn_profileVector, ae_mem_Icc_unitInterval, ae_restrict_mem measurableSet_Ioo |>.filter_mono
      (le_of_eq (by rw [unitIntervalMeasure_eq]))] with t h1 h2 h3 h4 h5
  change (pinnedVolterra thetaScoreVec : ℝ → ℂ) t = _
  rw [h1, h2, Pi.neg_apply, h3, pinnedVolterraFun, pinnedPrefix_thetaScoreVec h4, pinnedMean_thetaScoreVec,
    mul_zero, sub_zero, thetaNetworkProfile_of_mem h5]

/-- **`A s = −i P h`.** -/
theorem onePortPrimitive_thetaScoreVec : onePortPrimitive thetaScoreVec = -Complex.I • onePortOutputVector := by
  rw [onePortPrimitive, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, meanZeroProj_eq_self thetaScoreVec_mem, pinnedVolterraCLM_thetaScoreVec,
    map_neg, onePortOutputVector, smul_neg, neg_smul]

/-! ## The oblique score projection -/

theorem inner_quantileVec (f : ThetaL2) :
    ⟪quantileVec, f⟫_ℂ = ∫ t, (thetaSource.quantileFun t : ℂ) * f t ∂unitIntervalMeasure := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [quantileVec_ae] with t ht
  rw [RCLike.inner_apply, ht, Complex.conj_ofReal, mul_comm]

/-- `β(f) = −i ⟨Q, f⟩`. -/
theorem onePortInput_eq_inner_quantileVec (f : ThetaL2) :
    onePortInput f = -Complex.I * ⟪quantileVec, f⟫_ℂ := by
  rw [onePortInput_eq_quantile, inner_quantileVec]

/-- `⟨Q, s⟩ = 1`. -/
theorem inner_quantileVec_thetaScoreVec : ⟪quantileVec, thetaScoreVec⟫_ℂ = 1 := by
  rw [inner_quantileVec]
  have h := congrArg (fun r : ℝ => (r : ℂ)) integral_thetaQuantile_mul_score
  simp only [Complex.ofReal_one] at h
  rw [← h, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [thetaScoreVec_ae] with t ht
  rw [ht]
  push_cast
  rfl

/-- The oblique score projection `Π f = f − ⟨Q, f⟩ s`. -/
def scoreProjection : ThetaL2 →L[ℂ] ThetaL2 :=
  ContinuousLinearMap.id ℂ ThetaL2 - (innerSL ℂ quantileVec).smulRight thetaScoreVec

theorem scoreProjection_apply (f : ThetaL2) :
    scoreProjection f = f - ⟪quantileVec, f⟫_ℂ • thetaScoreVec := by
  simp [scoreProjection, innerSL_apply_apply]

theorem inner_quantileVec_scoreProjection (f : ThetaL2) : ⟪quantileVec, scoreProjection f⟫_ℂ = 0 := by
  rw [scoreProjection_apply, inner_sub_right, inner_smul_right, inner_quantileVec_thetaScoreVec, mul_one, sub_self]

/-- **`Π² = Π`.** -/
theorem scoreProjection_idem : scoreProjection ∘L scoreProjection = scoreProjection := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [ContinuousLinearMap.comp_apply, scoreProjection_apply (scoreProjection f),
    inner_quantileVec_scoreProjection, zero_smul, sub_zero]

/-- **`ran Π = Q^⊥`.** -/
theorem mem_range_scoreProjection_iff (f : ThetaL2) :
    f ∈ Set.range scoreProjection ↔ ⟪quantileVec, f⟫_ℂ = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    exact inner_quantileVec_scoreProjection g
  · intro h
    exact ⟨f, by rw [scoreProjection_apply, h, zero_smul, sub_zero]⟩

/-- **`ker Π = ℂ s`.** -/
theorem scoreProjection_eq_zero_iff (f : ThetaL2) :
    scoreProjection f = 0 ↔ ∃ c : ℂ, f = c • thetaScoreVec := by
  constructor
  · intro h
    exact ⟨⟪quantileVec, f⟫_ℂ, sub_eq_zero.1 ((scoreProjection_apply f).symm.trans h)⟩
  · rintro ⟨c, rfl⟩
    rw [scoreProjection_apply, inner_smul_right, inner_quantileVec_thetaScoreVec, mul_one, sub_self]

theorem scoreProjection_mem {f : ThetaL2} (hf : f ∈ meanZeroSpace) : scoreProjection f ∈ meanZeroSpace := by
  rw [scoreProjection_apply]
  exact meanZeroSpace.sub_mem hf (meanZeroSpace.smul_mem _ thetaScoreVec_mem)

/-- **`T D = A Π` on `H₀`.** -/
theorem onePortMetric_thetaQuotientOperator_eq_scoreProjection {f : ThetaL2} (hf : f ∈ meanZeroSpace) :
    onePortMetric (thetaQuotientOperator f) = onePortPrimitive (scoreProjection f) := by
  rw [onePortMetric_thetaQuotientOperator hf, scoreProjection_apply, map_sub, map_smul,
    onePortPrimitive_thetaScoreVec, onePortInput_eq_inner_quantileVec, smul_smul]
  congr 1
  ring_nf

/-! ## The exact zero vector of the coupled quotient -/

theorem thetaKernelOperator_thetaScoreVec : thetaKernelOperator thetaScoreVec = -Complex.I • constMode := by
  apply Lp.ext
  filter_upwards [thetaKernelOperator_ae thetaScoreVec, pinnedVolterra_coeFn thetaScoreVec,
    Lp.coeFn_smul (-Complex.I) constMode, coeFn_unitFourierBasis 0, ae_mem_Icc_unitInterval,
    ae_restrict_mem measurableSet_Ioo |>.filter_mono (le_of_eq (by rw [unitIntervalMeasure_eq]))]
    with t h1 h2 h3 h4 h5 h6
  rw [h1, h3, Pi.smul_apply, show (constMode : ThetaL2) = unitFourierBasis 0 from rfl, h4, fourierMode_zero,
    pinnedVolterraFun, pinnedPrefix_thetaScoreVec h5, pinnedMean_thetaScoreVec, mul_zero, sub_zero,
    thetaNetworkProfile_of_mem h6, thetaQuantileProfile, smul_eq_mul, mul_one]
  have hq : (thetaQuantileSpeed t : ℂ) ≠ 0 := by exact_mod_cast (thetaQuantileSpeed_pos t).ne'
  push_cast
  field_simp

/-- **`D s = 0`**: the coupled quotient has the exact zero vector `s`. -/
theorem thetaQuotientOperator_thetaScoreVec : thetaQuotientOperator thetaScoreVec = 0 := by
  rw [thetaQuotientOperator_apply, thetaKernelOperator_thetaScoreVec,
    map_smul, show (constMode : ThetaL2) = unitFourierBasis 0 from rfl,
    meanZeroProj_apply, show unitFourierBasis 0 = constMode from rfl, inner_constMode_self, one_smul, sub_self,
    smul_zero]

/-- **`ker D ∩ H₀ = ℂ s`.** -/
theorem thetaQuotientOperator_eq_zero_iff {f : ThetaL2} (hf : f ∈ meanZeroSpace) :
    thetaQuotientOperator f = 0 ↔ ∃ c : ℂ, f = c • thetaScoreVec := by
  constructor
  · intro h0
    set β := onePortInput f
    have hB : thetaKernelOperator f = β • constMode := by
      have h := meanZeroProj_thetaKernelOperator f
      rw [← thetaQuotientOperator_apply, h0] at h
      exact (sub_eq_zero.1 h.symm)
    set c : ℂ := Complex.I * β
    have hV : pinnedVolterraCLM f = c • pinnedVolterraCLM thetaScoreVec := by
      apply Lp.ext
      filter_upwards [pinnedVolterra_coeFn f, thetaKernelOperator_ae f,
        congrArg (fun g : ThetaL2 => (g : ℝ → ℂ)) hB ▸ (Lp.coeFn_smul β constMode),
        Lp.coeFn_smul c (pinnedVolterraCLM thetaScoreVec), pinnedVolterra_coeFn thetaScoreVec,
        coeFn_unitFourierBasis 0, ae_mem_Icc_unitInterval,
        ae_restrict_mem measurableSet_Ioo |>.filter_mono (le_of_eq (by rw [unitIntervalMeasure_eq]))]
        with t h1 h2 h3 h4 h5 h6 h7 h8
      change (pinnedVolterra f : ℝ → ℂ) t = _
      rw [h4, Pi.smul_apply]
      change _ = c • (pinnedVolterra thetaScoreVec : ℝ → ℂ) t
      have hs : pinnedVolterraFun thetaScoreVec t = -(thetaQuantileProfile t : ℂ) := by
        rw [pinnedVolterraFun, pinnedPrefix_thetaScoreVec h7, pinnedMean_thetaScoreVec, mul_zero, sub_zero,
          thetaNetworkProfile_of_mem h8]
      rw [h1, h5, hs, thetaQuantileProfile]
      rw [h3, Pi.smul_apply, show (constMode : ThetaL2) = unitFourierBasis 0 from rfl, h6, fourierMode_zero,
        smul_eq_mul, mul_one] at h2
      have hq : (thetaQuantileSpeed t : ℂ) ≠ 0 := by exact_mod_cast (thetaQuantileSpeed_pos t).ne'
      have hV : pinnedVolterraFun f t = -Complex.I * β / (thetaQuantileSpeed t : ℂ) := by
        rw [eq_div_iff hq]
        linear_combination (-Complex.I) * h2.symm + (pinnedVolterraFun f t * (thetaQuantileSpeed t : ℂ)) * Complex.I_sq
      rw [hV, smul_eq_mul]
      simp only [c]
      push_cast
      field_simp
    have hmean : pinnedMean (f - c • thetaScoreVec) = 0 := by
      rw [← inner_constMode_eq_pinnedMean, ← mem_meanZeroSpace_iff]
      exact meanZeroSpace.sub_mem hf (meanZeroSpace.smul_mem _ thetaScoreVec_mem)
    have hzero : pinnedVolterra (f - c • thetaScoreVec) = 0 := by
      change pinnedVolterraCLM (f - c • thetaScoreVec) = 0
      rw [map_sub, map_smul, hV, sub_self]
    exact ⟨c, sub_eq_zero.1 (HedenmalmClosedWeightedDerivative.eq_zero_of_pinnedMean_eq_zero_of_pinnedVolterra_eq_zero
      _ hmean hzero)⟩
  · rintro ⟨c, rfl⟩
    rw [map_smul, thetaQuotientOperator_thetaScoreVec, smul_zero]

end

end RHTower
