import GaloisForLFunctions.RHTower.ThetaCuspCassiniCalibratedReciprocalMomentNoGo

open Complex Filter MeasureTheory Metric Set Topology

namespace RHTower

noncomputable section

/-- Positive extension of `t ^ (-alpha)` used as a globally measurable pushforward map. -/
def negativePowerKernel (alpha t : ℝ) : ℝ :=
  Real.exp (-alpha * Real.log t)

theorem negativePowerKernel_eq_rpow {alpha t : ℝ} (ht : 0 < t) :
    negativePowerKernel alpha t = t ^ (-alpha) := by
  rw [negativePowerKernel, Real.rpow_def_of_pos ht]
  congr 1
  ring

theorem negativePowerKernel_pos (alpha t : ℝ) :
    0 < negativePowerKernel alpha t :=
  Real.exp_pos _

theorem measurable_negativePowerKernel (alpha : ℝ) :
    Measurable (negativePowerKernel alpha) := by
  exact Real.measurable_exp.comp
    (measurable_const.mul Real.measurable_log)

theorem continuous_negativePowerKernel_left (t : ℝ) :
    Continuous (fun alpha => negativePowerKernel alpha t) := by
  rw [show (fun alpha => negativePowerKernel alpha t) =
      fun alpha => Real.exp (-alpha * Real.log t) by rfl]
  exact Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)

/-- Average negative-power profile of a finite positive measure. -/
def normalizedNegativePowerProfile (mu : Measure ℝ) (alpha : ℝ) : ℝ :=
  (∫ t : ℝ, negativePowerKernel alpha t ∂mu) / mu.real Set.univ

section Generic

variable {mu : Measure ℝ} [IsFiniteMeasure mu] {c : ℝ}

theorem integrable_negativePowerKernel_of_ae_lower_bound
    (hc : 1 < c) (hsupport : ∀ᵐ t ∂mu, c ≤ t) {alpha : ℝ} (halpha : 0 ≤ alpha) :
    Integrable (negativePowerKernel alpha) mu := by
  refine Integrable.of_bound
    (measurable_negativePowerKernel alpha).aestronglyMeasurable 1 ?_
  filter_upwards [hsupport] with t ht
  have htpos : 0 < t := zero_lt_one.trans (hc.trans_le ht)
  rw [Real.norm_eq_abs, abs_of_pos (negativePowerKernel_pos alpha t),
    negativePowerKernel_eq_rpow htpos]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (le_trans (le_of_lt hc) ht) (neg_nonpos.mpr halpha)

theorem continuousOn_normalizedNegativePowerProfile
    (hc : 1 < c) (hsupport : ∀ᵐ t ∂mu, c ≤ t) :
    ContinuousOn (normalizedNegativePowerProfile mu) (Set.Ici 0) := by
  have hintegral : ContinuousOn
      (fun alpha : ℝ => ∫ t : ℝ, negativePowerKernel alpha t ∂mu) (Set.Ici 0) := by
    intro alpha halpha
    apply tendsto_integral_filter_of_norm_le_const
    · exact Eventually.of_forall fun beta =>
        (measurable_negativePowerKernel beta).aestronglyMeasurable
    · refine ⟨1, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with beta hbeta
      filter_upwards [hsupport] with t ht
      have htpos : 0 < t := zero_lt_one.trans (hc.trans_le ht)
      rw [Real.norm_eq_abs, abs_of_pos (negativePowerKernel_pos beta t),
        negativePowerKernel_eq_rpow htpos]
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (le_trans (le_of_lt hc) ht) (neg_nonpos.mpr hbeta)
    · exact Eventually.of_forall fun t =>
        (continuous_negativePowerKernel_left t).continuousAt.tendsto.mono_left inf_le_left
  exact hintegral.div_const _

theorem normalizedNegativePowerProfile_pos
    (hmu : 0 < mu Set.univ) (hc : 1 < c) (hsupport : ∀ᵐ t ∂mu, c ≤ t)
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    0 < normalizedNegativePowerProfile mu alpha := by
  letI : NeZero mu := ⟨by
    intro hzero
    rw [hzero] at hmu
    simp at hmu⟩
  rw [normalizedNegativePowerProfile]
  exact div_pos
    (integral_exp_pos
      (integrable_negativePowerKernel_of_ae_lower_bound hc hsupport halpha))
    (ENNReal.toReal_pos hmu.ne' (measure_ne_top mu Set.univ))

theorem normalizedNegativePowerProfile_zero
    (hmu : 0 < mu Set.univ) :
    normalizedNegativePowerProfile mu 0 = 1 := by
  have hmass : 0 < mu.real Set.univ :=
    ENNReal.toReal_pos hmu.ne' (measure_ne_top mu Set.univ)
  unfold normalizedNegativePowerProfile negativePowerKernel
  simp only [neg_zero, zero_mul, Real.exp_zero, integral_const, smul_eq_mul, mul_one]
  exact div_self hmass.ne'

theorem normalizedNegativePowerProfile_le_lower_rpow
    (hmu : 0 < mu Set.univ) (hc : 1 < c) (hsupport : ∀ᵐ t ∂mu, c ≤ t)
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    normalizedNegativePowerProfile mu alpha ≤ c ^ (-alpha) := by
  have hmass : 0 < mu.real Set.univ :=
    ENNReal.toReal_pos hmu.ne' (measure_ne_top mu Set.univ)
  have hint := integrable_negativePowerKernel_of_ae_lower_bound hc hsupport halpha
  have hconst : Integrable (fun _ : ℝ => c ^ (-alpha)) mu := integrable_const _
  have hleae : ∀ᵐ t ∂mu, negativePowerKernel alpha t ≤ c ^ (-alpha) := by
    filter_upwards [hsupport] with t ht
    rw [negativePowerKernel_eq_rpow (zero_lt_one.trans (hc.trans_le ht))]
    exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans hc) ht (neg_nonpos.mpr halpha)
  have hintegral := integral_mono_ae hint hconst hleae
  unfold normalizedNegativePowerProfile
  rw [integral_const, smul_eq_mul] at hintegral
  apply (div_le_iff₀ hmass).2
  nlinarith

theorem strictAntiOn_normalizedNegativePowerProfile
    (hmu : 0 < mu Set.univ) (hc : 1 < c) (hsupport : ∀ᵐ t ∂mu, c ≤ t) :
    StrictAntiOn (normalizedNegativePowerProfile mu) (Set.Ici 0) := by
  letI : NeZero mu := ⟨by
    intro hzero
    rw [hzero] at hmu
    simp at hmu⟩
  intro alpha halpha beta hbeta hab
  have hialpha := integrable_negativePowerKernel_of_ae_lower_bound hc hsupport halpha
  have hibeta := integrable_negativePowerKernel_of_ae_lower_bound hc hsupport hbeta
  have hlt : ∀ᵐ t ∂mu,
      negativePowerKernel beta t < negativePowerKernel alpha t := by
    filter_upwards [hsupport] with t ht
    have htone : 1 < t := hc.trans_le ht
    rw [negativePowerKernel_eq_rpow (zero_lt_one.trans htone),
      negativePowerKernel_eq_rpow (zero_lt_one.trans htone)]
    exact Real.rpow_lt_rpow_of_exponent_lt htone (neg_lt_neg hab)
  have hleae : negativePowerKernel beta ≤ᵐ[mu] negativePowerKernel alpha :=
    hlt.mono fun _ ht => ht.le
  have hle : (∫ t, negativePowerKernel beta t ∂mu) ≤
      ∫ t, negativePowerKernel alpha t ∂mu :=
    integral_mono_ae hibeta hialpha hleae
  have hne : (∫ t, negativePowerKernel beta t ∂mu) ≠
      ∫ t, negativePowerKernel alpha t ∂mu := by
    intro heq
    have hae := (integral_eq_iff_of_ae_le hibeta hialpha hleae).mp heq
    have hfalse : ∀ᵐ _t ∂mu, False := by
      filter_upwards [hlt, hae] with t ht hteq
      exact (ne_of_lt ht) hteq
    exact (Filter.Eventually.exists hfalse).elim fun _ h => h
  rw [normalizedNegativePowerProfile]
  exact (div_lt_div_iff_of_pos_right
    (ENNReal.toReal_pos hmu.ne' (measure_ne_top mu Set.univ))).2
      (lt_of_le_of_ne hle hne)

theorem tendsto_normalizedNegativePowerProfile_atTop
    (hc : 1 < c) (hsupport : ∀ᵐ t ∂mu, c ≤ t) :
    Tendsto (normalizedNegativePowerProfile mu) atTop (nhds 0) := by
  have hintegral : Tendsto
      (fun alpha : ℝ => ∫ t : ℝ, negativePowerKernel alpha t ∂mu) atTop (nhds 0) := by
    have hmeas : ∀ᶠ alpha : ℝ in atTop,
        AEStronglyMeasurable (negativePowerKernel alpha) mu :=
      Eventually.of_forall fun alpha =>
        (measurable_negativePowerKernel alpha).aestronglyMeasurable
    have hbound : ∃ C, ∀ᶠ alpha : ℝ in atTop,
        ∀ᵐ t ∂mu, ‖negativePowerKernel alpha t‖ ≤ C := by
      refine ⟨1, ?_⟩
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with alpha halpha
      filter_upwards [hsupport] with t ht
      have htpos : 0 < t := zero_lt_one.trans (hc.trans_le ht)
      rw [Real.norm_eq_abs, abs_of_pos (negativePowerKernel_pos alpha t),
        negativePowerKernel_eq_rpow htpos]
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (le_trans (le_of_lt hc) ht) (neg_nonpos.mpr halpha)
    have hlim : ∀ᵐ t ∂mu,
        Tendsto (fun alpha : ℝ => negativePowerKernel alpha t) atTop (nhds 0) := by
      filter_upwards [hsupport] with t ht
      have hlog : 0 < Real.log t := Real.log_pos (hc.trans_le ht)
      rw [show (fun alpha => negativePowerKernel alpha t) =
          fun alpha => Real.exp ((-Real.log t) * alpha) by
        funext alpha
        rw [negativePowerKernel]
        congr 1
        ring]
      exact Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hlog))
    have hDCT := tendsto_integral_filter_of_norm_le_const
      (μ := mu) (ι := ℝ) (l := atTop)
      (F := fun alpha t => negativePowerKernel alpha t)
      (f := fun _ => (0 : ℝ)) hmeas hbound hlim
    simpa only [integral_zero] using hDCT
  unfold normalizedNegativePowerProfile
  simpa only [zero_div] using hintegral.div_const (mu.real Set.univ)

theorem existsUnique_gt_one_normalizedNegativePowerProfile_eq
    (hmu : 0 < mu Set.univ) (hc : 1 < c) (hsupport : ∀ᵐ t ∂mu, c ≤ t)
    {y : ℝ} (hy : 0 < y) (hyone : y < normalizedNegativePowerProfile mu 1) :
    ∃! alpha : ℝ, 1 < alpha ∧ normalizedNegativePowerProfile mu alpha = y := by
  have hcont := continuousOn_normalizedNegativePowerProfile hc hsupport
  have hdecay := tendsto_normalizedNegativePowerProfile_atTop hc hsupport
  have hevent : ∀ᶠ alpha : ℝ in atTop,
      1 ≤ alpha ∧ normalizedNegativePowerProfile mu alpha < y := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      hdecay.eventually (Iio_mem_nhds hy)] with alpha halpha hsmall
    exact ⟨halpha, hsmall⟩
  obtain ⟨A, hA, hsmall⟩ := Filter.Eventually.exists hevent
  have hcontIcc : ContinuousOn (normalizedNegativePowerProfile mu) (Set.Icc 1 A) :=
    hcont.mono (by
      intro alpha halpha
      exact show 0 ≤ alpha by linarith [halpha.1])
  obtain ⟨alpha, halpha, heq⟩ :=
    intermediate_value_Ioo' hA hcontIcc ⟨hsmall, hyone⟩
  refine ⟨alpha, ⟨halpha.1, heq⟩, ?_⟩
  · intro beta hbeta
    have hstrict := strictAntiOn_normalizedNegativePowerProfile hmu hc hsupport
    have halpha0 : alpha ∈ Set.Ici (0 : ℝ) := by exact le_trans (by norm_num) halpha.1.le
    have hbeta0 : beta ∈ Set.Ici (0 : ℝ) := by exact le_trans (by norm_num) hbeta.1.le
    exact (hstrict.injOn halpha0 hbeta0 (heq.trans hbeta.2.symm)).symm

end Generic

/-! ## Theta-cusp specialization -/

/-- Normalized negative-power profile of the fixed higher theta likelihood carrier. -/
def thetaCuspNormalizedNegativePowerProfile (alpha : ℝ) : ℝ :=
  normalizedNegativePowerProfile
    (thetaCuspHigherLikelihoodTiltedMeasure (thetaCuspLikelihoodCoordinate 0)) alpha

/-- Uncalibrated higher theta carrier pushed through the power-reciprocal coordinate. -/
def thetaCuspCassiniHigherPowerReciprocalLikelihoodMeasure (alpha : ℝ) : Measure ℝ :=
  Measure.map (negativePowerKernel alpha)
    (thetaCuspHigherLikelihoodTiltedMeasure (thetaCuspLikelihoodCoordinate 0))

/-- Unique scalar calibrating every power-reciprocal pushforward to source mass `m₀`. -/
def thetaCuspCassiniPowerReciprocalCalibration : ENNReal :=
  ENNReal.ofReal (normalizedPrimeArchMoment 0) /
    thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0) Set.univ

/-- Source-calibrated power-reciprocal theta carrier. -/
def thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
    (alpha : ℝ) : Measure ℝ :=
  thetaCuspCassiniPowerReciprocalCalibration •
    thetaCuspCassiniHigherPowerReciprocalLikelihoodMeasure alpha

private theorem thetaCuspHigherLikelihoodTiltedMeasure_seam_finite :
    IsFiniteMeasure (thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)) := by
  exact thetaCuspHigherLikelihoodTiltedMeasure_finite
    (thetaCuspLikelihoodCoordinate_pos le_rfl)

theorem continuousOn_thetaCuspNormalizedNegativePowerProfile :
    ContinuousOn thetaCuspNormalizedNegativePowerProfile (Set.Ici 0) := by
  letI : IsFiniteMeasure (thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)) :=
    thetaCuspHigherLikelihoodTiltedMeasure_seam_finite
  exact continuousOn_normalizedNegativePowerProfile (c := 3) (by norm_num)
    (ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0))

theorem strictAntiOn_thetaCuspNormalizedNegativePowerProfile :
    StrictAntiOn thetaCuspNormalizedNegativePowerProfile (Set.Ici 0) := by
  letI : IsFiniteMeasure (thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)) :=
    thetaCuspHigherLikelihoodTiltedMeasure_seam_finite
  exact strictAntiOn_normalizedNegativePowerProfile
    thetaCuspHigherLikelihoodTiltedMeasure_seam_mass_pos (c := 3) (by norm_num)
    (ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0))

theorem tendsto_thetaCuspNormalizedNegativePowerProfile_atTop :
    Tendsto thetaCuspNormalizedNegativePowerProfile atTop (nhds 0) := by
  letI : IsFiniteMeasure (thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)) :=
    thetaCuspHigherLikelihoodTiltedMeasure_seam_finite
  exact tendsto_normalizedNegativePowerProfile_atTop
    (c := 3) (by norm_num)
    (ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0))

theorem thetaCuspNormalizedNegativePowerProfile_zero :
    thetaCuspNormalizedNegativePowerProfile 0 = 1 := by
  letI : IsFiniteMeasure (thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)) :=
    thetaCuspHigherLikelihoodTiltedMeasure_seam_finite
  exact normalizedNegativePowerProfile_zero
    thetaCuspHigherLikelihoodTiltedMeasure_seam_mass_pos

theorem thetaCuspNormalizedNegativePowerProfile_pos
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    0 < thetaCuspNormalizedNegativePowerProfile alpha := by
  letI : IsFiniteMeasure (thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)) :=
    thetaCuspHigherLikelihoodTiltedMeasure_seam_finite
  exact normalizedNegativePowerProfile_pos
    thetaCuspHigherLikelihoodTiltedMeasure_seam_mass_pos (c := 3) (by norm_num)
    (ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)) halpha

theorem thetaCuspNormalizedNegativePowerProfile_le_three_rpow
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    thetaCuspNormalizedNegativePowerProfile alpha ≤ (3 : ℝ) ^ (-alpha) := by
  letI : IsFiniteMeasure (thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)) :=
    thetaCuspHigherLikelihoodTiltedMeasure_seam_finite
  exact normalizedNegativePowerProfile_le_lower_rpow
    thetaCuspHigherLikelihoodTiltedMeasure_seam_mass_pos (c := 3) (by norm_num)
    (ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)) halpha

/-- The exact first theta atom beats the rational floor used in the paper proof. -/
theorem one_div_eightHundredSixtyFour_lt_thetaCuspHigherLikelihoodTiltedMeasure_singleton_three_real :
    (1 / 864 : ℝ) <
      (thetaCuspHigherLikelihoodTiltedMeasure
        (thetaCuspLikelihoodCoordinate 0)).real {3} := by
  have hcube : (1 / 24 : ℝ) ^ 3 < Real.exp (-Real.pi) ^ 3 :=
    pow_lt_pow_left₀ one_div_twentyFour_lt_exp_neg_pi (by norm_num) (by norm_num)
  have hexp : (1 / 13824 : ℝ) < Real.exp (-3 * Real.pi) := by
    rw [← Real.exp_nat_mul] at hcube
    convert hcube using 1 <;> norm_num
  rw [Measure.real_def,
    thetaCuspHigherLikelihoodTiltedMeasure_seam_singleton_three,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 16 * Real.exp (-3 * Real.pi))]
  nlinarith

private theorem thetaCuspHigherLikelihoodTiltedMeasure_seam_measureReal_univ_le :
    (thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)).real Set.univ ≤ (8 / 2997 : ℝ) := by
  have h := thetaCuspCassiniHigherReciprocalLikelihoodMeasure_measureReal_univ_le
  rw [thetaCuspCassiniHigherReciprocalLikelihoodMeasure, Measure.real_def,
    Measure.map_apply measurable_thetaCuspLikelihoodReciprocalGap MeasurableSet.univ] at h
  rw [Measure.real_def]
  simpa only [preimage_univ] using h

/-- The normalized reciprocal profile already lies above the sharp rational barrier `37/256`. -/
theorem thirtySeven_div_twoHundredFiftySix_lt_thetaCuspNormalizedNegativePowerProfile_one :
    (37 / 256 : ℝ) < thetaCuspNormalizedNegativePowerProfile 1 := by
  let nu : Measure ℝ := thetaCuspHigherLikelihoodTiltedMeasure
    (thetaCuspLikelihoodCoordinate 0)
  letI : IsFiniteMeasure nu := thetaCuspHigherLikelihoodTiltedMeasure_seam_finite
  have hmassENN : 0 < nu Set.univ := by
    simpa only [nu] using thetaCuspHigherLikelihoodTiltedMeasure_seam_mass_pos
  have hmass : 0 < nu.real Set.univ :=
    ENNReal.toReal_pos hmassENN.ne' (measure_ne_top nu Set.univ)
  have hmassLe : nu.real Set.univ ≤ (8 / 2997 : ℝ) := by
    simpa only [nu] using thetaCuspHigherLikelihoodTiltedMeasure_seam_measureReal_univ_le
  have hatom : (1 / 864 : ℝ) < nu.real {3} := by
    simpa only [nu] using
      one_div_eightHundredSixtyFour_lt_thetaCuspHigherLikelihoodTiltedMeasure_singleton_three_real
  have hsupport : ∀ᵐ t ∂nu, (3 : ℝ) ≤ t := by
    simpa only [nu] using
      (ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure
        (thetaCuspLikelihoodCoordinate 0))
  have hint : Integrable (negativePowerKernel 1) nu :=
    integrable_negativePowerKernel_of_ae_lower_bound (c := 3) (by norm_num)
      hsupport (by norm_num)
  have hsingle :
      ∫ t : ℝ in ({3} : Set ℝ), negativePowerKernel 1 t ∂nu =
        (1 / 3 : ℝ) * nu.real {3} := by
    rw [integral_singleton, smul_eq_mul,
      negativePowerKernel_eq_rpow (by norm_num : (0 : ℝ) < 3),
      Real.rpow_neg_one]
    norm_num
    ring
  have hle : ∫ t : ℝ in ({3} : Set ℝ), negativePowerKernel 1 t ∂nu ≤
      ∫ t : ℝ, negativePowerKernel 1 t ∂nu :=
    setIntegral_le_integral hint
      (Eventually.of_forall fun t => (negativePowerKernel_pos 1 t).le)
  unfold thetaCuspNormalizedNegativePowerProfile normalizedNegativePowerProfile
  apply (lt_div_iff₀ hmass).2
  calc
    (37 / 256 : ℝ) * nu.real Set.univ ≤
        (37 / 256 : ℝ) * (8 / 2997) :=
      mul_le_mul_of_nonneg_left hmassLe (by norm_num)
    _ = (1 / 3 : ℝ) * (1 / 864) := by norm_num
    _ < (1 / 3 : ℝ) * nu.real {3} :=
      mul_lt_mul_of_pos_left hatom (by norm_num)
    _ = ∫ t : ℝ in ({3} : Set ℝ), negativePowerKernel 1 t ∂nu := hsingle.symm
    _ ≤ ∫ t : ℝ, negativePowerKernel 1 t ∂nu := hle

/-- Exact source first-moment ceiling used by the quantitative reciprocal obstruction. -/
theorem normalizedPrimeArchMoment_one_lt_twentyNine_over_oneThousandTwoHundredFifty_mul_zero :
    normalizedPrimeArchMoment 1 <
      (29 / 1250 : ℝ) * normalizedPrimeArchMoment 0 := by
  have h0 := one_div_twentyFive_lt_normalizedPrimeArchMoment_zero
  have h1 := normalizedPrimeArchMoment_one_lt_nine_over_fiftyThousand
  nlinarith

/-- Canonical source first-to-zero moment ratio lies below the profile at exponent one. -/
theorem normalizedPrimeArchMoment_ratio_lt_thetaCuspNormalizedNegativePowerProfile_one :
    normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 <
      thetaCuspNormalizedNegativePowerProfile 1 := by
  have hratio : normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 <
      (29 / 1250 : ℝ) := by
    apply (div_lt_iff₀ normalizedPrimeArchMoment_zero_pos).2
    exact
      normalizedPrimeArchMoment_one_lt_twentyNine_over_oneThousandTwoHundredFifty_mul_zero
  exact hratio.trans (by
    have hprofile :=
      thirtySeven_div_twoHundredFiftySix_lt_thetaCuspNormalizedNegativePowerProfile_one
    norm_num at hprofile ⊢
    linarith)

/-- Unique source-selected exponent solving normalized barycenter calibration. -/
theorem existsUnique_thetaCuspSourceSelectedPowerReciprocalExponent :
    ∃! alpha : ℝ, 1 < alpha ∧
      thetaCuspNormalizedNegativePowerProfile alpha =
        normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 := by
  letI : IsFiniteMeasure (thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)) :=
    thetaCuspHigherLikelihoodTiltedMeasure_seam_finite
  exact existsUnique_gt_one_normalizedNegativePowerProfile_eq
    thetaCuspHigherLikelihoodTiltedMeasure_seam_mass_pos (c := 3) (by norm_num)
    (ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0))
    (div_pos normalizedPrimeArchMoment_one_pos normalizedPrimeArchMoment_zero_pos)
    normalizedPrimeArchMoment_ratio_lt_thetaCuspNormalizedNegativePowerProfile_one

/-- Canonical exponent selected by source zeroth and first moments. -/
noncomputable def thetaCuspSourceSelectedPowerReciprocalExponent : ℝ :=
  Classical.choose existsUnique_thetaCuspSourceSelectedPowerReciprocalExponent

theorem thetaCuspSourceSelectedPowerReciprocalExponent_gt_one :
    1 < thetaCuspSourceSelectedPowerReciprocalExponent :=
  (Classical.choose_spec existsUnique_thetaCuspSourceSelectedPowerReciprocalExponent).1.1

theorem thetaCuspSourceSelectedPowerReciprocalExponent_profile :
    thetaCuspNormalizedNegativePowerProfile
        thetaCuspSourceSelectedPowerReciprocalExponent =
      normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 :=
  (Classical.choose_spec existsUnique_thetaCuspSourceSelectedPowerReciprocalExponent).1.2

theorem thetaCuspCassiniHigherPowerReciprocalLikelihoodMeasure_finite (alpha : ℝ) :
    IsFiniteMeasure (thetaCuspCassiniHigherPowerReciprocalLikelihoodMeasure alpha) := by
  letI : IsFiniteMeasure (thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)) :=
    thetaCuspHigherLikelihoodTiltedMeasure_seam_finite
  rw [thetaCuspCassiniHigherPowerReciprocalLikelihoodMeasure]
  infer_instance

theorem thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_univ (alpha : ℝ) :
    thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure alpha Set.univ =
      ENNReal.ofReal (normalizedPrimeArchMoment 0) := by
  rw [thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure,
    Measure.smul_apply, smul_eq_mul, thetaCuspCassiniPowerReciprocalCalibration,
    thetaCuspCassiniHigherPowerReciprocalLikelihoodMeasure,
    Measure.map_apply (measurable_negativePowerKernel alpha) MeasurableSet.univ]
  simp only [preimage_univ]
  exact ENNReal.div_mul_cancel
    thetaCuspHigherLikelihoodTiltedMeasure_seam_mass_pos.ne'
    (by
      letI : IsFiniteMeasure (thetaCuspHigherLikelihoodTiltedMeasure
          (thetaCuspLikelihoodCoordinate 0)) :=
        thetaCuspHigherLikelihoodTiltedMeasure_seam_finite
      exact measure_ne_top _ _)

theorem thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_finite (alpha : ℝ) :
    IsFiniteMeasure (thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure alpha) := by
  refine IsFiniteMeasure.mk ?_
  rw [thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_univ]
  exact ENNReal.ofReal_lt_top

/-- Calibrated first moment is source mass times the normalized power profile. -/
theorem integral_thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_id
    (alpha : ℝ) :
    (∫ x : ℝ, x ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure alpha) =
      normalizedPrimeArchMoment 0 * thetaCuspNormalizedNegativePowerProfile alpha := by
  let nu : Measure ℝ := thetaCuspHigherLikelihoodTiltedMeasure
    (thetaCuspLikelihoodCoordinate 0)
  letI : IsFiniteMeasure nu := thetaCuspHigherLikelihoodTiltedMeasure_seam_finite
  rw [thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure,
    integral_smul_measure, smul_eq_mul,
    thetaCuspCassiniHigherPowerReciprocalLikelihoodMeasure]
  rw [integral_map
    (μ := thetaCuspHigherLikelihoodTiltedMeasure (thetaCuspLikelihoodCoordinate 0))
    (φ := negativePowerKernel alpha) (f := fun x : ℝ => x)
    (measurable_negativePowerKernel alpha).aemeasurable
    continuous_id.aestronglyMeasurable]
  rw [
    thetaCuspCassiniPowerReciprocalCalibration,
    ENNReal.toReal_div,
    ENNReal.toReal_ofReal normalizedPrimeArchMoment_zero_pos.le]
  unfold thetaCuspNormalizedNegativePowerProfile normalizedNegativePowerProfile
  rw [Measure.real_def]
  ring

theorem ae_thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_support
    {alpha : ℝ} (halpha : 1 < alpha) :
    ∀ᵐ x ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure alpha,
      0 < x ∧ x < 1 / 3 := by
  rw [thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure]
  apply Measure.ae_smul_measure
  rw [thetaCuspCassiniHigherPowerReciprocalLikelihoodMeasure]
  apply (ae_map_iff (measurable_negativePowerKernel alpha).aemeasurable
    (measurableSet_Ioi.inter measurableSet_Iio)).2
  filter_upwards [ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure
      (thetaCuspLikelihoodCoordinate 0)] with t ht
  constructor
  · exact negativePowerKernel_pos alpha t
  · rw [negativePowerKernel_eq_rpow (zero_lt_one.trans (by linarith : 1 < t))]
    have hbase : t ^ (-alpha) ≤ (3 : ℝ) ^ (-alpha) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) ht (by linarith)
    have hexponent : (3 : ℝ) ^ (-alpha) < (3 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    rw [Real.rpow_neg_one] at hexponent
    norm_num at hexponent
    exact hbase.trans_lt hexponent

/-- Chosen power carrier matches source mass and barycenter exactly. -/
theorem thetaCuspSourceSelectedPowerReciprocal_mass_and_firstMoment :
    thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
        thetaCuspSourceSelectedPowerReciprocalExponent Set.univ =
      ENNReal.ofReal (normalizedPrimeArchMoment 0) ∧
    (∫ x : ℝ, x ∂thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure
        thetaCuspSourceSelectedPowerReciprocalExponent) =
      normalizedPrimeArchMoment 1 := by
  constructor
  · exact thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_univ _
  · rw [integral_thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_id,
      thetaCuspSourceSelectedPowerReciprocalExponent_profile]
    field_simp [normalizedPrimeArchMoment_zero_pos.ne']

/-- At exponent one, the power-reciprocal construction is exactly the fixed reciprocal carrier. -/
theorem thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_one :
    thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure 1 =
      thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure := by
  rw [thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure,
    thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure]
  congr 1
  · rw [thetaCuspCassiniPowerReciprocalCalibration,
      thetaCuspCassiniHigherReciprocalCalibration,
      thetaCuspCassiniHigherReciprocalLikelihoodMeasure,
      Measure.map_apply measurable_thetaCuspLikelihoodReciprocalGap MeasurableSet.univ]
    simp
  · rw [thetaCuspCassiniHigherPowerReciprocalLikelihoodMeasure,
      thetaCuspCassiniHigherReciprocalLikelihoodMeasure]
    apply Measure.map_congr
    filter_upwards [ae_three_le_thetaCuspHigherLikelihoodTiltedMeasure
        (thetaCuspLikelihoodCoordinate 0)] with t ht
    rw [negativePowerKernel_eq_rpow (zero_lt_one.trans (by linarith : 1 < t)),
      Real.rpow_neg_one]
    rfl

/-- Sharp calibrated fixed-reciprocal barycenter floor from the first charged theta atom. -/
theorem thirtySeven_div_twoHundredFiftySix_mul_normalizedPrimeArchMoment_zero_lt_calibratedReciprocal_firstMoment :
    (37 / 256 : ℝ) * normalizedPrimeArchMoment 0 <
      ∫ x : ℝ, x ∂thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure := by
  rw [← thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_one,
    integral_thetaCuspCassiniCalibratedPowerReciprocalLikelihoodMeasure_id]
  nlinarith [mul_lt_mul_of_pos_left
    thirtySeven_div_twoHundredFiftySix_lt_thetaCuspNormalizedNegativePowerProfile_one
    normalizedPrimeArchMoment_zero_pos]

/-- Exact quantitative degree-one obstruction for the fixed reciprocal exponent. -/
theorem normalizedPrimeArchMoment_one_add_quantitativeGap_lt_calibratedReciprocal_firstMoment :
    normalizedPrimeArchMoment 1 +
        (19413 / 160000 : ℝ) * normalizedPrimeArchMoment 0 <
      ∫ x : ℝ, x ∂thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure := by
  nlinarith [
    normalizedPrimeArchMoment_one_lt_twentyNine_over_oneThousandTwoHundredFifty_mul_zero,
    thirtySeven_div_twoHundredFiftySix_mul_normalizedPrimeArchMoment_zero_lt_calibratedReciprocal_firstMoment]

end

end RHTower
