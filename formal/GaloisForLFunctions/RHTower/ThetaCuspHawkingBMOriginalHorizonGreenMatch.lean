import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCharacteristicTransform
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIncomingHorizonExpansion
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceHorizonModeLimits
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalIncomingPairingResidue
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCornerSpectralBalance

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalHorizonGreenMatch
open D4BMOriginalCausalAdmission D4BMOriginalHorizonTimeTrace
open D4BMOriginalCharacteristicTransform D4BMJointSource D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private theorem source_re (q : XiZeroCopy) (br : Bool) (w : ℂ) (hw : 3/2 < w.re) :
    (2*physicalRate q br).re < w.re := by
  have h := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at h
  linarith

private theorem reader_re (q : XiZeroCopy) (w : ℂ) (hw : 3/2 < w.re) :
    (D4BMOriginalCirclePeriod.readerExponent q).re < w.re := by
  have h := (xi_divisor_support_re_mem_open_unit q.1).1
  norm_num [D4BMOriginalCirclePeriod.readerExponent]
  linarith

/-- The original collar integral has the exact physical radial normalization. -/
theorem original_collar_transform_normalized (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2 < w.re) (hwi : w.im ≠ 0) {L : ℝ} (hL : 0 < L) :
    (∫ p in Ioi (0:ℝ), Complex.exp (-w*(p:ℂ))*originalScalar q br amp p (p+L)) /
        power w (1+radialUnit (-L/2)) =
      physicalSelfSourceCoefficient q *
        (response w (physicalRadialFrequency q) (physicalRate q br) amp 1
          (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1)
          (onsetTransform (2*physicalRate q br) w) (horizonCoordinate (-L/2)) /
            power (w/2) (horizonCoordinate (-L/2))) := by
  let f : ℝ → ℂ := fun p => originalScalar q br amp p (p+L)
  have hf (p : ℝ) (hp : p < 0) : f p = 0 := by
    have hz := D4BMNativeResponse.radialResponse_zero_outside
      (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q br) amp
      ((p+(p+L))/2) ((p-(p+L))/2) (by
        rw [show (p-(p+L))/2 = -L/2 by ring,abs_of_neg (by linarith : -L/2 < 0)]
        exact max_lt (by linarith) (by linarith))
    simp only [f,originalScalar,nullValue,hz,D4BMOriginalCausalPotential.nullLift,
      timeOnset_zero_of_nonpos (2*physicalRate q br) hp.le,mul_zero,add_zero]
  have hd := GaloisForLFunctions.HTGeometry.causal_laplace_delay f hf w (-L/2) (by linarith)
  have he (t : ℝ) : f (t+-L/2)=originalScalar q br amp (t+-L/2) (t-(-L/2)) := by
    dsimp only [f]
    congr 1
    ring
  simp_rw [he] at hd
  rw [original_scalar_timeIntegral_eq_green q br amp w hw hwi (by linarith)] at hd
  simp only [continuedReducedGreen,mul_one,sub_add_cancel] at hd
  rw [continuedTortoiseGreen_eq_original w (physicalRadialFrequency q) (physicalRate q br)
    amp 1 (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1)
    hwi (by linarith) (source_re q br w hw) (-L/2) (by linarith)] at hd
  rw [horizonPower_tortoise w (-L/2) (by linarith)]
  dsimp only [tortoiseGreen,f] at hd
  have hE := Complex.exp_ne_zero (w*((-L/2:ℝ):ℂ))
  have hP := power_ne_zero w (radialUnit_add_one_pos (-L/2))
  rw [← mul_div_assoc,hd]
  field_simp [hE,hP]

private theorem unit_collar_limit :
    Tendsto (fun L : ℝ => radialUnit (-L/2)) atTop (𝓝 (1:ℝ)) := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero
  have hform (L : ℝ) : radialUnit (-L/2)=(1-Real.exp (-L))/(1+Real.exp (-L)) := by
    apply (eq_div_iff (ne_of_gt (by positivity : 0 < 1+Real.exp (-L)))).mpr
    have h := radialUnit_one_sub (-L/2)
    rw [show 2*(-L/2) = -L by ring] at h
    nlinarith
  simp_rw [hform]
  convert! (tendsto_const_nhds.sub he).div (tendsto_const_nhds.add he)
    (by norm_num : (1:ℝ)+0 ≠ 0) using 1
  · norm_num

private theorem coordinate_collar_limit :
    Tendsto (fun L : ℝ => horizonCoordinate (-L/2)) atTop (𝓝[>] (0:ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [horizonCoordinate,one_pow,sub_self] using unit_collar_limit.pow 2 |>.const_sub 1
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    exact (horizonCoordinate_interior (-L/2) (by linarith)).1

private theorem cornerAmplitude_eq_div (q : XiZeroCopy) (br : Bool) (amp w : ℂ) :
    cornerAmplitude q br amp w = horizonTransform q br amp w / power w 2 := by
  rw [cornerAmplitude,power]
  norm_num only [Complex.ofReal_ofNat]
  have hlog : Complex.log (2:ℂ)=(Real.log 2:ℂ) := by
    simpa only [Complex.ofReal_ofNat] using (Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 2)).symm
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ) ≠ 0),
    hlog,div_eq_mul_inv,← Complex.exp_neg,mul_comm]
  congr 1
  congr 1
  ring

/-- The actual original horizon/time amplitude equals the full Green endpoint moment.
This identifies the coefficient required by the moving corner, without assigning it. -/
theorem cornerAmplitude_eq_original_endpoint (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2 < w.re) (hwi : w.im ≠ 0) :
    cornerAmplitude q br amp w = physicalSelfSourceCoefficient q *
      outerMoment w (physicalRadialFrequency q) (physicalRate q br) amp 1
        (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1)
        (onsetTransform (2*physicalRate q br) w) 0 := by
  have hpow : Tendsto (fun L : ℝ => power w (1+radialUnit (-L/2))) atTop
      (𝓝 (power w 2)) := by
    have hu : Tendsto (fun L : ℝ => 1+radialUnit (-L/2)) atTop (𝓝 (2:ℝ)) := by
      convert! unit_collar_limit.const_add 1 using 1
      · norm_num
    exact ((power_derivatives w (by norm_num : (0:ℝ)<2)).1.continuousAt.tendsto).comp hu
  have hm := original_horizon_moment_limit q br amp w 0 (reader_re q w hw)
  simp only [pow_zero,one_mul] at hm
  have hleft := hm.div hpow (power_ne_zero w (by norm_num : (0:ℝ)<2))
  have hc := physicalRadialFrequency_chamber q w (by linarith : 1/2 < w.re)
  have hright := ((response_ingoing hc (physicalRate q br) amp 1
    (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1)
    (onsetTransform (2*physicalRate q br) w)).comp coordinate_collar_limit).const_mul
      (physicalSelfSourceCoefficient q)
  have hr := hright.congr' (by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    exact (original_collar_transform_normalized q br amp w hw hwi hL).symm)
  rw [cornerAmplitude_eq_div]
  exact tendsto_nhds_unique hleft hr


/-- Horizon coefficient of the same continued source-forced Green response. -/
def greenHorizonAmplitude (s chi a J K w : ℂ) : ℂ :=
  limUnder (𝓝[>] (0:ℝ)) (fun z => continuedResponse s chi a J K z w/horizon w chi z)

private theorem endpoint_limit (s chi a J K w : ℂ) {b : ℝ} (hb : 0 < b)
    (hp : ContinuousOn (incomingSourcePrimitive s chi a J K w) (Icc (0:ℝ) b))
    (he : ∀ z ∈ Ioc (0:ℝ) b,
      continuedResponse s chi a J K z w/horizon w chi z =
        incomingResponseEndpoint s chi a J K w b+incomingSourcePrimitive s chi a J K w z) :
    Tendsto (fun z => continuedResponse s chi a J K z w/horizon w chi z)
      (𝓝[>] (0:ℝ)) (𝓝 (incomingResponseEndpoint s chi a J K w b)) := by
  have hP := (hp 0 ⟨le_rfl,hb.le⟩).mono Ioo_subset_Icc_self
  rw [ContinuousWithinAt,nhdsWithin_Ioo_eq_nhdsGT hb] at hP
  simp only [incomingSourcePrimitive,intervalIntegral.integral_same] at hP
  have ht := hP.const_add (incomingResponseEndpoint s chi a J K w b)
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsGT hb] with z hz
  exact (he z ⟨hz.1,hz.2.le⟩).symm

/-- The continued horizon coefficient has the original local Green/source split,
with a source primitive analytic across connection zeros. -/
theorem greenHorizonAmplitude_local (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (hs : w-2*s ≠ 0) :
    ∃ R b : ℝ, 0 < R ∧ 0 < b ∧ b ≤ 1/2 ∧
      AnalyticAt ℂ (fun u => incomingSourcePrimitive s chi a J K u b) w ∧
      ∀ u ∈ Metric.ball w R, connection u chi ≠ 0 →
        greenHorizonAmplitude s chi a J K u=incomingResponseEndpoint s chi a J K u b := by
  obtain ⟨R,b,C,M,hR,hb,hbhalf,hC,hM,hdata⟩ :=
    incomingSourcePrimitive_common_data s chi a J K w hw hwr hs
  refine ⟨R,b,hR,hb,hbhalf,(hdata w (Metric.mem_ball_self hR)).2.2.2.2 b ⟨hb,le_rfl⟩ |>.1,?_⟩
  intro u hu hc
  exact (endpoint_limit s chi a J K u hb (hdata u hu).2.2.2.1
    (fun z hz => ((hdata u hu).2.2.2.2 z hz).2.2.2 hc)).limUnder_eq

/-- Local endpoint choices glue as one meromorphic function of the original frequency. -/
theorem greenHorizonAmplitude_meromorphic (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (hs : w-2*s ≠ 0) :
    MeromorphicAt (greenHorizonAmplitude s chi a J K) w := by
  obtain ⟨R,b,hR,hb,hbhalf,hP,he⟩ := greenHorizonAmplitude_local s chi a J K w hw hwr hs
  have hb1 : b < 1 := lt_of_le_of_lt hbhalf (by norm_num)
  have hm : MeromorphicAt (fun u => incomingResponseEndpoint s chi a J K u b) w :=
    ((continuedResponse_meromorphicAt s chi a J K w hw hwr hb hb1).div
      (horizon_frequency_analyticAt w chi hw ⟨hb,hb1⟩).meromorphicAt).sub hP.meromorphicAt
  apply hm.congr
  filter_upwards [(show ∀ᶠ u in 𝓝[≠] w, u ∈ Metric.ball w R from
      nhdsWithin_le_nhds (Metric.ball_mem_nhds w hR)),
    connection_eventually_ne_zero w chi hw] with u hu hc
  exact (he u hu hc).symm

/-- On the convergence chamber, this horizon coefficient is the literal endpoint integral. -/
theorem greenHorizonAmplitude_eq_original {w chi : ℂ} (hc : Chamber w chi)
    (s a J K : ℂ) (hw : w.im ≠ 0) (hwr : -1 < w.re) (hs : (2*s).re < w.re) :
    greenHorizonAmplitude s chi a J K w=
      outerMoment w chi s a J K (onsetTransform (2*s) w) 0 := by
  have hg := (gaussFactor_derivatives (z := 0) hc false (by simp)).1.comp_ofReal.continuousAt.tendsto
  simp only [Complex.ofReal_zero,gaussFactor_zero] at hg
  have ht := (response_ingoing hc s a J K (onsetTransform (2*s) w)).div
    (hg.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)) (by norm_num : (1:ℂ) ≠ 0)
  simp only [div_one] at ht
  have hlim : Tendsto (fun z => continuedResponse s chi a J K z w/horizon w chi z)
      (𝓝[>] (0:ℝ)) (𝓝 (outerMoment w chi s a J K (onsetTransform (2*s) w) 0)) := by
    apply ht.congr'
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with z hz
    rw [continuedResponse_eq_original s chi a J K w hw hwr hs hz.1 hz.2]
    simp only [Pi.div_apply,horizon,dress,div_div]
  exact hlim.limUnder_eq

/-- Meromorphic continuation of the original, normalized causal horizon amplitude. -/
def continuedCornerAmplitude (q : XiZeroCopy) (br : Bool) (amp w : ℂ) : ℂ :=
  physicalSelfSourceCoefficient q * greenHorizonAmplitude
    (physicalRate q br) (physicalRadialFrequency q) amp 1
    (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) w

/-- Equality is derived from the original causal trace, not imposed as an admission premise. -/
theorem continuedCornerAmplitude_eq_original (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2 < w.re) (hwi : w.im ≠ 0) :
    continuedCornerAmplitude q br amp w=cornerAmplitude q br amp w := by
  rw [continuedCornerAmplitude,greenHorizonAmplitude_eq_original
    (physicalRadialFrequency_chamber q w (by linarith)) _ _ _ _ hwi (by linarith)
    (source_re q br w hw),cornerAmplitude_eq_original_endpoint q br amp w hw hwi]

/-- Source-derived horizon continuation throughout the nonreal fundamental strip. -/
theorem continuedCornerAmplitude_meromorphic (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hwi : w.im ≠ 0) (hw : -2 < w.re) :
    MeromorphicAt (continuedCornerAmplitude q br amp) w := by
  have hs : w-2*physicalRate q br ≠ 0 := by
    intro he
    have hre := congrArg Complex.re (sub_eq_zero.mp he)
    have h := currentRate_re_lt q br
    change (2*physicalRate q br).re < -2 at h
    linarith
  exact analyticAt_const.meromorphicAt.mul (greenHorizonAmplitude_meromorphic
    (physicalRate q br) (physicalRadialFrequency q) amp 1
    (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) w hwi hw hs)


/-- The residue of the continued original horizon amplitude, retaining the literal source coefficient. -/
def cornerResidue (q : XiZeroCopy) (br side : Bool) (amp : ℂ) : ℂ :=
  physicalSelfSourceCoefficient q*physicalIncomingPoleAmplitude q br side amp

theorem continuedCornerAmplitude_residue (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    Tendsto (fun w => (w-physicalFundamentalFrequency q side)*continuedCornerAmplitude q br amp w)
      (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 (cornerResidue q br side amp)) := by
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q br
  let chi := physicalRadialFrequency q
  let K := reducedGreenGradient chi s 1
  have hw := physicalFundamentalFrequency_strip q side
  obtain ⟨R,b,hR,hb,hbhalf,hP,he⟩ := greenHorizonAmplitude_local s chi amp 1 K w
    hw.1 (abs_lt.mp hw.2).1 (physicalFundamentalFrequency_sub_sourceRate_ne_zero q br side)
  have hx : Tendsto (fun u : ℂ => u-w) (𝓝[≠] w) (𝓝 0) := by
    simpa only [id_eq,sub_self] using!
      ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun u : ℂ => u) (𝓝[≠] w) (𝓝 w)).sub_const w)
  have hQ := physicalIncomingQuotient_residue q br side amp ⟨hb,by linarith⟩
  have hp := hP.continuousAt.tendsto.mono_left (show 𝓝[≠] w ≤ 𝓝 w from nhdsWithin_le_nhds)
  have ht := (hQ.sub (hx.mul hp)).const_mul (physicalSelfSourceCoefficient q)
  simp only [zero_mul,sub_zero] at ht
  apply ht.congr'
  filter_upwards [(show ∀ᶠ u in 𝓝[≠] w, u ∈ Metric.ball w R from
    nhdsWithin_le_nhds (Metric.ball_mem_nhds w hR)),connection_eventually_ne_zero w chi hw.1] with u hu hc
  change physicalSelfSourceCoefficient q*((u-w)*(continuedResponse s chi amp 1 K b u/horizon u chi b)-
    (u-w)*incomingSourcePrimitive s chi amp 1 K u b) =
      (u-w)*(physicalSelfSourceCoefficient q*greenHorizonAmplitude s chi amp 1 K u)
  rw [he u hu hc]
  dsimp only [incomingResponseEndpoint,incomingSourcePrimitive]
  ring

private theorem analytic_laurent_remainder {f : ℂ → ℂ} {w R : ℂ} (hm : MeromorphicAt f w)
    (hR : Tendsto (fun v => (v-w)*f v) (𝓝[≠] w) (𝓝 R)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ f =ᶠ[𝓝[≠] w] (fun v => R/(v-w)+g v) := by
  let F := Function.update (fun v => (v-w)*f v) w R
  have hM : MeromorphicAt F w :=
    ((show AnalyticAt ℂ (fun v : ℂ => v-w) w by fun_prop).meromorphicAt.mul hm).update w R
  have hF : AnalyticAt ℂ F w := hM.analyticAt (continuousAt_update_same.mpr hR)
  have hg : AnalyticAt ℂ (dslope F w) w := by
    obtain ⟨p,hp⟩ := hF
    exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩
  refine ⟨dslope F w,hg,?_⟩
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hvw : v ≠ w := hv
  rw [dslope_of_ne F hvw,slope_def_field]
  simp only [F,Function.update_of_ne hvw,Function.update_self]
  field_simp [sub_ne_zero.mpr hvw]
  ring

/-- The source-derived amplitude has no hidden higher pole at a physical fundamental QNM. -/
theorem continuedCornerAmplitude_laurent (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (physicalFundamentalFrequency q side) ∧
      continuedCornerAmplitude q br amp =ᶠ[𝓝[≠] physicalFundamentalFrequency q side]
        (fun w => cornerResidue q br side amp/(w-physicalFundamentalFrequency q side)+g w) := by
  have hw := physicalFundamentalFrequency_strip q side
  exact analytic_laurent_remainder
    (continuedCornerAmplitude_meromorphic q br amp _ hw.1 (abs_lt.mp hw.2).1)
    (continuedCornerAmplitude_residue q br side amp)

/-- The first temporal moment differentiates this same source-derived meromorphic amplitude. -/
theorem continuedCornerAmplitude_derivative_leading (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    Tendsto (fun w => (w-physicalFundamentalFrequency q side)^2 *
      deriv (continuedCornerAmplitude q br amp) w)
      (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 (-cornerResidue q br side amp)) := by
  let w₀ := physicalFundamentalFrequency q side
  let R := cornerResidue q br side amp
  obtain ⟨g,hg,he⟩ := continuedCornerAmplitude_laurent q br side amp
  change AnalyticAt ℂ g w₀ at hg
  change continuedCornerAmplitude q br amp =ᶠ[𝓝[≠] w₀] (fun w => R/(w-w₀)+g w) at he
  have hd := he.nhdsNE_deriv
  have hlim : Tendsto (fun w => -R+(w-w₀)^2*deriv g w) (𝓝 w₀) (𝓝 (-R)) := by
    simpa using (tendsto_const_nhds.add
      (((tendsto_id.sub_const w₀).pow 2).mul hg.deriv.continuousAt.tendsto))
  apply (hlim.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [hd,hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with w hw hgw hn
  have hn' : w-w₀ ≠ 0 := sub_ne_zero.mpr hn
  have hp := (hasDerivAt_const w R).div ((hasDerivAt_id w).sub_const w₀) hn'
  have hder : deriv (fun u : ℂ => R/(u-w₀)+g u) w = -R/(w-w₀)^2+deriv g w := by
    simpa only [Pi.add_def,Pi.div_def,id_eq,zero_mul,zero_sub,mul_one] using
      (hp.add hgw.differentiableAt.hasDerivAt).deriv
  rw [hw,hder]
  dsimp only [w₀] at hn' ⊢
  field_simp [hn']

/-- The vanishing opposite coefficient retains the pole of the original causal horizon's first moment. -/
theorem original_corner_derivative_residue (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    Tendsto (fun w => (w-physicalFundamentalFrequency q side)*
      (connection w (physicalRadialFrequency q)/(2*w))*deriv (continuedCornerAmplitude q br amp) w)
      (𝓝[≠] physicalFundamentalFrequency q side)
      (𝓝 (-D4BMFundamentalNorm.normFinitePart (physicalFundamentalFrequency q side)*cornerResidue q br side amp)) := by
  let w₀ := physicalFundamentalFrequency q side
  have hβ := (D4BMOriginalCornerSpectralBalance.physical_oppositeCoefficient_hasDerivAt q side).tendsto_slope
  have ht := hβ.mul (continuedCornerAmplitude_derivative_leading q br side amp)
  simp only [mul_neg,neg_mul] at ht ⊢
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hn : w-w₀ ≠ 0 := sub_ne_zero.mpr hw
  simp only [slope_def_field,physicalFundamentalFrequency_connection_zero,zero_div,sub_zero]
  change (connection w (physicalRadialFrequency q)/(2*w)/(w-w₀))*
    ((w-w₀)^2*deriv (continuedCornerAmplitude q br amp) w) = _
  dsimp only [w₀] at hn ⊢
  field_simp [hn]


/-- On its admitted half-plane the continued derivative is the original first temporal moment. -/
theorem continuedCornerAmplitude_original_firstMoment (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2 < w.re) (hwi : w.im ≠ 0) :
    HasDerivAt (continuedCornerAmplitude q br amp)
      (Complex.exp (-w*(Real.log 2:ℂ))*(-(Real.log 2:ℂ)*horizonTransform q br amp w-
        ∫ p in Ioi (0:ℝ), (p:ℂ)*Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p)) w := by
  have he : continuedCornerAmplitude q br amp =ᶠ[𝓝 w] cornerAmplitude q br amp := by
    filter_upwards [Complex.continuous_re.continuousAt.eventually_const_lt hw,
      Complex.continuous_im.continuousAt.eventually_ne hwi] with u hu hui
    exact continuedCornerAmplitude_eq_original q br amp u hu hui
  exact (corner_amplitude_hasDerivAt q br amp w (reader_re q w hw)).congr_of_eventuallyEq he

/-- The connection-weighted first moment exposes exactly the original source and onset. -/
theorem original_corner_connection_derivative_residue (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    Tendsto (fun w => (w-physicalFundamentalFrequency q side)*
      connection w (physicalRadialFrequency q)*deriv (continuedCornerAmplitude q br amp) w)
      (𝓝[≠] physicalFundamentalFrequency q side)
      (𝓝 (physicalSelfSourceCoefficient q*
        fundamentalSourceMoment (physicalFundamentalFrequency q side) (physicalRate q br) amp*
        continuedOnset (physicalRate q br) (physicalFundamentalFrequency q side))) := by
  let w₀ := physicalFundamentalFrequency q side
  have hvalue : -connectionSimpleSlope w₀ (physicalRadialFrequency q) side*cornerResidue q br side amp=
      physicalSelfSourceCoefficient q*fundamentalSourceMoment w₀ (physicalRate q br) amp*
        continuedOnset (physicalRate q br) w₀ := by
    dsimp only [w₀,cornerResidue,physicalIncomingPoleAmplitude,continuedOnset]
    field_simp [physicalFundamental_connectionSlope_ne_zero q side,
      physicalFundamentalFrequency_sub_sourceRate_ne_zero q br side]
  have ht := (physicalFundamental_connection_hasDerivAt q side).tendsto_slope.mul
    (continuedCornerAmplitude_derivative_leading q br side amp)
  simp only [mul_neg,← neg_mul] at ht
  rw [hvalue] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hn : w-w₀ ≠ 0 := sub_ne_zero.mpr hw
  simp only [slope_def_field,physicalFundamentalFrequency_connection_zero,sub_zero]
  dsimp only [w₀] at hn ⊢
  field_simp [hn]

/-- Exact residue of the response-trace part of the original corner candidate.
The separate forcing contact and full spacetime finite-part comparison are not asserted here. -/
theorem original_corner_response_residue (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    Tendsto (fun w => (w-physicalFundamentalFrequency q side)*
      (connection w (physicalRadialFrequency q)/(2*w))*
        (continuedCornerAmplitude q br amp w+2*w*deriv (continuedCornerAmplitude q br amp) w))
      (𝓝[≠] physicalFundamentalFrequency q side)
      (𝓝 (physicalSelfSourceCoefficient q*
        fundamentalSourceMoment (physicalFundamentalFrequency q side) (physicalRate q br) amp*
        continuedOnset (physicalRate q br) (physicalFundamentalFrequency q side))) := by
  let w₀ := physicalFundamentalFrequency q side
  have hβ := (D4BMOriginalCornerSpectralBalance.physical_oppositeCoefficient_hasDerivAt q side).continuousAt.tendsto
  simp only [physicalFundamentalFrequency_connection_zero,zero_div] at hβ
  have hzero := (continuedCornerAmplitude_residue q br side amp).mul
    (hβ.mono_left nhdsWithin_le_nhds)
  simp only [mul_zero] at hzero
  have ht := hzero.add (original_corner_connection_derivative_residue q br side amp)
  simp only [zero_add] at ht
  have hw0 : w₀ ≠ 0 := by
    intro h
    have hi := (physicalFundamentalFrequency_strip q side).1
    apply hi
    change w₀.im=0
    rw [h]
    rfl
  apply ht.congr'
  filter_upwards [(continuousAt_id.eventually_ne hw0).filter_mono nhdsWithin_le_nhds] with w hw
  change w ≠ 0 at hw
  field_simp [hw]

end
end RHTower.D4BMOriginalHorizonGreenMatch
