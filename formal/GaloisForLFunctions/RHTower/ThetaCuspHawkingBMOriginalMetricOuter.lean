import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalMetricTimeLimit
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMReducedOuterPairing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTemporalContactHorizonFactor

/-! Outer integration of the complete angular-restored original temporal metric. -/
open Set Filter Topology Metric MeasureTheory Complex
namespace RHTower.D4BMOriginalMetricOuter
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMLaplaceRadial D4BMModularCore
open D4BMJointWave D4BMOriginalCornerForcing D4BMOriginalMetricTimeLimit
noncomputable section
set_option autoImplicit false

private abbrev mu (q : XiZeroCopy) := D4BMLeftModeRadialEquation.eigenvalue q

/-- The frequency-independent original lift and forcing combination. -/
def regularCore (q : XiZeroCopy) (br : Bool) (amp : ℂ) (x : ℝ) : ℂ :=
  2*(mu q-2)*radialLift (physicalRate q br) 0 amp 1 x+
    forcingProfile (physicalRate q br) amp 1
      (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) (radialUnit x)

/-- The original lift and contact combine into one fixed gradient shift. -/
theorem regularCore_eq_forcingProfile (q : XiZeroCopy) (br : Bool) (amp : ℂ) (x : ℝ) :
    regularCore q br amp x = forcingProfile (physicalRate q br) amp 1
      (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1-(mu q-2))
      (radialUnit x) := by
  simp only [regularCore,forcingProfile,radialLift,sourceAmplitude,zero_mul,
    Complex.exp_zero,one_mul,mul_one]
  ring

private theorem core_continuous (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    Continuous (regularCore q br amp) := by
  have hL : Continuous (radialLift (physicalRate q br) 0 amp 1) :=
    continuous_iff_continuousAt.mpr (fun x => (radialLift_hasDerivAt _ _ _ _ x).continuousAt)
  have hu : Continuous radialUnit :=
    continuous_iff_continuousAt.mpr (fun x => (radialUnit_hasDerivAt x).continuousAt)
  have hP : Continuous (fun x : ℝ => power (2*physicalRate q br) (1+radialUnit x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((power_derivatives (2*physicalRate q br) (radialUnit_add_one_pos x)).1.scomp x
      ((radialUnit_hasDerivAt x).const_add 1)).continuousAt
  unfold regularCore forcingProfile
  fun_prop

/-- The whole regular contribution before the original onset transform is applied. -/
def regularKernel (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (w*(x:ℂ))*regularCore q br amp x*
    normalizable w (physicalRadialFrequency q) (horizonCoordinate x)

def regularOuterMoment (q : XiZeroCopy) (br : Bool) (amp : ℂ) (T : ℝ) (w : ℂ) : ℂ :=
  ∫ x in Ioo T (0:ℝ),regularKernel q br amp w x

private theorem kernel_continuousOn (q : XiZeroCopy) (br : Bool) (amp w : ℂ) :
    ContinuousOn (regularKernel q br amp w) (Iio (0:ℝ)) := by
  intro x hx
  have hn := ((normalizable_derivatives_continued (w:=w) (chi:=physicalRadialFrequency q)
    (horizonCoordinate_interior x hx)).1.continuousAt).comp_of_eq
      (horizonCoordinate_hasDerivAt x).continuousAt rfl
  exact (((show Continuous (fun x : ℝ => Complex.exp (w*(x:ℂ))) by fun_prop).continuousAt.mul
    (core_continuous q br amp).continuousAt).mul hn).continuousWithinAt

private theorem kernel_uniform (q : XiZeroCopy) (br : Bool) (amp w : ℂ) {T : ℝ} (hT : T<0) :
    ∃ B : ℝ, 0≤B ∧ ∀ v ∈ ball w 1, ∀ x ∈ Ioo T (0:ℝ), ‖regularKernel q br amp v x‖≤B := by
  let H : ℂ×ℝ→ℂ := fun p => Complex.exp (p.1*(p.2:ℂ))*regularCore q br amp p.2
  have hH : Continuous H := by
    have hC := (core_continuous q br amp).comp
      (show Continuous (fun p : ℂ×ℝ => p.2) from continuous_snd)
    unfold H
    fun_prop
  obtain ⟨A,hA⟩ := ((isCompact_closedBall w 1).prod (isCompact_Icc : IsCompact (Icc T (0:ℝ)))).exists_bound_of_continuousOn hH.continuousOn
  obtain ⟨N,hN,hV⟩ := tortoiseNormalizable_outer_uniform_bound w (physicalRadialFrequency q) hT
  refine ⟨max A 0*N,mul_nonneg (le_max_right _ _) hN,?_⟩
  intro v hv x hx
  rw [regularKernel,norm_mul]
  exact mul_le_mul ((hA (v,x) ⟨ball_subset_closedBall hv,⟨hx.1.le,hx.2.le⟩⟩).trans (le_max_left _ _))
    (hV v hv x hx) (norm_nonneg _) (le_max_right _ _)

/-- The complete original lift/contact outer integrand is admitted at every frequency. -/
theorem regularKernel_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ) {T : ℝ} (hT : T<0) :
    IntegrableOn (regularKernel q br amp w) (Ioo T (0:ℝ)) := by
  obtain ⟨B,_,hB⟩ := kernel_uniform q br amp w hT
  have hI : Integrable (fun _ : ℝ => B) (volume.restrict (Ioo T (0:ℝ))) := integrable_const _
  apply hI.mono' (((kernel_continuousOn q br amp w).mono (fun _ hx => hx.2)).aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact hB w (mem_ball_self (by norm_num)) x hx

/-- Outer integration does not create a pole in the restored lift/contact combination. -/
theorem regularOuterMoment_analyticAt (q : XiZeroCopy) (br : Bool) (amp w : ℂ) {T : ℝ} (hT : T<0) :
    AnalyticAt ℂ (regularOuterMoment q br amp T) w := by
  obtain ⟨B,_,hB⟩ := kernel_uniform q br amp w hT
  let F := regularKernel q br amp
  let G := fun v : ℂ => (Ioo T (0:ℝ)).indicator (F v)
  let bound := (Ioo T (0:ℝ)).indicator (fun _ : ℝ => B)
  have hm (v : ℂ) : AEStronglyMeasurable (G v) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ioo).mpr
      (((kernel_continuousOn q br amp v).mono (fun _ hx => hx.2)).aestronglyMeasurable measurableSet_Ioo)
  have hd (x : ℝ) : DifferentiableOn ℂ (fun v => G v x) (ball w 1) := by
    intro v hv
    by_cases hx : x ∈ Ioo T (0:ℝ)
    · have hn := (normalizable_frequency_entire (physicalRadialFrequency q)
        (horizonCoordinate_interior x hx.2)).analyticAt v
      have he : AnalyticAt ℂ (fun u : ℂ => Complex.exp (u*(x:ℂ))) v := by fun_prop
      have ha := (he.mul (show AnalyticAt ℂ (fun _ : ℂ => regularCore q br amp x) v from analyticAt_const)).mul hn
      simpa only [G,F,regularKernel,indicator_of_mem hx] using! ha.differentiableAt.differentiableWithinAt
    · simp only [G,indicator_of_notMem hx]
      fun_prop
  have hb (x : ℝ) (v : ℂ) (hv : v ∈ ball w 1) : ‖G v x‖≤bound x := by
    by_cases hx : x ∈ Ioo T (0:ℝ)
    · simp only [G,bound,F,indicator_of_mem hx]
      exact hB v hv x hx
    · simp only [G,bound,indicator_of_notMem hx,norm_zero,le_refl]
  have hi : Integrable bound volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (integrable_const B)
  have hD : DifferentiableOn ℂ (fun v => ∫ x,G v x) (ball w 1) := by
    intro v hv
    obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hv)
    exact (differentiableAt_integral_of_cauchy_dominated hr (fun u _ => hm u)
      (fun x => (hd x).mono hs) (fun x u hu => hb x u (hs hu)) hi).differentiableWithinAt
  have hA := hD.analyticOnNhd isOpen_ball w (mem_ball_self (by norm_num))
  simpa only [G,F,integral_indicator measurableSet_Ioo,regularOuterMoment] using! hA

private theorem onset_eq (q : XiZeroCopy) (br : Bool) (w : ℂ) (hw : -2<w.re) :
    onsetTransform (2*physicalRate q br) w=continuedOnset (physicalRate q br) w := by
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  exact onsetTransform_eq _ _ (hs.trans hw)

/-- The original metric time-limit density in the unchanged tortoise measure. -/
def outerDensity (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (x : ℝ) : ℂ :=
  ((tortoiseRadius x:ℂ)^2-1)*metricFrequencyDensity q br true amp w (tortoiseRadius x)

def outerIntegral (q : XiZeroCopy) (br : Bool) (amp : ℂ) (T : ℝ) (w : ℂ) : ℂ :=
  ∫ x in Ioo T (0:ℝ),outerDensity q br amp w x

/-- The restored original metric splits into its Green pairing and the full regular
lift/contact combination, after the exact radial Jacobian is applied. -/
theorem outerDensity_decomposition (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : -2<w.re) {x : ℝ} (hx : x<0) :
    outerDensity q br amp w x=
      (2*mu q*w*(mu q-2)*physicalSelfSourceCoefficient q)*
        (continuedReducedGreen w (physicalRadialFrequency q) (physicalRate q br) amp 1 x*
          normalizable w (physicalRadialFrequency q) (horizonCoordinate x))+
      (mu q*w*physicalSelfSourceCoefficient q*continuedOnset (physicalRate q br) w)*
        regularKernel q br amp w x := by
  have hf : (tortoiseRadius x:ℂ)^2-1≠0 := by
    exact_mod_cast (show tortoiseRadius x^2-1≠0 by nlinarith [tortoiseRadius_exterior x hx])
  have hr : (tortoiseRadius x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by
    have h := tortoiseRadius_exterior x hx
    linarith)
  have hz : (horizonCoordinate x:ℂ)=((tortoiseRadius x:ℂ)^2-1)/(tortoiseRadius x:ℂ)^2 := by
    apply (eq_div_iff (pow_ne_zero 2 hr)).mpr
    simpa only [mul_comm] using radius_sq_mul_horizonCoordinate x hx
  have hL : radialLift (physicalRate q br) w amp (continuedOnset (physicalRate q br) w) x=
      Complex.exp (w*(x:ℂ))*continuedOnset (physicalRate q br) w*
        radialLift (physicalRate q br) 0 amp 1 x := by
    simp only [radialLift,sourceAmplitude,zero_mul,Complex.exp_zero,one_mul,mul_one]
    ring
  simp only [outerDensity,metricFrequencyDensity,tortoise_original_inverse x hx,
    D4BMOriginalReaderEquation.modeProfile,tortoiseMode,radialMode,if_true,
    scalarFrequency,forcingFrequency,onset_eq q br w hw,hL,regularKernel,regularCore]
  rw [hz]
  field_simp [hf,hr]
  ring

private theorem reduced_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*physicalRate q br≠0)
    (hc : connection w (physicalRadialFrequency q)≠0) {T : ℝ} (hT : T<0) :
    IntegrableOn (fun x => continuedReducedGreen w (physicalRadialFrequency q) (physicalRate q br) amp 1 x*
      normalizable w (physicalRadialFrequency q) (horizonCoordinate x)) (Ioo T (0:ℝ)) := by
  let D := reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q br)
  have hD : D≠0 := mul_ne_zero (neg_ne_zero.mpr hs) hc
  have hi := (clearedReducedOuterPairing_integrable w (physicalRadialFrequency q) (physicalRate q br) amp hw hwr hT).div_const D
  apply hi.congr
  filter_upwards with x
  rw [clearedReducedGreen_eq w (physicalRadialFrequency q) (physicalRate q br) amp hs hc]
  change (D*_)*_/D=_
  field_simp

/-- Both pieces are admitted before the original outer metric integral is split. -/
theorem outerIntegral_decomposition (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*physicalRate q br≠0)
    (hc : connection w (physicalRadialFrequency q)≠0) {T : ℝ} (hT : T<0) :
    IntegrableOn (outerDensity q br amp w) (Ioo T (0:ℝ)) ∧
    outerIntegral q br amp T w=
      (2*mu q*w*(mu q-2)*physicalSelfSourceCoefficient q)*
        continuedReducedOuterPairing (physicalRadialFrequency q) (physicalRate q br) amp T w+
      (mu q*w*physicalSelfSourceCoefficient q*continuedOnset (physicalRate q br) w)*
        regularOuterMoment q br amp T w := by
  have hG := (reduced_integrable q br amp w hw hwr hs hc hT).const_mul
    (2*mu q*w*(mu q-2)*physicalSelfSourceCoefficient q)
  have hJ := (regularKernel_integrable q br amp w hT).const_mul
    (mu q*w*physicalSelfSourceCoefficient q*continuedOnset (physicalRate q br) w)
  have he : outerDensity q br amp w =ᵐ[volume.restrict (Ioo T (0:ℝ))]
      fun x => (2*mu q*w*(mu q-2)*physicalSelfSourceCoefficient q)*
        (continuedReducedGreen w (physicalRadialFrequency q) (physicalRate q br) amp 1 x*
          normalizable w (physicalRadialFrequency q) (horizonCoordinate x))+
        (mu q*w*physicalSelfSourceCoefficient q*continuedOnset (physicalRate q br) w)*
          regularKernel q br amp w x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact outerDensity_decomposition q br amp w hwr hx.2
  refine ⟨(hG.add hJ).congr he.symm,?_⟩
  unfold outerIntegral
  rw [integral_congr_ae he,integral_add hG hJ,integral_const_mul,integral_const_mul]
  rfl

/-- The entire outer lift/contact moment, with the original onset, has zero QNM residue. -/
theorem regularOuterMoment_onset_analytic (q : XiZeroCopy) (br side : Bool) (amp : ℂ)
    {T : ℝ} (hT : T<0) :
    AnalyticAt ℂ (fun w => continuedOnset (physicalRate q br) w*regularOuterMoment q br amp T w)
      (physicalFundamentalFrequency q side) := by
  have ho : AnalyticAt ℂ (continuedOnset (physicalRate q br)) (physicalFundamentalFrequency q side) :=
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (physicalFundamentalFrequency_sub_sourceRate_ne_zero q br side)).add
      ((onsetCorrection_entire (2*physicalRate q br)).analyticAt _)
  exact ho.mul (regularOuterMoment_analyticAt q br amp _ hT)

/-- The QNM residue of the complete original outer metric density is derived after
integration, with its original angular factor and both regular source terms retained. -/
theorem originalMetricOuter_QNM_residue (q : XiZeroCopy) (br side : Bool) (amp : ℂ)
    {T : ℝ} (hT : T<0) :
    let w := physicalFundamentalFrequency q side
    let s := physicalRate q br
    let chi := physicalRadialFrequency q
    Tendsto (fun v => (v-w)*outerIntegral q br amp T v) (𝓝[≠] w)
      (𝓝 ((2*mu q*w*(mu q-2)*physicalSelfSourceCoefficient q)*
        ((fundamentalSourceMoment w s amp*clearedOnset s w)*
          (∫ x in Ioo T (0:ℝ),normalizable w chi (horizonCoordinate x)^2)/
            physicalFundamentalDenominatorSlope q br side))) := by
  dsimp only
  let w := physicalFundamentalFrequency q side
  have hw := physicalFundamentalFrequency_strip q side
  have hG := physicalReducedOuterPairing_residue q br side amp hT
  have hi : Tendsto (fun v : ℂ => v) (𝓝[≠] w) (𝓝 w) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hz := hi.sub_const w
  have hA := (((hi.const_mul (2*mu q)).mul_const (mu q-2)).mul_const
    (physicalSelfSourceCoefficient q)).mul hG
  have hJ := (regularOuterMoment_onset_analytic q br side amp hT).continuousAt.tendsto.mono_left
    (show 𝓝[≠] w≤𝓝 w from nhdsWithin_le_nhds)
  have hB := ((hi.const_mul (mu q)).mul_const (physicalSelfSourceCoefficient q)).mul (hz.mul hJ)
  have h := hA.add hB
  simp only [sub_self,zero_mul,mul_zero,add_zero] at h
  apply h.congr'
  have hreal : ∀ᶠ v : ℂ in 𝓝 w,-2<v.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt (abs_lt.mp hw.2).1
  have hsource : ∀ᶠ v : ℂ in 𝓝 w,v-2*physicalRate q br≠0 :=
    (continuousAt_id.sub continuousAt_const).eventually_ne (physicalFundamentalFrequency_sub_sourceRate_ne_zero q br side)
  filter_upwards [(Complex.continuous_im.continuousAt.eventually_ne hw.1).filter_mono nhdsWithin_le_nhds,
    hreal.filter_mono nhdsWithin_le_nhds,hsource.filter_mono nhdsWithin_le_nhds,
    connection_eventually_ne_zero w (physicalRadialFrequency q) hw.1] with v hvi hvr hvs hvc
  rw [(outerIntegral_decomposition q br amp v hvi hvr hvs hvc hT).2]
  ring

end
end RHTower.D4BMOriginalMetricOuter
