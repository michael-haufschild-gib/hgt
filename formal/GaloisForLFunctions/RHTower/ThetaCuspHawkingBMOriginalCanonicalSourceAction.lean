/-
Complete original temporal/metric action as fixed-source finite parts.
The convergence-chamber identity extends meromorphically to the canonical
QNM values with the original endpoint counterterms preserved.
-/

import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalSourceFinitePart
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalNativeSourceFinitePart

open Set Filter Topology MeasureTheory Metric
namespace RHTower.D4BMOriginalSourceResolvent
open D4BMLaplaceRadial D4BMModularCore D4BMJointSource GaloisForLFunctions.HTGeometry
open D4BMOriginalMetricHorizon D4BMOriginalMetricRadial D4BMOriginalMetricOuter
open D4BMOriginalCanonicalHorizon D4BMOriginalCanonicalRestoration D4BMOriginalCanonicalMetricCutoff
open D4BMOriginalCanonicalMetricGerm D4BMOriginalCanonicalAction D4BMOriginalCornerForcing
noncomputable section
set_option autoImplicit false

private theorem physical_source_pole_ne (q : XiZeroCopy) (br : Bool) (w : ℂ) (hwr : -2<w.re) :
    w-2*physicalRate q br≠0 := by
  intro he
  have hre := congrArg Complex.re (sub_eq_zero.mp he)
  have hr := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hr
  linarith

/-- The actual response/reader overlap is admitted up to the outer endpoint
 in the original chamber, at any positive lower cutoff. -/
theorem mixedDensity_outer_integrable (s chi amp J K w : ℂ)
    (hw : Chamber w chi) (hwi : w.im≠0) (hs : (2*s).re<w.re)
    {b : ℝ} (hb : 0<b) (hb1 : b<1) :
    IntervalIntegrable (mixedDensity s chi amp J K w w) volume b 1 := by
  have hwr : -2<w.re := by linarith [chamber_re_pos hw]
  have hc : ContinuousOn (mixedDensity s chi amp J K w w) (Ioo (0:ℝ) 1) := by
    intro z hz
    exact (((continuedResponse_hasDerivAt s chi amp J K w hwi hwr hz).1.continuousAt.mul
      (normalizable_derivatives_continued (w:=w) (chi:=chi) hz).1.continuousAt).div
      (show ContinuousAt (fun t : ℝ => 2*(t:ℂ)*(Real.sqrt (1-t):ℂ)) z by fun_prop)
      (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hz.1.ne'))
        (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (sub_pos.mpr hz.2)).ne'))).continuousWithinAt
  have hleft : Tendsto (mixedDensity s chi amp J K w w) (𝓝[>] b)
      (𝓝 (mixedDensity s chi amp J K w w b)) :=
    (hc.continuousAt (isOpen_Ioo.mem_nhds ⟨hb,hb1⟩)).tendsto.mono_left nhdsWithin_le_nhds
  have hright : Tendsto (mixedDensity s chi amp J K w w) (𝓝[<] (1:ℝ)) (𝓝 0) := by
    have ht := ((response_boundary hw s amp J K (onsetTransform (2*s) w)).mul
      (normalizable_boundary_ratio hw)).div
      ((Complex.continuous_ofReal.tendsto (1:ℝ)).const_mul 2 |>.mono_left
        (show 𝓝[<] (1:ℝ)≤𝓝 1 from nhdsWithin_le_nhds)) (by norm_num : (2:ℂ)*1≠0)
    simp only [zero_mul,zero_div] at ht
    apply ht.congr'
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ)<1)] with z hz
    rw [mixedDensity,continuedResponse_eq_original s chi amp J K w hwi (by linarith [chamber_re_pos hw]) hs hz.1 hz.2]
    dsimp only [Pi.div_apply,Pi.mul_apply]
    ring
  have hco := hc.mono (fun z (hz : z∈Ioo b (1:ℝ)) => ⟨hb.trans hz.1,hz.2⟩)
  have he := continuousOn_Icc_extendFrom_Ioo hco hleft hright
  have hi : IntervalIntegrable (extendFrom (Ioo b (1:ℝ)) (mixedDensity s chi amp J K w w)) volume b 1 :=
    (he.mono (by rw [uIcc_of_le hb1.le])).intervalIntegrable
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hb1.le).mpr
  apply ((intervalIntegrable_iff_integrableOn_Ioo_of_le hb1.le).mp hi).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  exact extendFrom_extends hco z hz

/-- The complete original metric radial integral pulls back to the native
 Green and native forcing terms, including the true outer endpoint. -/
theorem original_metric_integral_source_pullback (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : Chamber w (physicalRadialFrequency q)) (hwi : w.im≠0)
    {e : ℝ} (he : e∈Ioo (0:ℝ) 1) :
    (∫ x in tortoiseOf e..0,outerDensity q br amp w x)=
      greenCoefficient q w*(∫ z in e..1,mixedDensity (physicalRate q br) (physicalRadialFrequency q)
        amp 1 (D4BMOriginalCanonicalMetricCutoff.gradient q br) w w z)+
      forcingCoefficient q br w*(∫ z in e..1,pullback q br amp (D4BMOriginalCanonicalMetricCutoff.gradient q br) w z) := by
  let G := mixedDensity (physicalRate q br) (physicalRadialFrequency q) amp 1 (D4BMOriginalCanonicalMetricCutoff.gradient q br) w w
  let F := pullback q br amp (D4BMOriginalCanonicalMetricCutoff.gradient q br) w
  have hwr : -2<w.re := by linarith [chamber_re_pos hw]
  have hs : (2*physicalRate q br).re<w.re := by
    have hr := currentRate_re_lt q br
    change (2*physicalRate q br).re < -2 at hr
    linarith
  have hte := tortoiseOf_neg he
  have hzero : horizonCoordinate 0=1 := by norm_num [horizonCoordinate,radialUnit]
  have hcv := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (f:=horizonCoordinate) (f':=coordinateFirst)
    (g:=fun z => greenCoefficient q w*G z+forcingCoefficient q br w*F z)
    (a:=tortoiseOf e) (b:=0)
    (continuous_iff_continuousAt.mpr (fun x => (horizonCoordinate_hasDerivAt x).continuousAt)).continuousOn
    (fun x _ => horizonCoordinate_hasDerivAt x)
    (fun x hx => by
      have hx0 : x<0 := by rw [max_eq_right hte.le] at hx; exact hx.2
      dsimp only [coordinateFirst]
      exact mul_nonneg (mul_nonneg (by norm_num) (radialUnit_bounds x hx0).1.le)
        (horizonCoordinate_interior x hx0).1.le)
  rw [horizonCoordinate_tortoiseOf he,hzero] at hcv
  have hI := mixedDensity_outer_integrable (physicalRate q br) (physicalRadialFrequency q) amp 1
    (D4BMOriginalCanonicalMetricCutoff.gradient q br) w hw hwi hs he.1 he.2
  have hF : IntervalIntegrable F volume e 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le he.2.le).mpr
      (nativeForcing_outer_integrable q br amp (D4BMOriginalCanonicalMetricCutoff.gradient q br) w he.1 he.2)
  rw [intervalIntegral.integral_add (hI.const_mul _) (hF.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hcv
  rw [← hcv]
  apply intervalIntegral.integral_congr_uIoo
  intro x hx
  rw [uIoo_of_le hte.le] at hx
  have hx0 := hx.2
  have hz0 : (horizonCoordinate x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (horizonCoordinate_interior x hx0).1.ne'
  have hu0 : (radialUnit x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (radialUnit_bounds x hx0).1.ne'
  rw [original_density_native q br amp w hwr hx0]
  dsimp only [Function.comp_def,G,F,mixedDensity,pullback,greenCoefficient,forcingCoefficient,D4BMOriginalCanonicalMetricCutoff.gradient]
  rw [tortoiseOf_horizonCoordinate hx0,← radialUnit_eq_sqrt x hx0]
  simp only [Complex.real_smul,coordinateFirst]
  push_cast
  field_simp [hz0,hu0]

/-- The full source expression with the native forcing and retained temporal corner. -/
def completeSourceAction (q : XiZeroCopy) (br : Bool) (amp w : ℂ) : ℂ :=
  let s := physicalRate q br
  let chi := physicalRadialFrequency q
  let K := D4BMOriginalCanonicalMetricCutoff.gradient q br
  let mu := physicalAngularParameter q^(2 : ℕ)-1/4
  let C := physicalSelfSourceCoefficient q;
  -mu*(mu-2)*C*sourceDerivativeFinitePart s chi amp 1 K w+
    forcingCoefficient q br w*nativeForcingSourceFinitePart q br amp K w+
    mu*connection w chi*C*deriv (continuedForcingTransform s amp 1 K) w/2

theorem completeSourceAction_analyticAt (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) : AnalyticAt ℂ (completeSourceAction q br amp) w := by
  have hs := physical_source_pole_ne q br w hwr
  have hD := sourceDerivativeFinitePart_analyticAt (physicalRate q br) (physicalRadialFrequency q)
    amp 1 (D4BMOriginalCanonicalMetricCutoff.gradient q br) w hw hwr hs
  have hN := nativeForcingSourceFinitePart_analyticAt q br amp (D4BMOriginalCanonicalMetricCutoff.gradient q br) w hw hwr
  have hT := continuedOnset_analyticAt (physicalRate q br) w hs
  have hFc : AnalyticAt ℂ (forcingCoefficient q br) w :=
    ((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul hT
  have hF := (continued_forcing_analyticAt (physicalRate q br) amp 1 (D4BMOriginalCanonicalMetricCutoff.gradient q br) w hs).deriv
  unfold completeSourceAction
  exact ((analyticAt_const.mul hD).add (hFc.mul hN)).add
    ((((analyticAt_const.mul (connection_frequency_analyticAt w (physicalRadialFrequency q) hw)).mul
      analyticAt_const).mul hF).div_const)

/-- The complete canonical metric and temporal action equals the original
 normalized source expression in its genuine convergence chamber. -/
theorem canonicalAction_eq_completeSourceAction_chamber (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : Chamber w (physicalRadialFrequency q)) (hwi : w.im≠0) :
    canonicalAction q br amp w=completeSourceAction q br amp w := by
  let s := physicalRate q br
  let chi := physicalRadialFrequency q
  let K := D4BMOriginalCanonicalMetricCutoff.gradient q br
  let G := mixedDensity s chi amp 1 K w w
  have hwr : -2<w.re := by linarith [chamber_re_pos hw]
  have hsp := physical_source_pole_ne q br w hwr
  have hs : (2*s).re<w.re := by
    have hr := currentRate_re_lt q br
    change (2*s).re < -2 at hr
    linarith
  have hc := connection_ne_zero hw
  obtain ⟨RG,BG,hRG,hBG,hBGh,hG⟩ := original_normalizable_local_data q br amp w hwi hwr
  obtain ⟨RE,BE,hRE,hBE,_,hE⟩ := original_green_endpoint_below s chi amp 1 K w hwi hwr hsp
  obtain ⟨BS,hBS,_,hS⟩ := physicalGreenMetric_corner_eq_source_below q br amp w hw hwi
  let b := min BG (min BE BS)
  have hb : 0<b := lt_min hBG (lt_min hBE hBS)
  have hbG : b≤BG := min_le_left _ _
  have hbE : b≤BE := (min_le_right _ _).trans (min_le_left _ _)
  have hbS : b≤BS := (min_le_right _ _).trans (min_le_right _ _)
  have hb1 : b<1 := by linarith [hbG.trans hBGh]
  have hEw := (hE b hb hbE).2 w (mem_ball_self hRE) hc
  have hlimG := (((hG b hb hbG).2 w (mem_ball_self hRG) hc).sub_const
    (continuedReducedOuterPairing chi s amp (tortoiseOf b) w))
  simp only [normalizableOuterPairingCutoff,normalizableOuterPairing,
    horizonCoordinate_tortoiseOf ⟨hb,hb1⟩,s,chi,add_sub_cancel_right] at hlimG
  have hlim := (((hlimG.add_const (∫ z in b..1,G z)).const_mul (greenCoefficient q w)).add
    ((nativeForcingSourceCutoff_tendsto q br amp K w hwi hwr).const_mul (forcingCoefficient q br w))).add_const
      (physicalCornerCandidate q br amp w)
  have hwhole : Tendsto (fun e => canonicalMetricCutoff q br amp w e+physicalCornerCandidate q br amp w)
      (𝓝[>] (0:ℝ)) (𝓝 (greenCoefficient q w*(normalizableHorizonPairingFinitePart s chi amp 1 K b w+
        ∫ z in b..1,G z)+forcingCoefficient q br w*nativeForcingSourceFinitePart q br amp K w+
        physicalCornerCandidate q br amp w)) := by
    apply hlim.congr'
    filter_upwards [Ioo_mem_nhdsGT hb] with e he
    have he1 : e<1 := he.2.trans hb1
    have hIe : IntervalIntegrable G volume e 1 :=
      mixedDensity_outer_integrable s chi amp 1 K w hw hwi hs he.1 he1
    have hIb : IntervalIntegrable G volume b 1 :=
      mixedDensity_outer_integrable s chi amp 1 K w hw hwi hs hb hb1
    have hIeb : IntervalIntegrable G volume e b := hIe.mono_set (by
      rw [uIcc_of_le he.2.le,uIcc_of_le he1.le]
      exact fun z hz => ⟨hz.1,hz.2.trans hb1.le⟩)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hIeb hIb
    have hgreen : (∫ z in e..1,G z)+canonicalGreenCounterterm q br amp w e=
        normalizableHorizonPairingCutoff s chi amp 1 K b w e+∫ z in b..1,G z := by
      rw [← hsplit]
      dsimp only [canonicalGreenCounterterm]
      change _+ (incomingCoefficient q w*((D4BMOriginalHorizonGreenMatch.greenHorizonAmplitude s chi amp 1 K w/2)*
        (e:ℂ)^w/w+((horizonGaussFirstCoefficient w chi+1/4)*D4BMOriginalHorizonGreenMatch.greenHorizonAmplitude s chi amp 1 K w+
        incomingResponseSlope s amp 1 K w/2)*(e:ℂ)^(w+1)/(w+1))+
        oppositeCoefficient q w*(D4BMOriginalHorizonGreenMatch.greenHorizonAmplitude s chi amp 1 K w/2)*(Real.log e:ℂ))=_
      rw [hEw]
      dsimp only [normalizableHorizonPairingCutoff,G,mixedDensity,incomingCoefficient,oppositeCoefficient]
      ring
    have hp := original_metric_integral_source_pullback q br amp w hw hwi ⟨he.1,he1⟩
    dsimp only [canonicalMetricCutoff]
    rw [hp]
    change _=(greenCoefficient q w*(∫ z in e..1,G z)+
      forcingCoefficient q br w*(∫ z in e..1,pullback q br amp K w z)+
      greenCoefficient q w*canonicalGreenCounterterm q br amp w e-
      forcingCoefficient q br w*forcingCounterterm
        (incomingValue q br amp K) (incomingSlope q br amp K) (oppositeValue q br amp K) w e)+
      physicalCornerCandidate q br amp w
    dsimp only [nativeForcingSourceCutoff,forcingCounterterm]
    dsimp only [s,chi,K,D4BMOriginalCanonicalMetricCutoff.gradient] at ⊢ hgreen
    linear_combination -(greenCoefficient q w)*hgreen
  have hcanon := (canonical_metric_cutoff_tendsto q br amp w hwi hwr hc).add_const
    (physicalCornerCandidate q br amp w)
  have hv : canonicalAction q br amp w=
      greenCoefficient q w*(normalizableHorizonPairingFinitePart s chi amp 1 K b w+
        ∫ z in b..1,G z)+forcingCoefficient q br w*nativeForcingSourceFinitePart q br amp K w+
        physicalCornerCandidate q br amp w := tendsto_nhds_unique hcanon hwhole
  have hsource := hS b hb hbS
  have hD := sourceDerivativeFinitePart_eq_integral s chi amp 1 K w hwi (chamber_re_pos hw) hsp
  rw [hv,completeSourceAction,hD]
  dsimp only [sourceActionDensity,G,s,chi,K,D4BMOriginalCanonicalMetricCutoff.gradient] at ⊢ hsource
  linear_combination hsource

private theorem canonical_source_germ_on_component (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    {U : Set ℂ} (hU : IsPreconnected U) (hi : ∀ u∈U,u.im≠0) (hr : ∀ u∈U,-2<u.re)
    {v w : ℂ} (hv : v∈U) (hvc : Chamber v (physicalRadialFrequency q)) (hw : w∈U) :
    canonicalAction q br amp =ᶠ[𝓝[≠] w] completeSourceAction q br amp := by
  let D : ℂ→ℂ := canonicalAction q br amp-completeSourceAction q br amp
  have hm : MeromorphicOn D U := fun u hu =>
    (canonical_action_meromorphic q br amp u (hi u hu) (hr u hu)).sub
      (completeSourceAction_analyticAt q br amp u (hi u hu) (hr u hu)).meromorphicAt
  have hzero : meromorphicOrderAt D v=⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hnear : ∀ᶠ u : ℂ in 𝓝 v,Chamber u (physicalRadialFrequency q) ∧ u.im≠0 :=
      (Complex.continuous_re.continuousAt.eventually_const_lt hvc).and
        (Complex.continuous_im.continuousAt.eventually_ne (hi v hv))
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with u hu
    exact sub_eq_zero.mpr (canonicalAction_eq_completeSourceAction_chamber q br amp u hu.1 hu.2)
  have hwzero : meromorphicOrderAt D w=⊤ := by
    by_contra hn
    exact (hm.meromorphicOrderAt_ne_top_of_isPreconnected hU hw hv hn) hzero
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hwzero] with u hu
  exact sub_eq_zero.mp hu

/-- The source identity continues on each full connected nonreal component,
 preserving the canonical cutoff normalization through connection zeros. -/
theorem canonicalAction_eventuallyEq_completeSourceAction (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) :
    canonicalAction q br amp =ᶠ[𝓝[≠] w] completeSourceAction q br amp := by
  let v : ℂ := ⟨|(physicalRadialFrequency q).im|+1,w.im⟩
  have hvc : Chamber v (physicalRadialFrequency q) := by dsimp [Chamber,v]; linarith
  have hvr : -2<v.re := by dsimp [v]; linarith [abs_nonneg ((physicalRadialFrequency q).im)]
  rcases lt_or_gt_of_ne hw with hn | hp
  · exact canonical_source_germ_on_component q br amp
      ((convex_halfSpace_re_gt (-2)).inter (convex_halfSpace_im_lt 0)).isPreconnected
      (fun _ hu => ne_of_lt hu.2) (fun _ hu => hu.1) ⟨hvr,hn⟩ hvc ⟨hwr,hn⟩
  · exact canonical_source_germ_on_component q br amp
      ((convex_halfSpace_re_gt (-2)).inter (convex_halfSpace_im_gt 0)).isPreconnected
      (fun _ hu => ne_of_gt hu.2) (fun _ hu => hu.1) ⟨hvr,hp⟩ hvc ⟨hwr,hp⟩

/-- The complete original QNM value equals the actual fixed-source finite
 parts; no metric/source matching or limit premise is supplied. -/
theorem canonicalQNMValue_eq_completeSourceAction (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    canonicalQNMValue q br side amp=completeSourceAction q br amp (physicalFundamentalFrequency q side) := by
  have hw := physicalFundamentalFrequency_strip q side
  have he := canonicalAction_eventuallyEq_completeSourceAction q br amp (physicalFundamentalFrequency q side)
    hw.1 (abs_lt.mp hw.2).1
  have ht := ((completeSourceAction_analyticAt q br amp (physicalFundamentalFrequency q side)
    hw.1 (abs_lt.mp hw.2).1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm
  exact tendsto_nhds_unique (canonical_action_QNM q br side amp).2.1 ht

/-- The finite canonical QNM action is now expressed entirely in the actual
 differentiated source and native forcing finite parts, with all coefficients fixed. -/
theorem canonicalQNMValue_eq_source_finiteParts (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    let w := physicalFundamentalFrequency q side
    let s := physicalRate q br
    let chi := physicalRadialFrequency q
    let K := D4BMOriginalCanonicalMetricCutoff.gradient q br
    let mu := physicalAngularParameter q^(2 : ℕ)-1/4
    let C := physicalSelfSourceCoefficient q
    canonicalQNMValue q br side amp=
      -mu*(mu-2)*C*sourceDerivativeFinitePart s chi amp 1 K w+
        mu*w*C*continuedOnset s w*nativeForcingSourceFinitePart q br amp K w := by
  dsimp only
  rw [canonicalQNMValue_eq_completeSourceAction,completeSourceAction,
    physicalFundamentalFrequency_connection_zero]
  simp only [mul_zero,zero_mul,zero_div,add_zero,forcingCoefficient]

end
end RHTower.D4BMOriginalSourceResolvent
