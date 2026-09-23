import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceContinuedForcedODE
import GaloisForLFunctions.HTGeometry.NormalizedFirstEndpointMellin
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalFundamentalFrequencies
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalRadialModes

/-! The actual Green quotient derivative after exact Wronskian cancellation of the connection factor. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The source-determined spatial derivative of the original Green quotient. -/
def incomingSourceTransport (s chi a J K w : ℂ) (b : ℝ) : ℂ :=
  firstEndpointMellin (horizonMellinCore s chi a J K) b w*
    (1/(w-2*s)+onsetCorrection (2*s) w)/
      (2*(b:ℂ)*(Real.sqrt (1-b):ℂ)*(horizon w chi b)^(2 : ℕ))

/-- The exact original Wronskian cancels the apparent connection pole in the quotient derivative. -/
theorem continuedResponse_div_horizon_hasDerivAt (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (hc : connection w chi ≠ 0)
    {b : ℝ} (hb : b ∈ Ioo 0 1) (hh : horizon w chi b ≠ 0) :
    HasDerivAt (fun t => continuedResponse s chi a J K t w/horizon w chi t)
      (incomingSourceTransport s chi a J K w b) b := by
  have hd := (continuedResponse_hasDerivAt s chi a J K w hw hwr hb).1
  have hH := (horizon_derivatives_continued (w := w) (chi := chi) hb).1
  have hb0 : (b:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hb.1)
  have hs : (Real.sqrt (1-b):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hb.2)))
  have hW := wronskian_eq_continued w chi hw hb
  dsimp only [wronskian,integratingFactor] at hW
  rw [power_half_eq_sqrt (sub_nonneg.mpr hb.2.le)] at hW
  have hW' : horizon w chi b*normalizableFirst w chi b-horizonFirst w chi b*normalizable w chi b=
      -connection w chi/(2*(b:ℂ)*(Real.sqrt (1-b):ℂ)) := by
    field_simp [hb0,hs] at hW ⊢
    linear_combination hW
  apply (hd.div hH hh).congr_deriv
  calc
    _ = (horizon w chi b*normalizableFirst w chi b-horizonFirst w chi b*normalizable w chi b)*
        continuedHorizonMoment s chi a J K b w/(horizon w chi b)^(2 : ℕ) := by
      dsimp only [continuedResponse,continuedResponseFirst]
      ring
    _ = _ := by
      rw [hW',continuedHorizonMoment,incomingSourceTransport]
      field_simp [hc]

/-- The derivative of the normalized actual Green response has an analytic continuation through connection zeros. -/
theorem incomingSourceTransport_analyticAt (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (hs : w-2*s ≠ 0)
    {b : ℝ} (hb : b ∈ Ioo 0 1) (hh : horizon w chi b ≠ 0) :
    AnalyticAt ℂ (fun v => incomingSourceTransport s chi a J K v b) w := by
  have hm := horizonFirstMellin_analyticAt s chi a J K w hw hwr hb.1 hb.2
  have ht : AnalyticAt ℂ (fun v : ℂ => 1/(v-2*s)+onsetCorrection (2*s) v) w :=
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const) hs).add
      ((onsetCorrection_entire (2*s)).analyticAt w)
  have hd : AnalyticAt ℂ (fun v : ℂ => 2*(b:ℂ)*(Real.sqrt (1-b):ℂ)*(horizon v chi b)^(2 : ℕ)) w :=
    analyticAt_const.mul ((horizon_frequency_analyticAt w chi hw hb).pow 2)
  have hb0 : (b:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hb.1)
  have hsq : (Real.sqrt (1-b):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hb.2)))
  exact (hm.mul ht).div hd (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hb0) hsq) (pow_ne_zero _ hh))

/-- The analytic source transport is the genuine spatial derivative on the whole punctured physical germ. -/
theorem continuedResponse_div_horizon_derivative_germ (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) {b : ℝ} (hb : b ∈ Ioo 0 1)
    (hh : horizon w chi b ≠ 0) :
    ∀ᶠ v in 𝓝[≠] w,
      HasDerivAt (fun t => continuedResponse s chi a J K t v/horizon v chi t)
        (incomingSourceTransport s chi a J K v b) b := by
  have hi := (Complex.continuous_im.continuousAt.eventually_ne hw).filter_mono
    (show 𝓝[≠] w ≤ 𝓝 w from nhdsWithin_le_nhds)
  have hr := (Complex.continuous_re.continuousAt.eventually_const_lt hwr).filter_mono
    (show 𝓝[≠] w ≤ 𝓝 w from nhdsWithin_le_nhds)
  have he := ((horizon_frequency_analyticAt w chi hw hb).continuousAt.eventually_ne hh).filter_mono
    (show 𝓝[≠] w ≤ 𝓝 w from nhdsWithin_le_nhds)
  filter_upwards [hi,hr,he,connection_eventually_ne_zero w chi hw] with v hvi hvr hvh hvc
  exact continuedResponse_div_horizon_hasDerivAt s chi a J K v hvi hvr hvc hb hvh

/-- Removing the explicit incoming powers exposes the actual source transport at the horizon. -/
def regularIncomingSourceTransport (s chi a J K w : ℂ) (b : ℝ) : ℂ :=
  normalizedFirstEndpointMellin (horizonMellinCore s chi a J K) w b*
    (1/(w-2*s)+onsetCorrection (2*s) w)/
      (2*(Real.sqrt (1-b):ℂ)*(gaussFactor w chi false (b:ℂ))^(2 : ℕ))

/-- Exact cancellation of the incoming powers, before taking a horizon limit. -/
theorem incomingSourceTransport_eq_regular (s chi a J K w : ℂ)
    {b : ℝ} (hb : 0 < b) :
    incomingSourceTransport s chi a J K w b=regularIncomingSourceTransport s chi a J K w b := by
  have hb0 : (b:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hb)
  have hp : (power (w/2) b)^(2 : ℕ)=(b:ℂ)^w := by
    rw [power,pow_two,← Complex.cpow_add _ _ hb0,show w/2+w/2=w by ring]
  have hbp : (b:ℂ)*(b:ℂ)^w=(b:ℂ)^(w+1) := by
    calc
      _ = (b:ℂ)^(1:ℂ)*(b:ℂ)^w := by rw [Complex.cpow_one]
      _ = _ := by rw [← Complex.cpow_add _ _ hb0,add_comm]
  have hd : 2*(b:ℂ)*(Real.sqrt (1-b):ℂ)*(horizon w chi b)^(2 : ℕ)=
      (b:ℂ)^(w+1)*(2*(Real.sqrt (1-b):ℂ)*(gaussFactor w chi false (b:ℂ))^(2 : ℕ)) := by
    rw [horizon,dress,mul_pow,hp,← hbp]
    ring
  rw [incomingSourceTransport,hd,regularIncomingSourceTransport,normalizedFirstEndpointMellin,
    if_neg (ne_of_gt hb)]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The full source transport has a derived finite horizon value, also at connection zeros. -/
theorem incomingSourceTransport_tendsto_horizon (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) :
    Tendsto (incomingSourceTransport s chi a J K w) (𝓝[>] (0:ℝ))
      (𝓝 (sourceRemainder s w a J K 1 0*
        (1/(w-2*s)+onsetCorrection (2*s) w)/(2*(w+1)))) := by
  obtain ⟨R,C,hR,_,_,hbound⟩ := horizonMellinCore_uniform_first_bound s chi a J K w hw
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  have hM := normalizedFirstEndpointMellin_tendsto (by norm_num : (0:ℝ) < 1/2) hwr
    (horizonMellinCore_measurable s chi a J K w)
    (fun b hb => hbound w (Metric.mem_ball_self hR) b ⟨hb.1.le,hb.2⟩)
  have hGc := (gaussFactor_derivatives_continued (w := w) (chi := chi) false
    (by simp : ‖(0:ℂ)‖ₑ < 1)).1.comp_ofReal.continuousAt
  have hG : Tendsto (fun b : ℝ => gaussFactor w chi false (b:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    simpa only [Complex.ofReal_zero,gaussFactor_zero] using hGc.tendsto.mono_left
      (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)
  have hS : Tendsto (fun b : ℝ => (Real.sqrt (1-b):ℂ)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have hh := (show Continuous (fun b : ℝ => (Real.sqrt (1-b):ℂ)) by fun_prop).tendsto 0
    simpa only [sub_zero,Real.sqrt_one,Complex.ofReal_one] using hh.mono_left
      (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)
  have hlim := (hM.mul_const (1/(w-2*s)+onsetCorrection (2*s) w)).div
    ((hS.const_mul 2).mul (hG.pow 2)) (by norm_num : (2:ℂ)*1*1^(2 : ℕ) ≠ 0)
  have he : Tendsto (regularIncomingSourceTransport s chi a J K w) (𝓝[>] (0:ℝ))
      (𝓝 (sourceRemainder s w a J K 1 0*(1/(w-2*s)+onsetCorrection (2*s) w)/(2*(w+1)))) := by
    have hv : horizonMellinCore s chi a J K w 0/(w+1)*
        (1/(w-2*s)+onsetCorrection (2*s) w)/(2*1*1^(2 : ℕ))=
        sourceRemainder s w a J K 1 0*(1/(w-2*s)+onsetCorrection (2*s) w)/(2*(w+1)) := by
      simp only [horizonMellinCore,Complex.ofReal_zero,gaussFactor_zero,one_mul,div_mul_eq_div_div]
      ring
    rw [hv] at hlim
    exact hlim
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with b hb
  exact (incomingSourceTransport_eq_regular s chi a J K w hb).symm

end
end RHTower.D4BMLaplaceRadial

namespace RHTower.D4BMJointSource
open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private theorem physical_horizon_fundamental_ne_zero (q : XiZeroCopy) (side : Bool)
    {b : ℝ} (hb : b ∈ Ioo 0 1) :
    horizon (physicalFundamentalFrequency q side) (physicalRadialFrequency q) b ≠ 0 := by
  have hf : physicalFundamentalFrequency q side=-3/2-Complex.I*physicalRadialFrequency q ∨
      physicalFundamentalFrequency q side=-3/2+Complex.I*physicalRadialFrequency q := by
    rw [physicalFundamentalFrequency_connection_root]
    cases side <;> simp
  rw [horizon_eq_normalizable_fundamental _ _ (physicalFundamentalFrequency_strip q side).1 hf hb,
    normalizable_fundamental_value _ _ hf b]
  exact mul_ne_zero (power_ne_zero _ hb.1) (power_ne_zero _ (sub_pos.mpr hb.2))

/-- At both actual Xi fundamental frequencies the original reduced-source Green quotient has analytic spatial transport. -/
theorem physical_fundamental_incomingSourceTransport_regular (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (b : Ioo (0:ℝ) 1) :
    let w := physicalFundamentalFrequency q side
    let chi := physicalRadialFrequency q
    let s := physicalRate q branch
    let K := reducedGreenGradient chi s 1
    AnalyticAt ℂ (fun v => incomingSourceTransport s chi a 1 K v b) w ∧
      ∀ᶠ v in 𝓝[≠] w,
        HasDerivAt (fun t => continuedResponse s chi a 1 K t v/horizon v chi t)
          (incomingSourceTransport s chi a 1 K v b) b := by
  dsimp only
  have hw := physicalFundamentalFrequency_strip q side
  have hh := physical_horizon_fundamental_ne_zero q side b.property
  exact ⟨incomingSourceTransport_analyticAt _ _ _ _ _ _ hw.1 (abs_lt.mp hw.2).1
    (physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side) b.property hh,
    continuedResponse_div_horizon_derivative_germ _ _ _ _ _ _ hw.1 (abs_lt.mp hw.2).1 b.property hh⟩

/-- The same literal source transport reaches its finite horizon value at both Xi fundamental frequencies. -/
theorem physical_fundamental_incomingSourceTransport_horizon (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) :
    let w := physicalFundamentalFrequency q side
    let chi := physicalRadialFrequency q
    let s := physicalRate q branch
    let K := reducedGreenGradient chi s 1
    Tendsto (incomingSourceTransport s chi a 1 K w) (𝓝[>] (0:ℝ))
      (𝓝 (sourceRemainder s w a 1 K 1 0*(1/(w-2*s)+onsetCorrection (2*s) w)/(2*(w+1)))) := by
  dsimp only
  exact incomingSourceTransport_tendsto_horizon _ _ _ _ _ _
    (physicalFundamentalFrequency_strip q side).1 (abs_lt.mp (physicalFundamentalFrequency_strip q side).2).1

end
end RHTower.D4BMJointSource
