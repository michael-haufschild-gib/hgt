import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIncomingPairingFinitePart
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalFundamentalSlope
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalGreenFactor

/-! Residue extraction after restoring the actual incoming radial integral. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The pole amplitude retains the complete source moment, fixed onset and original connection slope. -/
def physicalIncomingPoleAmplitude (q : XiZeroCopy) (branch side : Bool) (a : ℂ) : ℂ :=
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q branch
  fundamentalSourceMoment w s a*(1/(w-2*s)+onsetCorrection (2*s) w)/
    (-connectionSimpleSlope w (physicalRadialFrequency q) side)

/-- The incoming amplitude uses exactly the cleared source normalization already present in the physical current. -/
theorem physicalIncomingPoleAmplitude_eq_cleared (q : XiZeroCopy) (branch side : Bool) (a : ℂ) :
    physicalIncomingPoleAmplitude q branch side a=
      fundamentalSourceMoment (physicalFundamentalFrequency q side) (physicalRate q branch) a*
      clearedOnset (physicalRate q branch) (physicalFundamentalFrequency q side)/
      physicalFundamentalDenominatorSlope q branch side := by
  unfold physicalIncomingPoleAmplitude physicalFundamentalDenominatorSlope clearedOnset
  dsimp only
  field_simp [physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side,
    physicalFundamental_connectionSlope_ne_zero q side]

/-- The actual incoming quotient has the source-derived fundamental residue at every interior radius. -/
theorem physicalIncomingQuotient_residue (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1) :
    Tendsto (fun u => (u-physicalFundamentalFrequency q side)*
      (continuedResponse (physicalRate q branch) (physicalRadialFrequency q) a 1
        (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q branch) 1) b u/
          horizon u (physicalRadialFrequency q) b))
      (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 (physicalIncomingPoleAmplitude q branch side a)) := by
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q branch
  let chi := physicalRadialFrequency q
  let K := reducedGreenGradient chi s 1
  have hw := physicalFundamentalFrequency_strip q side
  have hwr := (abs_lt.mp hw.2).1
  have hs := physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  have hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi := by
    dsimp only [w,chi]
    rw [physicalFundamentalFrequency_connection_root]
    cases side <;> simp
  have hh : horizon w chi b ≠ 0 := by
    rw [horizon_eq_normalizable_fundamental w chi hw.1 hf hb,
      normalizable_fundamental_value w chi hf]
    exact mul_ne_zero (power_ne_zero _ hb.1) (power_ne_zero _ (sub_pos.mpr hb.2))
  let N := fun u : ℂ =>
    ((normalizable u chi b/horizon u chi b)*firstEndpointMellin (horizonMellinCore s chi a 1 K) b u+
      ∫ z in Ioc b (1:ℝ), normalizable u chi z*sourceProfile s u a 1 K 1 z)*
        (1/(u-2*s)+onsetCorrection (2*s) u)
  have hH := horizon_frequency_analyticAt w chi hw.1 hb
  have hS : AnalyticAt ℂ (fun u : ℂ => 1/(u-2*s)+onsetCorrection (2*s) u) w :=
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const) hs).add
      ((onsetCorrection_entire (2*s)).analyticAt w)
  have hN : AnalyticAt ℂ N w :=
    (((((normalizable_frequency_entire chi hb).analyticAt w).div hH hh).mul
      (horizonFirstMellin_analyticAt s chi a 1 K w hw.1 hwr hb.1 hb.2)).add
      ((outerSourceIntegral_entire s chi a 1 K hb.1 hb.2).analyticAt w)).mul hS
  have hD : HasDerivAt (fun u => -connection u chi) (-connectionSimpleSlope w chi side) w :=
    (physicalFundamental_connection_hasDerivAt q side).neg
  have hd : -connectionSimpleSlope w chi side ≠ 0 :=
    neg_ne_zero.mpr (physicalFundamental_connectionSlope_ne_zero q side)
  have hz : -connection w chi=0 := by
    simp only [w,chi,physicalFundamentalFrequency_connection_zero,neg_zero]
  have hlim := (hN.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).div hD.tendsto_slope hd
  have hvalue : N w/(-connectionSimpleSlope w chi side)=physicalIncomingPoleAmplitude q branch side a := by
    have hn : normalizable w chi b ≠ 0 := by
      rw [← horizon_eq_normalizable_fundamental w chi hw.1 hf hb]
      exact hh
    dsimp only [N,physicalIncomingPoleAmplitude]
    rw [horizon_eq_normalizable_fundamental w chi hw.1 hf hb,div_self hn,one_mul,
      fundamental_source_sum_eq_moment w chi s a hw.1 hwr hf hb]
  rw [hvalue] at hlim
  apply hlim.congr'
  have hhg : ∀ᶠ u in 𝓝[≠] w, horizon u chi b ≠ 0 :=
    (hH.continuousAt.eventually_ne hh).filter_mono nhdsWithin_le_nhds
  filter_upwards [hhg,hD.eventually_ne (c := 0) hd] with u hhu hcu
  have hc : connection u chi ≠ 0 := neg_ne_zero.mp hcu
  simp only [Pi.div_apply,slope_def_field,hz,sub_zero,div_div_eq_mul_div]
  change N u*(u-w)/(-connection u chi)=
    (u-w)*(continuedResponse s chi a 1 K b u/horizon u chi b)
  dsimp only [N,continuedResponse,continuedHorizonMoment,continuedOuterMoment]
  field_simp [hhu,hc]
  ring

/-- On one fixed horizon cut, restoration of the original integral precedes extraction of its physical residue. -/
theorem physicalIncomingPairing_residue_and_restoration (q : XiZeroCopy) (branch side : Bool) (a : ℂ) :
    let w := physicalFundamentalFrequency q side
    let s := physicalRate q branch
    let chi := physicalRadialFrequency q
    let K := reducedGreenGradient chi s 1
    ∃ R b : ℝ, 0 < R ∧ 0 < b ∧ b ≤ 1/2 ∧
      AnalyticAt ℂ (incomingNormFinitePart chi b) w ∧
      Tendsto (fun u => (u-w)*incomingPairingFinitePart s chi a 1 K b u)
        (𝓝[≠] w) (𝓝 (physicalIncomingPoleAmplitude q branch side a*incomingNormFinitePart chi b w)) ∧
      ∀ u ∈ ball w R, connection u chi ≠ 0 →
        Tendsto (fun e : ℝ =>
          (∫ z in e..b, continuedResponse s chi a 1 K z u*horizon u chi z/
            (2*(z:ℂ)*(Real.sqrt (1-z):ℂ)))+
          (incomingResponseEndpoint s chi a 1 K u b/2)*(e:ℂ)^u/u+
          ((horizonGaussFirstCoefficient u chi+1/4)*incomingResponseEndpoint s chi a 1 K u b+
            incomingResponseSlope s a 1 K u/2)*(e:ℂ)^(u+1)/(u+1))
          (𝓝[>] (0:ℝ)) (𝓝 (incomingPairingFinitePart s chi a 1 K b u)) := by
  dsimp only
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q branch
  let chi := physicalRadialFrequency q
  let K := reducedGreenGradient chi s 1
  have hw := physicalFundamentalFrequency_strip q side
  have hs := physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  obtain ⟨R,b,hR,hb,hbhalf,hN,hJ,hP,hcut⟩ := incomingPairingFinitePart_horizon_restoration
    s chi a 1 K w hw.1 (abs_lt.mp hw.2).1 hs
  refine ⟨R,b,hR,hb,hbhalf,hN,?_,hcut⟩
  have hx : Tendsto (fun u : ℂ => u-w) (𝓝[≠] w) (𝓝 0) := by
    have h : Tendsto (fun u : ℂ => u) (𝓝[≠] w) (𝓝 w) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [sub_self] using h.sub_const w
  have hQ := physicalIncomingQuotient_residue q branch side a ⟨hb,by linarith⟩
  have hp : Tendsto (fun u => incomingSourcePrimitive s chi a 1 K u b)
      (𝓝[≠] w) (𝓝 (incomingSourcePrimitive s chi a 1 K w b)) :=
    hP.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ha := hQ.sub (hx.mul hp)
  simp only [zero_mul,sub_zero] at ha
  have hA : Tendsto (fun u => (u-w)*incomingResponseEndpoint s chi a 1 K u b)
      (𝓝[≠] w) (𝓝 (physicalIncomingPoleAmplitude q branch side a)) := by
    apply ha.congr'
    filter_upwards [] with u
    dsimp only [incomingResponseEndpoint,incomingSourcePrimitive]
    ring
  have h := (hA.mul (hN.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).add
    (hx.mul (hJ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  simp only [zero_mul,add_zero] at h
  apply h.congr'
  filter_upwards [] with u
  dsimp only [incomingPairingFinitePart]
  ring

end
end RHTower.D4BMJointSource
