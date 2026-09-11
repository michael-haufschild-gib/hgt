import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOppositePairingFinitePart
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalFundamentalSlope
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalGreenFactor

/-! An explicit analytic extension of the restored physical opposite-horizon pairing. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Set Filter Topology Metric MeasureTheory GaloisForLFunctions.HTGeometry D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The actual source numerator after dividing only by the nonzero observation mode. -/
def oppositeEndpointPoleNumerator (s chi a J K : ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  ((normalizable w chi b/horizon w chi b)*firstEndpointMellin (horizonMellinCore s chi a J K) b w+
    ∫ z in Ioc b (1:ℝ), normalizable w chi z*sourceProfile s w a J K 1 z)*
      (1/(w-2*s)+onsetCorrection (2*s) w)

theorem oppositeEndpointPoleNumerator_analyticAt (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (hs : w-2*s ≠ 0)
    {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1) (hh : horizon w chi b ≠ 0) :
    AnalyticAt ℂ (oppositeEndpointPoleNumerator s chi a J K b) w := by
  have hS : AnalyticAt ℂ (fun u : ℂ => 1/(u-2*s)+onsetCorrection (2*s) u) w :=
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const) hs).add
      ((onsetCorrection_entire (2*s)).analyticAt w)
  unfold oppositeEndpointPoleNumerator
  exact (((((normalizable_frequency_entire chi hb).analyticAt w).div
    (horizon_frequency_analyticAt w chi hw hb) hh).mul
    (horizonFirstMellin_analyticAt s chi a J K w hw hwr hb.1 hb.2)).add
    ((outerSourceIntegral_entire s chi a J K hb.1 hb.2).analyticAt w)).mul hS

private theorem clear_endpoint_scalar (c h n m o t p : ℂ) (hc : c ≠ 0) (hh : h ≠ 0) :
    c*((n*(m*t/(-c))+h*(o*t/(-c)))/h-p) = -(((n/h)*m+o)*t)-c*p := by
  field_simp [hc,hh]
  ring

/-- The cleared endpoint identity is proved on its original punctured germ. -/
theorem connection_mul_incomingEndpoint_eq (s chi a J K w : ℂ) (b : ℝ)
    (hc : connection w chi ≠ 0) (hh : horizon w chi b ≠ 0) :
    connection w chi*incomingResponseEndpoint s chi a J K w b=
      -oppositeEndpointPoleNumerator s chi a J K b w-
        connection w chi*incomingSourcePrimitive s chi a J K w b := by
  exact clear_endpoint_scalar (connection w chi) (horizon w chi b) (normalizable w chi b)
    (firstEndpointMellin (horizonMellinCore s chi a J K) b w)
    (∫ z in Ioc b (1:ℝ), normalizable w chi z*sourceProfile s w a J K 1 z)
    (1/(w-2*s)+onsetCorrection (2*s) w) (incomingSourcePrimitive s chi a J K w b) hc hh

/-- The extension keeps both restored logarithmic source pieces and the full cleared numerator. -/
def oppositePairingExtension (s chi a J K : ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  ((-oppositeEndpointPoleNumerator s chi a J K b w-
    connection w chi*incomingSourcePrimitive s chi a J K w b)*oppositeNormFinitePart chi b w+
      connection w chi*oppositeSourcePairingFinitePart s chi a J K b w)/(2*w)

theorem oppositePairingFinitePart_eq_extension (s chi a J K w : ℂ) (b : ℝ)
    (hc : connection w chi ≠ 0) (hh : horizon w chi b ≠ 0) :
    oppositePairingFinitePart s chi a J K b w=oppositePairingExtension s chi a J K b w := by
  unfold oppositePairingFinitePart oppositePairingExtension
  calc
    _ = ((connection w chi*incomingResponseEndpoint s chi a J K w b)*oppositeNormFinitePart chi b w+
      connection w chi*oppositeSourcePairingFinitePart s chi a J K b w)/(2*w) := by ring
    _ = _ := by rw [connection_mul_incomingEndpoint_eq s chi a J K w b hc hh]

end
end RHTower.D4BMLaplaceRadial

namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The cleared incoming quotient retains the same complete fixed source moment at every interior cut. -/
theorem oppositeEndpointPoleNumerator_fundamental_value (w chi s a : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re)
    (hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi)
    {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1) :
    oppositeEndpointPoleNumerator s chi a 1 (reducedGreenGradient chi s 1) b w=
      fundamentalSourceMoment w s a*continuedOnset s w := by
  have hn : normalizable w chi b ≠ 0 := by
    rw [normalizable_fundamental_value w chi hf]
    exact mul_ne_zero (power_ne_zero _ hb.1) (power_ne_zero _ (sub_pos.mpr hb.2))
  rw [oppositeEndpointPoleNumerator,horizon_eq_normalizable_fundamental w chi hw hf hb,
    div_self hn,one_mul,fundamental_source_sum_eq_moment w chi s a hw hwr hf hb]
  rfl

/-- The regular extension has its source-determined value, rather than the artificial value of division at the pole. -/
theorem physicalOppositePairingExtension_value (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1) :
    let w := physicalFundamentalFrequency q side
    let s := physicalRate q branch
    let chi := physicalRadialFrequency q
    oppositePairingExtension s chi a 1 (reducedGreenGradient chi s 1) b w=
      -(fundamentalSourceMoment w s a*continuedOnset s w*oppositeNormFinitePart chi b w)/(2*w) := by
  dsimp only
  have hw := physicalFundamentalFrequency_strip q side
  have hf : physicalFundamentalFrequency q side=-3/2-Complex.I*physicalRadialFrequency q ∨
      physicalFundamentalFrequency q side=-3/2+Complex.I*physicalRadialFrequency q := by
    rw [physicalFundamentalFrequency_connection_root]
    cases side <;> simp
  simp only [oppositePairingExtension,physicalFundamentalFrequency_connection_zero,
    zero_mul,sub_zero,add_zero]
  rw [oppositeEndpointPoleNumerator_fundamental_value _ _ _ _ hw.1 (abs_lt.mp hw.2).1 hf hb]
  ring

/-- The actual restored opposite block has an analytic extension, with its original logarithmic cutoff identity, and no physical pole residue. -/
theorem physicalOppositePairing_analytic_restoration (q : XiZeroCopy) (branch side : Bool) (a : ℂ) :
    let w := physicalFundamentalFrequency q side
    let s := physicalRate q branch
    let chi := physicalRadialFrequency q
    let K := reducedGreenGradient chi s 1
    ∃ b : ℝ, 0 < b ∧ b ≤ 1/2 ∧
      AnalyticAt ℂ (oppositePairingExtension s chi a 1 K b) w ∧
      Tendsto (oppositePairingFinitePart s chi a 1 K b) (𝓝[≠] w)
        (𝓝 (oppositePairingExtension s chi a 1 K b w)) ∧
      Tendsto (fun u => (u-w)*oppositePairingFinitePart s chi a 1 K b u) (𝓝[≠] w) (𝓝 0) ∧
      ∀ᶠ u in 𝓝[≠] w,
        Tendsto (fun e : ℝ =>
          (∫ z in e..b, (connection u chi/(2*u))*(continuedResponse s chi a 1 K z u*horizon (-u) chi z/
            (2*(z:ℂ)*(Real.sqrt (1-z):ℂ))))+
          (connection u chi/(2*u))*(incomingResponseEndpoint s chi a 1 K u b/2)*(Real.log e:ℂ))
          (𝓝[>] (0:ℝ)) (𝓝 (oppositePairingExtension s chi a 1 K b u)) := by
  dsimp only
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q branch
  let chi := physicalRadialFrequency q
  let K := reducedGreenGradient chi s 1
  have hw := physicalFundamentalFrequency_strip q side
  have hwr := (abs_lt.mp hw.2).1
  have hs := physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  obtain ⟨R,b,hR,hb,hbhalf,hL,hK,hP,hcut⟩ := oppositePairingFinitePart_horizon_restoration
    s chi a 1 K w hw.1 hwr hs
  have hb1 : b < 1 := by linarith
  have hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi := by
    dsimp only [w,chi]
    rw [physicalFundamentalFrequency_connection_root]
    cases side <;> simp
  have hh : horizon w chi b ≠ 0 := by
    rw [horizon_eq_normalizable_fundamental w chi hw.1 hf ⟨hb,hb1⟩,
      normalizable_fundamental_value w chi hf]
    exact mul_ne_zero (power_ne_zero _ hb) (power_ne_zero _ (sub_pos.mpr hb1))
  have hH := horizon_frequency_analyticAt w chi hw.1 ⟨hb,hb1⟩
  have hB := oppositeEndpointPoleNumerator_analyticAt s chi a 1 K w hw.1 hwr hs ⟨hb,hb1⟩ hh
  have hC := connection_frequency_analyticAt w chi hw.1
  have hw0 : w ≠ 0 := by intro h; apply hw.1; change w.im=0; rw [h]; rfl
  have hE : AnalyticAt ℂ (oppositePairingExtension s chi a 1 K b) w := by
    unfold oppositePairingExtension
    exact (((hB.neg.sub (hC.mul hP)).mul hL).add (hC.mul hK)).div
      (analyticAt_const.mul analyticAt_id) (mul_ne_zero (by norm_num) hw0)
  have hcne : ∀ᶠ u in 𝓝[≠] w, connection u chi ≠ 0 :=
    (physicalFundamental_connection_hasDerivAt q side).eventually_ne (c := 0)
      (physicalFundamental_connectionSlope_ne_zero q side)
  have hhne : ∀ᶠ u in 𝓝[≠] w, horizon u chi b ≠ 0 :=
    (hH.continuousAt.eventually_ne hh).filter_mono nhdsWithin_le_nhds
  have heq : oppositePairingFinitePart s chi a 1 K b =ᶠ[𝓝[≠] w]
      oppositePairingExtension s chi a 1 K b := by
    filter_upwards [hcne,hhne] with u hcu hhu
    exact oppositePairingFinitePart_eq_extension s chi a 1 K u b hcu hhu
  have hlim : Tendsto (oppositePairingFinitePart s chi a 1 K b) (𝓝[≠] w)
      (𝓝 (oppositePairingExtension s chi a 1 K b w)) :=
    (hE.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm
  refine ⟨b,hb,hbhalf,hE,hlim,?_,?_⟩
  · have hx : Tendsto (fun u : ℂ => u-w) (𝓝[≠] w) (𝓝 0) := by
      have h : Tendsto (fun u : ℂ => u) (𝓝[≠] w) (𝓝 w) := tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [sub_self] using h.sub_const w
    simpa only [zero_mul] using hx.mul hlim
  · have hball : ∀ᶠ u : ℂ in 𝓝[≠] w, u ∈ ball w R :=
      (show ∀ᶠ u : ℂ in 𝓝 w, u ∈ ball w R from Metric.ball_mem_nhds w hR).filter_mono nhdsWithin_le_nhds
    filter_upwards [hball,hcne,heq] with u hu hcu he
    rw [← he]
    exact hcut u hu hcu

end
end RHTower.D4BMJointSource
