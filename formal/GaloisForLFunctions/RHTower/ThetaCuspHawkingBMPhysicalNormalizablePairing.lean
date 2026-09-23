import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNormalizableHorizonPairing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRegularOuterPairing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalOppositePairingRegularity

/-! Restoration and residue of both normalizable horizon branches at the original outer cutoff. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false

private theorem incoming_residue_at_cutoff (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1)
    (hN : AnalyticAt ℂ (incomingNormFinitePart (physicalRadialFrequency q) b) (physicalFundamentalFrequency q side))
    (hJ : AnalyticAt ℂ (incomingSourcePairingFinitePart (physicalRate q branch) (physicalRadialFrequency q)
      a 1 (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q branch) 1) b) (physicalFundamentalFrequency q side))
    (hP : AnalyticAt ℂ (fun u => incomingSourcePrimitive (physicalRate q branch) (physicalRadialFrequency q)
      a 1 (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q branch) 1) u b) (physicalFundamentalFrequency q side)) :
    let w := physicalFundamentalFrequency q side
    let s := physicalRate q branch
    let chi := physicalRadialFrequency q
    Tendsto (fun u => (u-w)*incomingPairingFinitePart s chi a 1 (reducedGreenGradient chi s 1) b u)
      (𝓝[≠] w) (𝓝 (physicalIncomingPoleAmplitude q branch side a*incomingNormFinitePart chi b w)) := by
  dsimp only
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q branch
  let chi := physicalRadialFrequency q
  let K := reducedGreenGradient chi s 1
  have hx : Tendsto (fun u : ℂ => u-w) (𝓝[≠] w) (𝓝 0) := by
    have h : Tendsto (fun u : ℂ => u) (𝓝[≠] w) (𝓝 w) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [sub_self] using h.sub_const w
  have ha := (physicalIncomingQuotient_residue q branch side a hb).sub
    (hx.mul (hP.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  simp only [zero_mul,sub_zero] at ha
  have hA : Tendsto (fun u => (u-w)*incomingResponseEndpoint s chi a 1 K u b)
      (𝓝[≠] w) (𝓝 (physicalIncomingPoleAmplitude q branch side a)) := by
    apply ha.congr'
    filter_upwards [] with u
    change (u-w)*(continuedResponse s chi a 1 K b u/horizon u chi b)-
      (u-w)*incomingSourcePrimitive s chi a 1 K u b=
      (u-w)*(continuedResponse s chi a 1 K b u/horizon u chi b-
        incomingSourcePrimitive s chi a 1 K u b)
    exact (mul_sub (u-w) _ _).symm
  have h := (hA.mul (hN.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).add
    (hx.mul (hJ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  simp only [zero_mul,add_zero] at h
  apply h.congr'
  filter_upwards [] with u
  dsimp only [incomingPairingFinitePart]
  ring

private theorem opposite_residue_at_cutoff (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1)
    (hL : AnalyticAt ℂ (oppositeNormFinitePart (physicalRadialFrequency q) b) (physicalFundamentalFrequency q side))
    (hK : AnalyticAt ℂ (oppositeSourcePairingFinitePart (physicalRate q branch) (physicalRadialFrequency q)
      a 1 (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q branch) 1) b) (physicalFundamentalFrequency q side))
    (hP : AnalyticAt ℂ (fun u => incomingSourcePrimitive (physicalRate q branch) (physicalRadialFrequency q)
      a 1 (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q branch) 1) u b) (physicalFundamentalFrequency q side)) :
    let w := physicalFundamentalFrequency q side
    let s := physicalRate q branch
    let chi := physicalRadialFrequency q
    Tendsto (fun u => (u-w)*oppositePairingFinitePart s chi a 1 (reducedGreenGradient chi s 1) b u)
      (𝓝[≠] w) (𝓝 0) := by
  dsimp only
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q branch
  let chi := physicalRadialFrequency q
  let K := reducedGreenGradient chi s 1
  have hw := physicalFundamentalFrequency_strip q side
  have hs := physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  have hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi := by
    dsimp only [w,chi]
    rw [physicalFundamentalFrequency_connection_root]
    cases side <;> simp
  have hh : horizon w chi b ≠ 0 := by
    rw [horizon_eq_normalizable_fundamental w chi hw.1 hf hb,normalizable_fundamental_value w chi hf]
    exact mul_ne_zero (power_ne_zero _ hb.1) (power_ne_zero _ (sub_pos.mpr hb.2))
  have hH := horizon_frequency_analyticAt w chi hw.1 hb
  have hB := oppositeEndpointPoleNumerator_analyticAt s chi a 1 K w hw.1 (abs_lt.mp hw.2).1 hs hb hh
  have hC := connection_frequency_analyticAt w chi hw.1
  have hw0 : w ≠ 0 := by intro he; apply hw.1; change w.im=0; rw [he]; rfl
  have hE : AnalyticAt ℂ (oppositePairingExtension s chi a 1 K b) w := by
    unfold oppositePairingExtension
    exact (((hB.neg.sub (hC.mul hP)).mul hL).add (hC.mul hK)).div
      (analyticAt_const.mul analyticAt_id) (mul_ne_zero (by norm_num) hw0)
  have hcne : ∀ᶠ u in 𝓝[≠] w, connection u chi ≠ 0 :=
    (physicalFundamental_connection_hasDerivAt q side).eventually_ne (c := 0)
      (physicalFundamental_connectionSlope_ne_zero q side)
  have hhne : ∀ᶠ u in 𝓝[≠] w, horizon u chi b ≠ 0 :=
    (hH.continuousAt.eventually_ne hh).filter_mono nhdsWithin_le_nhds
  have heq : oppositePairingExtension s chi a 1 K b =ᶠ[𝓝[≠] w]
      oppositePairingFinitePart s chi a 1 K b := by
    filter_upwards [hcne,hhne] with u hcu hhu
    exact (oppositePairingFinitePart_eq_extension s chi a 1 K u b hcu hhu).symm
  have hlim := (hE.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq
  have hx : Tendsto (fun u : ℂ => u-w) (𝓝[≠] w) (𝓝 0) := by
    have h : Tendsto (fun u : ℂ => u) (𝓝[≠] w) (𝓝 w) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [sub_self] using h.sub_const w
  simpa only [zero_mul] using hx.mul hlim

/-- Both normalizable horizon branches are joined to the original outer reduced-response pairing. -/
def normalizableOuterPairing (chi s a : ℂ) (T : ℝ) (w : ℂ) : ℂ :=
  normalizableHorizonPairingFinitePart s chi a 1 (reducedGreenGradient chi s 1) (horizonCoordinate T) w+
    continuedReducedOuterPairing chi s a T w

/-- The single original horizon integral, its three forced counterterms, and the original outer integral. -/
def normalizableOuterPairingCutoff (chi s a : ℂ) (T : ℝ) (w : ℂ) (e : ℝ) : ℂ :=
  normalizableHorizonPairingCutoff s chi a 1 (reducedGreenGradient chi s 1) (horizonCoordinate T) w e+
    continuedReducedOuterPairing chi s a T w

/-- Both horizon branches are restored at one source-derived cutoff before the physical residue is extracted. -/
theorem physicalNormalizableOuterPairing_residue_and_restoration_below (q : XiZeroCopy)
    (branch side : Bool) (a : ℂ) (cap : ℝ) (hcap : 0<cap) :
    let w := physicalFundamentalFrequency q side
    let s := physicalRate q branch
    let chi := physicalRadialFrequency q
    ∃ T R : ℝ, T < 0 ∧ 0 < R ∧ horizonCoordinate T≤cap ∧
      Tendsto (fun u => (u-w)*normalizableOuterPairing chi s a T u) (𝓝[≠] w)
        (𝓝 (physicalIncomingPoleAmplitude q branch side a*D4BMFundamentalNorm.normFinitePart w)) ∧
      ∀ u ∈ ball w R, connection u chi ≠ 0 →
        Tendsto (normalizableOuterPairingCutoff chi s a T u) (𝓝[>] (0:ℝ))
          (𝓝 (normalizableOuterPairing chi s a T u)) := by
  dsimp only
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q branch
  let chi := physicalRadialFrequency q
  let K := reducedGreenGradient chi s 1
  have hw := physicalFundamentalFrequency_strip q side
  have hwr := (abs_lt.mp hw.2).1
  have hs := physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  obtain ⟨RI,BI,hRI,hBI,hBIhalf,hsmallI⟩ :=
    incomingPairingFinitePart_horizon_restoration_below s chi a 1 K w hw.1 hwr hs
  obtain ⟨RO,BO,hRO,hBO,_,hsmallO⟩ :=
    oppositePairingFinitePart_horizon_restoration_below s chi a 1 K w hw.1 hwr hs
  let b := min cap (min BI BO)
  have hb : 0 < b := lt_min hcap (lt_min hBI hBO)
  have hbI : b ≤ BI := (min_le_right _ _).trans (min_le_left _ _)
  have hbO : b ≤ BO := (min_le_right _ _).trans (min_le_right _ _)
  have hb1 : b < 1 := lt_of_le_of_lt (hbI.trans hBIhalf) (by norm_num)
  obtain ⟨hN,hJ,hP,hcutI⟩ := hsmallI b hb hbI
  obtain ⟨hL,hQ,_,hcutO⟩ := hsmallO b hb hbO
  have hvalid : ∀ᶠ u : ℂ in 𝓝 w, u.im ≠ 0 ∧ -2 < u.re :=
    (Complex.continuous_im.continuousAt.eventually_ne hw.1).and
      (continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hwr)
  obtain ⟨RV,hRV,hV⟩ := Metric.eventually_nhds_iff.mp hvalid
  let R := min RI (min RO RV)
  have hR : 0 < R := lt_min hRI (lt_min hRO hRV)
  obtain ⟨T,hT,hTb⟩ := exists_matching_horizon_cutoff ⟨hb,hb1⟩
  have hIn := incoming_residue_at_cutoff q branch side a ⟨hb,hb1⟩ hN hJ hP
  have hOp := opposite_residue_at_cutoff q branch side a ⟨hb,hb1⟩ hL hQ hP
  have hA := normalizable_horizonRegularCoefficient_analyticAt w chi hw.1
  have hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi := by
    dsimp only [w,chi]
    rw [physicalFundamentalFrequency_connection_root]
    cases side <;> simp
  have hAlim := hA.continuousAt.tendsto.mono_left (show 𝓝[≠] w ≤ 𝓝 w from nhdsWithin_le_nhds)
  rw [fundamental_horizonRegularCoefficient w chi hw.1 hf] at hAlim
  have hO := physicalReducedOuterPairing_residue q branch side a hT
  have hlim := ((hAlim.mul hIn).add hOp).add hO
  simp only [one_mul,add_zero] at hlim
  have hNjoin := D4BMFundamentalNorm.physicalFundamentalNorm_join q side T hT
  have hvalue : physicalIncomingPoleAmplitude q branch side a*incomingNormFinitePart chi b w+
      (fundamentalSourceMoment w s a*clearedOnset s w)*
        (∫ t in Ioo T (0:ℝ), normalizable w chi (horizonCoordinate t)^(2 : ℕ))/
          physicalFundamentalDenominatorSlope q branch side=
      physicalIncomingPoleAmplitude q branch side a*D4BMFundamentalNorm.normFinitePart w := by
    change incomingNormFinitePart chi (horizonCoordinate T) w+_=D4BMFundamentalNorm.normFinitePart w at hNjoin
    rw [hTb] at hNjoin
    rw [← hNjoin,physicalIncomingPoleAmplitude_eq_cleared]
    ring
  change Tendsto _ _ (𝓝 (_+_)) at hlim
  rw [hvalue] at hlim
  refine ⟨T,R,hT,hR,by rw [hTb]; exact min_le_left _ _,?_,?_⟩
  · apply hlim.congr'
    filter_upwards [] with u
    dsimp only [normalizableOuterPairing,normalizableHorizonPairingFinitePart]
    rw [hTb]
    ring
  · intro u hu hcu
    have huI : u ∈ ball w RI := ball_subset_ball (min_le_left _ _) hu
    have huO : u ∈ ball w RO := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hu
    have huV : u ∈ ball w RV := ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hu
    obtain ⟨hui,hur⟩ := hV (mem_ball.mp huV)
    have hi := hcutI u huI hcu
    have ho := hcutO u huO hcu
    change Tendsto (incomingPairingCutoff s chi a 1 K b u) _ _ at hi
    change Tendsto (oppositePairingCutoff s chi a 1 K b u) _ _ at ho
    have hh := ((hi.const_mul (horizonRegularCoefficient u chi (normalizable u chi)
      (normalizableFirst u chi))).add ho).add_const (continuedReducedOuterPairing chi s a T u)
    rw [← hTb] at hh
    change Tendsto _ _ (𝓝 (normalizableOuterPairing chi s a T u)) at hh
    apply hh.congr'
    have he : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e < b :=
      (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < b from Iio_mem_nhds hb).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,he] with e he0 heb
    dsimp only [normalizableOuterPairingCutoff]
    rw [hTb,normalizableHorizonPairingCutoff_eq s chi a 1 K u hui hur he0 heb.le hb1]

/-- Both horizon branches are restored before the physical residue is extracted. -/
theorem physicalNormalizableOuterPairing_residue_and_restoration (q : XiZeroCopy)
    (branch side : Bool) (a : ℂ) :
    let w := physicalFundamentalFrequency q side
    let s := physicalRate q branch
    let chi := physicalRadialFrequency q
    ∃ T R : ℝ, T < 0 ∧ 0 < R ∧
      Tendsto (fun u => (u-w)*normalizableOuterPairing chi s a T u) (𝓝[≠] w)
        (𝓝 (physicalIncomingPoleAmplitude q branch side a*D4BMFundamentalNorm.normFinitePart w)) ∧
      ∀ u ∈ ball w R, connection u chi ≠ 0 →
        Tendsto (normalizableOuterPairingCutoff chi s a T u) (𝓝[>] (0:ℝ))
          (𝓝 (normalizableOuterPairing chi s a T u)) := by
  obtain ⟨T,R,hT,hR,_,hres,hcut⟩ :=
    physicalNormalizableOuterPairing_residue_and_restoration_below q branch side a 1 (by norm_num)
  exact ⟨T,R,hT,hR,hres,hcut⟩

end
end RHTower.D4BMJointSource
