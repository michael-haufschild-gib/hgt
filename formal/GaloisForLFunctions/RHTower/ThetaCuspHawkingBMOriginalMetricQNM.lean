import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalMetricRadial

/-! Analytic continuation and finite value of the complete original radial/corner action. -/
open Set Filter Topology Metric Complex MeasureTheory
namespace RHTower.D4BMOriginalMetricQNM
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMLaplaceRadial D4BMModularCore
open D4BMOriginalMetricRadial D4BMOriginalMetricHorizon D4BMOriginalCornerForcing
open D4BMOriginalHorizonGreenMatch
noncomputable section
set_option autoImplicit false

private abbrev chi (q : XiZeroCopy) := physicalRadialFrequency q
private abbrev rate (q : XiZeroCopy) (br : Bool) := physicalRate q br
private abbrev grad (q : XiZeroCopy) (br : Bool) := reducedGreenGradient (chi q) (rate q br) 1
private abbrev conn (q : XiZeroCopy) (w : ℂ) := connection w (chi q)
private abbrev mu (q : XiZeroCopy) := physicalAngularParameter q^2-1/4

/-- The source-defined numerator of the complete mixed Green pairing. -/
def greenNumerator (q : XiZeroCopy) (br : Bool) (amp : ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  incomingCoefficient q w*
    ((-oppositeEndpointPoleNumerator (rate q br) (chi q) amp 1 (grad q br) b w-
        conn q w*incomingSourcePrimitive (rate q br) (chi q) amp 1 (grad q br) w b)*
      incomingNormFinitePart (chi q) b w+
      conn q w*incomingSourcePairingFinitePart (rate q br) (chi q) amp 1 (grad q br) b w)+
    conn q w*oppositePairingExtension (rate q br) (chi q) amp 1 (grad q br) b w+
    clearedReducedOuterPairing (chi q) (rate q br) amp (tortoiseOf b) w/(-(w-2*rate q br))

private theorem greenNumerator_eq (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    {b : ℝ} (hb : b∈Ioo (0:ℝ) 1) (hs : w-2*rate q br≠0)
    (hc : conn q w≠0) (hh : horizon w (chi q) b≠0) :
    greenNumerator q br amp b w =
      conn q w*normalizableOuterPairing (chi q) (rate q br) amp (tortoiseOf b) w := by
  have hE := connection_mul_incomingEndpoint_eq (rate q br) (chi q) amp 1 (grad q br) w b hc hh
  have hO : clearedReducedOuterPairing (chi q) (rate q br) amp (tortoiseOf b) w/(-(w-2*rate q br))=
      conn q w*continuedReducedOuterPairing (chi q) (rate q br) amp (tortoiseOf b) w := by
    rw [clearedReducedOuterPairing_eq w (chi q) (rate q br) amp (tortoiseOf b) hs hc]
    unfold reducedGreenClearingFactor
    field_simp [hs]
  unfold greenNumerator normalizableOuterPairing normalizableHorizonPairingFinitePart
  rw [horizonCoordinate_tortoiseOf hb,
    oppositePairingFinitePart_eq_extension (rate q br) (chi q) amp 1 (grad q br) w b hc hh,hO,← hE]
  unfold incomingCoefficient incomingPairingFinitePart
  ring

private theorem greenNumerator_analytic_below (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    ∃ B : ℝ, 0<B ∧ B≤1/2 ∧ ∀ b : ℝ, 0<b → b≤B →
      AnalyticAt ℂ (greenNumerator q br amp b) (physicalFundamentalFrequency q side) := by
  let w := physicalFundamentalFrequency q side
  have hw := physicalFundamentalFrequency_strip q side
  have hs := physicalFundamentalFrequency_sub_sourceRate_ne_zero q br side
  obtain ⟨RI,BI,hRI,hBI,hBIh,hI⟩ := incomingPairingFinitePart_horizon_restoration_below
    (rate q br) (chi q) amp 1 (grad q br) w hw.1 (abs_lt.mp hw.2).1 hs
  obtain ⟨RO,BO,hRO,hBO,hBOh,hO⟩ := oppositePairingFinitePart_horizon_restoration_below
    (rate q br) (chi q) amp 1 (grad q br) w hw.1 (abs_lt.mp hw.2).1 hs
  refine ⟨min BI BO,lt_min hBI hBO,(min_le_left _ _).trans hBIh,?_⟩
  intro b hb hbB
  have hbI : b∈Ioo (0:ℝ) 1 := ⟨hb,lt_of_le_of_lt (hbB.trans ((min_le_left _ _).trans hBIh)) (by norm_num)⟩
  obtain ⟨hN,hJ,hP,_⟩ := hI b hb (hbB.trans (min_le_left _ _))
  obtain ⟨hL,hQ,_,_⟩ := hO b hb (hbB.trans (min_le_right _ _))
  have hf : w=-3/2-Complex.I*chi q ∨ w=-3/2+Complex.I*chi q := by
    dsimp only [w,chi]
    rw [physicalFundamentalFrequency_connection_root]
    cases side <;> simp
  have hh : horizon w (chi q) b≠0 := by
    rw [horizon_eq_normalizable_fundamental w (chi q) hw.1 hf hbI,
      normalizable_fundamental_value w (chi q) hf]
    exact mul_ne_zero (power_ne_zero _ hb) (power_ne_zero _ (sub_pos.mpr hbI.2))
  have hB := oppositeEndpointPoleNumerator_analyticAt (rate q br) (chi q) amp 1 (grad q br)
    w hw.1 (abs_lt.mp hw.2).1 hs hbI hh
  have hC := connection_frequency_analyticAt w (chi q) hw.1
  have hA := normalizable_horizonRegularCoefficient_analyticAt w (chi q) hw.1
  have hw0 : w≠0 := by intro h; apply hw.1; change w.im=0; rw [h]; rfl
  have hExt : AnalyticAt ℂ (oppositePairingExtension (rate q br) (chi q) amp 1 (grad q br) b) w :=
    (((hB.neg.sub (hC.mul hP)).mul hL).add (hC.mul hQ)).div
      (analyticAt_const.mul analyticAt_id) (mul_ne_zero (by norm_num) hw0)
  have hOut := physicalClearedReducedOuterPairing_analyticAt q br side amp (tortoiseOf_neg hbI)
  exact ((hA.mul (((hB.neg.sub (hC.mul hP)).mul hN).add (hC.mul hJ))).add (hC.mul hExt)).add
    (hOut.div (analyticAt_id.sub analyticAt_const).neg (neg_ne_zero.mpr hs))

/-- The actual connection-cleared causal horizon amplitude, including its fixed QNM value. -/
def clearedCornerAmplitude (q : XiZeroCopy) (br side : Bool) (amp : ℂ) : ℂ→ℂ :=
  Function.update (fun w => conn q w*continuedCornerAmplitude q br amp w)
    (physicalFundamentalFrequency q side)
    (connectionSimpleSlope (physicalFundamentalFrequency q side) (chi q) side*cornerResidue q br side amp)

private theorem clearedCornerAmplitude_analytic (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    AnalyticAt ℂ (clearedCornerAmplitude q br side amp) (physicalFundamentalFrequency q side) := by
  let w := physicalFundamentalFrequency q side
  have hw := physicalFundamentalFrequency_strip q side
  have hC := connection_frequency_analyticAt w (chi q) hw.1
  have hM := hC.meromorphicAt.mul (continuedCornerAmplitude_meromorphic q br amp w hw.1 (abs_lt.mp hw.2).1)
  apply (hM.update w _).analyticAt
  apply continuousAt_update_same.mpr
  have hc := (physicalFundamental_connection_hasDerivAt q side).tendsto_slope
  have hlim := hc.mul (continuedCornerAmplitude_residue q br side amp)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  simp only [slope_def_field,physicalFundamentalFrequency_connection_zero,sub_zero]
  change conn q u/(u-w)*((u-w)*continuedCornerAmplitude q br amp u)=
    conn q u*continuedCornerAmplitude q br amp u
  have hdelta : u-w≠0 := sub_ne_zero.mpr hu
  field_simp [hdelta]

/-- Clearing the actual temporal corner retains the derivative of its source amplitude. -/
def cornerNumerator (q : XiZeroCopy) (br side : Bool) (amp w : ℂ) : ℂ :=
  let H := clearedCornerAmplitude q br side amp
  mu q*((mu q-2)*(conn q w*H w/(2*w)+conn q w*deriv H w-H w*deriv (conn q) w)+
    conn q w^2*physicalSelfSourceCoefficient q/2*
      deriv (continuedForcingTransform (rate q br) amp 1 (grad q br)) w)

private theorem cornerNumerator_analytic (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    AnalyticAt ℂ (cornerNumerator q br side amp) (physicalFundamentalFrequency q side) := by
  let w := physicalFundamentalFrequency q side
  have hw := physicalFundamentalFrequency_strip q side
  have hC := connection_frequency_analyticAt w (chi q) hw.1
  have hH := clearedCornerAmplitude_analytic q br side amp
  have hF := physical_forcing_analyticAt q br side amp 1 (grad q br)
  have hw0 : w≠0 := by intro h; apply hw.1; change w.im=0; rw [h]; rfl
  exact analyticAt_const.mul ((analyticAt_const.mul
    ((((hC.mul hH).div (analyticAt_const.mul analyticAt_id) (mul_ne_zero (by norm_num) hw0)).add
      (hC.mul hH.deriv)).sub (hH.mul hC.deriv))).add
    ((((hC.pow 2).mul analyticAt_const).div analyticAt_const (by norm_num)).mul hF.deriv))

private theorem cornerNumerator_germ (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    cornerNumerator q br side amp =ᶠ[𝓝[≠] physicalFundamentalFrequency q side]
      (fun w => conn q w*physicalCornerCandidate q br amp w) := by
  let w₀ := physicalFundamentalFrequency q side
  let H := clearedCornerAmplitude q br side amp
  have hw := physicalFundamentalFrequency_strip q side
  have hC := connection_frequency_analyticAt w₀ (chi q) hw.1
  have hH := clearedCornerAmplitude_analytic q br side amp
  have hw₀ : w₀≠0 := by intro h; apply hw.1; change w₀.im=0; rw [h]; rfl
  have hwnz : ∀ᶠ w : ℂ in 𝓝[≠] w₀, w≠0 :=
    (continuousAt_id.eventually_ne hw₀).filter_mono nhdsWithin_le_nhds
  have hcne : ∀ᶠ w in 𝓝[≠] w₀, conn q w≠0 :=
    (physicalFundamental_connection_hasDerivAt q side).eventually_ne (c:=0)
      (physicalFundamental_connectionSlope_ne_zero q side)
  have he : continuedCornerAmplitude q br amp =ᶠ[𝓝[≠] w₀] (fun w => H w/conn q w) := by
    filter_upwards [self_mem_nhdsWithin,hcne] with w hw hcw
    dsimp only [H,clearedCornerAmplitude]
    rw [Function.update_of_ne hw]
    field_simp [hcw]
  have hd := he.nhdsNE_deriv
  filter_upwards [he,hd,hcne,hwnz,hC.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    hH.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with w hew hdw hcw hw0 hCw hHw
  have hder : deriv (fun u => H u/conn q u) w =
      (deriv H w*conn q w-H w*deriv (conn q) w)/(conn q w)^2 :=
    (hHw.differentiableAt.hasDerivAt.div hCw.differentiableAt.hasDerivAt hcw).deriv
  unfold cornerNumerator physicalCornerCandidate
  dsimp only
  rw [hew,hdw,hder]
  dsimp only [H,mu] at *
  field_simp [hcw,hw0]
  ring

/-- The complete connection-cleared metric numerator, with every finite regular term retained. -/
def actionNumerator (q : XiZeroCopy) (br side : Bool) (amp : ℂ)
    (c₀ c₁ d₀ : ℂ→ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  greenCoefficient q w*greenNumerator q br amp b w+
    conn q w*forcingCoefficient q br w*regularFinitePart q br amp c₀ c₁ d₀ b w+
    cornerNumerator q br side amp w

/-- The finite value is fixed by the source numerator and the original simple connection zero. -/
def finiteQNMValue (q : XiZeroCopy) (br side : Bool) (amp : ℂ)
    (c₀ c₁ d₀ : ℂ→ℂ) (b : ℝ) : ℂ :=
  deriv (actionNumerator q br side amp c₀ c₁ d₀ b) (physicalFundamentalFrequency q side)/
    connectionSimpleSlope (physicalFundamentalFrequency q side) (chi q) side

private theorem analytic_dslope {f : ℂ→ℂ} {w : ℂ} (h : AnalyticAt ℂ f w) :
    AnalyticAt ℂ (dslope f w) w := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩

/-- The canonical analytic representative of the actual corrected action at its QNM. -/
def regularAction (q : XiZeroCopy) (br side : Bool) (amp : ℂ)
    (c₀ c₁ d₀ : ℂ→ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  dslope (actionNumerator q br side amp c₀ c₁ d₀ b) (physicalFundamentalFrequency q side) w/
    dslope (conn q) (physicalFundamentalFrequency q side) w

/-- The complete original radial/corner action has a removable QNM singularity and a fixed
finite value, after the original radial cutoff is restored. Independent cusp removal is separate. -/
theorem original_corrected_action_QNM (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    ∃ R b : ℝ, ∃ c₀ c₁ d₀ : ℂ→ℂ, 0<R ∧ 0<b ∧ b≤1/2 ∧
      AnalyticAt ℂ (regularAction q br side amp c₀ c₁ d₀ b) (physicalFundamentalFrequency q side) ∧
      actionNumerator q br side amp c₀ c₁ d₀ b (physicalFundamentalFrequency q side)=0 ∧
      regularAction q br side amp c₀ c₁ d₀ b (physicalFundamentalFrequency q side)=
        finiteQNMValue q br side amp c₀ c₁ d₀ b ∧
      regularAction q br side amp c₀ c₁ d₀ b =ᶠ[𝓝[≠] physicalFundamentalFrequency q side]
        (fun w => radialFinitePart q br amp c₀ c₁ d₀ b w+physicalCornerCandidate q br amp w) ∧
      Tendsto (fun w => radialFinitePart q br amp c₀ c₁ d₀ b w+physicalCornerCandidate q br amp w)
        (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 (finiteQNMValue q br side amp c₀ c₁ d₀ b)) ∧
      ∀ w ∈ ball (physicalFundamentalFrequency q side) R, conn q w≠0 →
        Tendsto (fun e => radialCutoff q br amp c₀ c₁ d₀ b w e+physicalCornerCandidate q br amp w)
          (𝓝[>] (0:ℝ)) (𝓝 (radialFinitePart q br amp c₀ c₁ d₀ b w+physicalCornerCandidate q br amp w)) := by
  let w₀ := physicalFundamentalFrequency q side
  obtain ⟨B,hB,hBh,hG⟩ := greenNumerator_analytic_below q br side amp
  obtain ⟨R,b,c₀,c₁,d₀,hR,hb,hbh,hbB,hReg,_,hzero,hcut⟩ :=
    original_radial_restoration_and_corner_balance_below q br side amp B hB
  have hbI : b∈Ioo (0:ℝ) 1 := ⟨hb,lt_of_le_of_lt hbh (by norm_num)⟩
  let N := actionNumerator q br side amp c₀ c₁ d₀ b
  have hw := physicalFundamentalFrequency_strip q side
  have hs := physicalFundamentalFrequency_sub_sourceRate_ne_zero q br side
  have hC := connection_frequency_analyticAt w₀ (chi q) hw.1
  have hAG : AnalyticAt ℂ (greenCoefficient q) w₀ := by unfold greenCoefficient; fun_prop
  have hAF : AnalyticAt ℂ (forcingCoefficient q br) w₀ :=
    ((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul (continuedOnset_analyticAt _ _ hs)
  have hN : AnalyticAt ℂ N w₀ :=
    ((hAG.mul (hG b hb hbB)).add ((hC.mul hAF).mul hReg)).add (cornerNumerator_analytic q br side amp)
  have hf : w₀=-3/2-Complex.I*chi q ∨ w₀=-3/2+Complex.I*chi q := by
    dsimp only [w₀,chi]
    rw [physicalFundamentalFrequency_connection_root]
    cases side <;> simp
  have hh : horizon w₀ (chi q) b≠0 := by
    rw [horizon_eq_normalizable_fundamental w₀ (chi q) hw.1 hf hbI,
      normalizable_fundamental_value w₀ (chi q) hf]
    exact mul_ne_zero (power_ne_zero _ hb) (power_ne_zero _ (sub_pos.mpr hbI.2))
  have hcne : ∀ᶠ w in 𝓝[≠] w₀, conn q w≠0 :=
    (physicalFundamental_connection_hasDerivAt q side).eventually_ne (c:=0)
      (physicalFundamental_connectionSlope_ne_zero q side)
  have hsne : ∀ᶠ w : ℂ in 𝓝[≠] w₀, w-2*rate q br≠0 :=
    ((continuousAt_id.sub continuousAt_const).eventually_ne hs).filter_mono nhdsWithin_le_nhds
  have hhne : ∀ᶠ w in 𝓝[≠] w₀, horizon w (chi q) b≠0 :=
    ((horizon_frequency_analyticAt w₀ (chi q) hw.1 hbI).continuousAt.eventually_ne hh).filter_mono nhdsWithin_le_nhds
  have hEq : N =ᶠ[𝓝[≠] w₀] (fun w => conn q w*
      (radialFinitePart q br amp c₀ c₁ d₀ b w+physicalCornerCandidate q br amp w)) := by
    filter_upwards [hcne,hsne,hhne,cornerNumerator_germ q br side amp] with w hcw hsw hhw hK
    dsimp only [N,actionNumerator,radialFinitePart]
    rw [greenNumerator_eq q br amp w hbI hsw hcw hhw,hK]
    ring
  have hSlope : Tendsto (fun w => conn q w/(w-w₀)) (𝓝[≠] w₀)
      (𝓝 (connectionSimpleSlope w₀ (chi q) side)) := by
    apply (physicalFundamental_connection_hasDerivAt q side).tendsto_slope.congr'
    filter_upwards [] with w
    simp only [slope_def_field,physicalFundamentalFrequency_connection_zero,sub_zero]
    rfl
  have hlim0 := hSlope.mul hzero
  simp only [mul_zero] at hlim0
  have hlimN : Tendsto N (𝓝[≠] w₀) (𝓝 0) := by
    apply hlim0.congr'
    filter_upwards [self_mem_nhdsWithin,hEq] with w hw hNw
    rw [hNw]
    field_simp [sub_ne_zero.mpr hw]
    rfl
  have hN0 : N w₀=0 := tendsto_nhds_unique
    (hN.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlimN
  have hc0 : conn q w₀=0 := physicalFundamentalFrequency_connection_zero q side
  have hdc : deriv (conn q) w₀=connectionSimpleSlope w₀ (chi q) side :=
    (physicalFundamental_connection_hasDerivAt q side).deriv
  have hF : AnalyticAt ℂ (regularAction q br side amp c₀ c₁ d₀ b) w₀ := by
    apply (analytic_dslope hN).div (analytic_dslope hC)
    rw [dslope_same,hdc]
    exact physicalFundamental_connectionSlope_ne_zero q side
  have hvalue : regularAction q br side amp c₀ c₁ d₀ b w₀=finiteQNMValue q br side amp c₀ c₁ d₀ b := by
    unfold regularAction finiteQNMValue
    rw [dslope_same,dslope_same,hdc]
  have hFeq : regularAction q br side amp c₀ c₁ d₀ b =ᶠ[𝓝[≠] w₀]
      (fun w => radialFinitePart q br amp c₀ c₁ d₀ b w+physicalCornerCandidate q br amp w) := by
    filter_upwards [self_mem_nhdsWithin,hEq,hcne] with w hw hNw hcw
    change dslope N w₀ w/dslope (conn q) w₀ w=_
    rw [dslope_of_ne N hw,dslope_of_ne (conn q) hw,slope_def_field,slope_def_field,hN0,hc0,sub_zero,sub_zero,hNw]
    field_simp [sub_ne_zero.mpr hw,hcw]
  have hlimit := (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hFeq
  rw [hvalue] at hlimit
  refine ⟨R,b,c₀,c₁,d₀,hR,hb,hbh,hF,hN0,hvalue,hFeq,hlimit,?_⟩
  intro w hw hc
  exact (hcut w hw hc).add_const (physicalCornerCandidate q br amp w)

end
end RHTower.D4BMOriginalMetricQNM
