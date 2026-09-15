import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCanonicalMetricCutoff

open Set Filter Topology Metric MeasureTheory Complex
namespace RHTower.D4BMOriginalCanonicalMetricGerm
open D4BMJointSource D4BMModularCore D4BMLaplaceRadial D4BMOriginalHorizonGreenMatch
open D4BMOriginalMetricHorizon D4BMOriginalMetricRadial D4BMOriginalMetricOuter
open D4BMOriginalCanonicalHorizon D4BMOriginalCanonicalRestoration D4BMOriginalCanonicalMetricCutoff
noncomputable section
set_option autoImplicit false

private theorem source_pole_ne (q : XiZeroCopy) (br : Bool) (w : ℂ) (hwr : -2<w.re) :
    w-2*physicalRate q br≠0 := by
  intro he
  have hre := congrArg Complex.re (sub_eq_zero.mp he)
  have hr := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hr
  linarith

/-- The original outer integral is the meromorphic quotient of its actual
cleared integral; equality is established on its punctured frequency germ. -/
theorem original_outer_pairing_meromorphic (s chi amp w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*s≠0) {T : ℝ} (hT : T<0) :
    MeromorphicAt (continuedReducedOuterPairing chi s amp T) w := by
  have hN := (clearedReducedOuterPairing_analyticAt w chi s amp hw hwr hT).meromorphicAt
  have hD : AnalyticAt ℂ (fun u => reducedGreenClearingFactor u chi s) w :=
    (analyticAt_id.sub analyticAt_const).neg.mul (connection_frequency_analyticAt w chi hw)
  have h := hN.div hD.meromorphicAt
  apply h.congr
  have hsource : ∀ᶠ u : ℂ in 𝓝[≠] w,u-2*s≠0 :=
    ((continuousAt_id.sub continuousAt_const).eventually_ne hs).filter_mono nhdsWithin_le_nhds
  filter_upwards [connection_eventually_ne_zero w chi hw,hsource] with u hc hsu
  simp only [Pi.div_apply]
  rw [clearedReducedOuterPairing_eq u chi s amp T hsu hc]
  have hd : reducedGreenClearingFactor u chi s≠0 := by
    unfold reducedGreenClearingFactor
    exact mul_ne_zero (neg_ne_zero.mpr hsu) hc
  exact mul_div_cancel_left₀ _ hd

/-- Both original Green branches and the original outer pairing have one
common-interface meromorphic finite part, at every nonreal frequency above
real part minus two. All cutoff admission comes from the actual profiles. -/
theorem original_normalizable_local_data (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) :
    ∃ R B : ℝ,0<R ∧ 0<B ∧ B≤1/2 ∧ ∀ b : ℝ,0<b → b≤B →
      MeromorphicAt (normalizableOuterPairing (physicalRadialFrequency q) (physicalRate q br) amp (tortoiseOf b)) w ∧
      ∀ u∈ball w R,connection u (physicalRadialFrequency q)≠0 →
        Tendsto (normalizableOuterPairingCutoff (physicalRadialFrequency q) (physicalRate q br) amp (tortoiseOf b) u)
          (𝓝[>] (0:ℝ)) (𝓝 (normalizableOuterPairing (physicalRadialFrequency q) (physicalRate q br) amp (tortoiseOf b) u)) := by
  let s := physicalRate q br
  let chi := physicalRadialFrequency q
  let K := reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1
  have hs : w-2*s≠0 := source_pole_ne q br w hwr
  obtain ⟨RI,BI,hRI,hBI,hBIh,hI⟩ := incomingPairingFinitePart_horizon_restoration_below s chi amp 1 K w hw hwr hs
  obtain ⟨RO,BO,hRO,hBO,hBOh,hO⟩ := oppositePairingFinitePart_horizon_restoration_below s chi amp 1 K w hw hwr hs
  have hv : ∀ᶠ u : ℂ in 𝓝 w,u.im≠0 ∧ -2<u.re :=
    (Complex.continuous_im.continuousAt.eventually_ne hw).and
      (continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hwr)
  obtain ⟨RV,hRV,hV⟩ := Metric.eventually_nhds_iff.mp hv
  let R := min RI (min RO RV)
  let B := min BI BO
  have hR : 0<R := lt_min hRI (lt_min hRO hRV)
  have hB : 0<B := lt_min hBI hBO
  have hBh : B≤1/2 := (min_le_left BI BO).trans hBIh
  refine ⟨R,B,hR,hB,hBh,?_⟩
  intro b hb hbB
  have hbI : b≤BI := hbB.trans (min_le_left _ _)
  have hbO : b≤BO := hbB.trans (min_le_right _ _)
  have hb1 : b<1 := by linarith
  have hbU : b∈Ioo (0:ℝ) 1 := ⟨hb,hb1⟩
  have hT := tortoiseOf_neg hbU
  obtain ⟨hN,hJ,hP,hcutI⟩ := hI b hb hbI
  obtain ⟨hL,hQ,_,hcutO⟩ := hO b hb hbO
  have hE : MeromorphicAt (fun u => incomingResponseEndpoint s chi amp 1 K u b) w := by
    have h := ((continuedResponse_meromorphicAt s chi amp 1 K w hw hwr hb hb1).div
      (horizon_frequency_analyticAt w chi hw hbU).meromorphicAt).sub hP.meromorphicAt
    simpa only [incomingResponseEndpoint,incomingSourcePrimitive,Pi.sub_def,Pi.div_def] using h
  have hmI : MeromorphicAt (incomingPairingFinitePart s chi amp 1 K b) w := by
    unfold incomingPairingFinitePart
    exact (hE.mul hN.meromorphicAt).add hJ.meromorphicAt
  have hmO : MeromorphicAt (oppositePairingFinitePart s chi amp 1 K b) w := by
    have hC := (connection_frequency_analyticAt w chi hw).meromorphicAt.div
      (show AnalyticAt ℂ (fun u : ℂ => 2*u) w from analyticAt_const.mul analyticAt_id).meromorphicAt
    unfold oppositePairingFinitePart
    exact hC.mul ((hE.mul hL.meromorphicAt).add hQ.meromorphicAt)
  have hmH : MeromorphicAt (normalizableHorizonPairingFinitePart s chi amp 1 K b) w := by
    unfold normalizableHorizonPairingFinitePart
    exact ((normalizable_horizonRegularCoefficient_analyticAt w chi hw).meromorphicAt.mul hmI).add hmO
  constructor
  · have h := hmH.add (original_outer_pairing_meromorphic s chi amp w hw hwr hs hT)
    unfold normalizableOuterPairing
    rw [horizonCoordinate_tortoiseOf hbU]
    exact h
  intro u hu hc
  have huI : u∈ball w RI := ball_subset_ball (min_le_left _ _) hu
  have huO : u∈ball w RO := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hu
  have huV : u∈ball w RV := ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hu
  obtain ⟨hui,hur⟩ := hV (mem_ball.mp huV)
  have hi := hcutI u huI hc
  have ho := hcutO u huO hc
  change Tendsto (incomingPairingCutoff s chi amp 1 K b u) _ _ at hi
  change Tendsto (oppositePairingCutoff s chi amp 1 K b u) _ _ at ho
  have hh := ((hi.const_mul (horizonRegularCoefficient u chi (normalizable u chi)
    (normalizableFirst u chi))).add ho).add_const (continuedReducedOuterPairing chi s amp (tortoiseOf b) u)
  rw [normalizableOuterPairing,horizonCoordinate_tortoiseOf hbU]
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsGT hb] with e he
  rw [normalizableOuterPairingCutoff,horizonCoordinate_tortoiseOf hbU]
  change _ = normalizableHorizonPairingCutoff s chi amp 1 K b u e + _
  rw [normalizableHorizonPairingCutoff_eq s chi amp 1 K u hui hur he.1 he.2.le hb1]

/-- The actual full canonical metric cutoff has local meromorphic radial
finite parts, sharing one neighborhood and arbitrarily small interfaces. -/
theorem original_canonical_metric_local_data (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) :
    ∃ R B : ℝ,0<R ∧ 0<B ∧ B≤1/2 ∧ ∀ b : ℝ,0<b → b≤B →
      MeromorphicAt (radialFinitePart q br amp
        (incomingValue q br amp (gradient q br)) (incomingSlope q br amp (gradient q br))
        (oppositeValue q br amp (gradient q br)) b) w ∧
      ∀ u∈ball w R,connection u (physicalRadialFrequency q)≠0 →
        Tendsto (canonicalMetricCutoff q br amp u) (𝓝[>] (0:ℝ))
          (𝓝 (radialFinitePart q br amp
            (incomingValue q br amp (gradient q br)) (incomingSlope q br amp (gradient q br))
            (oppositeValue q br amp (gradient q br)) b u)) := by
  let K := reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1
  obtain ⟨RG,BG,hRG,hBG,hBGh,hG⟩ := original_normalizable_local_data q br amp w hw hwr
  obtain ⟨RF,BF,hRF,hBF,hBFh,hF⟩ := canonical_radial_restoration q br amp K w hw hwr
  obtain ⟨RC,BC,hRC,hBC,hBCh,hC⟩ := original_metric_cutoff_canonical q br amp w hw hwr
  have hv : ∀ᶠ u : ℂ in 𝓝 w,u.im≠0 ∧ -2<u.re :=
    (Complex.continuous_im.continuousAt.eventually_ne hw).and
      (continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hwr)
  obtain ⟨RV,hRV,hV⟩ := Metric.eventually_nhds_iff.mp hv
  let R := min RG (min RF (min RC RV))
  let B := min BG (min BF BC)
  have hR : 0<R := lt_min hRG (lt_min hRF (lt_min hRC hRV))
  have hB : 0<B := lt_min hBG (lt_min hBF hBC)
  have hBh : B≤1/2 := (min_le_left _ _).trans hBGh
  refine ⟨R,B,hR,hB,hBh,?_⟩
  intro b hb hbB
  have hbG : b≤BG := hbB.trans (min_le_left _ _)
  have hbF : b≤BF := hbB.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbC : b≤BC := hbB.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hb1 : b<1 := by linarith
  obtain ⟨hmG,hcutG⟩ := hG b hb hbG
  obtain ⟨haF,hcutF⟩ := hF b hb hbF
  have haR : AnalyticAt ℂ (regularFinitePart q br amp
      (incomingValue q br amp K) (incomingSlope q br amp K) (oppositeValue q br amp K) b) w :=
    haF.add (regularOuterMoment_analyticAt q br amp w (tortoiseOf_neg ⟨hb,hb1⟩))
  have hgc : AnalyticAt ℂ (greenCoefficient q) w := by unfold greenCoefficient;fun_prop
  have hfc : AnalyticAt ℂ (forcingCoefficient q br) w :=
    ((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul
      (continuedOnset_analyticAt _ _ (source_pole_ne q br w hwr))
  constructor
  · unfold radialFinitePart
    exact (hgc.meromorphicAt.mul hmG).add (hfc.meromorphicAt.mul haR.meromorphicAt)
  intro u hu hc
  have huG : u∈ball w RG := ball_subset_ball (min_le_left _ _) hu
  have huF : u∈ball w RF := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hu
  have huC : u∈ball w RC := ball_subset_ball ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) hu
  have huV : u∈ball w RV := ball_subset_ball ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) hu
  obtain ⟨hui,hur⟩ := hV (mem_ball.mp huV)
  have ht := ((hcutG u huG hc).const_mul (greenCoefficient q u)).add
    (((hcutF u huF).add_const (regularOuterMoment q br amp (tortoiseOf b) u)).const_mul (forcingCoefficient q br u))
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsGT hb] with e he
  rw [hC b hb hbC u huC hc e]
  change _ = radialCutoff q br amp (incomingValue q br amp K) (incomingSlope q br amp K)
    (oppositeValue q br amp K) b u e
  rw [radialCutoff_decomposition q br amp u (incomingValue q br amp K) (incomingSlope q br amp K)
    (oppositeValue q br amp K) hui hur (source_pole_ne q br u hur) hc he.1 he.2.le hb1]
  unfold forcingCounterterm
  change _ = greenCoefficient q u * _ + forcingCoefficient q br u *
    ((∫ x in tortoiseOf e..tortoiseOf b,forcingKernel q br amp K u x) -
      (incomingValue q br amp K u*(e:ℂ)^u/u + incomingSlope q br amp K u*(e:ℂ)^(u+1)/(u+1) +
        oppositeValue q br amp K u*(Real.log e:ℂ)) + _)
  ring

/-- One radial value defined by the literal cutoff, without a frequency-dependent interface. -/
def canonicalRadialValue (q : XiZeroCopy) (br : Bool) (amp w : ℂ) : ℂ :=
  limUnder (𝓝[>] (0:ℝ)) (canonicalMetricCutoff q br amp w)

/-- The canonical radial value agrees with every sufficiently small local formula. -/
theorem canonical_radial_value_local (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) :
    ∃ R B : ℝ,0<R ∧ 0<B ∧ B≤1/2 ∧ ∀ b : ℝ,0<b → b≤B →
      MeromorphicAt (radialFinitePart q br amp
        (incomingValue q br amp (gradient q br)) (incomingSlope q br amp (gradient q br))
        (oppositeValue q br amp (gradient q br)) b) w ∧
      ∀ u∈ball w R,connection u (physicalRadialFrequency q)≠0 →
        canonicalRadialValue q br amp u = radialFinitePart q br amp
          (incomingValue q br amp (gradient q br)) (incomingSlope q br amp (gradient q br))
          (oppositeValue q br amp (gradient q br)) b u := by
  obtain ⟨R,B,hR,hB,hBh,h⟩ := original_canonical_metric_local_data q br amp w hw hwr
  refine ⟨R,B,hR,hB,hBh,?_⟩
  intro b hb hbB
  obtain ⟨hm,hlim⟩ := h b hb hbB
  exact ⟨hm,fun u hu hc => (hlim u hu hc).limUnder_eq⟩

/-- The original canonical cutoff converges at every nonresonant frequency in its domain. -/
theorem canonical_metric_cutoff_tendsto (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hc : connection w (physicalRadialFrequency q)≠0) :
    Tendsto (canonicalMetricCutoff q br amp w) (𝓝[>] (0:ℝ)) (𝓝 (canonicalRadialValue q br amp w)) := by
  obtain ⟨R,B,hR,hB,_,h⟩ := original_canonical_metric_local_data q br amp w hw hwr
  have ht := (h B hB le_rfl).2 w (mem_ball_self hR) hc
  simpa only [canonicalRadialValue,ht.limUnder_eq] using ht

/-- All local finite parts glue to the same original cutoff limit, including
meromorphic germs at connection zeros. -/
theorem canonical_radial_value_meromorphic (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) :
    MeromorphicAt (canonicalRadialValue q br amp) w := by
  obtain ⟨R,B,hR,hB,_,h⟩ := canonical_radial_value_local q br amp w hw hwr
  obtain ⟨hm,heq⟩ := h B hB le_rfl
  apply hm.congr
  filter_upwards [(Filter.Eventually.filter_mono nhdsWithin_le_nhds (ball_mem_nhds w hR)),
    connection_eventually_ne_zero w (physicalRadialFrequency q) hw] with u hu hc
  exact (heq u hu hc).symm


end
end RHTower.D4BMOriginalCanonicalMetricGerm


open Set Filter Topology Metric MeasureTheory Complex
namespace RHTower.D4BMOriginalCanonicalAction
open D4BMJointSource D4BMModularCore D4BMLaplaceRadial D4BMOriginalHorizonGreenMatch
open D4BMOriginalMetricHorizon D4BMOriginalMetricRadial D4BMOriginalCornerForcing
open D4BMOriginalCanonicalHorizon D4BMOriginalCanonicalRestoration D4BMOriginalCanonicalMetricCutoff
open D4BMOriginalCanonicalMetricGerm
noncomputable section
set_option autoImplicit false

/-- The fixed original radial value together with the retained temporal corner. -/
def canonicalAction (q : XiZeroCopy) (br : Bool) (amp w : ℂ) : ℂ :=
  canonicalRadialValue q br amp w+physicalCornerCandidate q br amp w

/-- The entire canonical radial/corner action is meromorphic on its physical frequency domain. -/
theorem canonical_action_meromorphic (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) : MeromorphicAt (canonicalAction q br amp) w := by
  have hs : w-2*physicalRate q br≠0 := by
    intro he
    have hre := congrArg Complex.re (sub_eq_zero.mp he)
    have hr := currentRate_re_lt q br
    change (2*physicalRate q br).re < -2 at hr
    linarith
  have hA := continuedCornerAmplitude_meromorphic q br amp w hw hwr
  have hC := (connection_frequency_analyticAt w (physicalRadialFrequency q) hw).meromorphicAt
  have hW : MeromorphicAt (fun u : ℂ => u) w := analyticAt_id.meromorphicAt
  have hF := (continued_forcing_analyticAt (physicalRate q br) amp 1
    (gradient q br) w hs).deriv.meromorphicAt
  have hcorner : MeromorphicAt (physicalCornerCandidate q br amp) w := by
    unfold physicalCornerCandidate
    exact ((analyticAt_const.meromorphicAt).mul (hC.div ((analyticAt_const.meromorphicAt).mul hW))).mul
      ((((analyticAt_const.meromorphicAt).mul hA).add
        ((((analyticAt_const.meromorphicAt).mul hW).mul (analyticAt_const.meromorphicAt)).mul hA.deriv)).add
        ((hW.mul (analyticAt_const.meromorphicAt)).mul hF))
  unfold canonicalAction
  exact (canonical_radial_value_meromorphic q br amp w hw hwr).add hcorner

/-- Changing from a locally restored forcing formula to the canonical source
coefficients adds an analytic remainder. The original temporal corner still
cancels the entire canonical action residue. -/
theorem canonical_action_QNM_residue_zero (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    Tendsto (fun w => (w-physicalFundamentalFrequency q side)*canonicalAction q br amp w)
      (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 0) := by
  let w₀ := physicalFundamentalFrequency q side
  have hw := physicalFundamentalFrequency_strip q side
  have hwr := (abs_lt.mp hw.2).1
  obtain ⟨R,B,hR,hB,_,hlocal⟩ := canonical_radial_value_local q br amp w₀ hw.1 hwr
  obtain ⟨BF,hBF,_,hF⟩ := canonical_regular_part_analytic q br amp w₀ hw.1 hwr
  obtain ⟨Rold,b,c₀,c₁,d₀,hRold,hb,hbh,hbcap,hOld,_,hzero,_⟩ :=
    original_radial_restoration_and_corner_balance_below q br side amp (min B BF) (lt_min hB hBF)
  have hbB : b≤B := hbcap.trans (min_le_left _ _)
  have hbF : b≤BF := hbcap.trans (min_le_right _ _)
  let K := gradient q br
  let D : ℂ→ℂ := fun u => forcingCoefficient q br u*
    (regularFinitePart q br amp (incomingValue q br amp K) (incomingSlope q br amp K)
      (oppositeValue q br amp K) b u-regularFinitePart q br amp c₀ c₁ d₀ b u)
  have hD : AnalyticAt ℂ D w₀ := by
    have hfc : AnalyticAt ℂ (forcingCoefficient q br) w₀ :=
      ((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul
        (continuedOnset_analyticAt _ _ (physicalFundamentalFrequency_sub_sourceRate_ne_zero q br side))
    exact hfc.mul ((hF b hb hbF).sub hOld)
  have hdelta : Tendsto (fun u : ℂ => u-w₀) (𝓝[≠] w₀) (𝓝 0) := by
    simpa only [sub_self,id_eq] using
      ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun u : ℂ => u) (𝓝[≠] w₀) (𝓝 w₀)).sub_const w₀)
  have ht := hzero.add (hdelta.mul (hD.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  simp only [zero_mul,zero_add] at ht
  apply ht.congr'
  filter_upwards [(Filter.Eventually.filter_mono nhdsWithin_le_nhds (ball_mem_nhds w₀ hR)),
    connection_eventually_ne_zero w₀ (physicalRadialFrequency q) hw.1] with u hu hc
  unfold canonicalAction
  rw [(hlocal b hb hbB).2 u hu hc]
  dsimp only [D,radialFinitePart,K]
  ring

private theorem removable_of_scaled_limit_zero {f : ℂ→ℂ} {p : ℂ}
    (hf : MeromorphicAt f p)
    (hz : Tendsto (fun u => (u-p)*f u) (𝓝[≠] p) (𝓝 0)) :
    ∃ g : ℂ→ℂ,AnalyticAt ℂ g p ∧ f =ᶠ[𝓝[≠] p] g := by
  have hlin : MeromorphicAt (fun u : ℂ => u-p) p :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hpos := (tendsto_zero_iff_meromorphicOrderAt_pos (hlin.mul hf)).mp hz
  change 0 < meromorphicOrderAt ((fun u : ℂ => u-p)*f) p at hpos
  rw [meromorphicOrderAt_mul hlin hf,meromorphicOrderAt_id_sub_const] at hpos
  have hnonneg : 0 ≤ meromorphicOrderAt f p := by
    by_cases htop : meromorphicOrderAt f p=⊤
    · simp [htop]
    · lift meromorphicOrderAt f p to ℤ using htop with n hn
      have hi : (0:ℤ)<1+n := by exact_mod_cast hpos
      exact_mod_cast (show (0:ℤ)≤n by omega)
  exact hf.meromorphicOrderAt_nonneg_iff.mp hnonneg

/-- The canonical action has a unique, source-defined finite value at either QNM. -/
def canonicalQNMValue (q : XiZeroCopy) (br side : Bool) (amp : ℂ) : ℂ :=
  limUnder (𝓝[≠] physicalFundamentalFrequency q side) (canonicalAction q br amp)

def canonicalQNMAction (q : XiZeroCopy) (br side : Bool) (amp : ℂ) : ℂ→ℂ :=
  Function.update (canonicalAction q br amp) (physicalFundamentalFrequency q side)
    (canonicalQNMValue q br side amp)

/-- QNM removal for one canonical action: all original radial terms and the
actual temporal corner are retained, without arbitrary local subtraction coefficients. -/
theorem canonical_action_QNM (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    AnalyticAt ℂ (canonicalQNMAction q br side amp) (physicalFundamentalFrequency q side) ∧
    Tendsto (canonicalAction q br amp) (𝓝[≠] physicalFundamentalFrequency q side)
      (𝓝 (canonicalQNMValue q br side amp)) ∧
    ∀ w : ℂ,w.im≠0 → -2<w.re → connection w (physicalRadialFrequency q)≠0 →
      Tendsto (fun e => canonicalMetricCutoff q br amp w e+physicalCornerCandidate q br amp w)
        (𝓝[>] (0:ℝ)) (𝓝 (canonicalAction q br amp w)) := by
  let w₀ := physicalFundamentalFrequency q side
  have hw := physicalFundamentalFrequency_strip q side
  have hm := canonical_action_meromorphic q br amp w₀ hw.1 (abs_lt.mp hw.2).1
  obtain ⟨g,hg,heq⟩ := removable_of_scaled_limit_zero hm (canonical_action_QNM_residue_zero q br side amp)
  have ht := (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm
  have hv : canonicalQNMValue q br side amp=g w₀ := ht.limUnder_eq
  have hlim : Tendsto (canonicalAction q br amp) (𝓝[≠] w₀) (𝓝 (canonicalQNMValue q br side amp)) := by
    rw [hv]
    exact ht
  refine ⟨?_,hlim,?_⟩
  · exact (hm.update w₀ _).analyticAt (continuousAt_update_same.mpr hlim)
  intro w hwi hwr hc
  exact (canonical_metric_cutoff_tendsto q br amp w hwi hwr hc).add_const (physicalCornerCandidate q br amp w)

end
end RHTower.D4BMOriginalCanonicalAction
