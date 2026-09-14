import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalMetricHorizon
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalNormalizablePairing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCornerSpectralBalance

/-! The complete original radial metric finite part and its temporal corner. -/
open Set Filter Topology Metric MeasureTheory Complex
namespace RHTower.D4BMOriginalMetricRadial
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMLaplaceRadial D4BMModularCore
open D4BMOriginalMetricOuter D4BMOriginalMetricHorizon D4BMOriginalCornerForcing
noncomputable section
set_option autoImplicit false

private abbrev mu (q : XiZeroCopy) := D4BMLeftModeRadialEquation.eigenvalue q
private abbrev gradient (q : XiZeroCopy) (br : Bool) :=
  reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1

def greenCoefficient (q : XiZeroCopy) (w : ℂ) : ℂ :=
  2*mu q*w*(mu q-2)*physicalSelfSourceCoefficient q

def forcingCoefficient (q : XiZeroCopy) (br : Bool) (w : ℂ) : ℂ :=
  mu q*w*physicalSelfSourceCoefficient q*continuedOnset (physicalRate q br) w

/-- The original horizon response paired with its actual normalizable reader. -/
def nativeGreenKernel (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (x : ℝ) : ℂ :=
  continuedResponse (physicalRate q br) (physicalRadialFrequency q) amp 1 (gradient q br)
    (horizonCoordinate x) w*normalizable w (physicalRadialFrequency q) (horizonCoordinate x)

/-- The three counterterms already determined by the native Green horizon expansion. -/
def greenCounterterm (q : XiZeroCopy) (br : Bool) (amp : ℂ) (b : ℝ) (w : ℂ) (e : ℝ) : ℂ :=
  let s := physicalRate q br
  let chi := physicalRadialFrequency q
  let E := incomingResponseEndpoint s chi amp 1 (gradient q br) w b
  incomingCoefficient q w*((E/2)*(e:ℂ)^w/w+
    ((horizonGaussFirstCoefficient w chi+1/4)*E+incomingResponseSlope s amp 1 (gradient q br) w/2)*
      (e:ℂ)^(w+1)/(w+1))+
    oppositeCoefficient q w*(E/2)*(Real.log e:ℂ)

def forcingCounterterm (c₀ c₁ d₀ : ℂ→ℂ) (w : ℂ) (e : ℝ) : ℂ :=
  c₀ w*(e:ℂ)^w/w+c₁ w*(e:ℂ)^(w+1)/(w+1)+d₀ w*(Real.log e:ℂ)

/-- The literal original metric integral, with its source-determined counterterms. -/
def radialCutoff (q : XiZeroCopy) (br : Bool) (amp : ℂ) (c₀ c₁ d₀ : ℂ→ℂ)
    (b : ℝ) (w : ℂ) (e : ℝ) : ℂ :=
  (∫ x in tortoiseOf e..0,outerDensity q br amp w x)+
    greenCoefficient q w*greenCounterterm q br amp b w e-
    forcingCoefficient q br w*forcingCounterterm c₀ c₁ d₀ w e

/-- Native forcing on the horizon and combined lift/contact forcing outside. -/
def regularFinitePart (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (c₀ c₁ d₀ : ℂ→ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  horizonFinitePart q br amp (gradient q br) c₀ c₁ d₀ b w+
    regularOuterMoment q br amp (tortoiseOf b) w

/-- The complete original radial metric finite part in its fixed physical normalization. -/
def radialFinitePart (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (c₀ c₁ d₀ : ℂ→ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  greenCoefficient q w*normalizableOuterPairing (physicalRadialFrequency q) (physicalRate q br) amp (tortoiseOf b) w+
    forcingCoefficient q br w*regularFinitePart q br amp c₀ c₁ d₀ b w

private theorem nativeGreen_continuous (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) : ContinuousOn (nativeGreenKernel q br amp w) (Iio (0:ℝ)) := by
  intro x hx
  have hz := horizonCoordinate_interior x hx
  have hg := ((continuedResponse_hasDerivAt (physicalRate q br) (physicalRadialFrequency q) amp 1
    (gradient q br) w hw hwr hz).1.continuousAt).comp (horizonCoordinate_hasDerivAt x).continuousAt
  have hn := ((normalizable_derivatives_continued (w:=w) (chi:=physicalRadialFrequency q) hz).1.continuousAt).comp
    (horizonCoordinate_hasDerivAt x).continuousAt
  exact (hg.mul hn).continuousWithinAt

private theorem forcing_continuous (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) :
    ContinuousOn (forcingKernel q br amp K w) (Iio (0:ℝ)) := by
  have hP : Continuous (fun x : ℝ => power (2*physicalRate q br) (1+radialUnit x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((power_derivatives (2*physicalRate q br) (radialUnit_add_one_pos x)).1.scomp x
      ((radialUnit_hasDerivAt x).const_add 1)).continuousAt
  have hU : Continuous radialUnit :=
    continuous_iff_continuousAt.mpr (fun x => (radialUnit_hasDerivAt x).continuousAt)
  intro x hx
  have hn := ((normalizable_derivatives_continued (w:=w) (chi:=physicalRadialFrequency q)
    (horizonCoordinate_interior x hx)).1.continuousAt).comp (horizonCoordinate_hasDerivAt x).continuousAt
  unfold forcingKernel forcingProfile
  exact (show ContinuousAt (fun x : ℝ => Complex.exp (w*(x:ℂ))*(-2*(radialUnit x:ℂ)*
    power (2*physicalRate q br) (1+radialUnit x)*amp^2*
      (((5*physicalRate q br^2+15*physicalRate q br+4)/4)*1+
        physicalRate q br*(physicalRate q br-1)*(radialUnit x:ℂ)^2/4*
          ((physicalRate q br+2)^2*1-K)))) x by fun_prop).mul hn |>.continuousWithinAt

private theorem chart_order {e b : ℝ} (he : 0<e) (heb : e≤b) (hb : b<1) :
    tortoiseOf e≤tortoiseOf b := by
  have heI : e ∈ Ioo (0:ℝ) 1 := ⟨he,heb.trans_lt hb⟩
  have hbI : b ∈ Ioo (0:ℝ) 1 := ⟨he.trans_le heb,hb⟩
  by_contra h
  have hm := horizonCoordinate_strictMonoOn (tortoiseOf_neg hbI) (tortoiseOf_neg heI) (lt_of_not_ge h)
  rw [horizonCoordinate_tortoiseOf hbI,horizonCoordinate_tortoiseOf heI] at hm
  exact (not_lt_of_ge heb) hm

private theorem nativeGreen_integral (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    {e b : ℝ} (he : 0<e) (heb : e≤b) (hb : b<1) :
    (∫ x in tortoiseOf e..tortoiseOf b,nativeGreenKernel q br amp w x)=
      ∫ z in e..b,continuedResponse (physicalRate q br) (physicalRadialFrequency q) amp 1
        (gradient q br) z w*normalizable w (physicalRadialFrequency q) z/(2*(z:ℂ)*(Real.sqrt (1-z):ℂ)) := by
  have heI : e ∈ Ioo (0:ℝ) 1 := ⟨he,heb.trans_lt hb⟩
  have hbI : b ∈ Ioo (0:ℝ) 1 := ⟨he.trans_le heb,hb⟩
  have horder := chart_order he heb hb
  have htb := tortoiseOf_neg hbI
  have hcv := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (f:=horizonCoordinate) (f':=coordinateFirst)
    (g:=fun z : ℝ => continuedResponse (physicalRate q br) (physicalRadialFrequency q) amp 1
      (gradient q br) z w*normalizable w (physicalRadialFrequency q) z/(2*(z:ℂ)*(Real.sqrt (1-z):ℂ)))
    (a:=tortoiseOf e) (b:=tortoiseOf b)
    (continuous_iff_continuousAt.mpr (fun x => (horizonCoordinate_hasDerivAt x).continuousAt)).continuousOn
    (fun x _ => horizonCoordinate_hasDerivAt x)
    (fun x hx => by
      have hx0 : x<0 := by rw [max_eq_right horder] at hx; exact hx.2.trans htb
      dsimp only [coordinateFirst]
      exact mul_nonneg (mul_nonneg (by norm_num) (radialUnit_bounds x hx0).1.le)
        (horizonCoordinate_interior x hx0).1.le)
  rw [horizonCoordinate_tortoiseOf heI,horizonCoordinate_tortoiseOf hbI] at hcv
  rw [← hcv]
  apply intervalIntegral.integral_congr_uIoo
  intro x hx
  rw [uIoo_of_le horder] at hx
  have hx0 := hx.2.trans htb
  have hz0 : (horizonCoordinate x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (horizonCoordinate_interior x hx0).1.ne'
  have hu0 : (radialUnit x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (radialUnit_bounds x hx0).1.ne'
  simp only [Function.comp_def,nativeGreenKernel,← radialUnit_eq_sqrt x hx0,Complex.real_smul,coordinateFirst]
  push_cast
  field_simp [hz0,hu0]

/-- The original single radial cutoff splits into the existing Green cutoff and its two
corresponding forcing intervals before any limit or residue is taken. -/
theorem radialCutoff_decomposition (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (c₀ c₁ d₀ : ℂ→ℂ) (hw : w.im≠0) (hwr : -2<w.re)
    (hs : w-2*physicalRate q br≠0) (hc : connection w (physicalRadialFrequency q)≠0)
    {e b : ℝ} (he : 0<e) (heb : e≤b) (hb : b<1) :
    radialCutoff q br amp c₀ c₁ d₀ b w e=
      greenCoefficient q w*normalizableOuterPairingCutoff (physicalRadialFrequency q) (physicalRate q br)
        amp (tortoiseOf b) w e+
      forcingCoefficient q br w*((∫ x in tortoiseOf e..tortoiseOf b,
        forcingKernel q br amp (gradient q br) w x)-forcingCounterterm c₀ c₁ d₀ w e+
          regularOuterMoment q br amp (tortoiseOf b) w) := by
  have hbI : b ∈ Ioo (0:ℝ) 1 := ⟨he.trans_le heb,hb⟩
  have hte := tortoiseOf_neg (show e ∈ Ioo (0:ℝ) 1 from ⟨he,heb.trans_lt hb⟩)
  have htb := tortoiseOf_neg hbI
  have horder := chart_order he heb hb
  have hG : IntervalIntegrable (nativeGreenKernel q br amp w) volume (tortoiseOf e) (tortoiseOf b) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le horder]
    exact (nativeGreen_continuous q br amp w hw hwr).mono (fun x hx => hx.2.trans_lt htb)
  have hF : IntervalIntegrable (forcingKernel q br amp (gradient q br) w) volume (tortoiseOf e) (tortoiseOf b) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le horder]
    exact (forcing_continuous q br amp (gradient q br) w).mono (fun x hx => hx.2.trans_lt htb)
  have hD : (∫ x in tortoiseOf e..tortoiseOf b,outerDensity q br amp w x)=
      greenCoefficient q w*(∫ x in tortoiseOf e..tortoiseOf b,nativeGreenKernel q br amp w x)+
      forcingCoefficient q br w*(∫ x in tortoiseOf e..tortoiseOf b,forcingKernel q br amp (gradient q br) w x) := by
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hG.const_mul (greenCoefficient q w)) (hF.const_mul (forcingCoefficient q br w))]
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    rw [uIoo_of_le horder] at hx
    exact original_density_native q br amp w hwr (hx.2.trans htb)
  obtain ⟨hOE,hE⟩ := outerIntegral_decomposition q br amp w hw hwr hs hc hte
  obtain ⟨hOB,hB⟩ := outerIntegral_decomposition q br amp w hw hwr hs hc htb
  have hI : IntervalIntegrable (outerDensity q br amp w) volume (tortoiseOf e) (tortoiseOf b) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le horder,integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hOE.mono_set (fun x hx => ⟨hx.1,hx.2.trans htb⟩)
  have hO : IntervalIntegrable (outerDensity q br amp w) volume (tortoiseOf b) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le htb.le,integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hOB
  have houter : (∫ x in tortoiseOf b..0,outerDensity q br amp w x)=outerIntegral q br amp (tortoiseOf b) w := by
    rw [intervalIntegral.integral_of_le htb.le,outerIntegral]
    exact (setIntegral_congr_set Ioo_ae_eq_Ioc).symm
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals hI hO).symm
  rw [hD,houter,hB,nativeGreen_integral q br amp w he heb hb] at hsplit
  unfold radialCutoff
  rw [hsplit]
  simp only [normalizableOuterPairingCutoff,normalizableHorizonPairingCutoff,greenCounterterm,
    incomingCoefficient,oppositeCoefficient,horizonCoordinate_tortoiseOf hbI]
  dsimp only [greenCoefficient,forcingCoefficient,gradient,mu]
  ring

/-- The unchanged source factor appearing in the original temporal corner residue. -/
def sourceResidue (q : XiZeroCopy) (br side : Bool) (amp : ℂ) : ℂ :=
  mu q*(mu q-2)*(physicalSelfSourceCoefficient q*
    fundamentalSourceMoment (physicalFundamentalFrequency q side) (physicalRate q br) amp*
      continuedOnset (physicalRate q br) (physicalFundamentalFrequency q side))

private theorem green_residue_value (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    greenCoefficient q (physicalFundamentalFrequency q side)*
      (physicalIncomingPoleAmplitude q br side amp*
        D4BMFundamentalNorm.normFinitePart (physicalFundamentalFrequency q side)) = -sourceResidue q br side amp := by
  have hw := physicalFundamentalFrequency_strip q side
  have hw0 : physicalFundamentalFrequency q side≠0 := by intro h; apply hw.1; simp [h]
  have hn := D4BMFundamentalNorm.normFinitePart_ne_zero (physicalFundamentalFrequency q side)
    (abs_lt.mp hw.2).1 hw.1
  unfold greenCoefficient physicalIncomingPoleAmplitude sourceResidue
  dsimp only
  rw [D4BMOriginalCornerSpectralBalance.physical_connectionSlope_eq_norm]
  unfold continuedOnset
  field_simp [hw0,hn]

/-- The complete original radial metric integral is restored at one common cutoff. Its actual
source residue is exactly opposite to the retained temporal-corner residue. -/
theorem original_radial_restoration_and_corner_balance_below (q : XiZeroCopy) (br side : Bool) (amp : ℂ)
    (cap : ℝ) (hcap : 0<cap) :
    ∃ R b : ℝ, ∃ c₀ c₁ d₀ : ℂ→ℂ, 0<R ∧ 0<b ∧ b≤1/2 ∧ b≤cap ∧
      AnalyticAt ℂ (regularFinitePart q br amp c₀ c₁ d₀ b) (physicalFundamentalFrequency q side) ∧
      Tendsto (fun w => (w-physicalFundamentalFrequency q side)*radialFinitePart q br amp c₀ c₁ d₀ b w)
        (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 (-sourceResidue q br side amp)) ∧
      Tendsto (fun w => (w-physicalFundamentalFrequency q side)*
        (radialFinitePart q br amp c₀ c₁ d₀ b w+physicalCornerCandidate q br amp w))
        (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 0) ∧
      ∀ w ∈ ball (physicalFundamentalFrequency q side) R, connection w (physicalRadialFrequency q)≠0 →
        Tendsto (radialCutoff q br amp c₀ c₁ d₀ b w) (𝓝[>] (0:ℝ))
          (𝓝 (radialFinitePart q br amp c₀ c₁ d₀ b w)) := by
  let w₀ := physicalFundamentalFrequency q side
  obtain ⟨RF,B,c₀,c₁,d₀,hRF,hB,hBh,hForce⟩ := native_forcing_horizon_QNM q br side amp
  obtain ⟨T,RG,hT,hRG,hsmall,hGreen,hGreenCut⟩ :=
    physicalNormalizableOuterPairing_residue_and_restoration_below q br side amp (min B cap) (lt_min hB hcap)
  let b := horizonCoordinate T
  have hbI : b ∈ Ioo (0:ℝ) 1 := horizonCoordinate_interior T hT
  have hbB : b≤B := hsmall.trans (min_le_left _ _)
  have hbcap : b≤cap := hsmall.trans (min_le_right _ _)
  have hTb : tortoiseOf b=T := tortoiseOf_horizonCoordinate hT
  have hw := physicalFundamentalFrequency_strip q side
  have hs := physicalFundamentalFrequency_sub_sourceRate_ne_zero q br side
  have hvalid : ∀ᶠ u : ℂ in 𝓝 w₀, u.im≠0 ∧ -2<u.re ∧ u-2*physicalRate q br≠0 :=
    (Complex.continuous_im.continuousAt.eventually_ne hw.1).and
      ((continuousAt_const.eventually_lt Complex.continuous_re.continuousAt (abs_lt.mp hw.2).1).and
        ((continuousAt_id.sub continuousAt_const).eventually_ne hs))
  obtain ⟨RV,hRV,hV⟩ := Metric.eventually_nhds_iff.mp hvalid
  let R := min RF (min RG RV)
  have hR : 0<R := lt_min hRF (lt_min hRG hRV)
  have hFu (u : ℂ) (hu : u ∈ ball w₀ R) : u ∈ ball w₀ RF := ball_subset_ball (min_le_left _ _) hu
  have hGu (u : ℂ) (hu : u ∈ ball w₀ R) : u ∈ ball w₀ RG :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hu
  have hVu (u : ℂ) (hu : u ∈ ball w₀ R) :=
    hV (mem_ball.mp (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hu))
  have hF := hForce b hbI.1 hbB
  have hO := regularOuterMoment_analyticAt q br amp w₀ hT
  have hAreg : AnalyticAt ℂ (regularFinitePart q br amp c₀ c₁ d₀ b) w₀ := by
    have hO' : AnalyticAt ℂ (regularOuterMoment q br amp (tortoiseOf b)) w₀ := by simpa only [hTb] using hO
    exact hF.1.add hO'
  have hAF : AnalyticAt ℂ (fun w => forcingCoefficient q br w*regularFinitePart q br amp c₀ c₁ d₀ b w) w₀ :=
    (((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul (continuedOnset_analyticAt _ _ hs)).mul hAreg
  have hAG : AnalyticAt ℂ (greenCoefficient q) w₀ := by unfold greenCoefficient; fun_prop
  have hzero : Tendsto (fun w : ℂ => w-w₀) (𝓝[≠] w₀) (𝓝 0) := by
    have hi : Tendsto (fun w : ℂ => w) (𝓝[≠] w₀) (𝓝 w₀) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [sub_self] using hi.sub_const w₀
  have hGreen' : Tendsto (fun w => (w-w₀)*normalizableOuterPairing (physicalRadialFrequency q)
      (physicalRate q br) amp (tortoiseOf b) w) (𝓝[≠] w₀)
      (𝓝 (physicalIncomingPoleAmplitude q br side amp*D4BMFundamentalNorm.normFinitePart w₀)) := by
    simpa only [hTb] using hGreen
  have hres0 := ((hAG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul hGreen').add
    (hzero.mul (hAF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  simp only [zero_mul,add_zero] at hres0
  have hvalue : greenCoefficient q w₀*
      (physicalIncomingPoleAmplitude q br side amp*D4BMFundamentalNorm.normFinitePart w₀) =
      -sourceResidue q br side amp := green_residue_value q br side amp
  rw [hvalue] at hres0
  have hres : Tendsto (fun w => (w-w₀)*radialFinitePart q br amp c₀ c₁ d₀ b w)
      (𝓝[≠] w₀) (𝓝 (-sourceResidue q br side amp)) := by
    apply hres0.congr'
    filter_upwards [] with w
    dsimp only [radialFinitePart]
    ring
  refine ⟨R,b,c₀,c₁,d₀,hR,hbI.1,hbB.trans hBh,hbcap,hAreg,hres,?_,?_⟩
  · have hcorner := physical_corner_candidate_residue q br side amp
    change Tendsto _ _ (𝓝 (sourceResidue q br side amp)) at hcorner
    have hsum := hres.add hcorner
    simp only [neg_add_cancel] at hsum
    apply hsum.congr'
    filter_upwards [] with w
    ring
  intro w hwu hconn
  have hGcut : Tendsto (normalizableOuterPairingCutoff (physicalRadialFrequency q) (physicalRate q br)
      amp (tortoiseOf b) w) (𝓝[>] (0:ℝ))
      (𝓝 (normalizableOuterPairing (physicalRadialFrequency q) (physicalRate q br) amp (tortoiseOf b) w)) := by
    simpa only [hTb] using hGreenCut w (hGu w hwu) hconn
  have hFcut := (hF.2 w (hFu w hwu)).add_const (regularOuterMoment q br amp (tortoiseOf b) w)
  have hFcut' : Tendsto (fun e : ℝ => (∫ x in tortoiseOf e..tortoiseOf b,
      forcingKernel q br amp (gradient q br) w x)-forcingCounterterm c₀ c₁ d₀ w e+
      regularOuterMoment q br amp (tortoiseOf b) w) (𝓝[>] (0:ℝ))
      (𝓝 (regularFinitePart q br amp c₀ c₁ d₀ b w)) := by
    apply hFcut.congr'
    filter_upwards [] with e
    unfold forcingCounterterm
    ring
  have hlimit := (hGcut.const_mul (greenCoefficient q w)).add (hFcut'.const_mul (forcingCoefficient q br w))
  apply hlimit.congr'
  have heb : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e<b :=
    (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e<b from Iio_mem_nhds hbI.1).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,heb] with e he heb
  exact (radialCutoff_decomposition q br amp w c₀ c₁ d₀ (hVu w hwu).1 (hVu w hwu).2.1
    (hVu w hwu).2.2 hconn he heb.le hbI.2).symm

/-- The complete original radial restoration and its unchanged temporal-corner residue. -/
theorem original_radial_restoration_and_corner_balance (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    ∃ R b : ℝ, ∃ c₀ c₁ d₀ : ℂ→ℂ, 0<R ∧ 0<b ∧ b≤1/2 ∧
      Tendsto (fun w => (w-physicalFundamentalFrequency q side)*radialFinitePart q br amp c₀ c₁ d₀ b w)
        (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 (-sourceResidue q br side amp)) ∧
      Tendsto (fun w => (w-physicalFundamentalFrequency q side)*
        (radialFinitePart q br amp c₀ c₁ d₀ b w+physicalCornerCandidate q br amp w))
        (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 0) ∧
      ∀ w ∈ ball (physicalFundamentalFrequency q side) R, connection w (physicalRadialFrequency q)≠0 →
        Tendsto (radialCutoff q br amp c₀ c₁ d₀ b w) (𝓝[>] (0:ℝ))
          (𝓝 (radialFinitePart q br amp c₀ c₁ d₀ b w)) := by
  obtain ⟨R,b,c₀,c₁,d₀,hR,hb,hbh,_,_,hr,hc,hcut⟩ :=
    original_radial_restoration_and_corner_balance_below q br side amp 1 (by norm_num)
  exact ⟨R,b,c₀,c₁,d₀,hR,hb,hbh,hr,hc,hcut⟩

end
end RHTower.D4BMOriginalMetricRadial
