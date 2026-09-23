import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalMetricOuter
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRegularOuterPairing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTemporalOppositeCurrentProfile
import GaloisForLFunctions.HTGeometry.QuadraticEndpointMellin
import GaloisForLFunctions.HTGeometry.LogarithmicEndpointFinitePart

/-! The original lift/contact contribution at the physical horizon, with both radial branches. -/
open Set Filter Topology Metric MeasureTheory Complex
namespace RHTower.D4BMOriginalMetricHorizon
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMLaplaceRadial D4BMModularCore
open D4BMOriginalCornerForcing D4BMOriginalMetricOuter
noncomputable section
set_option autoImplicit false

/-- The gradient fixed by the original lift and forcing identity. -/
def shiftedGradient (q : XiZeroCopy) (br : Bool) : ℂ :=
  reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1-
    (D4BMLeftModeRadialEquation.eigenvalue q-2)

def remainderProfile (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) (z : ℝ) : ℂ :=
  sourceRemainder (physicalRate q br) w amp 1 K 1 z

def incomingCoefficient (q : XiZeroCopy) (w : ℂ) : ℂ :=
  horizonRegularCoefficient w (physicalRadialFrequency q)
    (normalizable w (physicalRadialFrequency q)) (normalizableFirst w (physicalRadialFrequency q))

def oppositeCoefficient (q : XiZeroCopy) (w : ℂ) : ℂ :=
  connection w (physicalRadialFrequency q)/(2*w)

def incomingProfile (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) (z : ℝ) : ℂ :=
  incomingCoefficient q w*(gaussProfile q w z*remainderProfile q br amp K w z)

def oppositeProfile (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) (z : ℝ) : ℂ :=
  oppositeCoefficient q w*(gaussProfile q (-w) z*remainderProfile q br amp K w z)

/-- The original forcing profile paired with the unchanged normalizable reader. -/
def forcingKernel (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (w*(x:ℂ))*forcingProfile (physicalRate q br) amp 1 K (radialUnit x)*
    normalizable w (physicalRadialFrequency q) (horizonCoordinate x)

/-- The forcing kernel with its actual coordinate Jacobian. -/
def pullback (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) (z : ℝ) : ℂ :=
  forcingKernel q br amp K w (tortoiseOf z)/(2*(z:ℂ)*(Real.sqrt (1-z):ℂ))

private theorem incomingCoefficient_analytic (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) :
    AnalyticAt ℂ (incomingCoefficient q) w :=
  normalizable_horizonRegularCoefficient_analyticAt w (physicalRadialFrequency q) hw

private theorem oppositeCoefficient_analytic (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) :
    AnalyticAt ℂ (oppositeCoefficient q) w := by
  have hw0 : w≠0 := by intro h; apply hw; simp [h]
  exact (connection_frequency_analyticAt w (physicalRadialFrequency q) hw).div
    (analyticAt_const.mul analyticAt_id) (mul_ne_zero (by norm_num) hw0)

/-- The unchanged source has an analytic quadratic horizon jet. -/
theorem remainderProfile_germ (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) :
    AnalyticJet2At w (remainderProfile q br amp K) := by
  let s := physicalRate q br
  let A : ℂ := (5*s^(2 : ℕ)+15*s+4)/4
  let B : ℂ := s*(s-1)/4*((s+2)^(2 : ℕ)-K)
  have hlin : AnalyticJet2At w (fun (_ : ℂ) (z : ℝ) => A+(1-(z:ℂ))*B) := by
    refine AnalyticJet2At.of_jet (R:=1) (b:=1/2) (C:=0)
      (c₀:=fun _ => A+B) (c₁:=fun _ => -B) (by norm_num) (by norm_num) le_rfl
      analyticAt_const analyticAt_const ?_
    intro u hu z hz
    have he : A+(1-(z:ℂ))*B-(A+B)-(-B)*(z:ℂ)=0 := by ring
    simp only [he,norm_zero,zero_mul,le_refl]
  have hA := amplitudeProfile_germ s amp (fun _ => 1) (w₀:=w) analyticAt_const
  refine (hA.mul hlin).congr (fun u z => ?_)
  simp only [remainderProfile,sourceRemainder,amplitudeProfile,power,mul_one]
  dsimp only [s,A,B]
  ring

private theorem profiles_germ (q : XiZeroCopy) (br side : Bool) (amp K : ℂ) :
    AnalyticJet2At (physicalFundamentalFrequency q side) (incomingProfile q br amp K) ∧
    AnalyticJet2At (physicalFundamentalFrequency q side) (oppositeProfile q br amp K) := by
  have hw := (physicalFundamentalFrequency_strip q side).1
  have hs := remainderProfile_germ q br amp K (physicalFundamentalFrequency q side)
  exact ⟨((gaussProfile_germ q side).mul hs).const_mul (incomingCoefficient_analytic q _ hw),
    ((negativeGaussProfile_germ q side).mul hs).const_mul (oppositeCoefficient_analytic q _ hw)⟩

private theorem profiles_continuous (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    ContinuousAt (incomingProfile q br amp K w) z ∧
    ContinuousAt (oppositeProfile q br amp K w) z := by
  have hs := (sourceRemainder_continuous (physicalRate q br) w amp 1 K 1).continuousAt (x:=z)
  exact ⟨continuousAt_const.mul ((gaussProfile_continuousAt q w hz).mul hs),
    continuousAt_const.mul ((gaussProfile_continuousAt q (-w) hz).mul hs)⟩

private theorem profiles_analytic (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    (hw : w.im≠0) {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    AnalyticAt ℂ (fun u => incomingProfile q br amp K u z) w ∧
    AnalyticAt ℂ (fun u => oppositeProfile q br amp K u z) w := by
  have hs := (sourceRemainder_frequency_entire (physicalRate q br) amp 1
    K 1 z).analyticAt w
  have hn : (-w).im≠0 := by simpa only [Complex.neg_im,neg_ne_zero] using hw
  exact ⟨(incomingCoefficient_analytic q w hw).mul ((gaussProfile_analyticAt q w hw hz).mul hs),
    (oppositeCoefficient_analytic q w hw).mul
      (((gaussProfile_analyticAt q (-w) hn hz).comp analyticAt_id.neg).mul hs)⟩

private theorem forcing_pullback (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    Complex.exp (w*(tortoiseOf z:ℂ))*forcingProfile (physicalRate q br) amp 1 K (radialUnit (tortoiseOf z)) =
      -2*(Real.sqrt (1-z):ℂ)*(z:ℂ)^(w/2)*remainderProfile q br amp K w z := by
  have ht := tortoiseOf_neg hz
  have hu : radialUnit (tortoiseOf z)=Real.sqrt (1-z) := by
    rw [radialUnit_eq_sqrt _ ht,horizonCoordinate_tortoiseOf hz]
  have hS := sourceAmplitude_eq_profile (physicalRate q br) amp (fun _ => 1) w (tortoiseOf z) ht
  rw [horizonCoordinate_tortoiseOf hz] at hS
  simp only [sourceAmplitude,mul_one,amplitudeProfile] at hS
  rw [hu] at hS
  have hr : (Real.sqrt (1-z):ℂ)^(2 : ℕ)=1-(z:ℂ) := by
    exact_mod_cast Real.sq_sqrt (show 0≤1-z by linarith [hz.2])
  simp only [forcingProfile,remainderProfile,sourceRemainder,mul_one,hu,hr,power] at hS ⊢
  linear_combination (-2*(Real.sqrt (1-z):ℂ)*
    ((5*physicalRate q br^(2 : ℕ)+15*physicalRate q br+4)/4+
      (1-(z:ℂ))*physicalRate q br*(physicalRate q br-1)/4*((physicalRate q br+2)^(2 : ℕ)-K)))*hS

/-- Both branches of the actual normalizable reader survive the coordinate change. -/
theorem pullback_decomposition (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    (hw : w.im≠0) {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    pullback q br amp K w z =
      -(z:ℂ)^(w-1)*incomingProfile q br amp K w z-oppositeProfile q br amp K w z/(z:ℂ) := by
  have hn := (original_homogeneous_horizon_representation w (physicalRadialFrequency q) hw
    (fun b hb => (normalizable_derivatives_continued hb).1)
    (fun b hb => (normalizable_derivatives_continued hb).2)
    (fun b hb => normalizable_equation_continued hb) hz).1
  rw [normalizable_opposite_coefficient w (physicalRadialFrequency q) hw] at hn
  have hz0 : (z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hz.1.ne'
  have hr0 : (Real.sqrt (1-z):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by linarith [hz.2])).ne'
  have hp : (z:ℂ)^(w/2)*(z:ℂ)^(w/2)=(z:ℂ)^w := by
    rw [← Complex.cpow_add _ _ hz0]; congr 1; ring
  have hm : (z:ℂ)^(w/2)*(z:ℂ)^((-w)/2)=1 := by
    rw [← Complex.cpow_add _ _ hz0,show w/2+(-w)/2=0 by ring,Complex.cpow_zero]
  simp only [pullback,forcingKernel,horizonCoordinate_tortoiseOf hz]
  rw [forcing_pullback q br amp K w hz,hn]
  simp only [horizon_eq_pow_mul,incomingProfile,oppositeProfile,incomingCoefficient,
    oppositeCoefficient,gaussProfile]
  rw [Complex.cpow_sub _ _ hz0,Complex.cpow_one]
  calc
    _ = -((z:ℂ)^(w/2)*(z:ℂ)^(w/2))*
          (horizonRegularCoefficient w (physicalRadialFrequency q)
            (normalizable w (physicalRadialFrequency q)) (normalizableFirst w (physicalRadialFrequency q))*
              gaussFactor w (physicalRadialFrequency q) false (z:ℂ)*remainderProfile q br amp K w z)/(z:ℂ)-
        ((z:ℂ)^(w/2)*(z:ℂ)^((-w)/2))*
          (connection w (physicalRadialFrequency q)/(2*w)*
            gaussFactor (-w) (physicalRadialFrequency q) false (z:ℂ)*remainderProfile q br amp K w z)/(z:ℂ) := by
      field_simp [hz0,hr0]
      ring
    _ = _ := by rw [hp,hm]; ring

/-- The restored regular value retains the finite contributions of both horizon branches. -/
def horizonFinitePart (q : XiZeroCopy) (br : Bool) (amp K : ℂ)
    (c₀ c₁ d₀ : ℂ→ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  -QuadraticEndpointMellin.finitePart (incomingProfile q br amp K) c₀ c₁ b w-
    LogarithmicEndpoint.finitePart (oppositeProfile q br amp K) d₀ b w

private theorem pullback_integral (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    (hw : w.im≠0) {e b : ℝ} (he : 0<e) (heb : e≤b) (hb : b<1) :
    (∫ z in e..b,pullback q br amp K w z) =
      -(∫ z in e..b,(z:ℂ)^(w-1)*incomingProfile q br amp K w z)-
        ∫ z in e..b,oppositeProfile q br amp K w z/(z:ℂ) := by
  have hz (z : ℝ) (hz : z ∈ uIcc e b) : z ∈ Ioo (0:ℝ) 1 := by
    rw [uIcc_of_le heb] at hz
    exact ⟨he.trans_le hz.1,hz.2.trans_lt hb⟩
  have hP : IntervalIntegrable (fun z : ℝ => (z:ℂ)^(w-1)*incomingProfile q br amp K w z) volume e b := by
    apply ContinuousOn.intervalIntegrable
    intro z hzi
    have hzz := hz z hzi
    exact ((continuousAt_ofReal_cpow_const z (w-1) (Or.inr hzz.1.ne')).mul
      (profiles_continuous q br amp K w hzz).1).continuousWithinAt
  have hL : IntervalIntegrable (fun z : ℝ => oppositeProfile q br amp K w z/(z:ℂ)) volume e b := by
    apply ContinuousOn.intervalIntegrable
    intro z hzi
    have hzz := hz z hzi
    exact ((profiles_continuous q br amp K w hzz).2.div Complex.continuous_ofReal.continuousAt
      (Complex.ofReal_ne_zero.mpr hzz.1.ne')).continuousWithinAt
  calc
    _ = ∫ z in e..b,-((z:ℂ)^(w-1)*incomingProfile q br amp K w z)-
        oppositeProfile q br amp K w z/(z:ℂ) := by
      apply intervalIntegral.integral_congr
      intro z hzi
      simpa only [neg_mul] using pullback_decomposition q br amp K w hw (hz z hzi)
    _ = _ := by
      have hn : IntervalIntegrable (fun z : ℝ => -((z:ℂ)^(w-1)*incomingProfile q br amp K w z)) volume e b := hP.neg
      rw [intervalIntegral.integral_sub hn hL,intervalIntegral.integral_neg]

/-- Every fixed forcing profile has source-determined power and logarithmic restoration,
analytic at either physical fundamental QNM. -/
theorem forcing_horizon_restoration (q : XiZeroCopy) (br side : Bool) (amp K : ℂ) :
    ∃ R B : ℝ, ∃ c₀ c₁ d₀ : ℂ→ℂ, 0<R ∧ 0<B ∧ B≤1/2 ∧
      ∀ b : ℝ, 0<b → b≤B →
        AnalyticAt ℂ (horizonFinitePart q br amp K c₀ c₁ d₀ b) (physicalFundamentalFrequency q side) ∧
        ∀ w ∈ ball (physicalFundamentalFrequency q side) R,
          Tendsto (fun e : ℝ => (∫ z in e..b,pullback q br amp K w z)-
            c₀ w*(e:ℂ)^w/w-c₁ w*(e:ℂ)^(w+1)/(w+1)-d₀ w*(Real.log e:ℂ))
            (𝓝[>] (0:ℝ)) (𝓝 (horizonFinitePart q br amp K c₀ c₁ d₀ b w)) := by
  let w₀ := physicalFundamentalFrequency q side
  have hw : w₀.im≠0 := (physicalFundamentalFrequency_strip q side).1
  have hwr : -2<w₀.re := (abs_lt.mp (physicalFundamentalFrequency_strip q side).2).1
  obtain ⟨hp,hl⟩ := profiles_germ q br side amp K
  obtain ⟨RJ,B,hRJ,hB,hBh,c₀,c₁,C,hC,ha₀,ha₁,hjp⟩ := hp
  obtain ⟨RL,D,hRL,hRLRJ,hD,hDB,hDh,d₀,d₁,E,M,hE,hM,hda₀,_,_,hdb₁,hjl⟩ :=
    hl.exists_bounded hRJ hB
  let β := (w₀.re-2)/2
  have hβ : -2<β := by dsimp [β]; linarith
  have hr : ∀ᶠ u : ℂ in 𝓝 w₀, β<u.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt (by dsimp [β]; linarith)
  obtain ⟨RA,hRA,hdata⟩ := Metric.eventually_nhds_iff.mp
    ((Complex.continuous_im.continuousAt.eventually_ne hw).and
      (hr.and (ha₀.eventually_analyticAt.and (ha₁.eventually_analyticAt.and hda₀.eventually_analyticAt))))
  let R := min RL RA
  have hR : 0<R := lt_min hRL hRA
  have hd (u : ℂ) (hu : u ∈ ball w₀ R) :=
    hdata (mem_ball.mp (ball_subset_ball (min_le_right RL RA) hu))
  have hJL (u : ℂ) (hu : u ∈ ball w₀ R) : u ∈ closedBall w₀ RL :=
    ball_subset_closedBall (ball_subset_ball (min_le_left RL RA) hu)
  have hJP (u : ℂ) (hu : u ∈ ball w₀ R) : u ∈ closedBall w₀ RJ :=
    closedBall_subset_closedBall hRLRJ (hJL u hu)
  have hnz (u : ℂ) (hui : u.im≠0) : u≠0 ∧ u+1≠0 := by
    constructor
    · intro h; apply hui; simp [h]
    · intro h; apply hui; have := congrArg Complex.im h; simpa using this
  refine ⟨R,D,c₀,c₁,d₀,hR,hD,hDh,?_⟩
  intro b hb hbD
  have hb1 : b<1 := by linarith
  have hsp (u : ℂ) (_hu : u ∈ ball w₀ R) :
      ContinuousOn (incomingProfile q br amp K u) (Ioc (0:ℝ) b) := by
    intro z hz
    exact (profiles_continuous q br amp K u ⟨hz.1,hz.2.trans_lt hb1⟩).1.continuousWithinAt
  have hsl (u : ℂ) (_hu : u ∈ ball w₀ R) :
      ContinuousOn (oppositeProfile q br amp K u) (Ioc (0:ℝ) b) := by
    intro z hz
    exact (profiles_continuous q br amp K u ⟨hz.1,hz.2.trans_lt hb1⟩).2.continuousWithinAt
  have hbp (u : ℂ) (hu : u ∈ ball w₀ R) (z : ℝ) (hz : z ∈ Ioc (0:ℝ) b) :=
    hjp u (hJP u hu) z ⟨hz.1,(hz.2.trans hbD).trans hDB⟩
  have hbl (u : ℂ) (hu : u ∈ ball w₀ R) (z : ℝ) (hz : z ∈ Ioc (0:ℝ) b) :
      ‖oppositeProfile q br amp K u z-d₀ u‖≤(M+E*D)*z := by
    have hjet := hjl u (hJL u hu) z ⟨hz.1,hz.2.trans hbD⟩
    have hcoef : ‖d₁ u*(z:ℂ)‖≤M*z := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz.1]
      exact mul_le_mul_of_nonneg_right (hdb₁ u (hJL u hu)) hz.1.le
    calc
      _ = ‖(oppositeProfile q br amp K u z-d₀ u-d₁ u*(z:ℂ))+d₁ u*(z:ℂ)‖ := by ring_nf
      _ ≤ ‖oppositeProfile q br amp K u z-d₀ u-d₁ u*(z:ℂ)‖+‖d₁ u*(z:ℂ)‖ := norm_add_le _ _
      _ ≤ E*z^(2 : ℕ)+M*z := add_le_add hjet hcoef
      _ ≤ (M+E*D)*z := by
        have hzz : z≤D := hz.2.trans hbD
        have := mul_le_mul_of_nonneg_left hzz (mul_nonneg hE hz.1.le)
        nlinarith
  have hAP : AnalyticAt ℂ (QuadraticEndpointMellin.finitePart
      (incomingProfile q br amp K) c₀ c₁ b) w₀ :=
    QuadraticEndpointMellin.finitePart_analyticAt hb hb1.le hR hC hβ
      (hnz w₀ hw).1 (hnz w₀ hw).2 (fun u hu => (hd u hu).2.1.le) hsp
      (fun u hu => ⟨(hd u hu).2.2.1,(hd u hu).2.2.2.1⟩)
      (fun z hz u hu => (profiles_analytic q br amp K u (hd u hu).1 ⟨hz.1,hz.2.trans_lt hb1⟩).1) hbp
  have hAL : AnalyticAt ℂ (LogarithmicEndpoint.finitePart
      (oppositeProfile q br amp K) d₀ b) w₀ :=
    LogarithmicEndpoint.finitePart_analyticAt hR hsl (fun u hu => (hd u hu).2.2.2.2)
      (fun z hz u hu => (profiles_analytic q br amp K u (hd u hu).1 ⟨hz.1,hz.2.trans_lt hb1⟩).2) hbl
  refine ⟨hAP.neg.sub hAL,?_⟩
  intro u hu
  have hP := QuadraticEndpointMellin.cutoff_tendsto hb (hβ.trans (hd u hu).2.1)
    (hnz u (hd u hu).1).1 (hnz u (hd u hu).1).2 (hsp u hu) (hbp u hu)
  have hL := LogarithmicEndpoint.cutoff_tendsto hb (hsl u hu) (hbl u hu)
  have h := hP.neg.sub hL
  apply h.congr'
  have heb : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e<b :=
    (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e<b from Iio_mem_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,heb] with e he heb
  rw [pullback_integral q br amp K u (hd u hu).1 he heb.le hb1]
  ring

/-- The pullback is the exact original radial cutoff integral, with no endpoint omitted. -/
theorem forcing_radial_integral_pullback (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    {e b : ℝ} (he : 0<e) (heb : e≤b) (hb : b<1) :
    (∫ x in tortoiseOf e..tortoiseOf b,forcingKernel q br amp K w x)=
      ∫ z in e..b,pullback q br amp K w z := by
  have heI : e ∈ Ioo (0:ℝ) 1 := ⟨he,heb.trans_lt hb⟩
  have hbI : b ∈ Ioo (0:ℝ) 1 := ⟨he.trans_le heb,hb⟩
  have hte := tortoiseOf_neg heI
  have htb := tortoiseOf_neg hbI
  have horder : tortoiseOf e≤tortoiseOf b := by
    by_contra h
    have hm := horizonCoordinate_strictMonoOn
      (show tortoiseOf b ∈ Iio (0:ℝ) from htb)
      (show tortoiseOf e ∈ Iio (0:ℝ) from hte) (lt_of_not_ge h)
    rw [horizonCoordinate_tortoiseOf hbI,horizonCoordinate_tortoiseOf heI] at hm
    exact (not_lt_of_ge heb) hm
  have hcv := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (f:=horizonCoordinate) (f':=coordinateFirst) (g:=pullback q br amp K w)
    (a:=tortoiseOf e) (b:=tortoiseOf b)
    (continuous_iff_continuousAt.mpr (fun x => (horizonCoordinate_hasDerivAt x).continuousAt)).continuousOn
    (fun x _ => horizonCoordinate_hasDerivAt x)
    (fun x hx => by
      have hx0 : x<0 := by
        rw [max_eq_right horder] at hx
        exact hx.2.trans htb
      dsimp only [coordinateFirst]
      exact mul_nonneg (mul_nonneg (by norm_num) (radialUnit_bounds x hx0).1.le)
        (horizonCoordinate_interior x hx0).1.le)
  rw [horizonCoordinate_tortoiseOf heI,horizonCoordinate_tortoiseOf hbI] at hcv
  rw [← hcv]
  apply intervalIntegral.integral_congr_uIoo
  intro x hx
  rw [uIoo_of_le horder] at hx
  have hx0 := hx.2.trans htb
  have hz0 : (horizonCoordinate x:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (horizonCoordinate_interior x hx0).1.ne'
  have hu0 : (radialUnit x:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (radialUnit_bounds x hx0).1.ne'
  simp only [Function.comp_def,pullback,tortoiseOf_horizonCoordinate hx0,
    ← radialUnit_eq_sqrt x hx0,Complex.real_smul,coordinateFirst]
  push_cast
  field_simp [hz0,hu0]


/-- The same coordinate identity for the original combined lift/contact kernel. -/
theorem regular_radial_integral_pullback (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    {e b : ℝ} (he : 0<e) (heb : e≤b) (hb : b<1) :
    (∫ x in tortoiseOf e..tortoiseOf b,regularKernel q br amp w x)=
      ∫ z in e..b,pullback q br amp (shiftedGradient q br) w z := by
  have h := forcing_radial_integral_pullback q br amp (shiftedGradient q br) w he heb hb
  simpa only [forcingKernel,regularKernel,regularCore_eq_forcingProfile,shiftedGradient] using h

private theorem regular_radial_split (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    {e b : ℝ} (he : 0<e) (heb : e≤b) (hb : b<1) :
    (∫ x in tortoiseOf e..0,regularKernel q br amp w x)=
      (∫ x in tortoiseOf e..tortoiseOf b,regularKernel q br amp w x)+
        regularOuterMoment q br amp (tortoiseOf b) w := by
  have heI : e ∈ Ioo (0:ℝ) 1 := ⟨he,heb.trans_lt hb⟩
  have hbI : b ∈ Ioo (0:ℝ) 1 := ⟨he.trans_le heb,hb⟩
  have hte := tortoiseOf_neg heI
  have htb := tortoiseOf_neg hbI
  have horder : tortoiseOf e≤tortoiseOf b := by
    by_contra h
    have hm := horizonCoordinate_strictMonoOn
      (show tortoiseOf b ∈ Iio (0:ℝ) from htb)
      (show tortoiseOf e ∈ Iio (0:ℝ) from hte) (lt_of_not_ge h)
    rw [horizonCoordinate_tortoiseOf hbI,horizonCoordinate_tortoiseOf heI] at hm
    exact (not_lt_of_ge heb) hm
  have hI := regularKernel_integrable q br amp w hte
  have hO : IntervalIntegrable (regularKernel q br amp w) volume (tortoiseOf b) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le htb.le,integrableOn_Ioc_iff_integrableOn_Ioo]
    exact regularKernel_integrable q br amp w htb
  have hH : IntervalIntegrable (regularKernel q br amp w) volume (tortoiseOf e) (tortoiseOf b) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le horder,integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hI.mono_set (fun x hx => ⟨hx.1,hx.2.trans htb⟩)
  rw [← intervalIntegral.integral_add_adjacent_intervals hH hO]
  congr 1
  rw [intervalIntegral.integral_of_le htb.le,regularOuterMoment]
  exact (setIntegral_congr_set Ioo_ae_eq_Ioc).symm

/-- The complete regular radial contribution, with its horizon finite part and outer integral. -/
def regularRadialFinitePart (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (c₀ c₁ d₀ : ℂ→ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  horizonFinitePart q br amp (shiftedGradient q br) c₀ c₁ d₀ b w+regularOuterMoment q br amp (tortoiseOf b) w

/-- For the unchanged original lift/contact term, horizon restoration creates no QNM residue.
The original onset and angular metric coefficient are retained. -/
theorem original_regular_radial_QNM (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    ∃ R B : ℝ, ∃ c₀ c₁ d₀ : ℂ→ℂ, 0<R ∧ 0<B ∧ B≤1/2 ∧
      ∀ b : ℝ, 0<b → b≤B →
        AnalyticAt ℂ (fun w => D4BMLeftModeRadialEquation.eigenvalue q*w*
          physicalSelfSourceCoefficient q*continuedOnset (physicalRate q br) w*
          regularRadialFinitePart q br amp c₀ c₁ d₀ b w) (physicalFundamentalFrequency q side) ∧
        Tendsto (fun w => (w-physicalFundamentalFrequency q side)*
          (D4BMLeftModeRadialEquation.eigenvalue q*w*physicalSelfSourceCoefficient q*
            continuedOnset (physicalRate q br) w*regularRadialFinitePart q br amp c₀ c₁ d₀ b w))
          (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 0) ∧
        ∀ w ∈ ball (physicalFundamentalFrequency q side) R,
          Tendsto (fun e : ℝ =>
            (∫ x in tortoiseOf e..0,regularKernel q br amp w x)-
              c₀ w*(e:ℂ)^w/w-c₁ w*(e:ℂ)^(w+1)/(w+1)-d₀ w*(Real.log e:ℂ))
            (𝓝[>] (0:ℝ)) (𝓝 (regularRadialFinitePart q br amp c₀ c₁ d₀ b w)) := by
  obtain ⟨R,B,c₀,c₁,d₀,hR,hB,hBh,h⟩ := forcing_horizon_restoration q br side amp (shiftedGradient q br)
  refine ⟨R,B,c₀,c₁,d₀,hR,hB,hBh,?_⟩
  intro b hb hbB
  have hb1 : b<1 := by linarith
  have hH := (h b hb hbB).1
  have hO := regularOuterMoment_analyticAt q br amp (physicalFundamentalFrequency q side)
    (tortoiseOf_neg ⟨hb,hb1⟩)
  have hsum : AnalyticAt ℂ (regularRadialFinitePart q br amp c₀ c₁ d₀ b)
      (physicalFundamentalFrequency q side) := hH.add hO
  have hA : AnalyticAt ℂ (fun w => D4BMLeftModeRadialEquation.eigenvalue q*w*
      physicalSelfSourceCoefficient q*continuedOnset (physicalRate q br) w*
      regularRadialFinitePart q br amp c₀ c₁ d₀ b w) (physicalFundamentalFrequency q side) :=
    (((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul
      (continuedOnset_analyticAt _ _ (physicalFundamentalFrequency_sub_sourceRate_ne_zero q br side))).mul hsum
  refine ⟨hA,?_,?_⟩
  · have hz : Tendsto (fun w : ℂ => w-physicalFundamentalFrequency q side)
        (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 0) := by
      have hi : Tendsto (fun w : ℂ => w) (𝓝[≠] physicalFundamentalFrequency q side)
          (𝓝 (physicalFundamentalFrequency q side)) := tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [sub_self] using hi.sub_const (physicalFundamentalFrequency q side)
    simpa only [zero_mul] using hz.mul (hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  intro w hw
  have ht := ((h b hb hbB).2 w hw).add_const (regularOuterMoment q br amp (tortoiseOf b) w)
  apply ht.congr'
  have heb : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e<b :=
    (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e<b from Iio_mem_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,heb] with e he heb
  rw [regular_radial_split q br amp w he heb.le hb1,regular_radial_integral_pullback q br amp w he heb.le hb1]
  ring

/-- In the complete original metric density, the lift subtracted from the reduced response
cancels the retained lift exactly. The native response and original forcing remain. -/
theorem original_density_native (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hwr : -2<w.re) {x : ℝ} (hx : x<0) :
    outerDensity q br amp w x=
      (2*D4BMLeftModeRadialEquation.eigenvalue q*w*(D4BMLeftModeRadialEquation.eigenvalue q-2)*
        physicalSelfSourceCoefficient q)*
        (continuedResponse (physicalRate q br) (physicalRadialFrequency q) amp 1
          (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1)
          (horizonCoordinate x) w*normalizable w (physicalRadialFrequency q) (horizonCoordinate x))+
      (D4BMLeftModeRadialEquation.eigenvalue q*w*physicalSelfSourceCoefficient q*
        continuedOnset (physicalRate q br) w)*
        forcingKernel q br amp (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) w x := by
  rw [outerDensity_decomposition q br amp w hwr hx]
  have hL : radialLift (physicalRate q br) w amp (continuedOnset (physicalRate q br) w) x=
      Complex.exp (w*(x:ℂ))*continuedOnset (physicalRate q br) w*
        radialLift (physicalRate q br) 0 amp 1 x := by
    simp only [radialLift,sourceAmplitude,zero_mul,Complex.exp_zero,one_mul,mul_one]
    ring
  simp only [continuedReducedGreen,continuedTortoiseGreen,mul_one,hL,regularKernel,regularCore,forcingKernel]
  ring

/-- The native original forcing has an analytic horizon finite part at either physical QNM,
with the literal radial integral and its forced counterterms retained. -/
theorem native_forcing_horizon_QNM (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    let K := reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1
    ∃ R B : ℝ, ∃ c₀ c₁ d₀ : ℂ→ℂ, 0<R ∧ 0<B ∧ B≤1/2 ∧
      ∀ b : ℝ, 0<b → b≤B →
        AnalyticAt ℂ (horizonFinitePart q br amp K c₀ c₁ d₀ b) (physicalFundamentalFrequency q side) ∧
        ∀ w ∈ ball (physicalFundamentalFrequency q side) R,
          Tendsto (fun e : ℝ => (∫ x in tortoiseOf e..tortoiseOf b,forcingKernel q br amp K w x)-
            c₀ w*(e:ℂ)^w/w-c₁ w*(e:ℂ)^(w+1)/(w+1)-d₀ w*(Real.log e:ℂ))
            (𝓝[>] (0:ℝ)) (𝓝 (horizonFinitePart q br amp K c₀ c₁ d₀ b w)) := by
  dsimp only
  let K := reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1
  obtain ⟨R,B,c₀,c₁,d₀,hR,hB,hBh,h⟩ := forcing_horizon_restoration q br side amp K
  refine ⟨R,B,c₀,c₁,d₀,hR,hB,hBh,?_⟩
  intro b hb hbB
  refine ⟨(h b hb hbB).1,?_⟩
  intro w hw
  apply ((h b hb hbB).2 w hw).congr'
  have heb : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e<b :=
    (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e<b from Iio_mem_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,heb] with e he heb
  rw [forcing_radial_integral_pullback q br amp K w he heb.le (show b<1 by linarith)]

end
end RHTower.D4BMOriginalMetricHorizon
