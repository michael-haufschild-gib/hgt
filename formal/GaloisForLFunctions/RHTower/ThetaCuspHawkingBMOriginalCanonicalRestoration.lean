import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCanonicalHorizon
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalMetricRadial

open Set Filter Topology Metric MeasureTheory Complex
namespace RHTower.D4BMOriginalCanonicalRestoration
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMLaplaceRadial D4BMModularCore
open D4BMOriginalMetricOuter D4BMOriginalMetricHorizon D4BMOriginalCanonicalHorizon
noncomputable section
set_option autoImplicit false

private theorem incomingCoefficient_analytic (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) :
    AnalyticAt ℂ (incomingCoefficient q) w :=
  normalizable_horizonRegularCoefficient_analyticAt w (physicalRadialFrequency q) hw

private theorem oppositeCoefficient_analytic (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) :
    AnalyticAt ℂ (oppositeCoefficient q) w := by
  have hw0 : w≠0 := by intro h; apply hw; simp [h]
  exact (connection_frequency_analyticAt w (physicalRadialFrequency q) hw).div
    (analyticAt_const.mul analyticAt_id) (mul_ne_zero (by norm_num) hw0)

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

/-- The original horizon finite part uses one fixed coefficient family at
all nonreal frequencies above Re(w)=-2, including the convergence chamber
and both physical fundamental QNMs. Both radial branches remain. -/
theorem canonical_horizon_restoration (q : XiZeroCopy) (br : Bool) (amp K w₀ : ℂ)
    (hw : w₀.im≠0) (hwr : -2<w₀.re) :
    ∃ R B : ℝ,0<R ∧ 0<B ∧ B≤1/2 ∧ ∀ b : ℝ,0<b → b≤B →
      AnalyticAt ℂ (horizonFinitePart q br amp K
        (incomingValue q br amp K) (incomingSlope q br amp K) (oppositeValue q br amp K) b) w₀ ∧
      ∀ w∈ball w₀ R,
        Tendsto (fun e : ℝ => (∫ z in e..b,pullback q br amp K w z)-
          incomingValue q br amp K w*(e:ℂ)^w/w-
          incomingSlope q br amp K w*(e:ℂ)^(w+1)/(w+1)-
          oppositeValue q br amp K w*(Real.log e:ℂ))
          (𝓝[>] (0:ℝ)) (𝓝 (horizonFinitePart q br amp K
            (incomingValue q br amp K) (incomingSlope q br amp K) (oppositeValue q br amp K) b w)) := by
  obtain ⟨hp,hl⟩ := original_profiles_germ q br amp K w₀ hw
  obtain ⟨ha₀,ha₁,RJ,B,C,hRJ,hB,hBh,hC,hjp⟩ := hp.canonical
  obtain ⟨RL,D,hRL,hRLRJ,hD,hDB,hDh,dold,d₁,E,M,hE,hM,_,_,_,hdb₁,hjold⟩ :=
    hl.exists_bounded hRJ hB
  let c₀ := incomingValue q br amp K
  let c₁ := incomingSlope q br amp K
  let d₀ := oppositeValue q br amp K
  have hda₀ : AnalyticAt ℂ d₀ w₀ := (original_coefficients_analytic q br amp K w₀ hw).2.2
  have hjl : HasUniformJet2 (closedBall w₀ RL) D (oppositeProfile q br amp K) d₀ d₁ E := by
    intro u hu z hz
    rw [show d₀ u=dold u from original_opposite_coefficient_unique q br amp K hjold hD hu]
    exact hjold u hu z hz
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
  refine ⟨R,D,hR,hD,hDh,?_⟩
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
  dsimp only [incomingValue,incomingSlope,oppositeValue,d₀]
  ring


/-- The same fixed coefficients restore the literal original radial integral. -/
theorem canonical_radial_restoration (q : XiZeroCopy) (br : Bool) (amp K w₀ : ℂ)
    (hw : w₀.im≠0) (hwr : -2<w₀.re) :
    ∃ R B : ℝ,0<R ∧ 0<B ∧ B≤1/2 ∧ ∀ b : ℝ,0<b → b≤B →
      AnalyticAt ℂ (horizonFinitePart q br amp K
        (incomingValue q br amp K) (incomingSlope q br amp K) (oppositeValue q br amp K) b) w₀ ∧
      ∀ w∈ball w₀ R,
        Tendsto (fun e : ℝ => (∫ x in tortoiseOf e..tortoiseOf b,forcingKernel q br amp K w x)-
          incomingValue q br amp K w*(e:ℂ)^w/w-
          incomingSlope q br amp K w*(e:ℂ)^(w+1)/(w+1)-
          oppositeValue q br amp K w*(Real.log e:ℂ))
          (𝓝[>] (0:ℝ)) (𝓝 (horizonFinitePart q br amp K
            (incomingValue q br amp K) (incomingSlope q br amp K) (oppositeValue q br amp K) b w)) := by
  obtain ⟨R,B,hR,hB,hBh,h⟩ := canonical_horizon_restoration q br amp K w₀ hw hwr
  refine ⟨R,B,hR,hB,hBh,?_⟩
  intro b hb hbB
  refine ⟨(h b hb hbB).1,?_⟩
  intro w hw
  apply ((h b hb hbB).2 w hw).congr'
  filter_upwards [Ioo_mem_nhdsGT hb] with e he
  rw [forcing_radial_integral_pullback q br amp K w he.1 he.2.le (show b<1 by linarith)]

/-- The complete regular term already present in the original metric action
has local analytic representatives with the same global subtraction family,
at every nonreal frequency with real part greater than minus two. -/
theorem canonical_regular_part_analytic (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) :
    let K := reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1
    ∃ B : ℝ,0<B ∧ B≤1/2 ∧ ∀ b : ℝ,0<b → b≤B →
      AnalyticAt ℂ (D4BMOriginalMetricRadial.regularFinitePart q br amp
        (incomingValue q br amp K) (incomingSlope q br amp K) (oppositeValue q br amp K) b) w := by
  dsimp only
  let K := reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1
  obtain ⟨R,B,hR,hB,hBh,h⟩ := canonical_horizon_restoration q br amp K w hw hwr
  refine ⟨B,hB,hBh,?_⟩
  intro b hb hbB
  exact ((h b hb hbB).1).add (regularOuterMoment_analyticAt q br amp w
    (tortoiseOf_neg ⟨hb,show b<1 by linarith⟩))

end
end RHTower.D4BMOriginalCanonicalRestoration
