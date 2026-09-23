import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIncomingPairingEndpoint
import GaloisForLFunctions.HTGeometry.QuadraticEndpointMellin

/-! Analytic horizon finite parts of the original incoming mode and actual source primitive. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set Metric MeasureTheory GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The original norm kernel is analytic in frequency, including connection zeros. -/
theorem incomingPairingFactor_analyticAt (w chi : ℂ) (hw : w.im ≠ 0)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    AnalyticAt ℂ (fun u => incomingPairingFactor u chi z) w := by
  have hg : AnalyticAt ℂ (fun u => gaussFactor u chi false (z:ℂ)) w := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [Complex.continuous_im.continuousAt.eventually_ne hw] with u hu
    exact horizonGauss_frequency_differentiableAt u chi (z:ℂ) hu
      (by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz.1] using hz.2)
  unfold incomingPairingFactor
  exact (hg.pow 2).div analyticAt_const
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by linarith [hz.2])))))

/-- Spatial continuity is inherited from the original Gauss solution and its actual Jacobian. -/
theorem incomingPairingFactor_continuousAt (w chi : ℂ) {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    ContinuousAt (incomingPairingFactor w chi) z := by
  have hg := (gaussFactor_derivatives_continued (w := w) (chi := chi) false
    (enorm_ofReal_lt_one hz.1 hz.2)).1.comp_ofReal.continuousAt
  unfold incomingPairingFactor
  exact (hg.pow 2).div (by fun_prop)
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by linarith [hz.2])))))

/-- The horizon norm's finite part uses its derived Gauss and Jacobian coefficients. -/
def incomingNormFinitePart (chi : ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  QuadraticEndpointMellin.finitePart (fun u => incomingPairingFactor u chi)
    (fun _ => 1/2) (fun u => horizonGaussFirstCoefficient u chi+1/4) b w

/-- The regular source contribution retains its actual linear endpoint coefficient. -/
def incomingSourcePairingFinitePart (s chi a J K : ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  QuadraticEndpointMellin.finitePart
    (fun u z => incomingSourcePrimitive s chi a J K u z*incomingPairingFactor u chi z)
    (fun _ => 0) (fun u => incomingResponseSlope s a J K u/2) b w

/-- The full incoming horizon finite part keeps the original endpoint amplitude. -/
def incomingPairingFinitePart (s chi a J K : ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  incomingResponseEndpoint s chi a J K w b*incomingNormFinitePart chi b w+
    incomingSourcePairingFinitePart s chi a J K b w

private theorem pairing_common_data (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (hs : w-2*s ≠ 0) :
    ∃ R b C D β : ℝ, 0 < R ∧ 0 < b ∧ b ≤ 1/2 ∧ 0 ≤ C ∧ 0 ≤ D ∧ -2 < β ∧
      ∀ u ∈ ball w R, u.im ≠ 0 ∧ β ≤ u.re ∧ u-2*s ≠ 0 ∧
        ContinuousOn (incomingSourcePrimitive s chi a J K u) (Icc (0:ℝ) b) ∧
        ∀ z ∈ Ioc (0:ℝ) b,
          AnalyticAt ℂ (fun v => incomingSourcePrimitive s chi a J K v z) u ∧
          ‖incomingPairingFactor u chi z-(1/2:ℂ)-
            (horizonGaussFirstCoefficient u chi+1/4)*(z:ℂ)‖ ≤ C*z^(2 : ℕ) ∧
          ‖incomingSourcePrimitive s chi a J K u z*incomingPairingFactor u chi z-
            (incomingResponseSlope s a J K u/2)*(z:ℂ)‖ ≤ D*z^(2 : ℕ) ∧
          (connection u chi ≠ 0 → continuedResponse s chi a J K z u/horizon u chi z=
            incomingResponseEndpoint s chi a J K u b+incomingSourcePrimitive s chi a J K u z) := by
  obtain ⟨RP,b,CP,MP,hRP,hb,hbhalf,hCP,_,hP⟩ := incomingSourcePrimitive_common_data s chi a J K w hw hwr hs
  obtain ⟨RM,CM,L,hRM,hCM,hL,hM⟩ := incomingPairingFactor_uniform_second_bound w chi hw
  let β := (w.re-2)/2
  let Md := ‖incomingResponseSlope s a J K w‖+1
  have hMd : 0 ≤ Md := by dsimp [Md]; positivity
  have hd : ∀ᶠ u in 𝓝 w, ‖incomingResponseSlope s a J K u‖ < Md :=
    (incomingResponseSlope_analyticAt s a J K w hw hs).continuousAt.norm.eventually_lt
      continuousAt_const (by dsimp [Md]; linarith)
  have hr : ∀ᶠ u : ℂ in 𝓝 w, β < u.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt (by dsimp [β]; linarith)
  obtain ⟨RD,hRD,hall⟩ := Metric.eventually_nhds_iff.mp (hd.and hr)
  let R := min RD (min RP RM)
  let D := CP*(1/2+L+CM)+Md*CM+Md*L
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨R,b,CM,D,β,lt_min hRD (lt_min hRP hRM),hb,hbhalf,hCM,hD,by dsimp [β]; linarith,?_⟩
  intro u hu
  have huD : u ∈ ball w RD := ball_subset_ball (min_le_left _ _) hu
  have huP : u ∈ ball w RP := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hu
  have huM : u ∈ ball w RM := ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hu
  obtain ⟨hdu,hru⟩ := hall (mem_ball.mp huD)
  obtain ⟨hui,_,hus,hPc,hPb⟩ := hP u huP
  refine ⟨hui,hru.le,hus,hPc,?_⟩
  intro z hz
  obtain ⟨hPa,_,hPe,hQ⟩ := hPb z hz
  have hMe := (hM u huM).2 z ⟨hz.1.le,hz.2.trans hbhalf⟩
  refine ⟨hPa,hMe,?_,hQ⟩
  change ‖incomingSourcePrimitive s chi a J K u z-incomingResponseSlope s a J K u*(z:ℂ)‖ ≤ CP*z^(2 : ℕ) at hPe
  have hPe' : ‖incomingSourcePrimitive s chi a J K u z-0-incomingResponseSlope s a J K u*(z:ℂ)‖ ≤ CP*z^(2 : ℕ) := by simpa using hPe
  have hp := quadratic_endpoint_product_bound
    (show z ∈ Icc (0:ℝ) 1 from ⟨hz.1.le,lt_of_le_of_lt (hz.2.trans hbhalf) (by norm_num) |>.le⟩)
    hCP hCM hPe' hMe
  simp only [zero_mul,zero_add,sub_zero,norm_zero,zero_add] at hp
  rw [show incomingResponseSlope s a J K u*(1/2)=incomingResponseSlope s a J K u/2 by ring] at hp
  refine hp.trans ?_
  rw [show ‖(1/2:ℂ)‖=(1/2:ℝ) by norm_num]
  dsimp [D]
  gcongr
  all_goals exact (hM u huM).1

/-- The original incoming horizon integral has its exact two-counterterm limit, and both source-derived restored pieces are analytic through the connection zero. -/
theorem incomingPairingFinitePart_horizon_restoration_below (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (hs : w-2*s ≠ 0) :
    ∃ R B : ℝ, 0 < R ∧ 0 < B ∧ B ≤ 1/2 ∧
      ∀ b : ℝ, 0 < b → b ≤ B →
      AnalyticAt ℂ (incomingNormFinitePart chi b) w ∧
      AnalyticAt ℂ (incomingSourcePairingFinitePart s chi a J K b) w ∧
      AnalyticAt ℂ (fun u => incomingSourcePrimitive s chi a J K u b) w ∧
      ∀ u ∈ ball w R, connection u chi ≠ 0 →
        Tendsto (fun e : ℝ =>
          (∫ z in e..b, continuedResponse s chi a J K z u*horizon u chi z/
            (2*(z:ℂ)*(Real.sqrt (1-z):ℂ)))+
          (incomingResponseEndpoint s chi a J K u b/2)*(e:ℂ)^u/u+
          ((horizonGaussFirstCoefficient u chi+1/4)*incomingResponseEndpoint s chi a J K u b+
            incomingResponseSlope s a J K u/2)*(e:ℂ)^(u+1)/(u+1))
          (𝓝[>] (0:ℝ)) (𝓝 (incomingPairingFinitePart s chi a J K b u)) := by
  obtain ⟨R,B,C,D,β,hR,hB,hBhalf,hC,hD,hβ,hbig⟩ := pairing_common_data s chi a J K w hw hwr hs
  refine ⟨R,B,hR,hB,hBhalf,?_⟩
  intro b hb hbB
  have hbhalf : b ≤ 1/2 := hbB.trans hBhalf
  have hbds (u : ℂ) (hu : u ∈ ball w R) :
      u.im ≠ 0 ∧ β ≤ u.re ∧ u-2*s ≠ 0 ∧
      ContinuousOn (incomingSourcePrimitive s chi a J K u) (Icc (0:ℝ) b) ∧
      ∀ z ∈ Ioc (0:ℝ) b,
        AnalyticAt ℂ (fun v => incomingSourcePrimitive s chi a J K v z) u ∧
        ‖incomingPairingFactor u chi z-(1/2:ℂ)-
          (horizonGaussFirstCoefficient u chi+1/4)*(z:ℂ)‖ ≤ C*z^(2 : ℕ) ∧
        ‖incomingSourcePrimitive s chi a J K u z*incomingPairingFactor u chi z-
          (incomingResponseSlope s a J K u/2)*(z:ℂ)‖ ≤ D*z^(2 : ℕ) ∧
        (connection u chi ≠ 0 → continuedResponse s chi a J K z u/horizon u chi z=
          incomingResponseEndpoint s chi a J K u b+incomingSourcePrimitive s chi a J K u z) := by
    obtain ⟨hui,hure,hus,hPc,hdata⟩ := hbig u hu
    refine ⟨hui,hure,hus,hPc.mono (Icc_subset_Icc le_rfl hbB),?_⟩
    intro z hz
    obtain ⟨hPa,hMe,hPe,hQz⟩ := hdata z ⟨hz.1,hz.2.trans hbB⟩
    refine ⟨hPa,hMe,hPe,?_⟩
    intro hc
    have hQb := (hdata b ⟨hb,hbB⟩).2.2.2 hc
    change continuedResponse s chi a J K z u/horizon u chi z=
      (continuedResponse s chi a J K b u/horizon u chi b-incomingSourcePrimitive s chi a J K u b)+
        incomingSourcePrimitive s chi a J K u z
    rw [hQz hc,hQb]
    ring
  have hMcont (u : ℂ) : ContinuousOn (incomingPairingFactor u chi) (Ioc (0:ℝ) b) := by
    intro z hz
    exact (incomingPairingFactor_continuousAt u chi
      ⟨hz.1,lt_of_le_of_lt (hz.2.trans hbhalf) (by norm_num)⟩).continuousWithinAt
  have hw0 : w ≠ 0 := by intro h; apply hw; rw [h]; rfl
  have hw1 : w+1 ≠ 0 := by intro h; apply hw; have hi := congrArg Complex.im h; simpa using hi
  refine ⟨?_,?_,?_,?_⟩
  · unfold incomingNormFinitePart
    apply QuadraticEndpointMellin.finitePart_analyticAt hb (by linarith) hR hC hβ hw0 hw1
    · intro u hu; exact (hbds u hu).2.1
    · intro u _; exact hMcont u
    · intro u hu
      exact ⟨analyticAt_const,(horizonGaussFirstCoefficient_analyticAt u chi (hbds u hu).1).add analyticAt_const⟩
    · intro z hz u hu
      exact incomingPairingFactor_analyticAt u chi (hbds u hu).1
        ⟨hz.1,lt_of_le_of_lt (hz.2.trans hbhalf) (by norm_num)⟩
    · intro u hu z hz; exact ((hbds u hu).2.2.2.2 z hz).2.1
  · unfold incomingSourcePairingFinitePart
    apply QuadraticEndpointMellin.finitePart_analyticAt hb (by linarith) hR hD hβ hw0 hw1
    · intro u hu; exact (hbds u hu).2.1
    · intro u hu
      exact (((hbds u hu).2.2.2.1).mono Ioc_subset_Icc_self).mul (hMcont u)
    · intro u hu
      exact ⟨analyticAt_const,(incomingResponseSlope_analyticAt s a J K u (hbds u hu).1
        (hbds u hu).2.2.1).div analyticAt_const (by norm_num)⟩
    · intro z hz u hu
      exact (((hbds u hu).2.2.2.2 z hz).1).mul (incomingPairingFactor_analyticAt u chi (hbds u hu).1
        ⟨hz.1,lt_of_le_of_lt (hz.2.trans hbhalf) (by norm_num)⟩)
    · intro u hu z hz
      simpa only [sub_zero] using ((hbds u hu).2.2.2.2 z hz).2.2.1

  · exact (((hbds w (mem_ball_self hR)).2.2.2.2 b ⟨hb,le_rfl⟩).1)
  · intro u hu hconn
    obtain ⟨hui,hure,_,hPc,hdata⟩ := hbds u hu
    have hur : -2 < u.re := hβ.trans_le hure
    have hu0 : u ≠ 0 := by intro h; apply hui; rw [h]; rfl
    have hu1 : u+1 ≠ 0 := by intro h; apply hui; have hi := congrArg Complex.im h; simpa using hi
    have hPMcont : ContinuousOn (fun z => incomingSourcePrimitive s chi a J K u z*incomingPairingFactor u chi z) (Ioc (0:ℝ) b) :=
      (hPc.mono Ioc_subset_Icc_self).mul (hMcont u)
    have hNM := QuadraticEndpointMellin.cutoff_tendsto
      (F := fun v => incomingPairingFactor v chi) (a₀ := fun _ => 1/2)
      (a₁ := fun v => horizonGaussFirstCoefficient v chi+1/4) (w := u) hb hur hu0 hu1 (hMcont u)
      (fun z hz => (hdata z hz).2.1)
    have hJM := QuadraticEndpointMellin.cutoff_tendsto
      (F := fun v z => incomingSourcePrimitive s chi a J K v z*incomingPairingFactor v chi z)
      (a₀ := fun _ => 0) (a₁ := fun v => incomingResponseSlope s a J K v/2) (w := u) hb hur hu0 hu1 hPMcont
      (fun z hz => show ‖incomingSourcePrimitive s chi a J K u z*incomingPairingFactor u chi z-0-
        (incomingResponseSlope s a J K u/2)*(z:ℂ)‖ ≤ D*z^(2 : ℕ) from by
        simpa only [sub_zero] using (hdata z hz).2.2.1)
    have hlim := (hNM.const_mul (incomingResponseEndpoint s chi a J K u b)).add hJM
    change Tendsto _ (𝓝[>] (0:ℝ)) (𝓝 (incomingPairingFinitePart s chi a J K b u)) at hlim
    apply hlim.congr'
    have he : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e < b :=
      (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < b from Iio_mem_nhds hb).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,he] with e he0 heb
    have hsubset : uIcc e b ⊆ Ioc (0:ℝ) b := by
      rw [uIcc_of_le heb.le]
      intro t ht
      exact ⟨he0.trans_le ht.1,ht.2⟩
    have hpcont : ContinuousOn (fun t : ℝ => (t:ℂ)^(u-1)) (uIcc e b) := by
      intro t ht
      exact ((Complex.hasStrictDerivAt_cpow_const (c := u-1)
        (show (t:ℂ) ∈ Complex.slitPlane by simp [Complex.mem_slitPlane_iff,(hsubset ht).1])).hasDerivAt.comp_ofReal).continuousAt.continuousWithinAt
    have hiN : IntervalIntegrable (fun t : ℝ => (t:ℂ)^(u-1)*incomingPairingFactor u chi t) volume e b :=
      (hpcont.mul ((hMcont u).mono hsubset)).intervalIntegrable
    have hiJ : IntervalIntegrable (fun t : ℝ => (t:ℂ)^(u-1)*
        (incomingSourcePrimitive s chi a J K u t*incomingPairingFactor u chi t)) volume e b :=
      (hpcont.mul (hPMcont.mono hsubset)).intervalIntegrable
    have hsplit : (∫ z in e..b, continuedResponse s chi a J K z u*horizon u chi z/
        (2*(z:ℂ)*(Real.sqrt (1-z):ℂ)))=
        incomingResponseEndpoint s chi a J K u b*(∫ z in e..b, (z:ℂ)^(u-1)*incomingPairingFactor u chi z)+
        (∫ z in e..b, (z:ℂ)^(u-1)*(incomingSourcePrimitive s chi a J K u z*incomingPairingFactor u chi z)) := by
      rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_add (hiN.const_mul _) hiJ,
        intervalIntegral.integral_of_le heb.le,intervalIntegral.integral_of_le heb.le]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro z hz
      have hz' : z ∈ Ioc (0:ℝ) b := ⟨he0.trans hz.1,hz.2⟩
      dsimp only
      rw [← incomingResponsePairingCore_density s chi a J K u
        ⟨hz'.1,lt_of_le_of_lt (hz'.2.trans hbhalf) (by norm_num)⟩]
      unfold incomingResponsePairingCore
      rw [(hdata z hz').2.2.2 hconn]
      ring
    rw [hsplit]
    ring

/-- The original restoration statement follows at the supplied upper cutoff. -/
theorem incomingPairingFinitePart_horizon_restoration (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (hs : w-2*s ≠ 0) :
    ∃ R b : ℝ, 0 < R ∧ 0 < b ∧ b ≤ 1/2 ∧
      AnalyticAt ℂ (incomingNormFinitePart chi b) w ∧
      AnalyticAt ℂ (incomingSourcePairingFinitePart s chi a J K b) w ∧
      AnalyticAt ℂ (fun u => incomingSourcePrimitive s chi a J K u b) w ∧
      ∀ u ∈ ball w R, connection u chi ≠ 0 →
        Tendsto (fun e : ℝ =>
          (∫ z in e..b, continuedResponse s chi a J K z u*horizon u chi z/
            (2*(z:ℂ)*(Real.sqrt (1-z):ℂ)))+
          (incomingResponseEndpoint s chi a J K u b/2)*(e:ℂ)^u/u+
          ((horizonGaussFirstCoefficient u chi+1/4)*incomingResponseEndpoint s chi a J K u b+
            incomingResponseSlope s a J K u/2)*(e:ℂ)^(u+1)/(u+1))
          (𝓝[>] (0:ℝ)) (𝓝 (incomingPairingFinitePart s chi a J K b u)) := by
  obtain ⟨R,b,hR,hb,hbhalf,hsmall⟩ := incomingPairingFinitePart_horizon_restoration_below s chi a J K w hw hwr hs
  exact ⟨R,b,hR,hb,hbhalf,hsmall b hb le_rfl⟩

end
end RHTower.D4BMLaplaceRadial
