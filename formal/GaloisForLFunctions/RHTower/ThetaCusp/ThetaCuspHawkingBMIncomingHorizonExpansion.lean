import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMIncomingSourceBound

/-! The original Green quotient has a source-determined horizon coefficient and quadratic remainder. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The endpoint coefficient is fixed by the actual response at a positive radius and its source transport. -/
def incomingResponseEndpoint (s chi a J K w : ℂ) (b : ℝ) : ℂ :=
  continuedResponse s chi a J K b w/horizon w chi b-
    ∫ t in 0..b, incomingSourceTransport s chi a J K w t

private theorem primitive_quadratic_bound {f f' : ℝ → ℂ} {d : ℂ} {b C : ℝ}
    (hC0 : 0 ≤ C) (hf : ∀ t ∈ Ioc (0:ℝ) b, HasDerivAt f (f' t) t)
    (hi : IntervalIntegrable f' volume 0 b)
    (hC : ∀ t ∈ Ioc (0:ℝ) b, ‖f' t-d‖ ≤ C*t)
    {z : ℝ} (hz : z ∈ Ioc (0:ℝ) b) :
    ‖f z-(f b-∫ t in 0..b, f' t)-d*(z:ℂ)‖ ≤ C*z^(2 : ℕ) := by
  have hiz : IntervalIntegrable f' volume 0 z := hi.mono_set (by
    rw [uIcc_of_le (hz.1.le.trans hz.2),uIcc_of_le hz.1.le]
    exact Icc_subset_Icc le_rfl hz.2)
  have hzb : IntervalIntegrable f' volume z b := hi.mono_set (by
    rw [uIcc_of_le (hz.1.le.trans hz.2),uIcc_of_le hz.2]
    exact Icc_subset_Icc hz.1.le le_rfl)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hf t (by
      rw [uIcc_of_le hz.2] at ht
      exact ⟨hz.1.trans_le ht.1,ht.2⟩)) hzb
  have hadd := intervalIntegral.integral_add_adjacent_intervals hiz hzb
  have heq : f z-(f b-∫ t in 0..b, f' t)-d*(z:ℂ)=∫ t in 0..z, f' t-d := by
    rw [intervalIntegral.integral_sub hiz intervalIntegrable_const,intervalIntegral.integral_const]
    simp only [sub_zero,Complex.real_smul]
    rw [← hadd,hFTC]
    ring
  rw [heq]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := z)
    (f := fun t => f' t-d) (C := C*z) (fun t ht => by
      rw [uIoc_of_le hz.1.le] at ht
      exact (hC t ⟨ht.1,ht.2.trans hz.2⟩).trans (mul_le_mul_of_nonneg_left ht.2 hC0))
  simpa only [sub_zero,abs_of_pos hz.1,pow_two,mul_assoc] using hn

private theorem source_horizon_value_continuous (s a J K w : ℂ)
    (hw : w.im ≠ 0) (hs : w-2*s ≠ 0) :
    ContinuousAt (fun u : ℂ => sourceRemainder s u a J K 1 0*
      (1/(u-2*s)+onsetCorrection (2*s) u)/(2*(u+1))) w := by
  have hw1 : w+1 ≠ 0 := by intro h; apply hw; have hi := congrArg Complex.im h; simpa using hi
  have hS := (sourceRemainder_frequency_entire s a J K 1 0).continuous.continuousAt (x := w)
  have hA : ContinuousAt (fun u : ℂ => 1/(u-2*s)+onsetCorrection (2*s) u) w :=
    ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) hs).add
      ((onsetCorrection_entire (2*s)).analyticAt w)).continuousAt
  exact (hS.mul hA).div (by fun_prop) (mul_ne_zero (by norm_num) hw1)

private theorem source_transport_common_neighborhood (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (hs : w-2*s ≠ 0) :
    ∃ R b C M : ℝ, 0 < R ∧ 0 < b ∧ b ≤ 1/2 ∧ 0 ≤ C ∧ 0 ≤ M ∧
      ∀ u ∈ ball w R, u.im ≠ 0 ∧ -2 < u.re ∧ u-2*s ≠ 0 ∧
        ∀ z ∈ Ioc (0:ℝ) b, horizon u chi z ≠ 0 ∧
          ‖incomingSourceTransport s chi a J K u z‖ ≤ M ∧
          ‖incomingSourceTransport s chi a J K u z-
            sourceRemainder s u a J K 1 0*(1/(u-2*s)+onsetCorrection (2*s) u)/(2*(u+1))‖ ≤ C*z := by
  obtain ⟨RT,bT,C,hRT,hbT,hbThalf,hC,hT⟩ := incomingSourceTransport_uniform_first_bound s chi a J K w hw hwr hs
  obtain ⟨RG,bG,CG,hRG,hbG,hbGhalf,_,hG⟩ := horizonGauss_uniform_nonzero w chi hw
  let d := fun u : ℂ => sourceRemainder s u a J K 1 0*(1/(u-2*s)+onsetCorrection (2*s) u)/(2*(u+1))
  let Md := ‖d w‖+1
  have hi := Complex.continuous_im.continuousAt.eventually_ne hw
  have hr := Complex.continuous_re.continuousAt.eventually_const_lt hwr
  have hs' := (show ContinuousAt (fun u : ℂ => u-2*s) w by fun_prop).eventually_ne hs
  have hd : ∀ᶠ u in 𝓝 w, ‖d u‖ < Md :=
    (source_horizon_value_continuous s a J K w hw hs).norm.eventually_lt continuousAt_const
      (by dsimp [Md]; linarith)
  obtain ⟨R,hR,hall⟩ := Metric.eventually_nhds_iff.mp (hi.and (hr.and (hs'.and hd)))
  let R0 := min R (min RT RG)
  let b := min bT bG
  let M := C*b+Md
  have hb : 0 < b := lt_min hbT hbG
  have hM : 0 ≤ M := by dsimp [M,Md]; positivity
  refine ⟨R0,b,C,M,lt_min hR (lt_min hRT hRG),hb,(min_le_left _ _).trans hbThalf,hC,hM,?_⟩
  intro u hu
  have huR : u ∈ ball w R := ball_subset_ball (min_le_left _ _) hu
  have huT : u ∈ ball w RT := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hu
  have huG : u ∈ ball w RG := ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hu
  obtain ⟨hui,hur,hus,hud⟩ := hall (mem_ball.mp huR)
  refine ⟨hui,hur,hus,?_⟩
  intro z hz
  have hzn : gaussFactor u chi false (z:ℂ) ≠ 0 := by
    have hn := (hG u huG z ⟨hz.1.le,hz.2.trans (min_le_right _ _)⟩).2.1
    exact norm_pos_iff.mp (by linarith)
  have hh : horizon u chi z ≠ 0 := by
    exact mul_ne_zero (power_ne_zero _ hz.1) hzn
  have he := hT u huT z ⟨hz.1,hz.2.trans (min_le_left _ _)⟩
  refine ⟨hh,?_,he⟩
  calc
    _ ≤ ‖incomingSourceTransport s chi a J K u z-d u‖+‖d u‖ := by
      have hn := norm_sub_norm_le (incomingSourceTransport s chi a J K u z) (d u)
      linarith
    _ ≤ C*z+Md := add_le_add he hud.le
    _ ≤ M := by dsimp [M]; linarith [mul_le_mul_of_nonneg_left hz.2 hC]

/-- The original response divided by its incoming mode has a uniform quadratic horizon expansion on the punctured connection germ. -/
theorem continuedResponse_horizon_quadratic_expansion (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (hs : w-2*s ≠ 0) :
    ∃ R b C : ℝ, 0 < R ∧ 0 < b ∧ b ≤ 1/2 ∧ 0 ≤ C ∧
      ∀ u ∈ ball w R, connection u chi ≠ 0 → ∀ z ∈ Ioc (0:ℝ) b,
        ‖continuedResponse s chi a J K z u/horizon u chi z-incomingResponseEndpoint s chi a J K u b-
          (sourceRemainder s u a J K 1 0*(1/(u-2*s)+onsetCorrection (2*s) u)/(2*(u+1)))*(z:ℂ)‖ ≤ C*z^(2 : ℕ) := by
  obtain ⟨R,b,C,M,hR,hb,hbhalf,hC,_,hbound⟩ := source_transport_common_neighborhood s chi a J K w hw hwr hs
  refine ⟨R,b,C,hR,hb,hbhalf,hC,?_⟩
  intro u hu hc z hz
  obtain ⟨hui,hur,_,ht⟩ := hbound u hu
  have hcont : ContinuousOn (incomingSourceTransport s chi a J K u) (Ioc (0:ℝ) b) := by
    intro t ht'
    exact (incomingSourceTransport_continuousAt s chi a J K u hui hur
      ⟨ht'.1,lt_of_le_of_lt (ht'.2.trans hbhalf) (by norm_num)⟩ (ht t ht').1).continuousWithinAt
  have hint : IntervalIntegrable (incomingSourceTransport s chi a J K u) volume 0 b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr
    exact Integrable.mono' (integrable_const M)
      (hcont.aestronglyMeasurable measurableSet_Ioc)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht'; exact (ht t ht').2.1)
  exact primitive_quadratic_bound hC
    (fun t ht' => continuedResponse_div_horizon_hasDerivAt s chi a J K u hui hur hc
      ⟨ht'.1,lt_of_le_of_lt (ht'.2.trans hbhalf) (by norm_num)⟩ (ht t ht').1)
    hint (fun t ht' => (ht t ht').2.2) hz

private theorem analyticAt_intervalIntegral_of_uniform_bound {F : ℂ → ℝ → ℂ}
    {w : ℂ} {R b M : ℝ} (hR : 0 < R) (hb : 0 ≤ b) (_hM : 0 ≤ M)
    (hc : ∀ u ∈ ball w R, ContinuousOn (F u) (Ioc (0:ℝ) b))
    (ha : ∀ t ∈ Ioc (0:ℝ) b, ∀ u ∈ ball w R, AnalyticAt ℂ (fun v => F v t) u)
    (hn : ∀ u ∈ ball w R, ∀ t ∈ Ioc (0:ℝ) b, ‖F u t‖ ≤ M) :
    AnalyticAt ℂ (fun u => ∫ t in 0..b, F u t) w := by
  let G := fun u : ℂ => (Ioc (0:ℝ) b).indicator (F u)
  let B := (Ioc (0:ℝ) b).indicator (fun _ : ℝ => M)
  have hmeas (u : ℂ) (hu : u ∈ ball w R) : AEStronglyMeasurable (G u) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ioc).mpr
      ((hc u hu).aestronglyMeasurable measurableSet_Ioc)
  have hdiff (t : ℝ) : DifferentiableOn ℂ (fun u => G u t) (ball w R) := by
    intro u hu
    by_cases ht : t ∈ Ioc (0:ℝ) b
    · simpa only [G,indicator_of_mem ht] using (ha t ht u hu).differentiableAt.differentiableWithinAt
    · simp only [G,indicator_of_notMem ht]
      fun_prop
  have hbound (t : ℝ) (u : ℂ) (hu : u ∈ ball w R) : ‖G u t‖ ≤ B t := by
    by_cases ht : t ∈ Ioc (0:ℝ) b
    · simpa only [G,B,indicator_of_mem ht] using hn u hu t ht
    · simp only [G,B,indicator_of_notMem ht,norm_zero,le_refl]
  have hBI : Integrable B volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (integrable_const M)
  have hDI : DifferentiableOn ℂ (fun u => ∫ t, G u t) (ball w R) := by
    intro v hv
    obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hv)
    exact (differentiableAt_integral_of_cauchy_dominated hr
      (fun u hu => hmeas u (hsub hu)) (fun t => (hdiff t).mono hsub)
      (fun t u hu => hbound t u (hsub hu)) hBI).differentiableWithinAt
  have hA := hDI.analyticOnNhd isOpen_ball w (mem_ball_self hR)
  simpa only [G,integral_indicator measurableSet_Ioc,intervalIntegral.integral_of_le hb] using hA

/-- Integration of the actual source transport reaches the horizon holomorphically; the endpoint coefficient inherits only the original response poles. -/
theorem incomingResponseEndpoint_meromorphic (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (hs : w-2*s ≠ 0) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1/2 ∧
      AnalyticAt ℂ (fun u => ∫ t in 0..b, incomingSourceTransport s chi a J K u t) w ∧
      MeromorphicAt (fun u => incomingResponseEndpoint s chi a J K u b) w := by
  obtain ⟨R,b,C,M,hR,hb,hbhalf,_,hM,hbound⟩ := source_transport_common_neighborhood s chi a J K w hw hwr hs
  have hi : AnalyticAt ℂ (fun u => ∫ t in 0..b, incomingSourceTransport s chi a J K u t) w := by
    apply analyticAt_intervalIntegral_of_uniform_bound hR hb.le hM
    · intro u hu t ht
      obtain ⟨hui,hur,_,hts⟩ := hbound u hu
      exact (incomingSourceTransport_continuousAt s chi a J K u hui hur
        ⟨ht.1,lt_of_le_of_lt (ht.2.trans hbhalf) (by norm_num)⟩ (hts t ht).1).continuousWithinAt
    · intro t ht u hu
      obtain ⟨hui,hur,hus,hts⟩ := hbound u hu
      exact incomingSourceTransport_analyticAt s chi a J K u hui hur hus
        ⟨ht.1,lt_of_le_of_lt (ht.2.trans hbhalf) (by norm_num)⟩ (hts t ht).1
    · intro u hu t ht
      exact ((hbound u hu).2.2.2 t ht).2.1
  refine ⟨b,hb,hbhalf,hi,?_⟩
  have hb1 : b < 1 := lt_of_le_of_lt hbhalf (by norm_num)
  exact ((continuedResponse_meromorphicAt s chi a J K w hw hwr hb hb1).div
    (horizon_frequency_analyticAt w chi hw ⟨hb,hb1⟩).meromorphicAt).sub hi.meromorphicAt


/-- The original source transport integrated from the actual horizon. -/
def incomingSourcePrimitive (s chi a J K w : ℂ) (z : ℝ) : ℂ :=
  ∫ t in 0..z, incomingSourceTransport s chi a J K w t

/-- A single derived neighborhood supplies the exact Green split, analytic source primitive,
spatial continuity, and its uniform quadratic remainder through connection zeros. -/
theorem incomingSourcePrimitive_common_data (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (hs : w-2*s ≠ 0) :
    ∃ R b C M : ℝ, 0 < R ∧ 0 < b ∧ b ≤ 1/2 ∧ 0 ≤ C ∧ 0 ≤ M ∧
      ∀ u ∈ ball w R, u.im ≠ 0 ∧ -2 < u.re ∧ u-2*s ≠ 0 ∧
        ContinuousOn (incomingSourcePrimitive s chi a J K u) (Icc (0:ℝ) b) ∧
        ∀ z ∈ Ioc (0:ℝ) b,
          AnalyticAt ℂ (fun v => incomingSourcePrimitive s chi a J K v z) u ∧
          ‖incomingSourcePrimitive s chi a J K u z‖ ≤ M*z ∧
          ‖incomingSourcePrimitive s chi a J K u z-
            (sourceRemainder s u a J K 1 0*(1/(u-2*s)+onsetCorrection (2*s) u)/(2*(u+1)))*(z:ℂ)‖ ≤ C*z^(2 : ℕ) ∧
          (connection u chi ≠ 0 → continuedResponse s chi a J K z u/horizon u chi z=
            incomingResponseEndpoint s chi a J K u b+incomingSourcePrimitive s chi a J K u z) := by
  obtain ⟨R,b,C,M,hR,hb,hbhalf,hC,hM,hbound⟩ := source_transport_common_neighborhood s chi a J K w hw hwr hs
  have hcont (u : ℂ) (hu : u ∈ ball w R) :
      ContinuousOn (incomingSourceTransport s chi a J K u) (Ioc (0:ℝ) b) := by
    intro t ht
    obtain ⟨hui,hur,_,hbds⟩ := hbound u hu
    exact (incomingSourceTransport_continuousAt s chi a J K u hui hur
      ⟨ht.1,lt_of_le_of_lt (ht.2.trans hbhalf) (by norm_num)⟩ (hbds t ht).1).continuousWithinAt
  have hint (u : ℂ) (hu : u ∈ ball w R) :
      IntervalIntegrable (incomingSourceTransport s chi a J K u) volume 0 b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr
    exact Integrable.mono' (integrable_const M)
      ((hcont u hu).aestronglyMeasurable measurableSet_Ioc)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact ((hbound u hu).2.2.2 t ht).2.1)
  refine ⟨R,b,C,M,hR,hb,hbhalf,hC,hM,?_⟩
  intro u hu
  obtain ⟨hui,hur,hus,hbds⟩ := hbound u hu
  have hi := hint u hu
  have hPcont : ContinuousOn (incomingSourcePrimitive s chi a J K u) (Icc (0:ℝ) b) := by
    have hp := intervalIntegral.continuousOn_primitive_interval' hi (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 b)
    change ContinuousOn (fun z : ℝ => ∫ t in 0..z, incomingSourceTransport s chi a J K u t) (Icc (0:ℝ) b)
    simpa only [uIcc_of_le hb.le] using hp
  refine ⟨hui,hur,hus,hPcont,?_⟩
  intro z hz
  have hiz : IntervalIntegrable (incomingSourceTransport s chi a J K u) volume 0 z :=
    hi.mono_set (by rw [uIcc_of_le hb.le,uIcc_of_le hz.1.le]; exact Icc_subset_Icc le_rfl hz.2)
  refine ⟨?_,?_,?_,?_⟩
  · obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hu)
    apply analyticAt_intervalIntegral_of_uniform_bound hr hz.1.le hM
    · intro v hv
      exact (hcont v (hsub hv)).mono (Ioc_subset_Ioc_right hz.2)
    · intro t ht v hv
      obtain ⟨hvi,hvr,hvs,hvb⟩ := hbound v (hsub hv)
      exact incomingSourceTransport_analyticAt s chi a J K v hvi hvr hvs
        ⟨ht.1,lt_of_le_of_lt (ht.2.trans (hz.2.trans hbhalf)) (by norm_num)⟩
        (hvb t ⟨ht.1,ht.2.trans hz.2⟩).1
    · intro v hv t ht
      exact ((hbound v (hsub hv)).2.2.2 t ⟨ht.1,ht.2.trans hz.2⟩).2.1
  · have hn := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := z)
      (f := incomingSourceTransport s chi a J K u) (C := M) (fun t ht => by
        rw [uIoc_of_le hz.1.le] at ht
        exact (hbds t ⟨ht.1,ht.2.trans hz.2⟩).2.1)
    simpa only [incomingSourcePrimitive,sub_zero,abs_of_pos hz.1,mul_comm] using hn
  · let d := sourceRemainder s u a J K 1 0*(1/(u-2*s)+onsetCorrection (2*s) u)/(2*(u+1))
    have he : incomingSourcePrimitive s chi a J K u z-d*(z:ℂ)=
        ∫ t in 0..z, incomingSourceTransport s chi a J K u t-d := by
      rw [intervalIntegral.integral_sub hiz intervalIntegrable_const,intervalIntegral.integral_const]
      simp only [incomingSourcePrimitive,sub_zero,Complex.real_smul]
      ring
    change ‖incomingSourcePrimitive s chi a J K u z-d*(z:ℂ)‖ ≤ C*z^(2 : ℕ)
    rw [he]
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := z)
      (f := fun t => incomingSourceTransport s chi a J K u t-d) (C := C*z) (fun t ht => by
        rw [uIoc_of_le hz.1.le] at ht
        exact ((hbds t ⟨ht.1,ht.2.trans hz.2⟩).2.2).trans
          (mul_le_mul_of_nonneg_left ht.2 hC))
    simpa only [sub_zero,abs_of_pos hz.1,pow_two,mul_assoc] using hn
  · intro hc
    have hzb : IntervalIntegrable (incomingSourceTransport s chi a J K u) volume z b :=
      hi.mono_set (by rw [uIcc_of_le hb.le,uIcc_of_le hz.2]; exact Icc_subset_Icc hz.1.le le_rfl)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => continuedResponse_div_horizon_hasDerivAt s chi a J K u hui hur hc
        (show t ∈ Ioo (0:ℝ) 1 from by
          rw [uIcc_of_le hz.2] at ht
          exact ⟨hz.1.trans_le ht.1,lt_of_le_of_lt (ht.2.trans hbhalf) (by norm_num)⟩)
        (hbds t (by rw [uIcc_of_le hz.2] at ht; exact ⟨hz.1.trans_le ht.1,ht.2⟩)).1) hzb
    have hadd := intervalIntegral.integral_add_adjacent_intervals hiz hzb
    unfold incomingResponseEndpoint incomingSourcePrimitive
    rw [← hadd,hFTC]
    ring

end
end RHTower.D4BMLaplaceRadial
