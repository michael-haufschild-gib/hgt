import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOppositePairingFactor
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMIncomingHorizonExpansion
import GaloisForLFunctions.HTGeometry.LogarithmicEndpointFinitePart

/-! Source-derived logarithmic restoration for the original opposite-horizon pairing. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Set Filter Topology Metric MeasureTheory GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def oppositeNormFinitePart (chi : ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  LogarithmicEndpoint.finitePart (fun u => oppositePairingFactor u chi) (fun _ => 1/2) b w

def oppositeSourcePairingFinitePart (s chi a J K : ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  LogarithmicEndpoint.finitePart
    (fun u z => incomingSourcePrimitive s chi a J K u z*oppositePairingFactor u chi z) (fun _ => 0) b w

def oppositePairingFinitePart (s chi a J K : ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  (connection w chi/(2*w))*(incomingResponseEndpoint s chi a J K w b*oppositeNormFinitePart chi b w+
    oppositeSourcePairingFinitePart s chi a J K b w)

private theorem opposite_common_data (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (hs : w-2*s ≠ 0) :
    ∃ R b C M : ℝ, 0 < R ∧ 0 < b ∧ b ≤ 1/2 ∧ 0 ≤ C ∧ 0 ≤ M ∧
      ∀ u ∈ ball w R, u.im ≠ 0 ∧ u-2*s ≠ 0 ∧
        ContinuousOn (incomingSourcePrimitive s chi a J K u) (Icc (0:ℝ) b) ∧
        ∀ z ∈ Ioc (0:ℝ) b,
          horizon u chi z ≠ 0 ∧
          AnalyticAt ℂ (fun v => incomingSourcePrimitive s chi a J K v z) u ∧
          ‖oppositePairingFactor u chi z-(1/2:ℂ)‖ ≤ C*z ∧
          ‖incomingSourcePrimitive s chi a J K u z*oppositePairingFactor u chi z‖ ≤ M*z ∧
          (connection u chi ≠ 0 → continuedResponse s chi a J K z u/horizon u chi z=
            incomingResponseEndpoint s chi a J K u b+incomingSourcePrimitive s chi a J K u z) := by
  obtain ⟨RP,bP,CP,MP,hRP,hbP,hbPhalf,_,hMP,hP⟩ := incomingSourcePrimitive_common_data s chi a J K w hw hwr hs
  obtain ⟨RG,bG,CG,hRG,hbG,_,_,hG⟩ := horizonGauss_uniform_nonzero w chi hw
  obtain ⟨RV,CV,MV,hRV,hCV,hMV,hV⟩ := oppositePairingFactor_uniform_first_bound w chi hw
  let R := min RP (min RG RV)
  let b := min bP bG
  have hR : 0 < R := lt_min hRP (lt_min hRG hRV)
  have hb : 0 < b := lt_min hbP hbG
  have hbp : b ≤ bP := min_le_left _ _
  have hbg : b ≤ bG := min_le_right _ _
  have hbhalf : b ≤ 1/2 := hbp.trans hbPhalf
  refine ⟨R,b,CV,MP*MV,hR,hb,hbhalf,hCV,mul_nonneg hMP hMV,?_⟩
  intro u hu
  have huP := ball_subset_ball (min_le_left RP (min RG RV)) hu
  have huG : u ∈ ball w RG := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hu
  have huV : u ∈ ball w RV := ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hu
  obtain ⟨hui,_,hus,hPc,hPd⟩ := hP u huP
  refine ⟨hui,hus,hPc.mono (Icc_subset_Icc le_rfl hbp),?_⟩
  intro z hz
  have hzP : z ∈ Ioc (0:ℝ) bP := ⟨hz.1,hz.2.trans hbp⟩
  obtain ⟨hPa,hPn,_,hQz⟩ := hPd z hzP
  have hGauss : gaussFactor u chi false (z:ℂ) ≠ 0 := by
    have hh := (hG u huG z ⟨hz.1.le,hz.2.trans hbg⟩).2.1
    exact norm_pos_iff.mp (by linarith)
  have hh : horizon u chi z ≠ 0 := mul_ne_zero (power_ne_zero _ hz.1) hGauss
  obtain ⟨hVe,hVn⟩ := hV u huV z ⟨hz.1.le,hz.2.trans hbhalf⟩
  refine ⟨hh,hPa,hVe,?_,?_⟩
  · rw [norm_mul]
    calc
      _ ≤ (MP*z)*MV := mul_le_mul hPn hVn (norm_nonneg _) (mul_nonneg hMP hz.1.le)
      _ = MP*MV*z := by ring
  · intro hc
    have hQb := (hPd b ⟨hb,hbp⟩).2.2.2 hc
    change continuedResponse s chi a J K z u/horizon u chi z=
      (continuedResponse s chi a J K b u/horizon u chi b-incomingSourcePrimitive s chi a J K u b)+
        incomingSourcePrimitive s chi a J K u z
    rw [hQz hc,hQb]
    ring

/-- The original opposite left-mode block has its actual logarithmic cutoff limit and analytic restored factors at every sufficiently small source-derived radius. -/
theorem oppositePairingFinitePart_horizon_restoration_below (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (hs : w-2*s ≠ 0) :
    ∃ R B : ℝ, 0 < R ∧ 0 < B ∧ B ≤ 1/2 ∧
      ∀ b : ℝ, 0 < b → b ≤ B →
      AnalyticAt ℂ (oppositeNormFinitePart chi b) w ∧
      AnalyticAt ℂ (oppositeSourcePairingFinitePart s chi a J K b) w ∧
      AnalyticAt ℂ (fun u => incomingSourcePrimitive s chi a J K u b) w ∧
      ∀ u ∈ ball w R, connection u chi ≠ 0 →
        Tendsto (fun e : ℝ =>
          (∫ z in e..b, (connection u chi/(2*u))*(continuedResponse s chi a J K z u*horizon (-u) chi z/
            (2*(z:ℂ)*(Real.sqrt (1-z):ℂ))))+
          (connection u chi/(2*u))*(incomingResponseEndpoint s chi a J K u b/2)*(Real.log e:ℂ))
          (𝓝[>] (0:ℝ)) (𝓝 (oppositePairingFinitePart s chi a J K b u)) := by
  obtain ⟨R,B,C,M,hR,hB,hBhalf,hC,hM,hbig⟩ := opposite_common_data s chi a J K w hw hwr hs
  refine ⟨R,B,hR,hB,hBhalf,?_⟩
  intro b hb hbB
  have hbhalf : b ≤ 1/2 := hbB.trans hBhalf
  have hdata (u : ℂ) (hu : u ∈ ball w R) :
      u.im ≠ 0 ∧ u-2*s ≠ 0 ∧
      ContinuousOn (incomingSourcePrimitive s chi a J K u) (Icc (0:ℝ) b) ∧
      ∀ z ∈ Ioc (0:ℝ) b,
        horizon u chi z ≠ 0 ∧
        AnalyticAt ℂ (fun v => incomingSourcePrimitive s chi a J K v z) u ∧
        ‖oppositePairingFactor u chi z-(1/2:ℂ)‖ ≤ C*z ∧
        ‖incomingSourcePrimitive s chi a J K u z*oppositePairingFactor u chi z‖ ≤ M*z ∧
        (connection u chi ≠ 0 → continuedResponse s chi a J K z u/horizon u chi z=
          incomingResponseEndpoint s chi a J K u b+incomingSourcePrimitive s chi a J K u z) := by
    obtain ⟨hui,hus,hPc,hpoint⟩ := hbig u hu
    refine ⟨hui,hus,hPc.mono (Icc_subset_Icc le_rfl hbB),?_⟩
    intro z hz
    obtain ⟨hH,hPa,hV,hP,hQz⟩ := hpoint z ⟨hz.1,hz.2.trans hbB⟩
    refine ⟨hH,hPa,hV,hP,?_⟩
    intro hc
    have hQb := (hpoint b ⟨hb,hbB⟩).2.2.2.2 hc
    change continuedResponse s chi a J K z u/horizon u chi z=
      (continuedResponse s chi a J K b u/horizon u chi b-incomingSourcePrimitive s chi a J K u b)+
        incomingSourcePrimitive s chi a J K u z
    rw [hQz hc,hQb]
    ring
  have hVcont (u : ℂ) : ContinuousOn (oppositePairingFactor u chi) (Ioc (0:ℝ) b) := by
    intro z hz
    exact (oppositePairingFactor_continuousAt u chi
      ⟨hz.1,lt_of_le_of_lt (hz.2.trans hbhalf) (by norm_num)⟩).continuousWithinAt
  refine ⟨?_,?_,?_,?_⟩
  · unfold oppositeNormFinitePart
    apply LogarithmicEndpoint.finitePart_analyticAt hR
    · intro u _; exact hVcont u
    · intro u _; exact analyticAt_const
    · intro z hz u hu
      exact oppositePairingFactor_analyticAt u chi (hdata u hu).1
        ⟨hz.1,lt_of_le_of_lt (hz.2.trans hbhalf) (by norm_num)⟩
    · intro u hu z hz; exact ((hdata u hu).2.2.2 z hz).2.2.1
  · unfold oppositeSourcePairingFinitePart
    apply LogarithmicEndpoint.finitePart_analyticAt hR
    · intro u hu
      exact (((hdata u hu).2.2.1).mono Ioc_subset_Icc_self).mul (hVcont u)
    · intro u _; exact analyticAt_const
    · intro z hz u hu
      exact (((hdata u hu).2.2.2 z hz).2.1).mul
        (oppositePairingFactor_analyticAt u chi (hdata u hu).1
          ⟨hz.1,lt_of_le_of_lt (hz.2.trans hbhalf) (by norm_num)⟩)
    · intro u hu z hz
      simpa only [sub_zero] using ((hdata u hu).2.2.2 z hz).2.2.2.1
  · exact ((hdata w (mem_ball_self hR)).2.2.2 b ⟨hb,le_rfl⟩).2.1
  · intro u hu hc
    obtain ⟨_,_,hPc,hpoint⟩ := hdata u hu
    have hPVcont : ContinuousOn (fun z => incomingSourcePrimitive s chi a J K u z*oppositePairingFactor u chi z) (Ioc (0:ℝ) b) :=
      (hPc.mono Ioc_subset_Icc_self).mul (hVcont u)
    have hLN := LogarithmicEndpoint.cutoff_tendsto
      (F := fun v => oppositePairingFactor v chi) (a₀ := fun _ => 1/2) (w := u) hb (hVcont u)
      (fun z hz => (hpoint z hz).2.2.1)
    have hLK := LogarithmicEndpoint.cutoff_tendsto
      (F := fun v z => incomingSourcePrimitive s chi a J K v z*oppositePairingFactor v chi z)
      (a₀ := fun _ => 0) (w := u) hb hPVcont
      (fun z hz => by simpa only [sub_zero] using (hpoint z hz).2.2.2.1)
    have hlim := ((hLN.const_mul (incomingResponseEndpoint s chi a J K u b)).add hLK).const_mul (connection u chi/(2*u))
    change Tendsto _ (𝓝[>] (0:ℝ)) (𝓝 (oppositePairingFinitePart s chi a J K b u)) at hlim
    apply hlim.congr'
    have he : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e < b :=
      (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < b from Iio_mem_nhds hb).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,he] with e he0 heb
    have hsub : uIcc e b ⊆ Ioc (0:ℝ) b := by
      rw [uIcc_of_le heb.le]
      intro t ht; exact ⟨he0.trans_le ht.1,ht.2⟩
    have hden (t : ℝ) (ht : t ∈ uIcc e b) : (t:ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (hsub ht).1)
    have hci : ContinuousOn (fun t : ℝ => (t:ℂ)) (uIcc e b) := by fun_prop
    have hiN : IntervalIntegrable (fun z : ℝ => oppositePairingFactor u chi z/(z:ℂ)) volume e b :=
      (((hVcont u).mono hsub).div hci hden).intervalIntegrable
    have hiK : IntervalIntegrable (fun z : ℝ =>
        (incomingSourcePrimitive s chi a J K u z*oppositePairingFactor u chi z)/(z:ℂ)) volume e b :=
      ((hPVcont.mono hsub).div hci hden).intervalIntegrable
    have hsplit : (∫ z in e..b, continuedResponse s chi a J K z u*horizon (-u) chi z/
        (2*(z:ℂ)*(Real.sqrt (1-z):ℂ)))=
      incomingResponseEndpoint s chi a J K u b*(∫ z in e..b, oppositePairingFactor u chi z/(z:ℂ))+
      (∫ z in e..b, (incomingSourcePrimitive s chi a J K u z*oppositePairingFactor u chi z)/(z:ℂ)) := by
      rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_add (hiN.const_mul _) hiK,
        intervalIntegral.integral_of_le heb.le,intervalIntegral.integral_of_le heb.le]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro z hz
      have hz' : z ∈ Ioc (0:ℝ) b := ⟨he0.trans hz.1,hz.2⟩
      dsimp only
      rw [← oppositePairingFactor_density s chi a J K u
        ⟨hz'.1,lt_of_le_of_lt (hz'.2.trans hbhalf) (by norm_num)⟩ (hpoint z hz').1,
        (hpoint z hz').2.2.2.2 hc]
      ring
    rw [intervalIntegral.integral_const_mul,hsplit]
    ring

/-- The original restoration statement follows at the supplied upper cutoff. -/
theorem oppositePairingFinitePart_horizon_restoration (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (hs : w-2*s ≠ 0) :
    ∃ R b : ℝ, 0 < R ∧ 0 < b ∧ b ≤ 1/2 ∧
      AnalyticAt ℂ (oppositeNormFinitePart chi b) w ∧
      AnalyticAt ℂ (oppositeSourcePairingFinitePart s chi a J K b) w ∧
      AnalyticAt ℂ (fun u => incomingSourcePrimitive s chi a J K u b) w ∧
      ∀ u ∈ ball w R, connection u chi ≠ 0 →
        Tendsto (fun e : ℝ =>
          (∫ z in e..b, (connection u chi/(2*u))*(continuedResponse s chi a J K z u*horizon (-u) chi z/
            (2*(z:ℂ)*(Real.sqrt (1-z):ℂ))))+
          (connection u chi/(2*u))*(incomingResponseEndpoint s chi a J K u b/2)*(Real.log e:ℂ))
          (𝓝[>] (0:ℝ)) (𝓝 (oppositePairingFinitePart s chi a J K b u)) := by
  obtain ⟨R,b,hR,hb,hbhalf,hsmall⟩ := oppositePairingFinitePart_horizon_restoration_below s chi a J K w hw hwr hs
  exact ⟨R,b,hR,hb,hbhalf,hsmall b hb le_rfl⟩

end
end RHTower.D4BMLaplaceRadial
