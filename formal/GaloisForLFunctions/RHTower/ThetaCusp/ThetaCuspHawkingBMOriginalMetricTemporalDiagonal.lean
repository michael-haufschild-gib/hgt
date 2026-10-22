import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalRegularizedSourceResolvent
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceOuterEndpointBounds

/-! The full original metric and temporal-corner diagonal in the source resolvent. -/
open Set Filter Topology MeasureTheory Metric
namespace RHTower.D4BMOriginalSourceResolvent
open D4BMLaplaceRadial D4BMOriginalHorizonGreenMatch D4BMModularCore
noncomputable section
set_option autoImplicit false

/-- The original fixed-source outer pairing is continuous in its independent
reader, including the physical outer endpoint. -/
theorem mixedOuterIntegral_continuousAt (s chi amp J K w v : ℂ)
    (hw : Chamber w chi) (hwi : w.im≠0) (hs : (2*s).re<w.re)
    {b : ℝ} (hb : 0<b) (hb1 : b<1) :
    ContinuousAt (fun u : ℂ => ∫ z in b..1,mixedDensity s chi amp J K w u z) v := by
  let U := fun z : ℝ => continuedResponse s chi amp J K z w
  have hwr : -2<w.re := by linarith [chamber_re_pos hw]
  have hc : ContinuousOn U (Ioo b (1:ℝ)) := by
    intro z hz
    exact (continuedResponse_hasDerivAt s chi amp J K w hwi hwr
      ⟨hb.trans hz.1,hz.2⟩).1.continuousAt.continuousWithinAt
  have hleft : Tendsto U (𝓝[>] b) (𝓝 (U b)) :=
    ((continuedResponse_hasDerivAt s chi amp J K w hwi hwr ⟨hb,hb1⟩).1.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have hright : Tendsto U (𝓝[<] (1:ℝ)) (𝓝 0) := by
    apply (response_boundary hw s amp J K (onsetTransform (2*s) w)).congr'
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ)<1)] with z hz
    exact (continuedResponse_eq_original s chi amp J K w hwi
      (by linarith [chamber_re_pos hw]) hs hz.1 hz.2).symm
  let V := extendFrom (Ioo b (1:ℝ)) U
  have hV : ContinuousOn V (Icc b (1:ℝ)) := continuousOn_Icc_extendFrom_Ioo hc hleft hright
  let Y := fun z : ℝ => V z/(2*(z:ℂ))
  have hY : ContinuousOn Y (Icc b (1:ℝ)) := by
    intro z hz
    exact (hV z hz).div
      (show ContinuousWithinAt (fun z : ℝ => 2*(z:ℂ)) (Icc b (1:ℝ)) z by fun_prop)
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (hb.trans_le hz.1).ne'))
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hY
  have hp : ContinuousOn (fun p : ℂ×ℝ => power (p.1/2) p.2) (closedBall v 1 ×ˢ Icc b (1:ℝ)) := by
    intro p hp
    have hz : 0<p.2 := hb.trans_le hp.2.1
    exact ((Complex.continuousAt_ofReal_cpow p.2 (p.1/2) (Or.inr hz.ne')).comp_of_eq
      (show ContinuousAt (fun q : ℂ×ℝ => (q.2,q.1/2)) p by fun_prop) rfl).continuousWithinAt
  obtain ⟨P,hP⟩ := ((isCompact_closedBall v 1).prod isCompact_Icc).exists_bound_of_continuousOn hp
  obtain ⟨Cg,hCg,hg⟩ := outerGauss_uniform_bound v chi (by linarith : 0<1-b) (by linarith : 1-b<1)
  let C := max M 0*max P 0*Cg
  have hbound (u : ℂ) (hu : u∈ball v 1) (z : ℝ) (hz : z∈Ioo b (1:ℝ)) :
      ‖mixedDensity s chi amp J K w u z‖≤C := by
    have hz0 : 0<z := hb.trans hz.1
    have ht0 : (Real.sqrt (1-z):ℂ)≠0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (sub_pos.mpr hz.2)).ne'
    have he : mixedDensity s chi amp J K w u z=Y z*power (u/2) z*gaussFactor u chi true (1-z) := by
      dsimp only [mixedDensity,Y,V]
      rw [extendFrom_extends hc z hz]
      dsimp only [U,normalizable,dress,outerFactor]
      rw [power_half_eq_sqrt (sub_nonneg.mpr hz.2.le)]
      field_simp
    have hn : ‖(1-(z:ℂ))‖≤1-b := by
      rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (by linarith [hz.2])]
      linarith [hz.1]
    rw [he,norm_mul,norm_mul]
    exact mul_le_mul
      (mul_le_mul ((hM z ⟨hz.1.le,hz.2.le⟩).trans (le_max_left _ _))
        ((hP (u,z) ⟨ball_subset_closedBall hu,⟨hz.1.le,hz.2.le⟩⟩).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _))
      (hg u hu _ hn) (norm_nonneg _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))
  have hmeas (u : ℂ) : AEStronglyMeasurable (mixedDensity s chi amp J K w u) (volume.restrict (Ioo b (1:ℝ))) := by
    apply ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    intro z hz
    have hz0 : 0<z := hb.trans hz.1
    exact (((continuedResponse_hasDerivAt s chi amp J K w hwi hwr ⟨hz0,hz.2⟩).1.continuousAt.mul
      (normalizable_derivatives_continued (w:=u) (chi:=chi) ⟨hz0,hz.2⟩).1.continuousAt).div
      (show ContinuousAt (fun z : ℝ => 2*(z:ℂ)*(Real.sqrt (1-z):ℂ)) z by fun_prop)
      (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hz0.ne'))
        (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (sub_pos.mpr hz.2)).ne'))).continuousWithinAt
  have hlim : Tendsto (fun u : ℂ => ∫ z in Ioo b (1:ℝ),mixedDensity s chi amp J K w u z)
      (𝓝 v) (𝓝 (∫ z in Ioo b (1:ℝ),mixedDensity s chi amp J K w v z)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => C)
    · exact Filter.Eventually.of_forall hmeas
    · filter_upwards [ball_mem_nhds v (by norm_num : (0:ℝ)<1)] with u hu
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      exact hbound u hu z hz
    · exact integrable_const C
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      exact (((normalizable_frequency_entire chi ⟨hb.trans hz.1,hz.2⟩ v).continuousAt.const_mul
        (continuedResponse s chi amp J K z w)).div_const (2*(z:ℂ)*(Real.sqrt (1-z):ℂ))).tendsto
  have heq (u : ℂ) : (∫ z in b..1,mixedDensity s chi amp J K w u z)=
      ∫ z in Ioo b (1:ℝ),mixedDensity s chi amp J K w u z := by
    rw [intervalIntegral.integral_of_le hb1.le,integral_Ioc_eq_integral_Ioo]
  change Tendsto _ _ _
  simp_rw [heq]
  exact hlim


/-- The actual horizon amplitude is analytic away from its two original
denominators. This concerns its value, not only a punctured meromorphic germ. -/
theorem greenHorizonAmplitude_analyticAt (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*s≠0) (hc : connection w chi≠0) :
    AnalyticAt ℂ (greenHorizonAmplitude s chi amp J K) w := by
  obtain ⟨RE,BE,hRE,hBE,hBEhalf,hE⟩ := incomingResponseEndpoint_eq_amplitude_below s chi amp J K w hw hwr hs
  obtain ⟨RP,BP,CP,MP,hRP,hBP,_,_,_,hP⟩ := incomingSourcePrimitive_common_data s chi amp J K w hw hwr hs
  obtain ⟨RG,BG,CG,hRG,hBG,_,_,hG⟩ := horizonGauss_uniform_nonzero w chi hw
  let b := min BE (min BP BG)
  have hb : 0<b := lt_min hBE (lt_min hBP hBG)
  have hbE : b≤BE := min_le_left _ _
  have hbP : b≤BP := (min_le_right _ _).trans (min_le_left _ _)
  have hbG : b≤BG := (min_le_right _ _).trans (min_le_right _ _)
  have hb1 : b<1 := lt_of_le_of_lt (hbE.trans hBEhalf) (by norm_num)
  have hg0 : gaussFactor w chi false (b:ℂ)≠0 := by
    have hh := (hG w (mem_ball_self hRG) b ⟨hb.le,hbG⟩).2.1
    intro he
    rw [he,norm_zero] at hh
    linarith
  have hh0 : horizon w chi b≠0 := mul_ne_zero (power_ne_zero _ hb) hg0
  have hT : AnalyticAt ℂ (fun u : ℂ => 1/(u-2*s)+onsetCorrection (2*s) u) w :=
    ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) hs).add
      ((onsetCorrection_entire (2*s)).analyticAt w))
  have hden := (connection_frequency_analyticAt w chi hw).neg
  have hHM := ((horizonFirstMellin_analyticAt s chi amp J K w hw hwr hb hb1).mul hT).div hden (neg_ne_zero.mpr hc)
  have hOM := (((outerSourceIntegral_entire s chi amp J K hb hb1).analyticAt w).mul hT).div hden (neg_ne_zero.mpr hc)
  have hH := horizon_frequency_analyticAt w chi hw ⟨hb,hb1⟩
  have hN := (normalizable_frequency_entire chi ⟨hb,hb1⟩).analyticAt w
  have hU : AnalyticAt ℂ (continuedResponse s chi amp J K b) w := (hN.mul hHM).add (hH.mul hOM)
  have hPS := ((hP w (mem_ball_self hRP)).2.2.2.2 b ⟨hb,hbP⟩).1
  have hEP : AnalyticAt ℂ (fun u => incomingResponseEndpoint s chi amp J K u b) w := (hU.div hH hh0).sub hPS
  apply hEP.congr
  filter_upwards [ball_mem_nhds w hRE,
    (connection_frequency_analyticAt w chi hw).continuousAt.eventually_ne hc] with u hu hcu
  exact hE u hu hcu b hb hbE

/-- The source-amplitude quotient in the full resolvent has exactly the
prescribed Green temporal-corner limit, including its `E/(2*w)` term. -/
theorem temporalSourceQuotient_tendsto (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*s≠0) (hc : connection w chi≠0) :
    Tendsto (fun v : ℂ => connection v chi*(greenHorizonAmplitude s chi amp J K v-
        (v+w)*greenHorizonAmplitude s chi amp J K w/(2*v))/(v-w))
      (𝓝[≠] w) (𝓝 (connection w chi*(deriv (greenHorizonAmplitude s chi amp J K) w+
        greenHorizonAmplitude s chi amp J K w/(2*w)))) := by
  let E := greenHorizonAmplitude s chi amp J K
  have hw0 : w≠0 := by intro he; exact hw (by simp [he])
  have hE := (greenHorizonAmplitude_analyticAt s chi amp J K w hw hwr hs hc).differentiableAt
  have hd : ContinuousAt (dslope E w) w := continuousAt_dslope_same.mpr hE
  have hr : ContinuousAt (fun v : ℂ => E w/(2*v)) w :=
    continuousAt_const.div (by fun_prop) (mul_ne_zero (by norm_num) hw0)
  have hlim := ((connection_frequency_analyticAt w chi hw).continuousAt.mul (hd.add hr)).tendsto.mono_left
    (show 𝓝[≠] w≤𝓝 w from nhdsWithin_le_nhds)
  change Tendsto (fun v : ℂ => connection v chi*(dslope E w v+E w/(2*v))) (𝓝[≠] w)
    (𝓝 (connection w chi*(dslope E w w+E w/(2*w)))) at hlim
  rw [dslope_same] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (continuousAt_id.eventually_ne hw0)] with v hv hv0
  change v≠0 at hv0
  have hvw : v-w≠0 := sub_ne_zero.mpr hv
  rw [dslope_of_ne _ hv,slope_def_field]
  dsimp only [E]
  field_simp [hvw,hv0]
  ring

/-- The full metric/temporal side of the source-difference identity tends to
the original metric finite part plus its prescribed temporal corner. -/
theorem fullMetricTemporal_diagonal_limit_below (s chi amp J K w : ℂ)
    (hw : Chamber w chi) (hwi : w.im≠0) (hs : (2*s).re<w.re) :
    ∃ B : ℝ, 0<B ∧ B≤1/2 ∧ ∀ b : ℝ, 0<b → b≤B →
      Tendsto (fun v : ℂ => (v+w)*readerFullRegularPart s chi amp J K w b v+
        connection v chi*(greenHorizonAmplitude s chi amp J K v-
          (v+w)*greenHorizonAmplitude s chi amp J K w/(2*v))/(v-w))
        (𝓝[≠] w) (𝓝 (2*w*(normalizableHorizonPairingFinitePart s chi amp J K b w+
          (∫ z in b..1,mixedDensity s chi amp J K w w z))+
          connection w chi*(deriv (greenHorizonAmplitude s chi amp J K) w+
            greenHorizonAmplitude s chi amp J K w/(2*w)))) := by
  have hwr := chamber_re_pos hw
  have hsp : w-2*s≠0 := sub_ne_zero.mpr (fun he => by rw [he] at hs; exact (lt_irrefl _ hs))
  have hc := connection_ne_zero hw
  obtain ⟨B,hB,hBhalf,hH⟩ := readerHorizonRegularPart_original_below s chi amp J K w hwi hwr hsp hc
  refine ⟨B,hB,hBhalf,?_⟩
  intro b hb hbB
  have hb1 : b<1 := lt_of_le_of_lt (hbB.trans hBhalf) (by norm_num)
  obtain ⟨hHC,hmatch⟩ := hH b hb hbB
  have hOC := mixedOuterIntegral_continuousAt s chi amp J K w w hw hwi hs hb hb1
  have hreg : ContinuousAt (readerFullRegularPart s chi amp J K w b) w := hHC.add hOC
  have hmetric := ((tendsto_id.add_const w).mul hreg.tendsto).mono_left
    (show 𝓝[≠] w≤𝓝 w from nhdsWithin_le_nhds)
  have htotal := hmetric.add (temporalSourceQuotient_tendsto s chi amp J K w hwi (by linarith) hsp hc)
  have he : readerFullRegularPart s chi amp J K w b w=
      normalizableHorizonPairingFinitePart s chi amp J K b w+
        (∫ z in b..1,mixedDensity s chi amp J K w w z) := by
    rw [readerFullRegularPart,hmatch]
  simpa only [he,show w+w=2*w by ring] using! htotal

end
end RHTower.D4BMOriginalSourceResolvent
