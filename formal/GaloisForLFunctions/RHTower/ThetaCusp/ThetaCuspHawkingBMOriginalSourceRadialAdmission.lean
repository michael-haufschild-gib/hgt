import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalSourceTailAdmission

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalSourceRadialAdmission
open D4BMJointSource D4BMModularCore D4BMOriginalReaderCuspBounds D4BMOriginalCausalPeriod
open D4BMOriginalSourceTailCollar D4BMOriginalSourceTailAdmission
noncomputable section
set_option autoImplicit false

private theorem radial_period_continuous (q : XiZeroCopy) (br : Bool) (amp : ℂ) (L : ℝ) :
    Continuous (fun p => originalRadialPeriod q br amp p (p+L)) := by
  have hR := (D4BMNativeResponse.radialResponse_continuous (-D4BMOriginalCirclePeriod.readerExponent q)
    (physicalRate q br) amp).comp (show Continuous (fun p : ℝ => ((p+(p+L))/2,(p-(p+L))/2)) by fun_prop)
  have hL : Continuous (radialLift (physicalRate q br) 0 amp 1) :=
    continuous_iff_continuousAt.mpr (fun x => (radialLift_hasDerivAt _ _ _ _ x).continuousAt)
  have hO : Continuous (timeOnset (2*physicalRate q br)) :=
    continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt _ p).continuousAt)
  have hN := (hL.comp (show Continuous (fun p : ℝ => (p-(p+L))/2) by fun_prop)).mul hO
  exact (hR.add hN).const_mul (physicalSelfSourceCoefficient q)

/-- The actual finite source discrepancy is separately admitted in positive
source time before comparison with its leading horizon trace. -/
theorem period_time_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (a b L k : ℝ) (ha : 0≤a) (hab : a≤b) (hL : 0<L) (hk : 4≤Real.exp k) :
    IntervalIntegrable (fun p => originalPeriodError q br amp w p L k) volume a b := by
  have hP := originalFiniteHeightPeriod_time_continuousOn q br amp a b (-L/2) (Real.exp k) ha hab (by linarith) hk
  have hP' : ContinuousOn (fun p => originalFiniteHeightPeriod q br amp p (p+L) (Real.exp k)) (Icc a b) := by
    convert hP using 1
    funext p; congr 1; ring
  have hD := hP'.sub (radial_period_continuous q br amp L).continuousOn
  have hE : Continuous (fun p : ℝ => Complex.exp (-w*(p:ℂ))*reader q w L) := by fun_prop
  exact (hE.continuousOn.mul hD).intervalIntegrable_of_Icc hab

/-- The actual leading scalar-period tail has arbitrary cusp decay, uniformly
in source time with its original integrable time envelope. -/
theorem horizon_period_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re → ∃ C : ℝ,0≤C ∧ ∀ p k : ℝ,0<p → 0≤k →
      ‖horizonPeriodError q br amp w p k‖≤C*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  obtain ⟨G,hG,hg⟩ := horizon_tail_density_bound q br amp N
  refine ⟨G,hG,?_⟩
  intro w hw
  obtain ⟨C,hC,hc⟩ := hg w hw
  refine ⟨C*measure.real univ,by positivity,?_⟩
  intro p k hp hk
  let B := C*Real.exp (-(N:ℝ)*k)*Real.exp (-p)
  have hB : 0≤B := by dsimp [B];positivity
  have hm : MeasurableSet (tailSet k) := measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable
  have hi : Integrable (fun _ : UpperHalfPlane => B) (measure.restrict (tailSet k)) := integrable_const B
  have h := norm_integral_le_of_norm_le hi (by
    filter_upwards [ae_restrict_mem hm] with z hz
    exact hc p k hp hk z hz)
  simp only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ] at h
  unfold horizonPeriodError
  rw [norm_neg]
  calc
    _ ≤ measure.real (tailSet k)*B := h
    _ ≤ measure.real univ*B := mul_le_mul_of_nonneg_right (measureReal_mono (subset_univ _)) hB
    _ = _ := by dsimp [B];ring

/-- Compact time admission of the retained horizon period is derived from the
actual physical periods and their uniform horizon error, without a trace premise. -/
theorem horizon_period_time_integrable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∀ a b k : ℝ,0<a → a≤b → 0≤k → 4≤Real.exp k →
      IntervalIntegrable (fun p => horizonPeriodError q br amp w p k) volume a b := by
  obtain ⟨G1,hG1,h1⟩ := original_period_mixed_error q br amp 0
  obtain ⟨G2,_,h2⟩ := horizon_period_bound q br amp 0
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw a b k ha hab hk hk4
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 G2]
  have hw2 : G2+1≤w.re := by linarith [le_max_right G1 G2]
  obtain ⟨C,hC,hc⟩ := h1 w hwi hw1
  obtain ⟨B,hB,hb⟩ := h2 w hw2
  have hm : AEStronglyMeasurable (fun p => horizonPeriodError q br amp w p k) (volume.restrict (Ioc a b)) := by
    apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter ℝ)
      (fun r => ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
        (period_time_integrable q br amp w a b (Real.exp r) k ha.le hab (Real.exp_pos r) hk4)).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with p hp
    have hp0 : 0<p := ha.trans hp.1
    apply Filter.Tendsto.comp (g:=fun L => originalPeriodError q br amp w p L k) _ Real.tendsto_exp_atTop
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have ht : Tendsto (fun L : ℝ => C*Real.exp (-L)*Real.exp (-p)) atTop (𝓝 0) := by
      simpa only [mul_zero,zero_mul] using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C).mul_const (Real.exp (-p))
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ ht
    filter_upwards [hc] with L hL
    simpa only [Nat.cast_zero,neg_zero,zero_mul,Real.exp_zero,mul_one] using hL p k hp0 hk hk4
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  apply (integrable_const B : Integrable (fun _ : ℝ => B) (volume.restrict (Ioc a b))).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with p hp
  have hp0 : 0<p := ha.trans hp.1
  have h := hb p k hp0 hk
  simp only [Nat.cast_zero,neg_zero,zero_mul,Real.exp_zero,mul_one] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith : -p≤0)) hB).trans_eq (mul_one B))

private theorem fixed_time_tail_measurable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (p A k : ℝ) (hp : 0<p) (hA : 0≤A) :
    AEStronglyMeasurable (fun v : ℝ×UpperHalfPlane => tailDensity q br amp w p v.1 v.2)
      ((volume.restrict (Ioi A)).prod (measure.restrict (tailSet k))) := by
  rw [Measure.prod_restrict]
  have hm : MeasurableSet (Ioi A ×ˢ tailSet k) := measurableSet_Ioi.prod
    (measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable)
  apply ContinuousOn.aestronglyMeasurable _ hm
  intro v hv
  exact ((tail_density_joint_continuousAt q br amp w ((v.1,p),v.2) (hA.trans_lt hv.1) hp).comp
    (f:=fun t : ℝ×UpperHalfPlane => ((t.1,p),t.2))
    (show ContinuousAt (fun t : ℝ×UpperHalfPlane => ((t.1,p),t.2)) v by fun_prop)).continuousWithinAt

/-- Every positive source-time slice of the original period error is radially
integrable after retaining its actual horizon trace; there is no exceptional set
of admissible temporal endpoints. -/
theorem endpoint_radial_error_integrable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ L0 : ℝ,0<L0 ∧ ∀ p k : ℝ,0<p → 0≤k → 4≤Real.exp k →
      IntegrableOn (fun L => originalPeriodError q br amp w p L k-horizonPeriodError q br amp w p k) (Ioi L0) volume := by
  obtain ⟨G1,hG1,h1⟩ := source_tail_density_error q br amp 0
  obtain ⟨G2,_,h2⟩ := horizon_tail_integrable q br amp
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 G2]
  have hw2 : G2+1≤w.re := by linarith [le_max_right G1 G2]
  obtain ⟨C,hC,hc⟩ := h1 w hwi hw1
  obtain ⟨A,hA⟩ := eventually_atTop.mp hc
  let L0 := max A 1
  have hL0 : 0<L0 := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  refine ⟨L0,hL0,?_⟩
  intro p k hp hk hk4
  have hH := h2 w hwi hw2 p k hp hk hk4
  have hm : AEStronglyMeasurable (fun v : ℝ×UpperHalfPlane =>
      tailDensity q br amp w p v.1 v.2-horizonTailDensity q br amp w p v.2)
      ((volume.restrict (Ioi L0)).prod (measure.restrict (tailSet k))) :=
    (fixed_time_tail_measurable q br amp w p L0 k hp hL0.le).sub hH.aestronglyMeasurable.comp_snd
  have hiL : IntegrableOn (fun L : ℝ => Real.exp (-L)) (Ioi L0) volume := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (a:=(-1:ℝ)) (by norm_num) L0
  have hi : Integrable (fun v : ℝ×UpperHalfPlane => (C*Real.exp (-p))*Real.exp (-v.1))
      ((volume.restrict (Ioi L0)).prod (measure.restrict (tailSet k))) := by
    simpa only [mul_one] using (hiL.const_mul (C*Real.exp (-p))).mul_prod
      (integrable_const (1:ℝ) : Integrable (fun _ : UpperHalfPlane => (1:ℝ)) (measure.restrict (tailSet k)))
  have he : Integrable (fun v : ℝ×UpperHalfPlane =>
      tailDensity q br amp w p v.1 v.2-horizonTailDensity q br amp w p v.2)
      ((volume.restrict (Ioi L0)).prod (measure.restrict (tailSet k))) := by
    apply hi.mono' hm
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod
      (measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable))] with v hv
    have h := hA v.1 ((le_max_left A 1).trans hv.1.le) p k hp hk v.2 hv.2
    simpa only [Nat.cast_zero,neg_zero,zero_mul,mul_zero,Real.exp_zero,mul_one,one_mul,mul_comm,mul_left_comm,mul_assoc] using h
  apply he.integral_prod_left.neg.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
  have hLp := hL0.trans hL
  simp only [Pi.neg_apply]
  rw [original_period_error_tail q br amp w p L k hp hLp hk4,horizonPeriodError,
    integral_sub (tail_density_integrable q br amp w p L k hp hLp hk4) hH]
  ring

/-- The actual source endpoints themselves have separate compact radial admission. -/
theorem endpoint_radial_integrable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ L0 : ℝ,0<L0 ∧ ∀ p k A B : ℝ,
      0<p → 0≤k → 4≤Real.exp k → L0≤A → A≤B →
      IntervalIntegrable (fun L => originalPeriodError q br amp w p L k) volume A B := by
  obtain ⟨G,hG,hg⟩ := endpoint_radial_error_integrable q br amp
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨L0,hL0,h⟩ := hg w hwi hw
  refine ⟨L0,hL0,?_⟩
  intro p k A B hp hk hk4 hA hAB
  have hi : IntervalIntegrable (fun L => originalPeriodError q br amp w p L k-horizonPeriodError q br amp w p k) volume A B := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hAB]
    exact (h p k hp hk hk4).mono_set (fun L hL => hA.trans_lt hL.1)
  have ht := hi.add (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => horizonPeriodError q br amp w p k) volume A B)
  simpa only [Pi.add_apply,sub_add_cancel] using ht

/-- Separate radial admission of the actual complete source time moment,
derived from its admitted time/horizon product and genuine horizon time trace. -/
theorem moment_radial_integrable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ L0 : ℝ,0<L0 ∧ ∀ a b k A B : ℝ,
      0<a → a≤b → 0≤k → 4≤Real.exp k → L0≤A → A≤B →
      IntervalIntegrable (fun L => ∫ p in a..b,originalPeriodError q br amp w p L k) volume A B := by
  obtain ⟨G1,hG1,h1⟩ := original_period_error_integrable q br amp
  obtain ⟨G2,_,h2⟩ := horizon_period_time_integrable q br amp
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 G2]
  have hw2 : G2+1≤w.re := by linarith [le_max_right G1 G2]
  obtain ⟨L0,hL0,h⟩ := h1 w hwi hw1
  refine ⟨L0,hL0,?_⟩
  intro a b k A B ha hab hk hk4 hA hAB
  have hH := h2 w hwi hw2 a b k ha hab hk hk4
  have hi : Integrable (fun v : ℝ×ℝ => originalPeriodError q br amp w v.2 v.1 k-horizonPeriodError q br amp w v.2 k)
      ((volume.restrict (Ioc A B)).prod (volume.restrict (Ioc a b))) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    exact (h k hk hk4).mono_set (fun v hv => ⟨hA.trans_lt hv.1.1,ha.trans hv.2.1⟩)
  have hI : IntervalIntegrable (fun L => ∫ p in a..b,
      originalPeriodError q br amp w p L k-horizonPeriodError q br amp w p k) volume A B := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hAB]
    simpa only [intervalIntegral.integral_of_le hab,IntegrableOn] using hi.integral_prod_left
  have hSum := hI.add (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ =>
    ∫ p in a..b,horizonPeriodError q br amp w p k) volume A B)
  apply hSum.congr
  intro L hL
  have hLI : L∈Ioc A B := by simpa only [uIoc_of_le hAB] using hL
  have hLp : 0<L := hL0.trans_le (hA.trans hLI.1.le)
  dsimp only
  rw [intervalIntegral.integral_sub (period_time_integrable q br amp w a b L k ha.le hab hLp hk4) hH,sub_add_cancel]

end
end RHTower.D4BMOriginalSourceRadialAdmission
