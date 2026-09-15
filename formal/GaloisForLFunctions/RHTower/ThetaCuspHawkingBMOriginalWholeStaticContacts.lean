import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalWholeStaticMetric

/-! Physical mass-tail corners of the complete original metric discrepancy. -/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalWholeStaticContacts
open D4BMJointSource D4BMLaplaceRadial D4BMModularCore
open D4BMOriginalWholeStaticMetric D4BMOriginalStaticPhysicalMass
open D4BMOriginalStaticTracePrimitive D4BMOriginalStaticTraceDensity
open D4BMOriginalFullMetricCollar D4BMOriginalStaticForcingTriangle D4BMOriginalForcingClockContact
noncomputable section
set_option autoImplicit false

private theorem onset_integrable (q : XiZeroCopy) (br : Bool) (w : ℂ) (hw : 0 ≤ w.re) :
    IntegrableOn (onsetDensity q br w) (Ioi (0:ℝ)) := by
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  exact timeOnset_integrable (2*physicalRate q br) w (by linarith)

private theorem onset_bound (q : XiZeroCopy) (br : Bool) (w : ℂ) (hw : 0 ≤ w.re)
    (p : ℝ) (hp : 0 ≤ p) : ‖onsetDensity q br w p‖ ≤ Real.exp (-p) := by
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  have ht : ‖(Real.smoothTransition p:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg p)]
      using Real.smoothTransition.le_one p
  unfold onsetDensity timeOnset
  rw [norm_mul,norm_mul]
  have he (v : ℂ) : ‖Complex.exp (v*(p:ℂ))‖=Real.exp (v.re*p) := by
    rw [Complex.norm_exp];congr 1;simp
  rw [he,he]
  calc
    _ ≤ Real.exp ((-w).re*p)*Real.exp ((2*physicalRate q br).re*p) :=
      mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (Real.exp_nonneg _) ht) (Real.exp_nonneg _)
    _ ≤ Real.exp (-p) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      simp only [Complex.neg_re]
      nlinarith

private theorem onset_mass_decay (q : XiZeroCopy) (br : Bool) (w : ℂ) (hw : 0 ≤ w.re)
    (a : ℝ) (ha : 0 ≤ a) : ‖onsetMass q br w a‖ ≤ Real.exp (-a) := by
  have h := norm_integral_le_of_norm_le (integrableOn_exp_neg_Ioi a) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    exact onset_bound q br w hw p (ha.trans hp.le))
  simpa only [integral_exp_neg_Ioi,onsetMass] using h

private theorem onset_mass_continuous (q : XiZeroCopy) (br : Bool) (w : ℂ) (hw : 0 ≤ w.re) :
    ContinuousOn (onsetMass q br w) (Ici (0:ℝ)) := by
  have ht : Continuous (timeOnset (2*physicalRate q br)) := continuous_iff_continuousAt.mpr
    (fun p => (timeOnset_hasDerivAt _ p).continuousAt)
  have hon : Continuous (onsetDensity q br w) := by unfold onsetDensity;fun_prop
  have hI : Continuous (fun p : ℝ => ∫ t in (0:ℝ)..p,onsetDensity q br w t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ:=volume) (a₀:=0) (f:=fun _ : ℝ => onsetDensity q br w)
      (hon.comp continuous_snd) continuous_id
  have hC : Continuous (fun p : ℝ => onsetMass q br w 0-
      (∫ t in (0:ℝ)..p,onsetDensity q br w t)) := continuous_const.sub hI
  apply hC.continuousOn.congr
  intro p hp
  have hi := onset_integrable q br w hw
  have he := intervalIntegral.integral_interval_add_Ioi hi (hi.mono_set (Ioi_subset_Ioi hp))
  change (∫ t in (0:ℝ)..p,onsetDensity q br w t)+onsetMass q br w p=onsetMass q br w 0 at he
  linear_combination he

private theorem onset_mass_integrable (q : XiZeroCopy) (br : Bool) (w : ℂ) (hw : 0 ≤ w.re)
    (a : ℝ) (ha : 0 ≤ a) : IntegrableOn (onsetMass q br w) (Ioi a) := by
  apply (integrableOn_exp_neg_Ioi a).mono'
    (((onset_mass_continuous q br w hw).mono (fun p hp => ha.trans hp.le)).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  exact onset_mass_decay q br w hw p (ha.trans hp.le)

/-- The corner is the tail integral of the actual complete physical mass. -/
def metricHorizonCornerDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (k a : ℝ) : ℂ :=
  ∫ p in Ioi a,metricHorizonMassDifference q br amp w k p

/-- Separate admission of the complete physical mass before taking its tail. -/
theorem physical_mass_tail_integrable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0 ≤ G ∧ ∀ w : ℂ,w.im≠0 → G+1 ≤ w.re → ∀ a k : ℝ,
      0<a → 0 ≤ k → 4 ≤ Real.exp k →
        IntegrableOn (metricHorizonMassDifference q br amp w k) (Ioi a) := by
  obtain ⟨G,hG,hg⟩ := trace_transient_halfline_integrable q br amp
  refine ⟨G,hG,?_⟩
  intro w hwi hw a k ha hk hk4
  have htrace : IntegrableOn (traceMass q br amp w k) (Ioi a) := by
    convert! (hg w hwi hw a k ha hk hk4).neg using 1
    funext p
    simp only [traceMass,traceTransient,Pi.neg_apply]
    ring
  exact htrace.add ((onset_mass_integrable q br w (by linarith) a ha.le).const_mul
    (D4BMLeftModeRadialEquation.eigenvalue q*w*horizonForcingDifference q br amp w k))

/-- Both physical moving corners are uniformly cusp-small, including their
complete forcing mass and the source/boundary endpoint contributions. -/
theorem physical_corner_uniform_restoration (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0 ≤ G ∧ ∀ w : ℂ,G+1 ≤ w.re →
      ∃ eta : ℝ→ℝ,(∀ k,0 ≤ eta k) ∧ Tendsto eta atTop (𝓝 0) ∧
        ∀ a k : ℝ,0<a → 0 ≤ k → ‖metricHorizonCornerDifference q br amp w k a‖ ≤ eta k := by
  obtain ⟨G,hG,hg⟩ := trace_mass_transient_decay q br amp 1
  refine ⟨G,hG,?_⟩
  intro w hw
  obtain ⟨C,hC,hc⟩ := hg w hw
  let eta := fun k : ℝ => C*Real.exp (-k)+
    ‖D4BMLeftModeRadialEquation.eigenvalue q*w*horizonForcingDifference q br amp w k‖
  have heta (k : ℝ) : 0 ≤ eta k := by dsimp [eta];positivity
  refine ⟨eta,heta,?_,?_⟩
  · have he := (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul C
    have hh := ((horizon_forcing_difference_tendsto q br amp w).const_mul
      (D4BMLeftModeRadialEquation.eigenvalue q*w)).norm
    simpa only [eta,Function.comp_def,mul_zero,norm_zero,add_zero] using! he.add hh
  · intro a k ha hk
    have hb (p : ℝ) (hp : a<p) : ‖metricHorizonMassDifference q br amp w k p‖ ≤ eta k*Real.exp (-p) := by
      unfold metricHorizonMassDifference
      apply (norm_add_le _ _).trans
      have htr := (hc p k (ha.trans hp) hk).1
      simp only [Nat.cast_one,neg_mul,one_mul] at htr
      rw [norm_mul]
      exact (add_le_add htr (mul_le_mul_of_nonneg_left
        (onset_mass_decay q br w (by linarith) p (ha.trans hp).le) (norm_nonneg _))).trans_eq (by dsimp [eta];ring)
    have hi := norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi a).const_mul (eta k)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
      exact hb p hp)
    rw [integral_const_mul,integral_exp_neg_Ioi] at hi
    exact hi.trans (mul_le_of_le_one_right (heta k) (Real.exp_le_one_iff.mpr (by linarith)))

/-- The full original horizon discrepancy, including its forcing time moment. -/
def completeHorizonTrace (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (k a b : ℝ) : ℂ :=
  metricTrace q br amp w a b k+
    (D4BMLeftModeRadialEquation.eigenvalue q*w*horizonForcingDifference q br amp w k)*
      (∫ p in a..b,onsetDensity q br w p)

/-- The actual trace is the difference of the same physical masses whose
tails define the retained corners. -/
theorem complete_horizon_trace_mass_identity (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0 ≤ G ∧ ∀ w : ℂ,w.im≠0 → G+1 ≤ w.re → ∀ a b k : ℝ,
      0<a → a ≤ b → 0 ≤ k → 4 ≤ Real.exp k →
        completeHorizonTrace q br amp w k a b=
          metricHorizonMassDifference q br amp w k a-metricHorizonMassDifference q br amp w k b := by
  obtain ⟨G,hG,hg⟩ := trace_mass_transient_decomposition q br amp
  refine ⟨G,hG,?_⟩
  intro w hwi hw a b k ha hab hk hk4
  have htrace := hg w hwi hw a b k ha hab hk hk4
  have hn : traceTransient q br amp w k b= -traceMass q br amp w k b := by
    unfold traceTransient traceMass
    ring
  have hi := onset_integrable q br w (by linarith)
  have hIa := hi.mono_set (Ioi_subset_Ioi ha.le)
  have hIb := hi.mono_set (Ioi_subset_Ioi (ha.le.trans hab))
  have htime := intervalIntegral.integral_interval_add_Ioi hIa hIb
  have htime' : (∫ p in a..b,onsetDensity q br w p)=onsetMass q br w a-onsetMass q br w b := by
    change _+onsetMass q br w b=onsetMass q br w a at htime
    linear_combination htime
  unfold completeHorizonTrace metricHorizonMassDifference
  rw [htrace,hn,htime']
  ring

/-- Exact two-corner identity of the full physical trace on every positive
temporal interval. Both mass tails are admitted before the identity is formed. -/
theorem complete_horizon_two_corner_identity (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0 ≤ G ∧ ∀ w : ℂ,w.im≠0 → G+1 ≤ w.re → ∀ a R S k : ℝ,
      0<a → a ≤ R → R ≤ S → 0 ≤ k → 4 ≤ Real.exp k →
        (∫ b in R..S,completeHorizonTrace q br amp w k a b)=
          (S-R)•metricHorizonMassDifference q br amp w k a+
            metricHorizonCornerDifference q br amp w k S-metricHorizonCornerDifference q br amp w k R := by
  obtain ⟨G1,hG1,h1⟩ := complete_horizon_trace_mass_identity q br amp
  obtain ⟨G2,hG2,h2⟩ := physical_mass_tail_integrable q br amp
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw a R S k ha haR hRS hk hk4
  have hw1 : G1+1 ≤ w.re := by linarith [le_max_left G1 G2]
  have hw2 : G2+1 ≤ w.re := by linarith [le_max_right G1 G2]
  have hR := h2 w hwi hw2 R k (ha.trans_le haR) hk hk4
  have hS := hR.mono_set (Ioi_subset_Ioi hRS)
  have hI : IntervalIntegrable (metricHorizonMassDifference q br amp w k) volume R S :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hRS).mpr (hR.mono_set Ioc_subset_Ioi_self)
  have he : (∫ b in R..S,completeHorizonTrace q br amp w k a b)=
      (S-R)•metricHorizonMassDifference q br amp w k a-
        (∫ b in R..S,metricHorizonMassDifference q br amp w k b) := by
    calc
      _ = ∫ b in R..S,metricHorizonMassDifference q br amp w k a-
          metricHorizonMassDifference q br amp w k b := by
        apply intervalIntegral.integral_congr
        intro b hb
        rw [uIcc_of_le hRS] at hb
        exact h1 w hwi hw1 a b k ha (haR.trans hb.1) hk hk4
      _ = _ := by rw [intervalIntegral.integral_sub intervalIntegrable_const hI,intervalIntegral.integral_const]
  have ht := intervalIntegral.integral_interval_add_Ioi hR hS
  change _+metricHorizonCornerDifference q br amp w k S=metricHorizonCornerDifference q br amp w k R at ht
  linear_combination he-ht

/-- The complete original metric difference with its actual finite-onset mass
and the lower moving corner relative to that onset. -/
def wholeStaticContactDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a B T k : ℝ) : ℂ :=
  wholeStaticMetricDifference q br amp w a B T k+
    metricHorizonCornerDifference q br amp w k (max a (T-B/2))-
      metricHorizonCornerDifference q br amp w k a

/-- The full original metric comparison retains the physical moving-corner
contact and still restores uniformly under all independent cutoff removals. -/
theorem whole_static_contacts_restoration (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0 ≤ G ∧ ∀ w : ℂ,w.im≠0 → G+1 ≤ w.re →
      ∃ B0 : ℝ,0<B0 ∧ ∃ eta : ℝ→ℝ,(∀ k,0 ≤ eta k) ∧ Tendsto eta atTop (𝓝 0) ∧
        ∀ a B T k : ℝ,0<a → B0 ≤ B → 0 ≤ k → 4 ≤ Real.exp k →
          IntegrableOn (metricHorizonMassDifference q br amp w k) (Ioi a) ∧
          IntervalIntegrable (fun L => metricDifference q br amp w a (max a (T-L/2)) L k) volume 0 B ∧
          ‖wholeStaticContactDifference q br amp w a B T k‖ ≤ eta k := by
  obtain ⟨G1,hG1,h1⟩ := whole_static_metric_restoration q br amp
  obtain ⟨G2,hG2,h2⟩ := physical_corner_uniform_restoration q br amp
  obtain ⟨G3,hG3,h3⟩ := physical_mass_tail_integrable q br amp
  refine ⟨max G1 (max G2 G3),le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  have hw1 : G1+1 ≤ w.re := by linarith [le_max_left G1 (max G2 G3)]
  have hw2 : G2+1 ≤ w.re := by linarith [(le_max_left G2 G3).trans (le_max_right G1 (max G2 G3))]
  have hw3 : G3+1 ≤ w.re := by linarith [(le_max_right G2 G3).trans (le_max_right G1 (max G2 G3))]
  obtain ⟨B0,hB0,em,hem,htm,hm⟩ := h1 w hwi hw1
  obtain ⟨ec,hec,htc,hc⟩ := h2 w hw2
  refine ⟨B0,hB0,fun k => em k+ec k+ec k,
    fun k => add_nonneg (add_nonneg (hem k) (hec k)) (hec k),?_,?_⟩
  · simpa only [zero_add] using (htm.add htc).add htc
  · intro a B T k ha hB hk hk4
    obtain ⟨hi,hb⟩ := hm a B T k ha hB hk hk4
    refine ⟨h3 w hwi hw3 a k ha hk hk4,hi,?_⟩
    unfold wholeStaticContactDifference
    exact ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
      (add_le_add (add_le_add hb (hc (max a (T-B/2)) k (ha.trans_le (le_max_left _ _)) hk))
        (hc a k ha hk))


end
end RHTower.D4BMOriginalWholeStaticContacts
