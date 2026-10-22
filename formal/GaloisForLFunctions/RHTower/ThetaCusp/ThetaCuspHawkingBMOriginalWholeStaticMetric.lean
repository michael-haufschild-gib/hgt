import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalOuterCuspMetric
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalStaticPhysicalMass

/-! Complete original static radial domain with its physical finite-onset mass. -/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalWholeStaticMetric
open D4BMJointSource D4BMLaplaceRadial D4BMModularCore
open D4BMOriginalFullMetricCollar D4BMOriginalOuterCuspMetric
open D4BMOriginalStaticPhysicalMass D4BMOriginalStaticTracePrimitive
open D4BMOriginalStaticForcingTriangle D4BMOriginalForcingClockContact
noncomputable section
set_option autoImplicit false

private theorem onset_mass_bound (q : XiZeroCopy) (br : Bool) (w : ℂ) (hw : 0≤w.re) :
    ∃ C : ℝ,0≤C ∧ ∀ a : ℝ,0≤a → ‖onsetMass q br w a‖≤C := by
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  have hi : IntegrableOn (onsetDensity q br w) (Ioi (0:ℝ)) :=
    timeOnset_integrable (2*physicalRate q br) w (by linarith)
  refine ⟨∫ p in Ioi (0:ℝ),‖onsetDensity q br w p‖,integral_nonneg (fun _ => norm_nonneg _),?_⟩
  intro a ha
  apply (norm_integral_le_integral_norm _).trans
  exact setIntegral_mono_set hi.norm (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (Filter.Eventually.of_forall (fun p hp => ha.trans_lt hp))

/-- The unchanged physical mass discrepancy tends uniformly to zero over
every positive onset. This does not discard its product with an unbounded clock. -/
theorem physical_mass_uniform_restoration (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re →
      ∃ eta : ℝ→ℝ,(∀ k,0≤eta k) ∧ Tendsto eta atTop (𝓝 0) ∧
        ∀ a k : ℝ,0<a → 0≤k → ‖metricHorizonMassDifference q br amp w k a‖≤eta k := by
  obtain ⟨G,hG,hg⟩ := trace_mass_transient_decay q br amp 1
  refine ⟨G,hG,?_⟩
  intro w hw
  obtain ⟨C,hC,hc⟩ := hg w hw
  obtain ⟨M,hM,hMbound⟩ := onset_mass_bound q br w (by linarith)
  let m := ‖D4BMLeftModeRadialEquation.eigenvalue q*w‖
  refine ⟨fun k => C*Real.exp (-k)+m*‖horizonForcingDifference q br amp w k‖*M,
    fun k => by dsimp [m];positivity,?_,?_⟩
  · simpa only [Function.comp_def,norm_zero,mul_zero,zero_mul,add_zero] using!
      ((Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul C).add
        (((horizon_forcing_difference_tendsto q br amp w).norm.const_mul m).mul_const M)
  · intro a k ha hk
    have htrace : ‖traceMass q br amp w k a‖≤C*Real.exp (-k) := by
      have h := (hc a k ha hk).1
      simp only [Nat.cast_one,neg_mul,one_mul] at h
      exact h.trans (mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by linarith)))
    unfold metricHorizonMassDifference
    apply (norm_add_le _ _).trans
    simp only [m,norm_mul]
    exact add_le_add htrace (mul_le_mul_of_nonneg_left (hMbound a ha.le) (by positivity))

/-- Full original radial discrepancy, including the outer endpoint and the
literal physical static-time window, with its original finite-onset mass. -/
def wholeStaticMetricDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a B T k : ℝ) : ℂ :=
  (∫ L in (0:ℝ)..B,metricDifference q br amp w a (max a (T-L/2)) L k)/2-
    (max a T-max a (T-B/2))•metricHorizonMassDifference q br amp w k a

/-- The complete original outer-plus-horizon metric restores uniformly under
independent onset, static time, radial and cusp cutoffs in its derived convergence
half-plane. No finite-height mass is set to zero or replaced by its zero-onset value. -/
theorem whole_static_metric_restoration (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re →
      ∃ B0 : ℝ,0<B0 ∧ ∃ eta : ℝ→ℝ,(∀ k,0≤eta k) ∧ Tendsto eta atTop (𝓝 0) ∧
        ∀ a B T k : ℝ,0<a → B0≤B → 0≤k → 4≤Real.exp k →
          IntervalIntegrable (fun L => metricDifference q br amp w a (max a (T-L/2)) L k) volume 0 B ∧
          ‖wholeStaticMetricDifference q br amp w a B T k‖≤eta k := by
  obtain ⟨G1,hG1,h1⟩ := full_outer_static_metric_restoration q br amp
  obtain ⟨G2,hG2,h2⟩ := full_static_physical_mass_restoration q br amp
  obtain ⟨G3,hG3,h3⟩ := physical_mass_uniform_restoration q br amp
  refine ⟨max G1 (max G2 G3),le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 (max G2 G3)]
  have hw2 : G2+1≤w.re := by linarith [(le_max_left G2 G3).trans (le_max_right G1 (max G2 G3))]
  have hw3 : G3+1≤w.re := by linarith [(le_max_right G2 G3).trans (le_max_right G1 (max G2 G3))]
  obtain ⟨A,hA,hArest⟩ := h2 w hwi hw2
  obtain ⟨ei,hei,hti,hi⟩ := hArest A le_rfl
  obtain ⟨eo,heo,hto,ho⟩ := h1 w hwi hw1 A hA
  obtain ⟨em,hem,htm,hm⟩ := h3 w hw3
  refine ⟨A,hA,fun k => eo k+ei k+(A/2)*em k,
    fun k => add_nonneg (add_nonneg (heo k) (hei k)) (mul_nonneg (by positivity) (hem k)),?_,?_⟩
  · simpa only [zero_add,mul_zero] using (hto.add hti).add (htm.const_mul (A/2))
  · intro a B T k ha hAB hk hk4
    obtain ⟨hoi,hob⟩ := ho a T k ha hk hk4
    obtain ⟨hii,hib⟩ := hi a B T k ha hAB hk hk4
    have hmass := hm a k ha hk
    let D := fun L => metricDifference q br amp w a (max a (T-L/2)) L k
    let delta := max a T-max a (T-A/2)
    have hd0 : 0≤delta := sub_nonneg.mpr (max_le_max_left a (by linarith))
    have hdA : delta≤A/2 := by
      have h : max a T ≤ max a (T-A/2)+A/2 := by
        apply max_le
        · linarith [le_max_left a (T-A/2)]
        · linarith [le_max_right a (T-A/2)]
      dsimp [delta]
      linarith
    have he : wholeStaticMetricDifference q br amp w a B T k=
        (∫ L in (0:ℝ)..A,D L)/2+massRestoredStaticDifference q br amp w a A B T k-
          delta•metricHorizonMassDifference q br amp w k a := by
      unfold wholeStaticMetricDifference massRestoredStaticDifference
      rw [← intervalIntegral.integral_add_adjacent_intervals hoi hii]
      simp only [Complex.real_smul,delta,D]
      push_cast
      ring
    refine ⟨hoi.trans hii,?_⟩
    rw [he]
    have ho' : ‖(∫ L in (0:ℝ)..A,D L)/2‖≤eo k := by
      simpa only [intervalIntegral.integral_div] using hob
    calc
      _ ≤ (‖(∫ L in (0:ℝ)..A,D L)/2‖+‖massRestoredStaticDifference q br amp w a A B T k‖)+
          ‖delta•metricHorizonMassDifference q br amp w k a‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ eo k+ei k+(A/2)*em k := by
        apply add_le_add (add_le_add ho' hib)
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd0]
        exact mul_le_mul hdA hmass (norm_nonneg _) (by linarith)

end
end RHTower.D4BMOriginalWholeStaticMetric
