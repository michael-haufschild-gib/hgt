import GaloisForLFunctions.RHTower.LiClockPairedEtaContiguousMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
/-!
# Actual finite eta difference density and radial order obstruction

The full disjoint logarithmic interval union and both independent half-tilts are
retained. Raw, normalized and folded source laws identify the canonical densities
with their literal measure pushforwards; both square normalizers remain explicit.

For `N ≥ 2`, the ratio decreases at small positive shifts and equals its sharp
normalization scale near the strict support edges. Both radial order directions
fail, including all Lebesgue and reference-law almost-everywhere versions. `N = 1`
is the exact equality exception. Quotient comparisons stay inside strict support.

The complete four-coordinate signed forcing density retains its coupled sign and
vanishes in the outer support band. These identities assert no inverse-clock sign,
uniform-prefix estimate or RH implication.
-/

open MeasureTheory Set Filter Topology RiemannGaussian
open scoped ENNReal Interval BigOperators
noncomputable section
namespace RHTower

private def intervalWeight (a b u : ℝ) : ℝ :=
  (Ioc a b).indicator (fun v : ℝ => Real.exp (-v/2)) u

private lemma integrable_intervalWeight (a b : ℝ) : Integrable (intervalWeight a b) := by
  unfold intervalWeight
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact (show Continuous (fun v : ℝ => Real.exp (-v/2)) by fun_prop).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self

private lemma intervalWeight_prod (a b c d x v : ℝ) :
  intervalWeight c d (v+x)*intervalWeight a b v =
    (Ioc (max a (c-x)) (min b (d-x))).indicator
      (fun v : ℝ => Real.exp (-x/2)*Real.exp (-v)) v := by
  have he : v∈Ioc (max a (c-x)) (min b (d-x)) ↔ v∈Ioc a b ∧ v+x∈Ioc c d := by
    simp only [mem_Ioc,max_lt_iff,le_min_iff]
    constructor <;> intro h <;> constructor <;> constructor <;> linarith [h.1.1,h.1.2,h.2.1,h.2.2]
  by_cases ha : v∈Ioc a b
  · by_cases hc : v+x∈Ioc c d
    · simp only [intervalWeight,indicator_of_mem ha,indicator_of_mem hc,indicator_of_mem (he.mpr ⟨ha,hc⟩)]
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    · simp [intervalWeight,ha,hc,he]
  · simp [intervalWeight,ha,he]

private lemma integral_Ioc_exp_neg (a b : ℝ) :
    (∫ v : ℝ in Ioc a b,Real.exp (-v)) = max 0 (Real.exp (-a)-Real.exp (-b)) := by
  by_cases hab : a≤b
  · rw [← intervalIntegral.integral_of_le hab,intervalIntegral.integral_comp_neg,integral_exp]
    exact (max_eq_right (sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg hab)))).symm
  · have hba : b<a := lt_of_not_ge hab
    rw [Ioc_eq_empty_of_le hba.le,setIntegral_empty]
    exact (max_eq_left (sub_nonpos.mpr (Real.exp_le_exp.mpr (neg_le_neg hba.le)))).symm

private lemma integral_intervalWeight_prod (a b c d x : ℝ) :
    (∫ v : ℝ,intervalWeight c d (v+x)*intervalWeight a b v) =
      Real.exp (-x/2)*max 0 (Real.exp (-max a (c-x))-Real.exp (-min b (d-x))) := by
  simp_rw [intervalWeight_prod]
  rw [integral_indicator measurableSet_Ioc,integral_const_mul,integral_Ioc_exp_neg]

private theorem map_sub_prod_density (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    Measure.map (fun p : ℝ × ℝ => p.1-p.2)
      ((volume.withDensity f).prod (volume.withDensity g)) =
      volume.withDensity (fun x : ℝ => ∫⁻ v : ℝ, f (v+x)*g v) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ (by fun_prop),prod_withDensity hf hg,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have hshift := (measurePreserving_add_prod (volume:Measure ℝ) volume).lintegral_comp
    (f:=fun p : ℝ×ℝ => (f p.1*g p.2)*φ (p.1-p.2)) (by fun_prop)
  have hm : Measurable (fun x : ℝ => ∫⁻ v : ℝ,f (v+x)*g v) :=
    (show Measurable (fun p : ℝ×ℝ=>f (p.2+p.1)*g p.2) by fun_prop).lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ hm hφ]
  simp only [Pi.mul_apply]
  rw [← hshift]
  simp only [add_sub_cancel_right]
  rw [lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro x
  rw [← lintegral_mul_const'' _ (by fun_prop)]
  apply lintegral_congr
  intro v
  rw [add_comm]

/-- Actual half-tilt weight of the full logarithmic interval union. -/
def liClockPairedEtaPartitionHalfTiltWeight (N : ℕ) (u : ℝ) : ℝ :=
  (liClockPairedEtaPartitionLogSupport N).indicator (fun v : ℝ => Real.exp (-v/2)) u

/-- Literal contiguous comparison half-tilt weight. -/
def liClockPairedEtaContiguousHalfTiltWeight (L u : ℝ) : ℝ :=
  intervalWeight 0 L u

/-- Canonical continuous raw difference density retaining both source coordinates. -/
def liClockPairedEtaPartitionRawDifferenceDensity (N : ℕ) (x : ℝ) : ℝ :=
  ∫ v : ℝ, liClockPairedEtaPartitionHalfTiltWeight N (v+x)*liClockPairedEtaPartitionHalfTiltWeight N v

/-- Canonical raw difference density of the literal contiguous comparison measure. -/
def liClockPairedEtaContiguousRawDifferenceDensity (L x : ℝ) : ℝ :=
  ∫ v : ℝ, liClockPairedEtaContiguousHalfTiltWeight L (v+x)*liClockPairedEtaContiguousHalfTiltWeight L v

private theorem actualWeight_sum (N : ℕ) (u : ℝ) :
    liClockPairedEtaPartitionHalfTiltWeight N u =
      ∑ n ∈ Finset.range N, intervalWeight (Real.log (2*n+1)) (Real.log (2*n+2)) u := by
  by_cases hu : u∈liClockPairedEtaPartitionLogSupport N
  · obtain ⟨n,hn,hun⟩ := (show ∃n∈Finset.range N,u∈Ioc (Real.log (2*n+1)) (Real.log (2*n+2)) by
      simpa only [liClockPairedEtaPartitionLogSupport,mem_iUnion,exists_prop] using hu)
    rw [liClockPairedEtaPartitionHalfTiltWeight,indicator_of_mem hu]
    rw [Finset.sum_eq_single n]
    · simp [intervalWeight,hun]
    · intro m hm hmn
      have hum : u∉Ioc (Real.log (2*m+1)) (Real.log (2*m+2)) := by
        intro hum
        exact Set.disjoint_left.mp (liClockPairedEtaPartitionLogIntervals_pairwiseDisjoint hmn) hum hun
      simp [intervalWeight,hum]
    · exact fun h => (h hn).elim
  · have hn (n : ℕ) (hn : n∈Finset.range N) :
        u∉Ioc (Real.log (2*n+1)) (Real.log (2*n+2)) := by
      intro hun
      exact hu (by simp only [liClockPairedEtaPartitionLogSupport,mem_iUnion]; exact ⟨n,hn,hun⟩)
    rw [liClockPairedEtaPartitionHalfTiltWeight,indicator_of_notMem hu]
    symm
    apply Finset.sum_eq_zero
    intro n hmem
    simp [intervalWeight,hn n hmem]

private theorem integrable_actualWeight (N : ℕ) : Integrable (liClockPairedEtaPartitionHalfTiltWeight N) := by
  have heq : liClockPairedEtaPartitionHalfTiltWeight N = fun u =>
      ∑ n ∈ Finset.range N, intervalWeight (Real.log (2*n+1)) (Real.log (2*n+2)) u :=
    funext (actualWeight_sum N)
  rw [heq]
  exact integrable_finsetSum _ (fun n hn => integrable_intervalWeight _ _)

private theorem actualWeight_nonneg (N : ℕ) (u : ℝ) : 0≤liClockPairedEtaPartitionHalfTiltWeight N u := by
  unfold liClockPairedEtaPartitionHalfTiltWeight
  exact indicator_nonneg (fun v hv => (Real.exp_pos _).le) u

private theorem actualWeight_le_one (N : ℕ) (u : ℝ) : liClockPairedEtaPartitionHalfTiltWeight N u ≤ 1 := by
  by_cases hu : u∈liClockPairedEtaPartitionLogSupport N
  · have hpos := (liClockPairedEtaPartitionLogSupport_subset_Ioc N hu).1
    simp only [liClockPairedEtaPartitionHalfTiltWeight,indicator_of_mem hu]
    exact Real.exp_le_one_iff.mpr (by linarith)
  · simp [liClockPairedEtaPartitionHalfTiltWeight,hu]


private theorem intervalWeight_nonneg (a b u : ℝ) : 0 ≤ intervalWeight a b u := by
  unfold intervalWeight
  exact indicator_nonneg (fun v hv => (Real.exp_pos _).le) u

private theorem intervalWeight_le (a b u : ℝ) : intervalWeight a b u ≤ Real.exp (-a/2) := by
  by_cases hu : u∈Ioc a b
  · simp only [intervalWeight,indicator_of_mem hu]
    exact Real.exp_le_exp.mpr (by linarith [hu.1])
  · simp [intervalWeight,hu,(Real.exp_pos _).le]

private theorem measurable_intervalWeight (a b : ℝ) : Measurable (intervalWeight a b) := by
  unfold intervalWeight
  exact (show Measurable (fun v : ℝ => Real.exp (-v/2)) by fun_prop).indicator measurableSet_Ioc

private theorem integrable_intervalWeight_prod (a b c d x : ℝ) :
    Integrable (fun v : ℝ => intervalWeight c d (v+x)*intervalWeight a b v) := by
  apply (integrable_intervalWeight a b).bdd_mul (c:=Real.exp (-c/2))
    ((measurable_intervalWeight c d).comp (measurable_id.add measurable_const)).aestronglyMeasurable
  exact Eventually.of_forall (fun v => by
    change ‖intervalWeight c d (v+x)‖ ≤ Real.exp (-c/2)
    rw [Real.norm_eq_abs,abs_of_nonneg (intervalWeight_nonneg c d _)]
    exact intervalWeight_le c d _)

/-- Complete finite interval-pair expansion of the actual raw density. -/
theorem liClockPairedEtaPartitionRawDifferenceDensity_eq_sum (N : ℕ) (x : ℝ) :
    liClockPairedEtaPartitionRawDifferenceDensity N x =
      ∑ n ∈ Finset.range N,∑ m ∈ Finset.range N,
        Real.exp (-x/2)*max 0
          (Real.exp (-max (Real.log (2*m+1)) (Real.log (2*n+1)-x))-
            Real.exp (-min (Real.log (2*m+2)) (Real.log (2*n+2)-x))) := by
  unfold liClockPairedEtaPartitionRawDifferenceDensity
  simp_rw [actualWeight_sum,Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro m hm
      exact integral_intervalWeight_prod _ _ _ _ x
    · intro m hm
      exact integrable_intervalWeight_prod _ _ _ _ x
  · intro n hn
    exact integrable_finsetSum _ (fun m hm => integrable_intervalWeight_prod _ _ _ _ x)

theorem continuous_liClockPairedEtaPartitionRawDifferenceDensity (N : ℕ) :
    Continuous (liClockPairedEtaPartitionRawDifferenceDensity N) := by
  have heq : liClockPairedEtaPartitionRawDifferenceDensity N = fun x : ℝ =>
      ∑ n ∈ Finset.range N,∑ m ∈ Finset.range N,
        Real.exp (-x/2)*max 0
          (Real.exp (-max (Real.log (2*m+1)) (Real.log (2*n+1)-x))-
            Real.exp (-min (Real.log (2*m+2)) (Real.log (2*n+2)-x))) :=
    funext (liClockPairedEtaPartitionRawDifferenceDensity_eq_sum N)
  rw [heq]
  fun_prop

theorem liClockPairedEtaContiguousRawDifferenceDensity_eq (L x : ℝ) :
    liClockPairedEtaContiguousRawDifferenceDensity L x =
      Real.exp (-x/2)*max 0
        (Real.exp (-max 0 (-x))-Real.exp (-min L (L-x))) := by
  simpa only [liClockPairedEtaContiguousRawDifferenceDensity,liClockPairedEtaContiguousHalfTiltWeight,zero_sub] using integral_intervalWeight_prod 0 L 0 L x

theorem continuous_liClockPairedEtaContiguousRawDifferenceDensity (L : ℝ) :
    Continuous (liClockPairedEtaContiguousRawDifferenceDensity L) := by
  have heq : liClockPairedEtaContiguousRawDifferenceDensity L = fun x : ℝ =>
      Real.exp (-x/2)*max 0
        (Real.exp (-max 0 (-x))-Real.exp (-min L (L-x))) :=
    funext (liClockPairedEtaContiguousRawDifferenceDensity_eq L)
  rw [heq]
  fun_prop


private theorem measurable_actualWeight (N : ℕ) : Measurable (liClockPairedEtaPartitionHalfTiltWeight N) := by
  unfold liClockPairedEtaPartitionHalfTiltWeight
  exact (show Measurable (fun v : ℝ => Real.exp (-v/2)) by fun_prop).indicator
    (measurableSet_liClockPairedEtaPartitionLogSupport N)

private theorem integrable_actualWeight_prod (N : ℕ) (x : ℝ) :
    Integrable (fun v : ℝ => liClockPairedEtaPartitionHalfTiltWeight N (v+x)*liClockPairedEtaPartitionHalfTiltWeight N v) := by
  apply (integrable_actualWeight N).bdd_mul (c:=1)
    ((measurable_actualWeight N).comp (measurable_id.add measurable_const)).aestronglyMeasurable
  exact Eventually.of_forall (fun v => by
    change ‖liClockPairedEtaPartitionHalfTiltWeight N (v+x)‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (actualWeight_nonneg N _)]
    exact actualWeight_le_one N _)

private theorem raw_even (f : ℝ → ℝ) (x : ℝ) :
    (∫ v : ℝ,f (v-x)*f v) = ∫ v : ℝ,f (v+x)*f v := by
  calc
    _ = ∫ v : ℝ,f v*f (v+x) := by
      have h := integral_add_right_eq_self (μ:=volume) (fun v : ℝ=>f (v-x)*f v) x
      simpa only [add_sub_cancel_right] using h.symm
    _ = _ := by apply integral_congr_ae; filter_upwards [] with v; exact mul_comm _ _

theorem liClockPairedEtaPartitionRawDifferenceDensity_even (N : ℕ) (x : ℝ) :
    liClockPairedEtaPartitionRawDifferenceDensity N (-x) = liClockPairedEtaPartitionRawDifferenceDensity N x := by
  simpa only [liClockPairedEtaPartitionRawDifferenceDensity,sub_eq_add_neg] using
    raw_even (liClockPairedEtaPartitionHalfTiltWeight N) x

theorem liClockPairedEtaContiguousRawDifferenceDensity_even (L x : ℝ) :
    liClockPairedEtaContiguousRawDifferenceDensity L (-x) = liClockPairedEtaContiguousRawDifferenceDensity L x := by
  simpa only [liClockPairedEtaContiguousRawDifferenceDensity,sub_eq_add_neg] using
    raw_even (liClockPairedEtaContiguousHalfTiltWeight L) x

theorem liClockPairedEtaPartitionRawDifferenceDensity_nonneg (N : ℕ) (x : ℝ) :
    0 ≤ liClockPairedEtaPartitionRawDifferenceDensity N x := by
  exact integral_nonneg (fun v => mul_nonneg (actualWeight_nonneg N _) (actualWeight_nonneg N _))

theorem liClockPairedEtaContiguousRawDifferenceDensity_nonneg (L x : ℝ) :
    0 ≤ liClockPairedEtaContiguousRawDifferenceDensity L x := by
  exact integral_nonneg (fun v => mul_nonneg (intervalWeight_nonneg 0 L _) (intervalWeight_nonneg 0 L _))

private theorem actualWeight_le_contiguous (N : ℕ) (u : ℝ) :
    liClockPairedEtaPartitionHalfTiltWeight N u ≤
      liClockPairedEtaContiguousHalfTiltWeight (Real.log (2*(N:ℝ))) u := by
  by_cases hu : u∈liClockPairedEtaPartitionLogSupport N
  · have hv := liClockPairedEtaPartitionLogSupport_subset_Ioc N hu
    simp [liClockPairedEtaPartitionHalfTiltWeight,liClockPairedEtaContiguousHalfTiltWeight,intervalWeight,hu,hv]
  · have hv := intervalWeight_nonneg 0 (Real.log (2*(N:ℝ))) u
    simpa [liClockPairedEtaPartitionHalfTiltWeight,liClockPairedEtaContiguousHalfTiltWeight,hu] using hv

theorem liClockPairedEtaPartitionRawDifferenceDensity_le_contiguous (N : ℕ) (x : ℝ) :
    liClockPairedEtaPartitionRawDifferenceDensity N x ≤
      liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) x := by
  apply integral_mono (integrable_actualWeight_prod N x)
    (integrable_intervalWeight_prod 0 _ 0 _ x)
  intro v
  exact mul_le_mul (actualWeight_le_contiguous N _) (actualWeight_le_contiguous N _)
    (actualWeight_nonneg N _) (intervalWeight_nonneg 0 _ _)

theorem liClockPairedEtaContiguousRawDifferenceDensity_eq_of_nonneg {L x : ℝ}
    (hx : 0 ≤ x) (hxL : x < L) :
    liClockPairedEtaContiguousRawDifferenceDensity L x =
      Real.exp (-x/2)*(1-Real.exp (x-L)) := by
  rw [liClockPairedEtaContiguousRawDifferenceDensity_eq]
  rw [max_eq_left (by linarith : -x ≤ 0),min_eq_right (by linarith : L-x ≤ L)]
  rw [neg_zero,Real.exp_zero,show -(L-x)=x-L by ring]
  rw [max_eq_right (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (sub_nonpos.mpr hxL.le)))]


/-- Width of the literal last retained logarithmic interval. -/
def liClockPairedEtaPartitionEdgeWidth (N : ℕ) : ℝ :=
  Real.log (2*(N:ℝ)/(2*(N:ℝ)-1))

private theorem cast_one_le {N : ℕ} (hN : 0 < N) : (1:ℝ)≤(N:ℝ) := by exact_mod_cast hN

private theorem last_endpoint_pos {N : ℕ} (hN : 0 < N) : 0 < 2*(N:ℝ)-1 := by
  linarith [cast_one_le hN]

theorem liClockPairedEtaPartitionEdgeWidth_pos {N : ℕ} (hN : 0 < N) :
    0 < liClockPairedEtaPartitionEdgeWidth N := by
  unfold liClockPairedEtaPartitionEdgeWidth
  apply Real.log_pos
  exact (one_lt_div (last_endpoint_pos hN)).mpr (by linarith)

theorem liClockPairedEtaPartitionEdgeWidth_le_log_two {N : ℕ} (hN : 0 < N) :
    liClockPairedEtaPartitionEdgeWidth N ≤ Real.log 2 := by
  unfold liClockPairedEtaPartitionEdgeWidth
  apply Real.log_le_log (div_pos (by positivity) (last_endpoint_pos hN))
  exact (div_le_iff₀ (last_endpoint_pos hN)).mpr (by linarith [cast_one_le hN])

theorem liClockPairedEtaPartitionLog_sub_edgeWidth_eq {N : ℕ} (hN : 0 < N) :
    Real.log (2*(N:ℝ))-liClockPairedEtaPartitionEdgeWidth N = Real.log (2*(N:ℝ)-1) := by
  unfold liClockPairedEtaPartitionEdgeWidth
  rw [Real.log_div (by positivity) (last_endpoint_pos hN).ne']
  ring

theorem liClockPairedEtaPartitionEdgeWidth_le_log {N : ℕ} (hN : 0 < N) :
    liClockPairedEtaPartitionEdgeWidth N ≤ Real.log (2*(N:ℝ)) := by
  have he := liClockPairedEtaPartitionLog_sub_edgeWidth_eq hN
  have hp : 0 ≤ Real.log (2*(N:ℝ)-1) := Real.log_nonneg (by linarith [cast_one_le hN])
  linarith

private theorem edgeWidth_le_interval {N n : ℕ} (hn : n < N) :
    liClockPairedEtaPartitionEdgeWidth N ≤ Real.log (2*(n:ℝ)+2)-Real.log (2*(n:ℝ)+1) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le n) hn
  have hnp : 0 < 2*(n:ℝ)+1 := by positivity
  rw [← Real.log_div (by positivity) hnp.ne']
  unfold liClockPairedEtaPartitionEdgeWidth
  apply Real.log_le_log (div_pos (by positivity) (last_endpoint_pos hN))
  apply (div_le_div_iff₀ (last_endpoint_pos hN) hnp).mpr
  have hncast : (n:ℝ)+1 ≤ (N:ℝ) := by exact_mod_cast hn
  nlinarith

private theorem edgeWidth_lt_cross_gap {N n m : ℕ} (hm : m < N) (hnm : n < m) :
    liClockPairedEtaPartitionEdgeWidth N < Real.log (2*(m:ℝ)+1)-Real.log (2*(n:ℝ)+2) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le m) hm
  have hnp : 0 < 2*(n:ℝ)+2 := by positivity
  rw [← Real.log_div (by positivity) hnp.ne']
  unfold liClockPairedEtaPartitionEdgeWidth
  apply Real.log_lt_log (div_pos (by positivity) (last_endpoint_pos hN))
  apply (div_lt_div_iff₀ (last_endpoint_pos hN) hnp).mpr
  have hnmcast : (n:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast hnm
  have hmcast : (m:ℝ)+1 ≤ (N:ℝ) := by exact_mod_cast hm
  have hmul := mul_nonneg (show 0 ≤ (N:ℝ) by positivity) (show 0 ≤ (m:ℝ)-(n:ℝ)-1 by linarith)
  nlinarith


private theorem contiguousRaw_zero_of_nonneg {L x : ℝ} (hx : 0 ≤ x) (hxL : L ≤ x) :
    liClockPairedEtaContiguousRawDifferenceDensity L x = 0 := by
  rw [liClockPairedEtaContiguousRawDifferenceDensity_eq]
  rw [max_eq_left (by linarith : -x ≤ 0),min_eq_right (by linarith : L-x ≤ L)]
  rw [neg_zero,Real.exp_zero]
  have he : 1 ≤ Real.exp (-(L-x)) := Real.one_le_exp_iff.mpr (by linarith)
  rw [max_eq_left (by linarith : 1-Real.exp (-(L-x)) ≤ 0),mul_zero]

theorem liClockPairedEtaContiguousRawDifferenceDensity_zero_of_le_abs {L x : ℝ}
    (hxL : L ≤ |x|) : liClockPairedEtaContiguousRawDifferenceDensity L x = 0 := by
  by_cases hx : 0 ≤ x
  · apply contiguousRaw_zero_of_nonneg hx
    simpa only [abs_of_nonneg hx] using hxL
  · have hxneg : x<0 := lt_of_not_ge hx
    rw [← liClockPairedEtaContiguousRawDifferenceDensity_even L x]
    apply contiguousRaw_zero_of_nonneg (by linarith)
    simpa only [abs_of_neg hxneg] using hxL

theorem liClockPairedEtaPartitionRawDifferenceDensity_zero_of_log_le_abs {N : ℕ} {x : ℝ}
    (hxL : Real.log (2*(N:ℝ)) ≤ |x|) : liClockPairedEtaPartitionRawDifferenceDensity N x = 0 := by
  apply le_antisymm _ (liClockPairedEtaPartitionRawDifferenceDensity_nonneg N x)
  exact (liClockPairedEtaPartitionRawDifferenceDensity_le_contiguous N x).trans_eq
    (liClockPairedEtaContiguousRawDifferenceDensity_zero_of_le_abs hxL)

private theorem integrable_pow_mul_raw {g : ℝ → ℝ} {L : ℝ} (hg : Continuous g)
    (hz : ∀x:ℝ,L ≤ |x| → g x=0) (j : ℕ) : Integrable (fun x : ℝ => x^(2*j)*g x) := by
  have hs : Function.support (fun x : ℝ => x^(2*j)*g x) ⊆ Icc (-L) L := by
    intro x hx
    have hxg : g x≠0 := (mul_ne_zero_iff.mp hx).2
    have hxL : |x|<L := lt_of_not_ge (fun h => hxg (hz x h))
    exact ⟨by linarith [(abs_lt.mp hxL).1],(abs_lt.mp hxL).2.le⟩
  exact (integrableOn_iff_integrable_of_support_subset hs).mp
    ((show Continuous (fun x : ℝ=>x^(2*j)*g x) by fun_prop).continuousOn.integrableOn_Icc)

theorem integrable_pow_mul_liClockPairedEtaPartitionRawDifferenceDensity (N j : ℕ) :
    Integrable (fun x : ℝ => x^(2*j)*liClockPairedEtaPartitionRawDifferenceDensity N x) :=
  integrable_pow_mul_raw (continuous_liClockPairedEtaPartitionRawDifferenceDensity N)
    (fun _ hx => liClockPairedEtaPartitionRawDifferenceDensity_zero_of_log_le_abs hx) j

theorem integrable_pow_mul_liClockPairedEtaContiguousRawDifferenceDensity (L : ℝ) (j : ℕ) :
    Integrable (fun x : ℝ => x^(2*j)*liClockPairedEtaContiguousRawDifferenceDensity L x) :=
  integrable_pow_mul_raw (continuous_liClockPairedEtaContiguousRawDifferenceDensity L)
    (fun _ hx => liClockPairedEtaContiguousRawDifferenceDensity_zero_of_le_abs hx) j

/-- Full raw source product pushforward, prior to probability normalization. -/
theorem liClockPairedEtaPartitionRawDifferenceDensity_map (N : ℕ) :
    Measure.map (fun p : ℝ×ℝ=>p.1-p.2)
      ((volume.withDensity (fun u=>ENNReal.ofReal (liClockPairedEtaPartitionHalfTiltWeight N u))).prod
        (volume.withDensity (fun u=>ENNReal.ofReal (liClockPairedEtaPartitionHalfTiltWeight N u)))) =
      volume.withDensity (fun x=>ENNReal.ofReal (liClockPairedEtaPartitionRawDifferenceDensity N x)) := by
  rw [map_sub_prod_density _ _ (measurable_actualWeight N).ennreal_ofReal (measurable_actualWeight N).ennreal_ofReal]
  congr 1
  funext x
  rw [liClockPairedEtaPartitionRawDifferenceDensity,
    ofReal_integral_eq_lintegral_ofReal (integrable_actualWeight_prod N x)
      (Eventually.of_forall fun v=>mul_nonneg (actualWeight_nonneg N _) (actualWeight_nonneg N _))]
  apply lintegral_congr
  intro v
  exact (ENNReal.ofReal_mul (actualWeight_nonneg N _)).symm

/-- Full raw contiguous product pushforward. -/
theorem liClockPairedEtaContiguousRawDifferenceDensity_map (L : ℝ) :
    Measure.map (fun p : ℝ×ℝ=>p.1-p.2)
      ((volume.withDensity (fun u=>ENNReal.ofReal (liClockPairedEtaContiguousHalfTiltWeight L u))).prod
        (volume.withDensity (fun u=>ENNReal.ofReal (liClockPairedEtaContiguousHalfTiltWeight L u)))) =
      volume.withDensity (fun x=>ENNReal.ofReal (liClockPairedEtaContiguousRawDifferenceDensity L x)) := by
  unfold liClockPairedEtaContiguousHalfTiltWeight
  rw [map_sub_prod_density _ _ (measurable_intervalWeight 0 L).ennreal_ofReal
    (measurable_intervalWeight 0 L).ennreal_ofReal]
  congr 1
  funext x
  change (∫⁻ v:ℝ, ENNReal.ofReal (intervalWeight 0 L (v+x))*ENNReal.ofReal (intervalWeight 0 L v)) =
    ENNReal.ofReal (∫v:ℝ,intervalWeight 0 L (v+x)*intervalWeight 0 L v)
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_intervalWeight_prod 0 L 0 L x)
      (Eventually.of_forall fun v=>mul_nonneg (intervalWeight_nonneg 0 L _) (intervalWeight_nonneg 0 L _))]
  apply lintegral_congr
  intro v
  exact (ENNReal.ofReal_mul (intervalWeight_nonneg 0 L _)).symm

/-- Exact arithmetic heads retained in the local overlap formula. -/
def liClockPairedEtaPartitionOddReciprocalHead (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,1/(2*(n:ℝ)+1)

def liClockPairedEtaPartitionEvenReciprocalHead (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,1/(2*(n:ℝ)+2)

private theorem rawPair_zero {N n m : ℕ} (hn : n<N) (hm : m<N) (hnm : n≠m)
    {x : ℝ} (hx : 0≤x) (hxeps : x<liClockPairedEtaPartitionEdgeWidth N) :
    Real.exp (-x/2)*max 0
      (Real.exp (-max (Real.log (2*(m:ℝ)+1)) (Real.log (2*(n:ℝ)+1)-x))-
        Real.exp (-min (Real.log (2*(m:ℝ)+2)) (Real.log (2*(n:ℝ)+2)-x))) = 0 := by
  have he : min (Real.log (2*(m:ℝ)+2)) (Real.log (2*(n:ℝ)+2)-x) ≤
      max (Real.log (2*(m:ℝ)+1)) (Real.log (2*(n:ℝ)+1)-x) := by
    rcases lt_or_gt_of_ne hnm with hnm | hmn
    · have hgap := edgeWidth_lt_cross_gap hm hnm
      have heps := liClockPairedEtaPartitionEdgeWidth_pos (lt_of_le_of_lt (Nat.zero_le m) hm)
      exact (min_le_right _ _).trans ((by linarith : Real.log (2*(n:ℝ)+2)-x ≤ Real.log (2*(m:ℝ)+1)).trans (le_max_left _ _))
    · have hgap := edgeWidth_lt_cross_gap hn hmn
      exact (min_le_left _ _).trans ((by linarith : Real.log (2*(m:ℝ)+2) ≤ Real.log (2*(n:ℝ)+1)-x).trans (le_max_right _ _))
  rw [max_eq_left (sub_nonpos.mpr (Real.exp_le_exp.mpr (neg_le_neg he))),mul_zero]

private theorem rawPair_self {N n : ℕ} (hn : n<N) {x : ℝ} (hx : 0≤x)
    (hxeps : x<liClockPairedEtaPartitionEdgeWidth N) :
    Real.exp (-x/2)*max 0
      (Real.exp (-max (Real.log (2*(n:ℝ)+1)) (Real.log (2*(n:ℝ)+1)-x))-
        Real.exp (-min (Real.log (2*(n:ℝ)+2)) (Real.log (2*(n:ℝ)+2)-x))) =
      Real.exp (-x/2)*(1/(2*(n:ℝ)+1)-Real.exp x/(2*(n:ℝ)+2)) := by
  have hw := edgeWidth_le_interval hn
  rw [max_eq_left (by linarith : Real.log (2*(n:ℝ)+1)-x ≤ Real.log (2*(n:ℝ)+1)),
    min_eq_right (by linarith : Real.log (2*(n:ℝ)+2)-x ≤ Real.log (2*(n:ℝ)+2))]
  rw [max_eq_right (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith)))]
  rw [Real.exp_neg,Real.exp_log (by positivity),show -(Real.log (2*(n:ℝ)+2)-x)=x-Real.log (2*(n:ℝ)+2) by ring,
    Real.exp_sub,Real.exp_log (by positivity)]
  rw [one_div]

/-- Every small shift retains exactly the same-interval contributions. -/
theorem liClockPairedEtaPartitionRawDifferenceDensity_eq_local {N : ℕ} {x : ℝ}
    (hx : 0≤x) (hxeps : x<liClockPairedEtaPartitionEdgeWidth N) :
    liClockPairedEtaPartitionRawDifferenceDensity N x = Real.exp (-x/2)*
      (liClockPairedEtaPartitionOddReciprocalHead N-Real.exp x*liClockPairedEtaPartitionEvenReciprocalHead N) := by
  rw [liClockPairedEtaPartitionRawDifferenceDensity_eq_sum]
  have he : ∀ n∈Finset.range N,(∑ m∈Finset.range N,Real.exp (-x/2)*max 0
      (Real.exp (-max (Real.log (2*(m:ℝ)+1)) (Real.log (2*(n:ℝ)+1)-x))-
        Real.exp (-min (Real.log (2*(m:ℝ)+2)) (Real.log (2*(n:ℝ)+2)-x)))) =
      Real.exp (-x/2)*(1/(2*(n:ℝ)+1)-Real.exp x/(2*(n:ℝ)+2)) := by
    intro n hn
    rw [Finset.sum_eq_single n]
    · exact rawPair_self (Finset.mem_range.mp hn) hx hxeps
    · intro m hm hmn
      exact rawPair_zero (Finset.mem_range.mp hn) (Finset.mem_range.mp hm) hmn.symm hx hxeps
    · exact fun h => (h hn).elim
  simp_rw [Finset.sum_congr rfl he]
  rw [liClockPairedEtaPartitionOddReciprocalHead,liClockPairedEtaPartitionEvenReciprocalHead,
    Finset.mul_sum,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

private theorem rawWeight_measure (S : Set ℝ) (hS : MeasurableSet S) :
    volume.withDensity (fun u=>ENNReal.ofReal (S.indicator (fun v:ℝ=>Real.exp (-v/2)) u)) =
      (volume.restrict S).withDensity (fun u=>ENNReal.ofReal (Real.exp (-u/2))) := by
  rw [← withDensity_indicator hS]
  congr 1
  funext u
  by_cases hu:u∈S <;> simp [hu]

private theorem rawProd_weight (ν : Measure ℝ) [SFinite ν] :
    (ν.withDensity (fun u=>ENNReal.ofReal (Real.exp (-u/2)))).prod
      (ν.withDensity (fun u=>ENNReal.ofReal (Real.exp (-u/2)))) =
      (ν.prod ν).withDensity (fun p:ℝ×ℝ=>ENNReal.ofReal (Real.exp (-(p.1+p.2)/2))) := by
  rw [prod_withDensity (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  ring

private theorem tilted_eq_scaled_raw (ν : Measure ℝ) [SFinite ν] (Z : ℝ)
    (hZ : 0<Z)
    (hnorm : (∫p:ℝ×ℝ,Real.exp (-(p.1+p.2)/2) ∂ν.prod ν)=Z^2) :
    (ν.prod ν).tilted (fun p:ℝ×ℝ=>-(p.1+p.2)/2) =
      ENNReal.ofReal (1/Z^2) • ((ν.withDensity (fun u=>ENNReal.ofReal (Real.exp (-u/2)))).prod
        (ν.withDensity (fun u=>ENNReal.ofReal (Real.exp (-u/2))))) := by
  rw [rawProd_weight,Measure.tilted,hnorm,← withDensity_smul _ (by fun_prop)]
  congr 1
  funext p
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

private theorem actual_joint_integral (N : ℕ) :
    (∫p:ℝ×ℝ,Real.exp (-(p.1+p.2)/2) ∂(pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N)) =
      liClockPairedEtaPartitionNormalizer N^2 := by
  have he : ∀p:ℝ×ℝ,Real.exp (-(p.1+p.2)/2)=Real.exp (-p.1/2)*Real.exp (-p.2/2) := by
    intro p
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  simpa only [liClockPairedEtaPartitionNormalizer,pow_two] using
    integral_prod_mul (μ:=pairedEtaFiniteLogMeasure N) (ν:=pairedEtaFiniteLogMeasure N)
      (fun u:ℝ=>Real.exp (-u/2)) (fun u:ℝ=>Real.exp (-u/2))

/-- Actual normalized continuous difference density, with the full square normalizer. -/
def liClockPairedEtaPartitionDifferenceDensity (N : ℕ) (x : ℝ) : ℝ :=
  liClockPairedEtaPartitionRawDifferenceDensity N x / liClockPairedEtaPartitionNormalizer N^2

/-- Reference normalized continuous difference density. -/
def liClockPairedEtaContiguousDifferenceDensity (L x : ℝ) : ℝ :=
  liClockPairedEtaContiguousRawDifferenceDensity L x / liClockPairedEtaContiguousPartitionNormalizer L^2

/-- Source-typed probability pushforward, with both half-tilts and both normalizers retained. -/
theorem liClockPairedEtaPartitionDifferenceDensity_map {N : ℕ} (hN : 0<N) :
    Measure.map (fun p:ℝ×ℝ=>p.1-p.2) (liClockPairedEtaSymmetrizedMeasure N) =
      volume.withDensity (fun x=>ENNReal.ofReal (liClockPairedEtaPartitionDifferenceDensity N x)) := by
  rw [liClockPairedEtaSymmetrizedMeasure,
    tilted_eq_scaled_raw _ _ (liClockPairedEtaPartitionNormalizer_pos hN) (actual_joint_integral N),
    pairedEtaFiniteLogMeasure_eq_restrict_union N,
    ← rawWeight_measure _ (measurableSet_liClockPairedEtaPartitionLogSupport N)]
  change Measure.map (fun p:ℝ×ℝ=>p.1-p.2)
    (ENNReal.ofReal (1/liClockPairedEtaPartitionNormalizer N^2) •
      ((volume.withDensity (fun u=>ENNReal.ofReal (liClockPairedEtaPartitionHalfTiltWeight N u))).prod
        (volume.withDensity (fun u=>ENNReal.ofReal (liClockPairedEtaPartitionHalfTiltWeight N u))))) = _
  rw [Measure.map_smul,liClockPairedEtaPartitionRawDifferenceDensity_map,
    ← withDensity_smul _ (continuous_liClockPairedEtaPartitionRawDifferenceDensity N).measurable.ennreal_ofReal]
  congr 1
  funext x
  simp only [Pi.smul_apply,smul_eq_mul,liClockPairedEtaPartitionDifferenceDensity]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- Exact normalized reference difference law. -/
theorem liClockPairedEtaContiguousDifferenceDensity_map {L : ℝ} (hL : 0<L) :
    Measure.map (fun p:ℝ×ℝ=>p.1-p.2) (liClockPairedEtaContiguousSymmetrizedMeasure L) =
      volume.withDensity (fun x=>ENNReal.ofReal (liClockPairedEtaContiguousDifferenceDensity L x)) := by
  rw [liClockPairedEtaContiguousSymmetrizedMeasure,
    tilted_eq_scaled_raw _ _ (liClockPairedEtaContiguousPartitionNormalizer_pos hL)
      (liClockPairedEtaContiguousJointWeight_integral L),
    liClockPairedEtaContiguousLogMeasure,← rawWeight_measure _ measurableSet_Ioc]
  change Measure.map (fun p:ℝ×ℝ=>p.1-p.2)
    (ENNReal.ofReal (1/liClockPairedEtaContiguousPartitionNormalizer L^2) •
      ((volume.withDensity (fun u=>ENNReal.ofReal (liClockPairedEtaContiguousHalfTiltWeight L u))).prod
        (volume.withDensity (fun u=>ENNReal.ofReal (liClockPairedEtaContiguousHalfTiltWeight L u))))) = _
  rw [Measure.map_smul,liClockPairedEtaContiguousRawDifferenceDensity_map,
    ← withDensity_smul _ (continuous_liClockPairedEtaContiguousRawDifferenceDensity L).measurable.ennreal_ofReal]
  congr 1
  funext x
  simp only [Pi.smul_apply,smul_eq_mul,liClockPairedEtaContiguousDifferenceDensity]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- Sharp fixed-prefix normalization comparison scale. -/
def liClockPairedEtaPartitionComparisonScale (N : ℕ) : ℝ :=
  (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ))) /
    liClockPairedEtaPartitionNormalizer N)^2

private theorem log_endpoint_pos {N : ℕ} (hN : 0<N) : 0<Real.log (2*(N:ℝ)) :=
  Real.log_pos (by have h := cast_one_le hN; linarith)

/-- Both source coordinates lie in retained first and last intervals on the strict edge band. -/
theorem liClockPairedEtaPartitionRawDifferenceDensity_eq_contiguous_on_edge {N : ℕ}
    (hN : 0<N) {x : ℝ} (hxlo : Real.log (2*(N:ℝ))-liClockPairedEtaPartitionEdgeWidth N < |x|)
    (hxhi : |x|<Real.log (2*(N:ℝ))) :
    liClockPairedEtaPartitionRawDifferenceDensity N x =
      liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) x := by
  have hp {x : ℝ} (hx : 0≤x)
      (hxlo : Real.log (2*(N:ℝ))-liClockPairedEtaPartitionEdgeWidth N<x)
      (hxhi : x<Real.log (2*(N:ℝ))) :
      liClockPairedEtaPartitionRawDifferenceDensity N x =
        liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) x := by
    apply integral_congr_ae
    filter_upwards [] with v
    by_cases hv:v∈Ioc 0 (Real.log (2*(N:ℝ)))
    · by_cases hw:v+x∈Ioc 0 (Real.log (2*(N:ℝ)))
      · have hv2 : v∈Ioc (Real.log (2*(0:ℝ)+1)) (Real.log (2*(0:ℝ)+2)) := by
          constructor
          · simpa using hv.1
          · have he := liClockPairedEtaPartitionEdgeWidth_le_log_two hN
            norm_num only [mul_zero,zero_add]
            linarith [hw.2]
        have hnlast : N-1<N := by omega
        have hncast : ((N-1:ℕ):ℝ)+1=(N:ℝ) := by exact_mod_cast Nat.sub_add_cancel (by omega : 1≤N)
        have hwlast : v+x∈Ioc (Real.log (2*((N-1:ℕ):ℝ)+1)) (Real.log (2*((N-1:ℕ):ℝ)+2)) := by
          have hlow : Real.log (2*((N-1:ℕ):ℝ)+1)=Real.log (2*(N:ℝ))-liClockPairedEtaPartitionEdgeWidth N := by
            rw [liClockPairedEtaPartitionLog_sub_edgeWidth_eq hN]
            congr 1
            linarith
          have hhigh : Real.log (2*((N-1:ℕ):ℝ)+2)=Real.log (2*(N:ℝ)) := by congr 1; linarith
          rw [hlow,hhigh]
          exact ⟨by linarith [hv.1],hw.2⟩
        have hvA : v∈liClockPairedEtaPartitionLogSupport N := by
          simp only [liClockPairedEtaPartitionLogSupport,mem_iUnion]
          exact ⟨0,Finset.mem_range.mpr hN,by simpa using hv2⟩
        have hwA : v+x∈liClockPairedEtaPartitionLogSupport N := by
          simp only [liClockPairedEtaPartitionLogSupport,mem_iUnion]
          exact ⟨N-1,Finset.mem_range.mpr hnlast,hwlast⟩
        simp [liClockPairedEtaPartitionHalfTiltWeight,liClockPairedEtaContiguousHalfTiltWeight,intervalWeight,hv,hw,hvA,hwA]
      · have hwA : v+x∉liClockPairedEtaPartitionLogSupport N := fun h=>hw (liClockPairedEtaPartitionLogSupport_subset_Ioc N h)
        simp [liClockPairedEtaPartitionHalfTiltWeight,liClockPairedEtaContiguousHalfTiltWeight,intervalWeight,hw,hwA]
    · have hvA : v∉liClockPairedEtaPartitionLogSupport N := fun h=>hv (liClockPairedEtaPartitionLogSupport_subset_Ioc N h)
      simp [liClockPairedEtaPartitionHalfTiltWeight,liClockPairedEtaContiguousHalfTiltWeight,intervalWeight,hv,hvA]
  rcases le_or_gt 0 x with hx | hx
  · exact hp hx (by simpa [abs_of_nonneg hx] using hxlo) (by simpa [abs_of_nonneg hx] using hxhi)
  · rw [← liClockPairedEtaPartitionRawDifferenceDensity_even N x,
      ← liClockPairedEtaContiguousRawDifferenceDensity_even (Real.log (2*(N:ℝ))) x]
    exact hp (by linarith) (by simpa [abs_of_neg hx] using hxlo) (by simpa [abs_of_neg hx] using hxhi)

theorem liClockPairedEtaPartitionComparisonScale_pos {N : ℕ} (hN : 0<N) :
    0<liClockPairedEtaPartitionComparisonScale N := by
  exact sq_pos_of_pos (div_pos (liClockPairedEtaContiguousPartitionNormalizer_pos (log_endpoint_pos hN))
    (liClockPairedEtaPartitionNormalizer_pos hN))

theorem liClockPairedEtaPartitionComparisonScale_one_lt {N : ℕ} (hN : 2≤N) :
    1<liClockPairedEtaPartitionComparisonScale N := by
  have hA := liClockPairedEtaPartitionNormalizer_pos (by omega : 0<N)
  have hlt := liClockPairedEtaPartitionNormalizer_lt_contiguous hN
  have hd : 1<liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/liClockPairedEtaPartitionNormalizer N :=
    (one_lt_div hA).mpr hlt
  unfold liClockPairedEtaPartitionComparisonScale
  nlinarith

/-- The raw reference density is strictly positive precisely inside its support. -/
theorem liClockPairedEtaContiguousRawDifferenceDensity_pos {L x : ℝ} (hx : |x|<L) :
    0<liClockPairedEtaContiguousRawDifferenceDensity L x := by
  have hp {x:ℝ} (hx:0≤x) (hxL:x<L) : 0<liClockPairedEtaContiguousRawDifferenceDensity L x := by
    rw [liClockPairedEtaContiguousRawDifferenceDensity_eq_of_nonneg hx hxL]
    exact mul_pos (Real.exp_pos _) (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  rcases le_or_gt 0 x with h | h
  · exact hp h (by simpa [abs_of_nonneg h] using hx)
  · rw [← liClockPairedEtaContiguousRawDifferenceDensity_even L x]
    exact hp (by linarith) (by simpa [abs_of_neg h] using hx)

/-- Ratio comparisons use strict support; signed forcing uses the zero-density extension. -/
def liClockPairedEtaPartitionDensityRatio (N : ℕ) (x : ℝ) : ℝ :=
  liClockPairedEtaPartitionDifferenceDensity N x /
    liClockPairedEtaContiguousDifferenceDensity (Real.log (2*(N:ℝ))) x

private theorem ratio_eq_raw {N : ℕ} (hN : 0<N) {x : ℝ} (hx:|x|<Real.log (2*(N:ℝ))) :
    liClockPairedEtaPartitionDensityRatio N x = liClockPairedEtaPartitionComparisonScale N *
      liClockPairedEtaPartitionRawDifferenceDensity N x /
        liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) x := by
  have hA := (liClockPairedEtaPartitionNormalizer_pos hN).ne'
  have hU := (liClockPairedEtaContiguousPartitionNormalizer_pos (log_endpoint_pos hN)).ne'
  have hg := (liClockPairedEtaContiguousRawDifferenceDensity_pos hx).ne'
  unfold liClockPairedEtaPartitionDensityRatio liClockPairedEtaPartitionDifferenceDensity
    liClockPairedEtaContiguousDifferenceDensity liClockPairedEtaPartitionComparisonScale
  field_simp

/-- Exact arithmetic local formula, with all odd/even reciprocal heads. -/
theorem liClockPairedEtaPartitionDensityRatio_eq_local {N : ℕ} (hN : 0<N) {x : ℝ}
    (hx:0≤x) (hxeps:x<liClockPairedEtaPartitionEdgeWidth N) :
    liClockPairedEtaPartitionDensityRatio N x = liClockPairedEtaPartitionComparisonScale N *
      (liClockPairedEtaPartitionOddReciprocalHead N-Real.exp x*liClockPairedEtaPartitionEvenReciprocalHead N) /
      (1-Real.exp x/(2*(N:ℝ))) := by
  have hxL := hxeps.trans_le (liClockPairedEtaPartitionEdgeWidth_le_log hN)
  rw [ratio_eq_raw hN (by simpa [abs_of_nonneg hx] using hxL),
    liClockPairedEtaPartitionRawDifferenceDensity_eq_local hx hxeps,
    liClockPairedEtaContiguousRawDifferenceDensity_eq_of_nonneg hx hxL,
    Real.exp_sub,Real.exp_log (by positivity : 0<2*(N:ℝ))]
  have he := (Real.exp_pos (-x/2)).ne'
  field_simp

/-- Exact edge plateau; no boundary quotient is asserted. -/
theorem liClockPairedEtaPartitionDensityRatio_eq_scale_on_edge {N : ℕ} (hN : 0<N) {x : ℝ}
    (hxlo:Real.log (2*(N:ℝ))-liClockPairedEtaPartitionEdgeWidth N < |x|)
    (hxhi:|x|<Real.log (2*(N:ℝ))) :
    liClockPairedEtaPartitionDensityRatio N x=liClockPairedEtaPartitionComparisonScale N := by
  rw [ratio_eq_raw hN hxhi,
    liClockPairedEtaPartitionRawDifferenceDensity_eq_contiguous_on_edge hN hxlo hxhi]
  exact mul_div_cancel_right₀ _ (liClockPairedEtaContiguousRawDifferenceDensity_pos hxhi).ne'

private theorem local_denominator_pos {N : ℕ} (hN:0<N) {x:ℝ}
    (hx:x<Real.log (2*(N:ℝ))) : 0<1-Real.exp x/(2*(N:ℝ)) := by
  have hp : 0<2*(N:ℝ) := by positivity
  exact sub_pos.mpr ((div_lt_one hp).mpr (by rw [← Real.exp_log hp]; exact Real.exp_lt_exp.mpr hx))

/-- Strict arithmetic coefficient inequality from the retained reciprocal heads. -/
theorem liClockPairedEtaPartition_reciprocal_head_strict {N : ℕ} (hN:2≤N) :
    liClockPairedEtaPartitionOddReciprocalHead N/(2*(N:ℝ)) <
      liClockPairedEtaPartitionEvenReciprocalHead N := by
  unfold liClockPairedEtaPartitionOddReciprocalHead liClockPairedEtaPartitionEvenReciprocalHead
  rw [Finset.sum_div]
  have hn : (2:ℝ)≤(N:ℝ) := by exact_mod_cast hN
  apply Finset.sum_lt_sum
  · intro n hmem
    rw [div_div,show (2*(n:ℝ)+1)*(2*(N:ℝ))=(2*(N:ℝ))*(2*(n:ℝ)+1) by ring]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith [show 0≤(n:ℝ) by positivity])
  · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
    norm_num only [Nat.cast_zero,mul_zero,zero_add,div_one]
    exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)

private theorem reciprocal_gap_identity (n:ℕ) :
    liClockPairedEtaPartitionOddReciprocalHead (n+1)-liClockPairedEtaPartitionEvenReciprocalHead (n+1) =
      1-1/(2*((n+1:ℕ):ℝ))-
        ∑ j∈Finset.range n,(1/(2*(j:ℝ)+2)-1/(2*(j:ℝ)+3)) := by
  induction n with
  | zero => norm_num [liClockPairedEtaPartitionOddReciprocalHead,liClockPairedEtaPartitionEvenReciprocalHead]
  | succ n ih =>
      unfold liClockPairedEtaPartitionOddReciprocalHead liClockPairedEtaPartitionEvenReciprocalHead at ih ⊢
      simp only [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one] at ih ⊢
      linear_combination ih

/-- Exact missing-gap overlap mass at zero. -/
theorem liClockPairedEtaPartitionRawDifferenceDensity_zero_gap {N:ℕ} (hN:0<N) :
    liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) 0-
      liClockPairedEtaPartitionRawDifferenceDensity N 0 =
        ∑j∈Finset.range (N-1),(1/(2*(j:ℝ)+2)-1/(2*(j:ℝ)+3)) := by
  have hsucc : N-1+1=N := by omega
  have hi := reciprocal_gap_identity (N-1)
  rw [hsucc] at hi
  rw [liClockPairedEtaPartitionRawDifferenceDensity_eq_local (le_refl 0) (liClockPairedEtaPartitionEdgeWidth_pos hN),
    liClockPairedEtaContiguousRawDifferenceDensity_eq_of_nonneg (le_refl 0) (log_endpoint_pos hN)]
  simp only [neg_zero,zero_div,Real.exp_zero,one_mul,zero_sub]
  rw [Real.exp_neg,Real.exp_log (by positivity)]
  simp only [one_div] at hi ⊢
  linarith

theorem liClockPairedEtaPartitionRawDifferenceDensity_zero_lt_contiguous {N:ℕ} (hN:2≤N) :
    liClockPairedEtaPartitionRawDifferenceDensity N 0 <
      liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) 0 := by
  have h := liClockPairedEtaPartitionRawDifferenceDensity_zero_gap (by omega : 0<N)
  have hp : 0<(∑j∈Finset.range (N-1),(1/(2*(j:ℝ)+2)-1/(2*(j:ℝ)+3))) := by
    apply Finset.sum_pos
    · intro j hj
      exact sub_pos.mpr (one_div_lt_one_div_of_lt (by positivity) (by linarith))
    · exact ⟨0,Finset.mem_range.mpr (by omega)⟩
  linarith

/-- Strict decrease occurs on the whole literal small-shift interval. -/
theorem strictAntiOn_liClockPairedEtaPartitionDensityRatio_local {N:ℕ} (hN:2≤N) :
    StrictAntiOn (liClockPairedEtaPartitionDensityRatio N)
      (Ico 0 (liClockPairedEtaPartitionEdgeWidth N)) := by
  intro x hx y hy hxy
  have hn:0<N := by omega
  rw [liClockPairedEtaPartitionDensityRatio_eq_local hn hx.1 hx.2,
    liClockPairedEtaPartitionDensityRatio_eq_local hn hy.1 hy.2]
  have hdx := local_denominator_pos hn (hx.2.trans_le (liClockPairedEtaPartitionEdgeWidth_le_log hn))
  have hdy := local_denominator_pos hn (hy.2.trans_le (liClockPairedEtaPartitionEdgeWidth_le_log hn))
  have hc := liClockPairedEtaPartitionComparisonScale_pos hn
  have hheads := liClockPairedEtaPartition_reciprocal_head_strict hN
  have hex : Real.exp x<Real.exp y := Real.exp_lt_exp.mpr hxy
  have hNpos : 0<2*(N:ℝ) := by positivity
  apply (div_lt_div_iff₀ hdy hdx).mpr
  have hhead : liClockPairedEtaPartitionOddReciprocalHead N -
      (2*(N:ℝ))*liClockPairedEtaPartitionEvenReciprocalHead N<0 :=
    sub_neg.mpr (by simpa only [mul_comm] using (div_lt_iff₀ hNpos).mp hheads)
  have hprod := mul_neg_of_pos_of_neg (mul_pos hc (sub_pos.mpr hex)) hhead
  field_simp at hprod ⊢
  nlinarith

/-- Strictly sub-edge central intercept, with no quotient at a support boundary. -/
theorem liClockPairedEtaPartitionDensityRatio_zero_lt_scale {N:ℕ} (hN:2≤N) :
    liClockPairedEtaPartitionDensityRatio N 0<liClockPairedEtaPartitionComparisonScale N := by
  have hn:0<N := by omega
  have hg := liClockPairedEtaContiguousRawDifferenceDensity_pos (x:=0) (L:=Real.log (2*(N:ℝ))) (by simpa using log_endpoint_pos hn)
  rw [ratio_eq_raw hn (by simpa using log_endpoint_pos hn)]
  exact (div_lt_iff₀ hg).mpr (mul_lt_mul_of_pos_left
    (liClockPairedEtaPartitionRawDifferenceDensity_zero_lt_contiguous hN)
    (liClockPairedEtaPartitionComparisonScale_pos hn))


/-- Canonical ratio has a negative right derivative, not a two-sided derivative at its cusp. -/
theorem hasDerivWithinAt_liClockPairedEtaPartitionDensityRatio_zero {N:ℕ} (hN:0<N) :
    HasDerivWithinAt (liClockPairedEtaPartitionDensityRatio N)
      (liClockPairedEtaPartitionComparisonScale N *
        (liClockPairedEtaPartitionOddReciprocalHead N/(2*(N:ℝ))-
          liClockPairedEtaPartitionEvenReciprocalHead N)/(1-1/(2*(N:ℝ)))^2) (Ici 0) 0 := by
  let a:=liClockPairedEtaPartitionOddReciprocalHead N
  let b:=liClockPairedEtaPartitionEvenReciprocalHead N
  let κ:=liClockPairedEtaPartitionComparisonScale N
  have hd : 1-1/(2*(N:ℝ))≠0 := (by simpa only [Real.exp_zero] using (local_denominator_pos hN (x:=0) (log_endpoint_pos hN)).ne')
  have he : HasDerivAt (fun x:ℝ=>κ*(a-Real.exp x*b)/(1-Real.exp x/(2*(N:ℝ))))
      (κ*(a/(2*(N:ℝ))-b)/(1-1/(2*(N:ℝ)))^2) 0 := by
    have hnum := ((Real.hasDerivAt_exp 0).mul_const b).const_sub a
    have hden := ((Real.hasDerivAt_exp 0).div_const (2*(N:ℝ))).const_sub 1
    have hquot : HasDerivAt (fun x:ℝ=>κ*((a-Real.exp x*b)/(1-Real.exp x/(2*(N:ℝ)))))
        (κ*((-(Real.exp 0*b)*(1-Real.exp 0/(2*(N:ℝ)))-(a-Real.exp 0*b)*(-(Real.exp 0/(2*(N:ℝ)))))/
          (1-Real.exp 0/(2*(N:ℝ)))^2)) 0 := (hnum.div hden (by simpa using hd)).const_mul κ
    have hf : (fun x:ℝ=>κ*(a-Real.exp x*b)/(1-Real.exp x/(2*(N:ℝ)))) =
        (fun x:ℝ=>κ*((a-Real.exp x*b)/(1-Real.exp x/(2*(N:ℝ))))) := by funext x; ring
    have hc : κ*(a/(2*(N:ℝ))-b)/(1-1/(2*(N:ℝ)))^2 =
        κ*((-(Real.exp 0*b)*(1-Real.exp 0/(2*(N:ℝ)))-(a-Real.exp 0*b)*(-(Real.exp 0/(2*(N:ℝ)))))/
          (1-Real.exp 0/(2*(N:ℝ)))^2) := by simp only [Real.exp_zero,one_mul]; ring
    rw [hf,hc]
    exact hquot
  have hsmall : ∀ᶠx in 𝓝[Ici (0:ℝ)] 0,x<liClockPairedEtaPartitionEdgeWidth N :=
    nhdsWithin_le_nhds (Iio_mem_nhds (liClockPairedEtaPartitionEdgeWidth_pos hN))
  apply he.hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,hsmall] with x hx hxe
    exact liClockPairedEtaPartitionDensityRatio_eq_local hN hx hxe
  · exact liClockPairedEtaPartitionDensityRatio_eq_local hN (le_refl 0) (liClockPairedEtaPartitionEdgeWidth_pos hN)

theorem liClockPairedEtaPartitionDensityRatio_rightDerivative_neg {N:ℕ} (hN:2≤N) :
    liClockPairedEtaPartitionComparisonScale N *
      (liClockPairedEtaPartitionOddReciprocalHead N/(2*(N:ℝ))-
        liClockPairedEtaPartitionEvenReciprocalHead N)/(1-1/(2*(N:ℝ)))^2<0 := by
  have hn:0<N := by omega
  have hd := local_denominator_pos hn (x:=0) (log_endpoint_pos hn)
  simpa only [Real.exp_zero] using div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (liClockPairedEtaPartitionComparisonScale_pos hn)
      (sub_neg.mpr (liClockPairedEtaPartition_reciprocal_head_strict hN))) (sq_pos_of_pos hd)

private theorem twice_edgeWidth_lt_log {N:ℕ} (hN:2≤N) :
    2*liClockPairedEtaPartitionEdgeWidth N<Real.log (2*(N:ℝ)) := by
  have he := liClockPairedEtaPartitionEdgeWidth_le_log_two (by omega : 0<N)
  have hn : (2:ℝ)≤(N:ℝ) := by exact_mod_cast hN
  have hl : Real.log 2<Real.log (2*(N:ℝ)-1) := Real.log_lt_log (by norm_num) (by linarith)
  have hs := liClockPairedEtaPartitionLog_sub_edgeWidth_eq (by omega : 0<N)
  linarith

/-- The positive half-support ratio is neither nondecreasing nor nonincreasing. -/
theorem liClockPairedEtaPartitionDensityRatio_not_monotoneOn {N:ℕ} (hN:2≤N) :
    ¬MonotoneOn (liClockPairedEtaPartitionDensityRatio N) (Ico 0 (Real.log (2*(N:ℝ)))) := by
  intro hm
  have hn:0<N := by omega
  have he := liClockPairedEtaPartitionEdgeWidth_pos hn
  have hL := liClockPairedEtaPartitionEdgeWidth_le_log hn
  have hd := strictAntiOn_liClockPairedEtaPartitionDensityRatio_local hN
    (show (0:ℝ)∈Ico 0 (liClockPairedEtaPartitionEdgeWidth N) by exact ⟨le_refl 0,he⟩)
    (show liClockPairedEtaPartitionEdgeWidth N/2∈Ico 0 (liClockPairedEtaPartitionEdgeWidth N) by constructor <;> linarith)
    (by linarith : 0<liClockPairedEtaPartitionEdgeWidth N/2)
  exact (not_lt_of_ge (hm ⟨le_refl 0,log_endpoint_pos hn⟩ (by constructor <;> linarith) (by linarith))) hd

theorem liClockPairedEtaPartitionDensityRatio_not_antitoneOn {N:ℕ} (hN:2≤N) :
    ¬AntitoneOn (liClockPairedEtaPartitionDensityRatio N) (Ico 0 (Real.log (2*(N:ℝ)))) := by
  intro hm
  have hn:0<N := by omega
  have he := liClockPairedEtaPartitionEdgeWidth_pos hn
  have hL := liClockPairedEtaPartitionEdgeWidth_le_log hn
  let y:=Real.log (2*(N:ℝ))-liClockPairedEtaPartitionEdgeWidth N/2
  have hy0 : 0<y := by dsimp [y]; linarith
  have hyL : y<Real.log (2*(N:ℝ)) := by dsimp [y]; linarith
  have hyedge : Real.log (2*(N:ℝ))-liClockPairedEtaPartitionEdgeWidth N < |y| := by rw [abs_of_pos hy0]; dsimp [y]; linarith
  have heq := liClockPairedEtaPartitionDensityRatio_eq_scale_on_edge hn hyedge (by simpa [abs_of_pos hy0] using hyL)
  have hle := hm ⟨le_refl 0,log_endpoint_pos hn⟩ ⟨hy0.le,hyL⟩ hy0.le
  rw [heq] at hle
  exact (not_lt_of_ge hle) (liClockPairedEtaPartitionDensityRatio_zero_lt_scale hN)

private theorem good_interval_point {f g:ℝ→ℝ} {L a b:ℝ}
    (heq:f=ᵐ[volume.restrict (Ico 0 L)]g) (hab:a<b) (ha:0≤a) (hb:b≤L) :
    ∃x∈Ioo a b,f x=g x := by
  apply Measure.exists_mem_of_measure_ne_zero_of_ae
  · rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  · apply ae_restrict_of_ae_restrict_of_subset _ heq
    intro x hx
    exact ⟨ha.trans hx.1.le,hx.2.trans_le hb⟩

/-- Null-set modification cannot repair the local decreasing open witnesses. -/
theorem liClockPairedEtaPartitionDensityRatio_no_ae_monotone_version {N:ℕ} (hN:2≤N)
    (g:ℝ→ℝ) (heq:g=ᵐ[volume.restrict (Ico 0 (Real.log (2*(N:ℝ))))]liClockPairedEtaPartitionDensityRatio N) :
    ¬MonotoneOn g (Ico 0 (Real.log (2*(N:ℝ)))) := by
  intro hm
  have hn:0<N := by omega
  have he := liClockPairedEtaPartitionEdgeWidth_pos hn
  have hL := liClockPairedEtaPartitionEdgeWidth_le_log hn
  obtain ⟨x,hx,hgx⟩ := good_interval_point heq
    (by linarith : liClockPairedEtaPartitionEdgeWidth N/8<liClockPairedEtaPartitionEdgeWidth N/4)
    (by linarith : 0≤liClockPairedEtaPartitionEdgeWidth N/8)
    (by linarith : liClockPairedEtaPartitionEdgeWidth N/4≤Real.log (2*(N:ℝ)))
  obtain ⟨y,hy,hgy⟩ := good_interval_point heq
    (by linarith : liClockPairedEtaPartitionEdgeWidth N/2<3*liClockPairedEtaPartitionEdgeWidth N/4)
    (by linarith : 0≤liClockPairedEtaPartitionEdgeWidth N/2)
    (by linarith : 3*liClockPairedEtaPartitionEdgeWidth N/4≤Real.log (2*(N:ℝ)))
  have hxy:x<y := by linarith [hx.2,hy.1]
  have hd := strictAntiOn_liClockPairedEtaPartitionDensityRatio_local hN
    (show x∈Ico 0 (liClockPairedEtaPartitionEdgeWidth N) by constructor <;> linarith [hx.1,hx.2])
    (show y∈Ico 0 (liClockPairedEtaPartitionEdgeWidth N) by constructor <;> linarith [hy.1,hy.2]) hxy
  have hle := hm (by constructor <;> linarith [hx.1,hx.2]) (by constructor <;> linarith [hy.1,hy.2]) hxy.le
  rw [hgx,hgy] at hle
  exact (not_lt_of_ge hle) hd

/-- Positive-length local and edge witnesses also exclude a.e. antitone versions. -/
theorem liClockPairedEtaPartitionDensityRatio_no_ae_antitone_version {N:ℕ} (hN:2≤N)
    (g:ℝ→ℝ) (heq:g=ᵐ[volume.restrict (Ico 0 (Real.log (2*(N:ℝ))))]liClockPairedEtaPartitionDensityRatio N) :
    ¬AntitoneOn g (Ico 0 (Real.log (2*(N:ℝ)))) := by
  intro hm
  have hn:0<N := by omega
  have he := liClockPairedEtaPartitionEdgeWidth_pos hn
  have hL := liClockPairedEtaPartitionEdgeWidth_le_log hn
  have h2 := twice_edgeWidth_lt_log hN
  obtain ⟨x,hx,hgx⟩ := good_interval_point heq
    (by linarith : liClockPairedEtaPartitionEdgeWidth N/8<liClockPairedEtaPartitionEdgeWidth N/4)
    (by linarith : 0≤liClockPairedEtaPartitionEdgeWidth N/8)
    (by linarith : liClockPairedEtaPartitionEdgeWidth N/4≤Real.log (2*(N:ℝ)))
  obtain ⟨y,hy,hgy⟩ := good_interval_point heq
    (by linarith : Real.log (2*(N:ℝ))-liClockPairedEtaPartitionEdgeWidth N/2<Real.log (2*(N:ℝ))-liClockPairedEtaPartitionEdgeWidth N/4)
    (by linarith : 0≤Real.log (2*(N:ℝ))-liClockPairedEtaPartitionEdgeWidth N/2)
    (by linarith : Real.log (2*(N:ℝ))-liClockPairedEtaPartitionEdgeWidth N/4≤Real.log (2*(N:ℝ)))
  have hx0:0<x := by linarith [hx.1]
  have hd := strictAntiOn_liClockPairedEtaPartitionDensityRatio_local hN
    (show (0:ℝ)∈Ico 0 (liClockPairedEtaPartitionEdgeWidth N) by exact ⟨le_refl 0,he⟩)
    (show x∈Ico 0 (liClockPairedEtaPartitionEdgeWidth N) by constructor <;> linarith [hx.1,hx.2]) hx0
  have hy0:0<y := by linarith [hy.1]
  have heqY := liClockPairedEtaPartitionDensityRatio_eq_scale_on_edge hn
    (by rw [abs_of_pos hy0]; linarith [hy.1]) (by rw [abs_of_pos hy0]; linarith [hy.2])
  have hxy:x<y := by linarith [hx.2,hy.1]
  have hle := hm (by constructor <;> linarith [hx.1,hx.2]) (by constructor <;> linarith [hy.1,hy.2]) hxy.le
  rw [hgx,hgy,heqY] at hle
  exact (not_lt_of_ge hle) (hd.trans (liClockPairedEtaPartitionDensityRatio_zero_lt_scale hN))

private theorem reference_ae_to_volume {N:ℕ} (hN:0<N) {g:ℝ→ℝ}
    (heq:g=ᵐ[(Measure.map (fun p:ℝ×ℝ=>p.1-p.2) (liClockPairedEtaContiguousSymmetrizedMeasure (Real.log (2*(N:ℝ))))).restrict (Ico 0 (Real.log (2*(N:ℝ))))]liClockPairedEtaPartitionDensityRatio N) :
    g=ᵐ[volume.restrict (Ico 0 (Real.log (2*(N:ℝ))))]liClockPairedEtaPartitionDensityRatio N := by
  rw [liClockPairedEtaContiguousDifferenceDensity_map (log_endpoint_pos hN),restrict_withDensity measurableSet_Ico] at heq
  have hm : Measurable (fun x=>ENNReal.ofReal (liClockPairedEtaContiguousDifferenceDensity (Real.log (2*(N:ℝ))) x)) :=
    ((continuous_liClockPairedEtaContiguousRawDifferenceDensity _).div_const _).measurable.ennreal_ofReal
  simp only [Filter.EventuallyEq] at heq
  rw [ae_withDensity_iff hm] at heq
  filter_upwards [heq,ae_restrict_mem measurableSet_Ico] with x hx hmem
  apply hx
  apply (ENNReal.ofReal_pos.mpr _).ne'
  unfold liClockPairedEtaContiguousDifferenceDensity
  exact div_pos (liClockPairedEtaContiguousRawDifferenceDensity_pos (by rw [abs_of_nonneg hmem.1]; exact hmem.2))
    (sq_pos_of_pos (liClockPairedEtaContiguousPartitionNormalizer_pos (log_endpoint_pos hN)))

/-- Reference-law null sets cannot remove either radial order obstruction. -/
theorem liClockPairedEtaPartitionDensityRatio_no_reference_ae_monotone_version {N:ℕ} (hN:2≤N)
    (g:ℝ→ℝ)
    (heq:g=ᵐ[(Measure.map (fun p:ℝ×ℝ=>p.1-p.2) (liClockPairedEtaContiguousSymmetrizedMeasure (Real.log (2*(N:ℝ))))).restrict (Ico 0 (Real.log (2*(N:ℝ))))]liClockPairedEtaPartitionDensityRatio N) :
    ¬MonotoneOn g (Ico 0 (Real.log (2*(N:ℝ)))) ∧ ¬AntitoneOn g (Ico 0 (Real.log (2*(N:ℝ)))) := by
  have hv:=reference_ae_to_volume (by omega : 0<N) heq
  exact ⟨liClockPairedEtaPartitionDensityRatio_no_ae_monotone_version hN g hv,
    liClockPairedEtaPartitionDensityRatio_no_ae_antitone_version hN g hv⟩

private theorem integral_difference_density (μ : Measure (ℝ×ℝ)) (g:ℝ→ℝ)
    (hg:Continuous g) (hgn:∀x,0≤g x)
    (hmap:Measure.map (fun p:ℝ×ℝ=>p.1-p.2) μ=volume.withDensity (fun x=>ENNReal.ofReal (g x))) (j:ℕ) :
    (∫p:ℝ×ℝ,(p.1-p.2)^(2*j) ∂μ) = ∫x:ℝ,x^(2*j)*g x := by
  rw [← integral_map (by fun_prop : AEMeasurable (fun p:ℝ×ℝ=>p.1-p.2) μ)
    (by fun_prop : AEStronglyMeasurable (fun x:ℝ=>x^(2*j)) (Measure.map (fun p:ℝ×ℝ=>p.1-p.2) μ)),hmap,
    integral_withDensity_eq_integral_toReal_smul hg.measurable.ennreal_ofReal
      (Eventually.of_forall fun x=>ENNReal.ofReal_lt_top) (fun x:ℝ=>x^(2*j))]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (hgn x),smul_eq_mul,mul_comm]

/-- All raw moments match the literal normalized product source. -/
theorem liClockPairedEtaPartitionRawDifferenceDensity_moment {N:ℕ} (hN:0<N) (j:ℕ) :
    (∫x:ℝ,x^(2*j)*liClockPairedEtaPartitionRawDifferenceDensity N x) =
      liClockPairedEtaPartitionNormalizer N^2*liClockPairedEtaSymmetrizedEvenMoment N j := by
  have hi:=integral_difference_density (liClockPairedEtaSymmetrizedMeasure N)
    (liClockPairedEtaPartitionDifferenceDensity N)
    ((continuous_liClockPairedEtaPartitionRawDifferenceDensity N).div_const _)
    (fun x=>div_nonneg (liClockPairedEtaPartitionRawDifferenceDensity_nonneg N x) (sq_nonneg _))
    (liClockPairedEtaPartitionDifferenceDensity_map hN) j
  have he : (fun x:ℝ=>x^(2*j)*liClockPairedEtaPartitionDifferenceDensity N x) =
    fun x=>x^(2*j)*liClockPairedEtaPartitionRawDifferenceDensity N x/liClockPairedEtaPartitionNormalizer N^2 := by
    funext x
    unfold liClockPairedEtaPartitionDifferenceDensity
    ring
  rw [he,integral_div] at hi
  change liClockPairedEtaSymmetrizedEvenMoment N j = _ at hi
  exact ((eq_div_iff (pow_ne_zero _ (liClockPairedEtaPartitionNormalizer_pos hN).ne')).mp hi).symm.trans (by ring)

theorem liClockPairedEtaContiguousRawDifferenceDensity_moment {L:ℝ} (hL:0<L) (j:ℕ) :
    (∫x:ℝ,x^(2*j)*liClockPairedEtaContiguousRawDifferenceDensity L x) =
      liClockPairedEtaContiguousPartitionNormalizer L^2*liClockPairedEtaContiguousSymmetrizedEvenMoment L j := by
  have hi:=integral_difference_density (liClockPairedEtaContiguousSymmetrizedMeasure L)
    (liClockPairedEtaContiguousDifferenceDensity L)
    ((continuous_liClockPairedEtaContiguousRawDifferenceDensity L).div_const _)
    (fun x=>div_nonneg (liClockPairedEtaContiguousRawDifferenceDensity_nonneg L x) (sq_nonneg _))
    (liClockPairedEtaContiguousDifferenceDensity_map hL) j
  have he : (fun x:ℝ=>x^(2*j)*liClockPairedEtaContiguousDifferenceDensity L x) =
    fun x=>x^(2*j)*liClockPairedEtaContiguousRawDifferenceDensity L x/liClockPairedEtaContiguousPartitionNormalizer L^2 := by
    funext x
    unfold liClockPairedEtaContiguousDifferenceDensity
    ring
  rw [he,integral_div] at hi
  change liClockPairedEtaContiguousSymmetrizedEvenMoment L j = _ at hi
  exact ((eq_div_iff (pow_ne_zero _ (liClockPairedEtaContiguousPartitionNormalizer_pos hL).ne')).mp hi).symm.trans (by ring)

/-- Exact N=1 exception retains the filled source intervals and their normalizers. -/
theorem liClockPairedEtaPartitionRawDifferenceDensity_one_eq_contiguous (x:ℝ) :
    liClockPairedEtaPartitionRawDifferenceDensity 1 x=liClockPairedEtaContiguousRawDifferenceDensity (Real.log 2) x := by
  have hw : liClockPairedEtaPartitionHalfTiltWeight 1=liClockPairedEtaContiguousHalfTiltWeight (Real.log 2) := by
    funext u
    simp [liClockPairedEtaPartitionHalfTiltWeight,liClockPairedEtaPartitionLogSupport,
      liClockPairedEtaContiguousHalfTiltWeight,intervalWeight]
  simp only [liClockPairedEtaPartitionRawDifferenceDensity,hw,liClockPairedEtaContiguousRawDifferenceDensity]

theorem liClockPairedEtaPartitionComparisonScale_one : liClockPairedEtaPartitionComparisonScale 1=1 := by
  unfold liClockPairedEtaPartitionComparisonScale
  norm_num only [Nat.cast_one,mul_one]
  rw [liClockPairedEtaPartitionNormalizer_one_eq_contiguous,div_self
    (liClockPairedEtaContiguousPartitionNormalizer_pos (Real.log_pos (by norm_num))).ne']
  norm_num

theorem liClockPairedEtaPartitionDensityRatio_one {x:ℝ} (hx:|x|<Real.log 2) :
    liClockPairedEtaPartitionDensityRatio 1 x=1 := by
  rw [ratio_eq_raw (by omega : 0<1) (by simpa using hx),liClockPairedEtaPartitionComparisonScale_one,
    liClockPairedEtaPartitionRawDifferenceDensity_one_eq_contiguous]
  norm_num only [Nat.cast_one,mul_one,one_mul]
  exact div_self (liClockPairedEtaContiguousRawDifferenceDensity_pos hx).ne'

/-- The absolute-value pushforward is the radial reference source law. -/
def liClockPairedEtaContiguousRadialDifferenceMeasure (L:ℝ) : Measure ℝ :=
  Measure.map (fun x:ℝ=>|x|) (Measure.map (fun p:ℝ×ℝ=>p.1-p.2) (liClockPairedEtaContiguousSymmetrizedMeasure L))

/-- Neither order direction can hold after radial reference-law null-set changes. -/
theorem liClockPairedEtaPartitionDensityRatio_no_radial_ae_monotone_version {N:ℕ} (hN:2≤N)
    (g:ℝ→ℝ)
    (heq:g=ᵐ[(liClockPairedEtaContiguousRadialDifferenceMeasure (Real.log (2*(N:ℝ)))).restrict
      (Iio (Real.log (2*(N:ℝ))))]liClockPairedEtaPartitionDensityRatio N) :
    ¬MonotoneOn g (Ico 0 (Real.log (2*(N:ℝ)))) ∧ ¬AntitoneOn g (Ico 0 (Real.log (2*(N:ℝ)))) := by
  simp only [Filter.EventuallyEq,liClockPairedEtaContiguousRadialDifferenceMeasure] at heq
  rw [ae_restrict_iff' measurableSet_Iio] at heq
  have hp := ae_of_ae_map (by fun_prop : AEMeasurable (fun x:ℝ=>|x|)
    (Measure.map (fun p:ℝ×ℝ=>p.1-p.2) (liClockPairedEtaContiguousSymmetrizedMeasure (Real.log (2*(N:ℝ)))))) heq
  have hr : g=ᵐ[(Measure.map (fun p:ℝ×ℝ=>p.1-p.2) (liClockPairedEtaContiguousSymmetrizedMeasure (Real.log (2*(N:ℝ))))).restrict (Ico 0 (Real.log (2*(N:ℝ))))]liClockPairedEtaPartitionDensityRatio N := by
    filter_upwards [ae_restrict_of_ae hp,ae_restrict_mem measurableSet_Ico] with x hx hm
    simp only [abs_of_nonneg hm.1] at hx
    exact hx hm.2
  exact liClockPairedEtaPartitionDensityRatio_no_reference_ae_monotone_version hN g hr

/-- Literal normalized signed forcing density of the two complete difference laws. -/
def liClockPairedEtaPartitionSignedForcingDensity (N:ℕ) (w:ℝ) : ℝ :=
  ∫x:ℝ,(2*x-w)*liClockPairedEtaPartitionDifferenceDensity N x*
    liClockPairedEtaContiguousDifferenceDensity (Real.log (2*(N:ℝ))) (w-x)

private theorem normalized_edge {N:ℕ} (hN:0<N) {x:ℝ}
    (hxlo:Real.log (2*(N:ℝ))-liClockPairedEtaPartitionEdgeWidth N < |x|)
    (hxhi:|x|<Real.log (2*(N:ℝ))) :
    liClockPairedEtaPartitionDifferenceDensity N x = liClockPairedEtaPartitionComparisonScale N *
      liClockPairedEtaContiguousDifferenceDensity (Real.log (2*(N:ℝ))) x := by
  have hA:liClockPairedEtaPartitionNormalizer N≠0 := (liClockPairedEtaPartitionNormalizer_pos hN).ne'
  have hU:liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))≠0 :=
    (liClockPairedEtaContiguousPartitionNormalizer_pos (log_endpoint_pos hN)).ne'
  unfold liClockPairedEtaPartitionDifferenceDensity liClockPairedEtaContiguousDifferenceDensity liClockPairedEtaPartitionComparisonScale
  rw [liClockPairedEtaPartitionRawDifferenceDensity_eq_contiguous_on_edge hN hxlo hxhi]
  field_simp

/-- The signed forcing vanishes in the strict outer band; this supplies no inverse-clock sign. -/
theorem liClockPairedEtaPartitionSignedForcingDensity_zero_on_outer_band {N:ℕ} (hN:0<N) {w:ℝ}
    (hw:2*Real.log (2*(N:ℝ))-liClockPairedEtaPartitionEdgeWidth N < |w|) :
    liClockPairedEtaPartitionSignedForcingDensity N w=0 := by
  let L:=Real.log (2*(N:ℝ))
  let u:=liClockPairedEtaContiguousDifferenceDensity L
  have heq : ∀x:ℝ,(2*x-w)*liClockPairedEtaPartitionDifferenceDensity N x*u (w-x) =
      liClockPairedEtaPartitionComparisonScale N*((2*x-w)*u x*u (w-x)) := by
    intro x
    by_cases hx:|x|<L
    · by_cases hy:|w-x|<L
      · have ht : |w|≤|x|+|w-x| := by
          have h:=abs_add_le x (w-x)
          rwa [show x+(w-x)=w by ring] at h
        have hxedge:L-liClockPairedEtaPartitionEdgeWidth N < |x| := by dsimp [L] at hx hy ⊢; linarith
        rw [normalized_edge hN hxedge hx]
        ring
      · have hg : u (w-x)=0 := by
          dsimp [u,liClockPairedEtaContiguousDifferenceDensity]
          rw [liClockPairedEtaContiguousRawDifferenceDensity_zero_of_le_abs (le_of_not_gt hy),zero_div]
        simp [hg]
    · have hgA : liClockPairedEtaPartitionDifferenceDensity N x=0 := by
        unfold liClockPairedEtaPartitionDifferenceDensity
        rw [liClockPairedEtaPartitionRawDifferenceDensity_zero_of_log_le_abs (le_of_not_gt hx),zero_div]
      have hgU : u x=0 := by
        dsimp [u,liClockPairedEtaContiguousDifferenceDensity]
        rw [liClockPairedEtaContiguousRawDifferenceDensity_zero_of_le_abs (le_of_not_gt hx),zero_div]
      simp [hgA,hgU]
  have hsym : (∫x:ℝ,(2*x-w)*u x*u (w-x))=0 := by
    have ht := integral_sub_left_eq_self (μ:=volume) (fun x:ℝ=>(2*x-w)*u x*u (w-x)) w
    have he : (fun x:ℝ=>(2*(w-x)-w)*u (w-x)*u (w-(w-x))) =
        fun x=>-((2*x-w)*u x*u (w-x)) := by funext x; rw [sub_sub_cancel]; ring
    rw [he,integral_neg] at ht
    linarith
  unfold liClockPairedEtaPartitionSignedForcingDensity
  change (∫x:ℝ,(2*x-w)*liClockPairedEtaPartitionDifferenceDensity N x*u (w-x))=0
  simp_rw [heq]
  rw [integral_const_mul,hsym,mul_zero]

theorem continuous_liClockPairedEtaPartitionDifferenceDensity (N:ℕ) :
    Continuous (liClockPairedEtaPartitionDifferenceDensity N) :=
  (continuous_liClockPairedEtaPartitionRawDifferenceDensity N).div_const _

theorem continuous_liClockPairedEtaContiguousDifferenceDensity (L:ℝ) :
    Continuous (liClockPairedEtaContiguousDifferenceDensity L) :=
  (continuous_liClockPairedEtaContiguousRawDifferenceDensity L).div_const _

theorem liClockPairedEtaPartitionDifferenceDensity_nonneg (N:ℕ) (x:ℝ) :
    0≤liClockPairedEtaPartitionDifferenceDensity N x :=
  div_nonneg (liClockPairedEtaPartitionRawDifferenceDensity_nonneg N x) (sq_nonneg _)

theorem liClockPairedEtaContiguousDifferenceDensity_nonneg (L x:ℝ) :
    0≤liClockPairedEtaContiguousDifferenceDensity L x :=
  div_nonneg (liClockPairedEtaContiguousRawDifferenceDensity_nonneg L x) (sq_nonneg _)

theorem liClockPairedEtaContiguousDifferenceDensity_pos {L x:ℝ} (hx:|x|<L) :
    0<liClockPairedEtaContiguousDifferenceDensity L x :=
  div_pos (liClockPairedEtaContiguousRawDifferenceDensity_pos hx)
    (sq_pos_of_pos (liClockPairedEtaContiguousPartitionNormalizer_pos ((abs_nonneg x).trans_lt hx)))

theorem liClockPairedEtaPartitionDifferenceDensity_even (N:ℕ) (x:ℝ) :
    liClockPairedEtaPartitionDifferenceDensity N (-x)=liClockPairedEtaPartitionDifferenceDensity N x := by
  unfold liClockPairedEtaPartitionDifferenceDensity
  rw [liClockPairedEtaPartitionRawDifferenceDensity_even]

theorem liClockPairedEtaContiguousDifferenceDensity_even (L x:ℝ) :
    liClockPairedEtaContiguousDifferenceDensity L (-x)=liClockPairedEtaContiguousDifferenceDensity L x := by
  unfold liClockPairedEtaContiguousDifferenceDensity
  rw [liClockPairedEtaContiguousRawDifferenceDensity_even]

theorem liClockPairedEtaPartitionDifferenceDensity_zero_of_log_le_abs {N:ℕ} {x:ℝ}
    (hx:Real.log (2*(N:ℝ))≤|x|) : liClockPairedEtaPartitionDifferenceDensity N x=0 := by
  unfold liClockPairedEtaPartitionDifferenceDensity
  rw [liClockPairedEtaPartitionRawDifferenceDensity_zero_of_log_le_abs hx,zero_div]

theorem liClockPairedEtaContiguousDifferenceDensity_zero_of_le_abs {L x:ℝ} (hx:L≤|x|) :
    liClockPairedEtaContiguousDifferenceDensity L x=0 := by
  unfold liClockPairedEtaContiguousDifferenceDensity
  rw [liClockPairedEtaContiguousRawDifferenceDensity_zero_of_le_abs hx,zero_div]

theorem liClockPairedEtaPartitionDensityRatio_bounds {N:ℕ} (hN:0<N) {x:ℝ}
    (hx:|x|<Real.log (2*(N:ℝ))) :
    0≤liClockPairedEtaPartitionDensityRatio N x ∧
      liClockPairedEtaPartitionDensityRatio N x≤liClockPairedEtaPartitionComparisonScale N := by
  have hg:=liClockPairedEtaContiguousRawDifferenceDensity_pos hx
  rw [ratio_eq_raw hN hx]
  constructor
  · exact div_nonneg (mul_nonneg (liClockPairedEtaPartitionComparisonScale_pos hN).le
      (liClockPairedEtaPartitionRawDifferenceDensity_nonneg N x)) hg.le
  · exact (div_le_iff₀ hg).mpr (mul_le_mul_of_nonneg_left
      (liClockPairedEtaPartitionRawDifferenceDensity_le_contiguous N x)
      (liClockPairedEtaPartitionComparisonScale_pos hN).le)

theorem continuousOn_liClockPairedEtaPartitionDensityRatio {N:ℕ} (_hN:0<N) :
    ContinuousOn (liClockPairedEtaPartitionDensityRatio N)
      (Ioo (-Real.log (2*(N:ℝ))) (Real.log (2*(N:ℝ)))) := by
  exact (continuous_liClockPairedEtaPartitionDifferenceDensity N).continuousOn.div
    (continuous_liClockPairedEtaContiguousDifferenceDensity _).continuousOn
    (fun x hx=>(liClockPairedEtaContiguousDifferenceDensity_pos (abs_lt.mpr hx)).ne')

private theorem integrable_signed_density (N:ℕ) (w:ℝ) :
    Integrable (fun x:ℝ=>(2*x-w)*liClockPairedEtaPartitionDifferenceDensity N x*
      liClockPairedEtaContiguousDifferenceDensity (Real.log (2*(N:ℝ))) (w-x)) := by
  have hc : Continuous (fun x:ℝ=>(2*x-w)*liClockPairedEtaPartitionDifferenceDensity N x*
      liClockPairedEtaContiguousDifferenceDensity (Real.log (2*(N:ℝ))) (w-x)) := by
    exact ((continuous_const.mul continuous_id).sub continuous_const).mul
      (continuous_liClockPairedEtaPartitionDifferenceDensity N) |>.mul
      ((continuous_liClockPairedEtaContiguousDifferenceDensity _).comp (continuous_const.sub continuous_id))
  simpa only [mul_zero,Nat.mul_zero,pow_zero,one_mul] using
    integrable_pow_mul_raw (L:=Real.log (2*(N:ℝ))) hc
      (fun x hx=>by rw [liClockPairedEtaPartitionDifferenceDensity_zero_of_log_le_abs hx,mul_zero,zero_mul]) 0

/-- Retains the signed coupling inside the complete convolution integral. -/
theorem liClockPairedEtaPartitionSignedForcingDensity_eq_antisymmetric (N:ℕ) (w:ℝ) :
    liClockPairedEtaPartitionSignedForcingDensity N w = (1/2:ℝ)*
      (∫x:ℝ,(2*x-w)*(liClockPairedEtaPartitionDifferenceDensity N x*
        liClockPairedEtaContiguousDifferenceDensity (Real.log (2*(N:ℝ))) (w-x)-
        liClockPairedEtaPartitionDifferenceDensity N (w-x)*
          liClockPairedEtaContiguousDifferenceDensity (Real.log (2*(N:ℝ))) x)) := by
  let f:=liClockPairedEtaPartitionDifferenceDensity N
  let g:=liClockPairedEtaContiguousDifferenceDensity (Real.log (2*(N:ℝ)))
  have ht:=integral_sub_left_eq_self (μ:=volume) (fun x:ℝ=>(2*x-w)*f x*g (w-x)) w
  have he:(fun x:ℝ=>(2*(w-x)-w)*f (w-x)*g (w-(w-x)))=
      fun x=>-((2*x-w)*f (w-x)*g x) := by funext x; rw [sub_sub_cancel]; ring
  rw [he,integral_neg] at ht
  have hI:Integrable (fun x:ℝ=>(2*x-w)*f (w-x)*g x) := by
    have h := (integrable_signed_density N w).comp_sub_left w
    convert h.neg using 1
    funext x
    dsimp [f,g]
    rw [sub_sub_cancel]
    ring
  have he2:(fun x:ℝ=>(2*x-w)*(f x*g (w-x)-f (w-x)*g x)) =
      fun x=>(2*x-w)*f x*g (w-x)-(2*x-w)*f (w-x)*g x := by funext x; ring
  change (∫x:ℝ,(2*x-w)*f x*g (w-x))=(1/2:ℝ)*(∫x:ℝ,(2*x-w)*(f x*g (w-x)-f (w-x)*g x))
  rw [he2,integral_sub (integrable_signed_density N w) hI]
  linarith

private theorem signed_shear_test_integral {f g φ : ℝ → ℝ}
    (hI : Integrable (fun p : ℝ×ℝ => (p.1-p.2)*φ (p.1+p.2)*f p.1*g p.2)
      (volume.prod volume)) :
    (∫ w : ℝ, φ w*(∫ x : ℝ, (2*x-w)*f x*g (w-x))) =
      ∫ p : ℝ×ℝ, (p.1-p.2)*φ (p.1+p.2)*f p.1*g p.2 ∂volume.prod volume := by
  let F := fun p : ℝ×ℝ => (p.1-p.2)*φ (p.1+p.2)*f p.1*g p.2
  let G := fun p : ℝ×ℝ => (2*p.2-p.1)*φ p.1*f p.2*g (p.1-p.2)
  have hT := measurePreserving_prod_sub_swap (volume : Measure ℝ) volume
  have heq : F ∘ (fun p : ℝ×ℝ => (p.2,p.1-p.2)) = G := by
    funext p
    dsimp only [F,G,Function.comp_def]
    rw [show p.2-(p.1-p.2)=2*p.2-p.1 by ring,
      show p.2+(p.1-p.2)=p.1 by ring]
  have hG := hT.integrable_comp_of_integrable hI
  change Integrable (F ∘ (fun p : ℝ×ℝ => (p.2,p.1-p.2))) (volume.prod volume) at hG
  rw [heq] at hG
  have hEmb : MeasurableEmbedding (fun p : ℝ×ℝ => (p.2,p.1-p.2)) :=
    ((MeasurableEquiv.prodComm : ℝ×ℝ ≃ᵐ ℝ×ℝ).trans (MeasurableEquiv.shearSubRight ℝ)).measurableEmbedding
  have hchange := hT.integral_comp hEmb F
  change (∫ p : ℝ×ℝ, (F ∘ (fun q : ℝ×ℝ => (q.2,q.1-q.2))) p ∂volume.prod volume) = _ at hchange
  rw [heq] at hchange
  calc
    _ = ∫ w : ℝ, ∫ x : ℝ, G (w,x) := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [G]
      ring
    _ = ∫ p : ℝ×ℝ, G p ∂volume.prod volume := (integral_prod G hG).symm
    _ = _ := hchange

private theorem signed_density_product_integrable {f g φ:ℝ→ℝ} {L:ℝ}
    (hf:Continuous f) (hg:Continuous g) (hφ:Continuous φ)
    (hfz:∀x:ℝ,L≤|x| → f x=0) (hgz:∀x:ℝ,L≤|x| → g x=0) :
    Integrable (fun p:ℝ×ℝ=>(p.1-p.2)*φ (p.1+p.2)*f p.1*g p.2) (volume.prod volume) := by
  have hc : Continuous (fun p:ℝ×ℝ=>(p.1-p.2)*φ (p.1+p.2)*f p.1*g p.2) :=
    (((continuous_fst.sub continuous_snd).mul (hφ.comp (continuous_fst.add continuous_snd))).mul
      (hf.comp continuous_fst)).mul (hg.comp continuous_snd)
  have hs : Function.support (fun p:ℝ×ℝ=>(p.1-p.2)*φ (p.1+p.2)*f p.1*g p.2) ⊆
      Icc (-L,-L) (L,L) := by
    intro p hp
    change (p.1-p.2)*φ (p.1+p.2)*f p.1*g p.2≠0 at hp
    have hf0:f p.1≠0 := by intro h; apply hp; simp only [h,mul_zero,zero_mul]
    have hg0:g p.2≠0 := by intro h; apply hp; simp only [h,mul_zero]
    have hpx:|p.1|<L := lt_of_not_ge (fun h=>hf0 (hfz p.1 h))
    have hpy:|p.2|<L := lt_of_not_ge (fun h=>hg0 (hgz p.2 h))
    exact ⟨⟨(abs_lt.mp hpx).1.le,(abs_lt.mp hpy).1.le⟩,⟨(abs_lt.mp hpx).2.le,(abs_lt.mp hpy).2.le⟩⟩
  exact (integrableOn_iff_integrable_of_support_subset hs).mp hc.continuousOn.integrableOn_Icc

private theorem signed_shear_integrable {f g φ:ℝ→ℝ}
    (hI:Integrable (fun p:ℝ×ℝ=>(p.1-p.2)*φ (p.1+p.2)*f p.1*g p.2) (volume.prod volume)) :
    Integrable (fun w:ℝ=>φ w*(∫x:ℝ,(2*x-w)*f x*g (w-x))) := by
  have h:= (measurePreserving_prod_sub_swap (volume:Measure ℝ) volume).integrable_comp_of_integrable hI
  have he : (fun p:ℝ×ℝ=>((p.2-(p.1-p.2))*φ (p.2+(p.1-p.2))*f p.2*g (p.1-p.2))) =
      fun p:ℝ×ℝ=>(2*p.2-p.1)*φ p.1*f p.2*g (p.1-p.2) := by
        funext p
        rw [show p.2-(p.1-p.2)=2*p.2-p.1 by ring,show p.2+(p.1-p.2)=p.1 by ring]
  change Integrable (fun p:ℝ×ℝ=>((p.2-(p.1-p.2))*φ (p.2+(p.1-p.2))*f p.2*g (p.1-p.2))) (volume.prod volume) at h
  rw [he] at h
  have hi:=h.integral_prod_left
  convert hi using 1
  funext w
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

private theorem integral_prod_real_densities (f g:ℝ→ℝ) (hf:Continuous f) (hg:Continuous g)
    (hfn:∀x,0≤f x) (hgn:∀x,0≤g x) (ψ:ℝ×ℝ→ℝ) :
    (∫p:ℝ×ℝ,ψ p ∂(volume.withDensity (fun x=>ENNReal.ofReal (f x))).prod
      (volume.withDensity (fun x=>ENNReal.ofReal (g x)))) =
      ∫p:ℝ×ℝ,ψ p*f p.1*g p.2 ∂volume.prod volume := by
  rw [prod_withDensity hf.measurable.ennreal_ofReal hg.measurable.ennreal_ofReal,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun p=>ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (hfn p.1),ENNReal.toReal_ofReal (hgn p.2),smul_eq_mul]
  ring

/-- Every continuous test is absolutely integrable against the complete signed forcing density. -/
theorem integrable_mul_liClockPairedEtaPartitionSignedForcingDensity (N:ℕ) (φ:ℝ→ℝ) (hφ:Continuous φ) :
    Integrable (fun w:ℝ=>φ w*liClockPairedEtaPartitionSignedForcingDensity N w) :=
  signed_shear_integrable (signed_density_product_integrable
    (continuous_liClockPairedEtaPartitionDifferenceDensity N)
    (continuous_liClockPairedEtaContiguousDifferenceDensity _) hφ
    (fun _ h=>liClockPairedEtaPartitionDifferenceDensity_zero_of_log_le_abs h)
    (fun _ h=>liClockPairedEtaContiguousDifferenceDensity_zero_of_le_abs h))

/-- Exact source identity for all four independent tilted coordinates and every continuous test. -/
theorem liClockPairedEtaPartitionSignedForcingDensity_integral_eq_source {N:ℕ} (hN:0<N)
    (φ:ℝ→ℝ) (hφ:Continuous φ) :
    (∫w:ℝ,φ w*liClockPairedEtaPartitionSignedForcingDensity N w) =
      ∫p:(ℝ×ℝ)×(ℝ×ℝ), ((p.1.1-p.1.2)-(p.2.1-p.2.2))*
        φ ((p.1.1-p.1.2)+(p.2.1-p.2.2))
        ∂(liClockPairedEtaSymmetrizedMeasure N).prod
          (liClockPairedEtaContiguousSymmetrizedMeasure (Real.log (2*(N:ℝ)))) := by
  let f:=liClockPairedEtaPartitionDifferenceDensity N
  let g:=liClockPairedEtaContiguousDifferenceDensity (Real.log (2*(N:ℝ)))
  let ψ:=fun p:ℝ×ℝ=>(p.1-p.2)*φ (p.1+p.2)
  have hI:=signed_density_product_integrable
    (continuous_liClockPairedEtaPartitionDifferenceDensity N)
    (continuous_liClockPairedEtaContiguousDifferenceDensity _) hφ
    (fun _ h=>liClockPairedEtaPartitionDifferenceDensity_zero_of_log_le_abs h)
    (fun _ h=>liClockPairedEtaContiguousDifferenceDensity_zero_of_le_abs h)
  change (∫w:ℝ,φ w*(∫x:ℝ,(2*x-w)*f x*g (w-x))) = _
  rw [signed_shear_test_integral hI]
  letI:=liClockPairedEtaSymmetrizedMeasure_isProbability hN
  letI:=liClockPairedEtaContiguousSymmetrizedMeasure_isProbability (log_endpoint_pos hN)
  have hm : Measure.map (Prod.map (fun p:ℝ×ℝ=>p.1-p.2) (fun p:ℝ×ℝ=>p.1-p.2))
      ((liClockPairedEtaSymmetrizedMeasure N).prod
        (liClockPairedEtaContiguousSymmetrizedMeasure (Real.log (2*(N:ℝ))))) =
      (volume.withDensity (fun x=>ENNReal.ofReal (f x))).prod
        (volume.withDensity (fun x=>ENNReal.ofReal (g x))) := by
    rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      liClockPairedEtaPartitionDifferenceDensity_map hN,
      liClockPairedEtaContiguousDifferenceDensity_map (log_endpoint_pos hN)]
  have hi:=integral_map (μ:=(liClockPairedEtaSymmetrizedMeasure N).prod
      (liClockPairedEtaContiguousSymmetrizedMeasure (Real.log (2*(N:ℝ)))))
    (φ:=Prod.map (fun p:ℝ×ℝ=>p.1-p.2) (fun p:ℝ×ℝ=>p.1-p.2))
    (by fun_prop) (f:=ψ) (by exact (show Continuous ψ from (continuous_fst.sub continuous_snd).mul
      (hφ.comp (continuous_fst.add continuous_snd))).aestronglyMeasurable)
  rw [hm,integral_prod_real_densities f g
    (continuous_liClockPairedEtaPartitionDifferenceDensity N)
    (continuous_liClockPairedEtaContiguousDifferenceDensity _)
    (liClockPairedEtaPartitionDifferenceDensity_nonneg N)
    (liClockPairedEtaContiguousDifferenceDensity_nonneg _) ψ] at hi
  exact hi

private theorem even_density_neg_map (g:ℝ→ℝ) (hg:Continuous g) (he:∀x,g (-x)=g x) :
    Measure.map (fun x:ℝ=>-x) (volume.withDensity (fun x=>ENNReal.ofReal (g x))) =
      volume.withDensity (fun x=>ENNReal.ofReal (g x)) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ (by fun_prop)]
  have hφneg:Measurable (fun x:ℝ=>φ (-x)):=hφ.comp measurable_neg
  rw [lintegral_withDensity_eq_lintegral_mul _ hg.measurable.ennreal_ofReal hφneg,
    lintegral_withDensity_eq_lintegral_mul _ hg.measurable.ennreal_ofReal hφ]
  have hn := (Measure.measurePreserving_neg (volume:Measure ℝ)).lintegral_comp
    (f:=fun x:ℝ=>ENNReal.ofReal (g x)*φ x) (by fun_prop)
  simp only [Pi.mul_apply]
  rw [← hn]
  apply lintegral_congr
  intro x
  exact congrArg (fun a:ℝ=>ENNReal.ofReal a*φ (-x)) (he x).symm

private theorem map_abs_even_density (g:ℝ→ℝ) (hg:Continuous g) (he:∀x,g (-x)=g x) :
    Measure.map (fun x:ℝ=>|x|) (volume.withDensity (fun x=>ENNReal.ofReal (g x))) =
      volume.withDensity ((Ioi (0:ℝ)).indicator (fun x=>ENNReal.ofReal (2*g x))) := by
  let μ:=volume.withDensity (fun x=>ENNReal.ofReal (g x))
  have hn : μ.restrict (Iio 0)=Measure.map (fun x:ℝ=>-x) (μ.restrict (Ioi 0)) := by
    have h:=measurableEmbedding_neg.restrict_map μ (Iio (0:ℝ))
    have hpre : (fun x:ℝ=>-x)⁻¹' Iio 0=Ioi 0 := by ext x; simp
    rw [even_density_neg_map g hg he,hpre] at h
    exact h
  have hp : Measure.map (fun x:ℝ=>|x|) (μ.restrict (Ioi 0))=μ.restrict (Ioi 0) := by
    rw [Measure.map_congr (show (fun x:ℝ=>|x|)=ᵐ[μ.restrict (Ioi 0)](fun x=>x) by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact abs_of_pos hx),Measure.map_id']
  have hsplit : μ=μ.restrict (Ioi 0)+μ.restrict (Iio 0) := by
    rw [restrict_Iio_eq_restrict_Iic,← compl_Ioi]
    exact (Measure.restrict_add_restrict_compl measurableSet_Ioi).symm
  have hfold : Measure.map (fun x:ℝ=>|x|) μ = (2:ℝ≥0∞) • μ.restrict (Ioi 0) := by
    calc
      _ = Measure.map (fun x:ℝ=>|x|) (μ.restrict (Ioi 0)+μ.restrict (Iio 0)) := congrArg _ hsplit
      _ = μ.restrict (Ioi 0)+μ.restrict (Ioi 0) := by
        rw [Measure.map_add _ _ (by fun_prop),hp,hn,Measure.map_map (by fun_prop) (by fun_prop)]
        simpa only [Function.comp_def,abs_neg] using congrArg (fun m:Measure ℝ=>μ.restrict (Ioi 0)+m) hp
      _ = _ := (two_smul ℝ≥0∞ (μ.restrict (Ioi 0))).symm
  rw [hfold]
  change (2:ℝ≥0∞) • (volume.withDensity (fun x=>ENNReal.ofReal (g x))).restrict (Ioi 0) = _
  rw [restrict_withDensity measurableSet_Ioi,← withDensity_indicator measurableSet_Ioi,
    ← withDensity_smul _ (hg.measurable.ennreal_ofReal.indicator measurableSet_Ioi)]
  congr 1
  funext x
  by_cases hx:x∈Ioi (0:ℝ)
  · simp only [Pi.smul_apply,indicator_of_mem hx,smul_eq_mul]
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
    norm_num
  · simp [hx]

/-- Canonical radial actual density: the factor two occurs after folding, not before normalization. -/
def liClockPairedEtaPartitionRadialDifferenceDensity (N:ℕ) (x:ℝ) : ℝ :=
  (Ioi (0:ℝ)).indicator (fun y=>2*liClockPairedEtaPartitionDifferenceDensity N y) x

def liClockPairedEtaContiguousRadialDifferenceDensity (L x:ℝ) : ℝ :=
  (Ioi (0:ℝ)).indicator (fun y=>2*liClockPairedEtaContiguousDifferenceDensity L y) x

def liClockPairedEtaPartitionRadialDifferenceMeasure (N:ℕ) : Measure ℝ :=
  Measure.map (fun x:ℝ=>|x|) (Measure.map (fun p:ℝ×ℝ=>p.1-p.2) (liClockPairedEtaSymmetrizedMeasure N))

/-- Full folded actual law, including zero mass at the fold endpoint. -/
theorem liClockPairedEtaPartitionRadialDifferenceDensity_map {N:ℕ} (hN:0<N) :
    liClockPairedEtaPartitionRadialDifferenceMeasure N =
      volume.withDensity (fun x=>ENNReal.ofReal (liClockPairedEtaPartitionRadialDifferenceDensity N x)) := by
  rw [liClockPairedEtaPartitionRadialDifferenceMeasure,liClockPairedEtaPartitionDifferenceDensity_map hN,
    map_abs_even_density _ (continuous_liClockPairedEtaPartitionDifferenceDensity N)
      (liClockPairedEtaPartitionDifferenceDensity_even N)]
  congr 1
  funext x
  by_cases hx:x∈Ioi (0:ℝ) <;> simp [liClockPairedEtaPartitionRadialDifferenceDensity,hx]

theorem liClockPairedEtaContiguousRadialDifferenceDensity_map {L:ℝ} (hL:0<L) :
    liClockPairedEtaContiguousRadialDifferenceMeasure L =
      volume.withDensity (fun x=>ENNReal.ofReal (liClockPairedEtaContiguousRadialDifferenceDensity L x)) := by
  rw [liClockPairedEtaContiguousRadialDifferenceMeasure,liClockPairedEtaContiguousDifferenceDensity_map hL,
    map_abs_even_density _ (continuous_liClockPairedEtaContiguousDifferenceDensity L)
      (liClockPairedEtaContiguousDifferenceDensity_even L)]
  congr 1
  funext x
  by_cases hx:x∈Ioi (0:ℝ) <;> simp [liClockPairedEtaContiguousRadialDifferenceDensity,hx]

/-- Literal radial likelihood ratio agrees inside the strict positive support. -/
theorem liClockPairedEtaPartitionRadialDifferenceDensity_ratio {N:ℕ} {x:ℝ}
    (hx:0<x) (_hxL:x<Real.log (2*(N:ℝ))) :
    liClockPairedEtaPartitionRadialDifferenceDensity N x /
      liClockPairedEtaContiguousRadialDifferenceDensity (Real.log (2*(N:ℝ))) x =
        liClockPairedEtaPartitionDensityRatio N x := by
  unfold liClockPairedEtaPartitionRadialDifferenceDensity liClockPairedEtaContiguousRadialDifferenceDensity
    liClockPairedEtaPartitionDensityRatio
  rw [indicator_of_mem (show x∈Ioi (0:ℝ) from hx),indicator_of_mem (show x∈Ioi (0:ℝ) from hx)]
  exact mul_div_mul_left _ _ (by norm_num : (2:ℝ)≠0)

/-- The literal first omitted interval contributes at least one sixth of raw central overlap loss. -/
theorem liClockPairedEtaPartitionRawDifferenceDensity_zero_gap_lower {N:ℕ} (hN:2≤N) :
    (1/6:ℝ)≤liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) 0-
      liClockPairedEtaPartitionRawDifferenceDensity N 0 := by
  rw [liClockPairedEtaPartitionRawDifferenceDensity_zero_gap (by omega : 0<N)]
  have h:=Finset.single_le_sum (s:=Finset.range (N-1)) (a:=0)
    (f:=fun j:ℕ=>1/(2*(j:ℝ)+2)-1/(2*(j:ℝ)+3))
    (fun j hj=>sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith)))
    (Finset.mem_range.mpr (by omega : 0<N-1))
  norm_num only [Nat.cast_zero,mul_zero,zero_add] at h
  norm_num at h ⊢
  exact h

private theorem differenceDensity_eq_ratio_mul_reference {N:ℕ} (_hN:0<N) (x:ℝ) :
    liClockPairedEtaPartitionDifferenceDensity N x = liClockPairedEtaPartitionDensityRatio N x*
      liClockPairedEtaContiguousDifferenceDensity (Real.log (2*(N:ℝ))) x := by
  by_cases hx:|x|<Real.log (2*(N:ℝ))
  · unfold liClockPairedEtaPartitionDensityRatio
    exact (div_mul_cancel₀ _ (liClockPairedEtaContiguousDifferenceDensity_pos hx).ne').symm
  · rw [liClockPairedEtaPartitionDifferenceDensity_zero_of_log_le_abs (le_of_not_gt hx),
      liClockPairedEtaContiguousDifferenceDensity_zero_of_le_abs (le_of_not_gt hx),mul_zero]

/-- Exact signed ratio coupling, including zero-density support boundaries. -/
theorem liClockPairedEtaPartitionSignedForcingDensity_eq_ratio_difference {N:ℕ} (hN:0<N) (w:ℝ) :
    liClockPairedEtaPartitionSignedForcingDensity N w = (1/2:ℝ)*
      (∫x:ℝ,(2*x-w)*(liClockPairedEtaPartitionDensityRatio N x-
        liClockPairedEtaPartitionDensityRatio N (w-x))*
        liClockPairedEtaContiguousDifferenceDensity (Real.log (2*(N:ℝ))) x*
        liClockPairedEtaContiguousDifferenceDensity (Real.log (2*(N:ℝ))) (w-x)) := by
  rw [liClockPairedEtaPartitionSignedForcingDensity_eq_antisymmetric]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [differenceDensity_eq_ratio_mul_reference hN x,differenceDensity_eq_ratio_mul_reference hN (w-x)]
  ring

end RHTower
