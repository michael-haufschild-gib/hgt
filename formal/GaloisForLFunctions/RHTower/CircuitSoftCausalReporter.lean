import GaloisForLFunctions.RHTower.CircuitCausalAccessibility
import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw

/-!
# The soft causal reporter of a circuit trace dictionary

Replacing a hard target by the clipped ramp of its distance function turns the concurrent causal
accessibility into a bounded Lipschitz observable: the Boltzmann expectation of the best causal
prefix score.  Its Lipschitz constant is the reciprocal softening radius, independent of circuit
depth, alphabet size, dependence degree, prefix count and ambient dimension.

The soft reporter dominates the hard accessibility, is dominated by the accessibility of the
enlarged targets, and calibrates the robust circuit complexity exactly as the hard reporter does.
-/

open MeasureTheory

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.RHTower

section SoftScore

variable {X : Type*} [PseudoMetricSpace X]

/-- Clipped ramp of the distance to a target set. -/
noncomputable def softTargetScore (δ : ℝ) (B : Set X) (x : X) : ℝ :=
  max (1 - Metric.infDist x B / δ) 0

theorem softTargetScore_nonneg (δ : ℝ) (B : Set X) (x : X) : 0 ≤ softTargetScore δ B x :=
  le_max_right _ _

theorem softTargetScore_le_one {δ : ℝ} (hδ : 0 < δ) (B : Set X) (x : X) :
    softTargetScore δ B x ≤ 1 := by
  rw [softTargetScore, max_le_iff]
  refine ⟨?_, zero_le_one⟩
  have : 0 ≤ Metric.infDist x B / δ := div_nonneg Metric.infDist_nonneg hδ.le
  linarith

theorem softTargetScore_eq_one_of_mem {δ : ℝ} {B : Set X} {x : X} (hx : x ∈ B) :
    softTargetScore δ B x = 1 := by
  rw [softTargetScore, Metric.infDist_zero_of_mem hx]
  simp

theorem infDist_lt_of_softTargetScore_pos {δ : ℝ} (hδ : 0 < δ) {B : Set X} {x : X}
    (hx : 0 < softTargetScore δ B x) : Metric.infDist x B < δ := by
  rw [softTargetScore, lt_max_iff] at hx
  rcases hx with h | h
  · have : Metric.infDist x B / δ < 1 := by linarith
    exact (div_lt_one hδ).mp this
  · exact absurd h (lt_irrefl 0)

theorem abs_softTargetScore_sub_le {δ : ℝ} (hδ : 0 < δ) (B : Set X) (x y : X) :
    |softTargetScore δ B x - softTargetScore δ B y| ≤ dist x y / δ := by
  have hd : |Metric.infDist x B - Metric.infDist y B| ≤ dist x y := by
    rw [abs_sub_le_iff]
    constructor
    · have h1 := Metric.infDist_le_infDist_add_dist (s := B) (x := x) (y := y)
      linarith
    · have h2 := Metric.infDist_le_infDist_add_dist (s := B) (x := y) (y := x)
      rw [dist_comm] at h2
      linarith
  have hmax : |softTargetScore δ B x - softTargetScore δ B y| ≤
      |(1 - Metric.infDist x B / δ) - (1 - Metric.infDist y B / δ)| :=
    abs_max_sub_max_le_abs _ _ _
  calc |softTargetScore δ B x - softTargetScore δ B y|
      ≤ |(1 - Metric.infDist x B / δ) - (1 - Metric.infDist y B / δ)| := hmax
    _ = |Metric.infDist x B - Metric.infDist y B| / δ := by
        rw [show (1 - Metric.infDist x B / δ) - (1 - Metric.infDist y B / δ) =
            -((Metric.infDist x B - Metric.infDist y B) / δ) by ring, abs_neg, abs_div,
          abs_of_pos hδ]
    _ ≤ dist x y / δ := by gcongr

end SoftScore

section PrefixScore

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
variable {X : Type*} [PseudoMetricSpace X]

theorem tracePrefixSet_toFinset_nonempty (independent : α → α → Prop) (T : Trace independent) :
    ((tracePrefixSet_finite independent T).toFinset).Nonempty :=
  ⟨1, (Set.Finite.mem_toFinset _).mpr (tracePrefix_one independent T)⟩

/-- Best soft score over the causal prefixes of a heap. -/
noncomputable def prefixMaxScore (independent : α → α → Prop) (δ : ℝ)
    (B : Trace independent → Set X) (x : X) (T : Trace independent) : ℝ :=
  ((tracePrefixSet_finite independent T).toFinset).sup'
    (tracePrefixSet_toFinset_nonempty independent T)
    fun u => softTargetScore δ (B u) x

theorem softTargetScore_le_prefixMaxScore (independent : α → α → Prop) (δ : ℝ)
    (B : Trace independent → Set X) (x : X) {u T : Trace independent}
    (hu : TracePrefix independent u T) :
    softTargetScore δ (B u) x ≤ prefixMaxScore independent δ B x T :=
  Finset.le_sup' (fun u => softTargetScore δ (B u) x) ((Set.Finite.mem_toFinset _).mpr hu)

theorem prefixMaxScore_nonneg (independent : α → α → Prop) (δ : ℝ)
    (B : Trace independent → Set X) (x : X) (T : Trace independent) :
    0 ≤ prefixMaxScore independent δ B x T :=
  le_trans (softTargetScore_nonneg δ (B 1) x)
    (softTargetScore_le_prefixMaxScore independent δ B x (tracePrefix_one independent T))

theorem prefixMaxScore_le_one (independent : α → α → Prop) {δ : ℝ} (hδ : 0 < δ)
    (B : Trace independent → Set X) (x : X) (T : Trace independent) :
    prefixMaxScore independent δ B x T ≤ 1 :=
  Finset.sup'_le _ _ fun u _ => softTargetScore_le_one hδ (B u) x

theorem abs_sup'_sub_sup'_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f g : ι → ℝ) {c : ℝ}
    (h : ∀ i ∈ s, |f i - g i| ≤ c) : |s.sup' hs f - s.sup' hs g| ≤ c := by
  rw [abs_sub_le_iff]
  constructor
  · refine sub_le_iff_le_add.mpr (Finset.sup'_le hs f fun i hi => ?_)
    have := (abs_le.mp (h i hi)).2
    exact le_trans (by linarith) (add_le_add_right (Finset.le_sup' g hi) c)
  · refine sub_le_iff_le_add.mpr (Finset.sup'_le hs g fun i hi => ?_)
    have := (abs_le.mp (h i hi)).1
    exact le_trans (by linarith) (add_le_add_right (Finset.le_sup' f hi) c)

theorem abs_prefixMaxScore_sub_le (independent : α → α → Prop) {δ : ℝ} (hδ : 0 < δ)
    (B : Trace independent → Set X) (x y : X) (T : Trace independent) :
    |prefixMaxScore independent δ B x T - prefixMaxScore independent δ B y T| ≤ dist x y / δ :=
  abs_sup'_sub_sup'_le _ _ _ fun u _ => abs_softTargetScore_sub_le hδ (B u) x y

end PrefixScore

section SoftReporter

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
variable {X : Type*} [PseudoMetricSpace X]

/-- The soft causal reporter: Boltzmann expectation of the best causal prefix score. -/
noncomputable def softCausalReporter (independent : α → α → Prop) (z δ : ℝ)
    (B : Trace independent → Set X) (x : X) : ℝ :=
  ∑' T : Trace independent,
    traceWeight independent z T * prefixMaxScore independent δ B x T

/-- Targets enlarged by the softening radius. -/
def enlargedTarget (δ : ℝ) {ι : Type*} (B : ι → Set X) (u : ι) : Set X :=
  {x | Metric.infDist x (B u) ≤ δ}

theorem summable_softCausalTerm (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) {δ : ℝ} (hδ : 0 < δ)
    (B : Trace independent → Set X) (x : X) :
    Summable fun T : Trace independent =>
      traceWeight independent z T * prefixMaxScore independent δ B x T := by
  have hpos := tracePartition_pos independent hsymm Δ hdegree hz0 hz
  refine Summable.of_nonneg_of_le (fun T => ?_) (fun T => ?_)
    (summable_traceWeight independent hsymm Δ hdegree hz0 hz)
  · exact mul_nonneg (traceWeight_nonneg independent hz0 hpos T)
      (prefixMaxScore_nonneg independent δ B x T)
  · nlinarith [prefixMaxScore_le_one independent hδ B x T,
      traceWeight_nonneg independent hz0 hpos T,
      prefixMaxScore_nonneg independent δ B x T]

theorem softCausalReporter_nonneg (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) (δ : ℝ)
    (B : Trace independent → Set X) (x : X) :
    0 ≤ softCausalReporter independent z δ B x := by
  have hpos := tracePartition_pos independent hsymm Δ hdegree hz0 hz
  refine tsum_nonneg fun T => ?_
  exact mul_nonneg (traceWeight_nonneg independent hz0 hpos T)
    (prefixMaxScore_nonneg independent δ B x T)

theorem softCausalReporter_le_one (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) {δ : ℝ} (hδ : 0 < δ)
    (B : Trace independent → Set X) (x : X) :
    softCausalReporter independent z δ B x ≤ 1 := by
  have hpos := tracePartition_pos independent hsymm Δ hdegree hz0 hz
  have hterm : ∀ T : Trace independent,
      traceWeight independent z T * prefixMaxScore independent δ B x T ≤
        traceWeight independent z T := by
    intro T
    nlinarith [prefixMaxScore_le_one independent hδ B x T,
      traceWeight_nonneg independent hz0 hpos T,
      prefixMaxScore_nonneg independent δ B x T]
  rw [softCausalReporter]
  calc (∑' T : Trace independent,
        traceWeight independent z T * prefixMaxScore independent δ B x T)
      ≤ ∑' T : Trace independent, traceWeight independent z T :=
        Summable.tsum_le_tsum hterm
          (summable_softCausalTerm independent hsymm Δ hdegree hz0 hz hδ B x)
          (summable_traceWeight independent hsymm Δ hdegree hz0 hz)
    _ = 1 := tsum_traceWeight independent hsymm Δ hdegree hz0 hz

/-- **Softening dominates the hard reporter.** -/
theorem causalAccessibility_le_softCausalReporter (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) {δ : ℝ} (hδ : 0 < δ)
    (B : Trace independent → Set X) (x : X) :
    causalAccessibility independent z B x ≤ softCausalReporter independent z δ B x := by
  have hpos := tracePartition_pos independent hsymm Δ hdegree hz0 hz
  have hterm : ∀ T : Trace independent,
      Set.indicator (causalSuccessEvent independent B x) (traceWeight independent z) T ≤
        traceWeight independent z T * prefixMaxScore independent δ B x T := by
    intro T
    by_cases hT : T ∈ causalSuccessEvent independent B x
    · rw [Set.indicator_of_mem hT]
      obtain ⟨u, hprefix, hu⟩ := hT
      have hscore : (1 : ℝ) ≤ prefixMaxScore independent δ B x T := by
        have := softTargetScore_le_prefixMaxScore independent δ B x hprefix
        rwa [softTargetScore_eq_one_of_mem hu] at this
      nlinarith [traceWeight_nonneg independent hz0 hpos T]
    · rw [Set.indicator_of_notMem hT]
      exact mul_nonneg (traceWeight_nonneg independent hz0 hpos T)
        (prefixMaxScore_nonneg independent δ B x T)
  rw [causalAccessibility, traceMass_eq_tsum_traceWeight,
    tsum_subtype (causalSuccessEvent independent B x) (traceWeight independent z)]
  exact Summable.tsum_le_tsum hterm
    ((summable_traceWeight independent hsymm Δ hdegree hz0 hz).indicator _)
    (summable_softCausalTerm independent hsymm Δ hdegree hz0 hz hδ B x)

/-- **Dimension-free boundary regularity.**  The soft causal reporter is `1/δ`-Lipschitz. -/
theorem abs_softCausalReporter_sub_le (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) {δ : ℝ} (hδ : 0 < δ)
    (B : Trace independent → Set X) (x y : X) :
    |softCausalReporter independent z δ B x - softCausalReporter independent z δ B y| ≤
      dist x y / δ := by
  have hpos := tracePartition_pos independent hsymm Δ hdegree hz0 hz
  have hsx := summable_softCausalTerm independent hsymm Δ hdegree hz0 hz hδ B x
  have hsy := summable_softCausalTerm independent hsymm Δ hdegree hz0 hz hδ B y
  have hbound : ∀ T : Trace independent,
      ‖traceWeight independent z T * prefixMaxScore independent δ B x T -
        traceWeight independent z T * prefixMaxScore independent δ B y T‖ ≤
        traceWeight independent z T * (dist x y / δ) := by
    intro T
    rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (traceWeight_nonneg independent hz0 hpos T)]
    exact mul_le_mul_of_nonneg_left (abs_prefixMaxScore_sub_le independent hδ B x y T)
      (traceWeight_nonneg independent hz0 hpos T)
  have hsumNorm : Summable fun T : Trace independent =>
      ‖traceWeight independent z T * prefixMaxScore independent δ B x T -
        traceWeight independent z T * prefixMaxScore independent δ B y T‖ :=
    Summable.of_nonneg_of_le (fun T => norm_nonneg _) hbound
      ((summable_traceWeight independent hsymm Δ hdegree hz0 hz).mul_right (dist x y / δ))
  calc |softCausalReporter independent z δ B x - softCausalReporter independent z δ B y|
      = ‖∑' T : Trace independent,
          (traceWeight independent z T * prefixMaxScore independent δ B x T -
            traceWeight independent z T * prefixMaxScore independent δ B y T)‖ := by
        rw [softCausalReporter, softCausalReporter, ← hsx.tsum_sub hsy, Real.norm_eq_abs]
    _ ≤ ∑' T : Trace independent,
          ‖traceWeight independent z T * prefixMaxScore independent δ B x T -
            traceWeight independent z T * prefixMaxScore independent δ B y T‖ :=
        norm_tsum_le_tsum_norm hsumNorm
    _ ≤ ∑' T : Trace independent, traceWeight independent z T * (dist x y / δ) :=
        Summable.tsum_le_tsum hbound hsumNorm
          ((summable_traceWeight independent hsymm Δ hdegree hz0 hz).mul_right _)
    _ = dist x y / δ := by
        rw [tsum_mul_right, tsum_traceWeight independent hsymm Δ hdegree hz0 hz, one_mul]

/-- **Soft-to-hard transfer.**  The soft reporter is dominated by the causal accessibility of the
targets enlarged by the softening radius. -/
theorem softCausalReporter_le_enlarged (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) {δ : ℝ} (hδ : 0 < δ)
    (B : Trace independent → Set X) (x : X) :
    softCausalReporter independent z δ B x ≤
      causalAccessibility independent z (enlargedTarget δ B) x := by
  have hpos := tracePartition_pos independent hsymm Δ hdegree hz0 hz
  have hterm : ∀ T : Trace independent,
      traceWeight independent z T * prefixMaxScore independent δ B x T ≤
        Set.indicator (causalSuccessEvent independent (enlargedTarget δ B) x)
          (traceWeight independent z) T := by
    intro T
    rcases eq_or_lt_of_le (prefixMaxScore_nonneg independent δ B x T) with hzero | hposScore
    · rw [← hzero, mul_zero]
      by_cases hT : T ∈ causalSuccessEvent independent (enlargedTarget δ B) x
      · rw [Set.indicator_of_mem hT]
        exact traceWeight_nonneg independent hz0 hpos T
      · rw [Set.indicator_of_notMem hT]
    · rw [prefixMaxScore] at hposScore
      obtain ⟨u, hu, hscore⟩ :=
        (Finset.lt_sup'_iff (tracePrefixSet_toFinset_nonempty independent T)).mp hposScore
      have hmem : u ∈ tracePrefixSet independent T := (Set.Finite.mem_toFinset _).mp hu
      have hx : x ∈ enlargedTarget δ B u :=
        le_of_lt (infDist_lt_of_softTargetScore_pos hδ hscore)
      have hT : T ∈ causalSuccessEvent independent (enlargedTarget δ B) x := ⟨u, hmem, hx⟩
      rw [Set.indicator_of_mem hT]
      nlinarith [prefixMaxScore_le_one independent hδ B x T,
        traceWeight_nonneg independent hz0 hpos T]
  rw [causalAccessibility, traceMass_eq_tsum_traceWeight,
    tsum_subtype (causalSuccessEvent independent (enlargedTarget δ B) x)
      (traceWeight independent z)]
  exact Summable.tsum_le_tsum hterm
    (summable_softCausalTerm independent hsymm Δ hdegree hz0 hz hδ B x)
    ((summable_traceWeight independent hsymm Δ hdegree hz0 hz).indicator _)

/-- **Soft complexity calibration.**  The measure of the states reachable at depth at most `s` is
controlled by the integral of the soft causal reporter. -/
theorem measure_heapAccessible_le_softCausalReporter [MeasurableSpace X] (ν : Measure X)
    (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) (hz : 2 ^ Δ * z < 1) {δ : ℝ} (hδ : 0 < δ)
    {B : Trace independent → Set X} (hB : ∀ u, MeasurableSet (B u)) (s : ℕ) :
    ν (heapAccessible (traceLen independent) B s) ≤
      ENNReal.ofReal ((z ^ s)⁻¹) *
        ∫⁻ x, ENNReal.ofReal (softCausalReporter independent z δ B x) ∂ν := by
  have hpt : ∀ x : X, (heapAccessible (traceLen independent) B s).indicator 1 x ≤
      ENNReal.ofReal ((z ^ s)⁻¹) *
        ENNReal.ofReal (softCausalReporter independent z δ B x) := by
    intro x
    by_cases hx : x ∈ heapAccessible (traceLen independent) B s
    · rw [Set.indicator_of_mem hx, Pi.one_apply]
      obtain ⟨u, hu, hxu⟩ : ∃ u : Trace independent, traceLen independent u ≤ s ∧ x ∈ B u := by
        simpa only [heapAccessible, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] using hx
      have hlow : z ^ s ≤ softCausalReporter independent z δ B x :=
        le_trans (le_trans (pow_le_pow_of_le_one hz0.le hz1 hu)
          (pow_le_causalAccessibility independent hsymm Δ hdegree hz0.le hz hxu))
          (causalAccessibility_le_softCausalReporter independent hsymm Δ hdegree hz0.le hz hδ B x)
      calc
        (1 : ℝ≥0∞) = ENNReal.ofReal ((z ^ s)⁻¹) * ENNReal.ofReal (z ^ s) := by
          rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity),
            ENNReal.ofReal_one]
        _ ≤ ENNReal.ofReal ((z ^ s)⁻¹) *
            ENNReal.ofReal (softCausalReporter independent z δ B x) :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal hlow) _
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  calc
    ν (heapAccessible (traceLen independent) B s)
        = ∫⁻ x, (heapAccessible (traceLen independent) B s).indicator 1 x ∂ν :=
      (lintegral_indicator_one (measurableSet_heapAccessible hB s)).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal ((z ^ s)⁻¹) *
          ENNReal.ofReal (softCausalReporter independent z δ B x) ∂ν := lintegral_mono hpt
    _ = ENNReal.ofReal ((z ^ s)⁻¹) *
          ∫⁻ x, ENNReal.ofReal (softCausalReporter independent z δ B x) ∂ν :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end SoftReporter

section Transport

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/-- Kantorovich--Rubinstein dual form of the first Wasserstein distance: the supremum of the
integral gap over one-Lipschitz test functions integrable against both laws. -/
noncomputable def kantorovichRubinstein (ν μ : Measure X) : ℝ≥0∞ :=
  ⨆ f : {f : X → ℝ // LipschitzWith 1 f ∧ Integrable f ν ∧ Integrable f μ},
    ENNReal.ofReal |∫ x, (f : X → ℝ) x ∂ν - ∫ x, (f : X → ℝ) x ∂μ|

/-- **Dimension-free transport stability.**  The soft reporter changes across endpoint laws by at
most the Kantorovich--Rubinstein distance divided by the softening radius. -/
theorem ofReal_mul_abs_integral_softCausalReporter_sub_le (ν μ : Measure X)
    (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) {δ : ℝ} (hδ : 0 < δ)
    (B : Trace independent → Set X)
    (hν : Integrable (fun x => δ * softCausalReporter independent z δ B x) ν)
    (hμ : Integrable (fun x => δ * softCausalReporter independent z δ B x) μ) :
    ENNReal.ofReal (δ * |∫ x, softCausalReporter independent z δ B x ∂ν -
        ∫ x, softCausalReporter independent z δ B x ∂μ|) ≤
      kantorovichRubinstein ν μ := by
  have hlip : LipschitzWith 1 (fun x => δ * softCausalReporter independent z δ B x) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hδ, NNReal.coe_one, one_mul]
    have := abs_softCausalReporter_sub_le independent hsymm Δ hdegree hz0 hz hδ B x y
    calc δ * |softCausalReporter independent z δ B x - softCausalReporter independent z δ B y|
        ≤ δ * (dist x y / δ) := by
          exact mul_le_mul_of_nonneg_left this hδ.le
      _ = dist x y := by field_simp
  have hval : |∫ x, δ * softCausalReporter independent z δ B x ∂ν -
      ∫ x, δ * softCausalReporter independent z δ B x ∂μ| =
      δ * |∫ x, softCausalReporter independent z δ B x ∂ν -
        ∫ x, softCausalReporter independent z δ B x ∂μ| := by
    rw [integral_const_mul, integral_const_mul, ← mul_sub, abs_mul, abs_of_pos hδ]
  rw [← hval]
  exact le_iSup (fun f : {f : X → ℝ // LipschitzWith 1 f ∧ Integrable f ν ∧ Integrable f μ} =>
    ENNReal.ofReal |∫ x, (f : X → ℝ) x ∂ν - ∫ x, (f : X → ℝ) x ∂μ|)
    ⟨fun x => δ * softCausalReporter independent z δ B x, hlip, hν, hμ⟩

end Transport

section EvolutionStability

open NormedSpace

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- **Source stability of the soft reporter.**  Two self-adjoint generators move the soft reporter
by at most `|t| ‖H - K‖ ‖χ‖ / δ`, with no dimension, depth or dictionary dependence. -/
theorem abs_softCausalReporter_evolution_sub_le (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) {δ : ℝ} (hδ : 0 < δ)
    (B : Trace independent → Set X) (χ : X) (H K : X →L[ℂ] X)
    (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) (t : ℝ) :
    |softCausalReporter independent z δ B (exp (t • ((-Complex.I) • H)) χ) -
        softCausalReporter independent z δ B (exp (t • ((-Complex.I) • K)) χ)| ≤
      |t| * ‖H - K‖ * ‖χ‖ / δ := by
  have hop := GaloisForLFunctions.HTGeometry.selfAdjoint_unitaryEvolution_norm_sub_le H K hH hK t
  have hdist : dist (exp (t • ((-Complex.I) • H)) χ) (exp (t • ((-Complex.I) • K)) χ) ≤
      |t| * ‖H - K‖ * ‖χ‖ := by
    rw [dist_eq_norm, ← sub_apply]
    exact le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_right hop (norm_nonneg χ))
  refine le_trans (abs_softCausalReporter_sub_le independent hsymm Δ hdegree hz0 hz hδ B _ _) ?_
  gcongr

end EvolutionStability

section SoftCapacity

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem measurable_finset_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (f : ι → X → ℝ) (h : ∀ i, Measurable (f i)) :
    Measurable fun x => s.sup' hs fun i => f i x := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simpa using h i
  | cons i s hi hs ih =>
      have hstep : ∀ x : X, (Finset.cons i s hi).sup' (by simp) (fun j => f j x) =
          max (f i x) (s.sup' hs fun j => f j x) := fun x =>
        Finset.sup'_cons hs (fun j => f j x)
      simp_rw [hstep]
      exact (h i).max ih

theorem continuous_softTargetScore (δ : ℝ) (B : Set X) :
    Continuous fun x => softTargetScore δ B x := by
  refine Continuous.max ?_ continuous_const
  exact continuous_const.sub ((Metric.continuous_infDist_pt B).div_const δ)

theorem measurable_softTargetScore (δ : ℝ) (B : Set X) :
    Measurable fun x => softTargetScore δ B x :=
  (continuous_softTargetScore δ B).measurable

theorem measurable_prefixMaxScore (independent : α → α → Prop) (δ : ℝ)
    (B : Trace independent → Set X) (T : Trace independent) :
    Measurable fun x => prefixMaxScore independent δ B x T :=
  measurable_finset_sup' (tracePrefixSet_toFinset_nonempty independent T)
    (fun u => fun x => softTargetScore δ (B u) x) fun u => measurable_softTargetScore δ (B u)

/-- **Soft heap-capacity law.**  A uniform soft target cap is paid at the trace partition
function, exactly as in the hard case. -/
theorem lintegral_softCausalReporter_le (μ : Measure X) (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) {δ : ℝ} (hδ : 0 < δ)
    (B : Trace independent → Set X) {Bδ : ℝ≥0∞}
    (hcap : ∀ u, ∫⁻ x, ENNReal.ofReal (softTargetScore δ (B u) x) ∂μ ≤ Bδ) :
    ∫⁻ x, ENNReal.ofReal (softCausalReporter independent z δ B x) ∂μ ≤
      Bδ * ENNReal.ofReal (tracePartition independent z) := by
  have hZpos := tracePartition_pos independent hsymm Δ hdegree hz0 hz
  have hexpand : ∀ x : X, ENNReal.ofReal (softCausalReporter independent z δ B x) =
      ∑' T : Trace independent, ENNReal.ofReal (traceWeight independent z T) *
        ENNReal.ofReal (prefixMaxScore independent δ B x T) := by
    intro x
    rw [softCausalReporter, ENNReal.ofReal_tsum_of_nonneg
      (fun T => mul_nonneg (traceWeight_nonneg independent hz0 hZpos T)
        (prefixMaxScore_nonneg independent δ B x T))
      (summable_softCausalTerm independent hsymm Δ hdegree hz0 hz hδ B x)]
    exact tsum_congr fun T =>
      ENNReal.ofReal_mul (traceWeight_nonneg independent hz0 hZpos T)
  have hprefixCap : ∀ T : Trace independent,
      ∫⁻ x, ENNReal.ofReal (prefixMaxScore independent δ B x T) ∂μ ≤
        (Nat.card (tracePrefixSet independent T) : ℝ≥0∞) * Bδ := by
    intro T
    have hsumBound : ∀ x : X,
        ENNReal.ofReal (prefixMaxScore independent δ B x T) ≤
          ∑ u ∈ (tracePrefixSet_finite independent T).toFinset,
            ENNReal.ofReal (softTargetScore δ (B u) x) := by
      intro x
      have hle : prefixMaxScore independent δ B x T ≤
          ∑ u ∈ (tracePrefixSet_finite independent T).toFinset,
            softTargetScore δ (B u) x := by
        refine Finset.sup'_le _ _ fun u hu => ?_
        exact Finset.single_le_sum
          (fun v _ => softTargetScore_nonneg δ (B v) x) hu
      refine le_trans (ENNReal.ofReal_le_ofReal hle) (le_of_eq ?_)
      exact ENNReal.ofReal_sum_of_nonneg fun u _ => softTargetScore_nonneg δ (B u) x
    calc ∫⁻ x, ENNReal.ofReal (prefixMaxScore independent δ B x T) ∂μ
        ≤ ∫⁻ x, ∑ u ∈ (tracePrefixSet_finite independent T).toFinset,
            ENNReal.ofReal (softTargetScore δ (B u) x) ∂μ := lintegral_mono hsumBound
      _ = ∑ u ∈ (tracePrefixSet_finite independent T).toFinset,
            ∫⁻ x, ENNReal.ofReal (softTargetScore δ (B u) x) ∂μ :=
          lintegral_finsetSum _ fun u _ =>
            (measurable_softTargetScore δ (B u)).ennreal_ofReal
      _ ≤ ∑ _u ∈ (tracePrefixSet_finite independent T).toFinset, Bδ :=
          Finset.sum_le_sum fun u _ => hcap u
      _ = (Nat.card (tracePrefixSet independent T) : ℝ≥0∞) * Bδ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          congr 2
          exact (Nat.card_eq_card_finite_toFinset (tracePrefixSet_finite independent T)).symm
  calc ∫⁻ x, ENNReal.ofReal (softCausalReporter independent z δ B x) ∂μ
      = ∫⁻ x, ∑' T : Trace independent, ENNReal.ofReal (traceWeight independent z T) *
          ENNReal.ofReal (prefixMaxScore independent δ B x T) ∂μ := by
        exact lintegral_congr hexpand
    _ = ∑' T : Trace independent, ∫⁻ x, ENNReal.ofReal (traceWeight independent z T) *
          ENNReal.ofReal (prefixMaxScore independent δ B x T) ∂μ :=
        lintegral_tsum fun T =>
          ((measurable_prefixMaxScore independent δ B T).ennreal_ofReal.const_mul _).aemeasurable
    _ = ∑' T : Trace independent, ENNReal.ofReal (traceWeight independent z T) *
          ∫⁻ x, ENNReal.ofReal (prefixMaxScore independent δ B x T) ∂μ := by
        exact tsum_congr fun T => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∑' T : Trace independent, ENNReal.ofReal (traceWeight independent z T) *
          ((Nat.card (tracePrefixSet independent T) : ℝ≥0∞) * Bδ) :=
        ENNReal.tsum_le_tsum fun T => mul_le_mul_right (hprefixCap T) _
    _ = Bδ * ∑' T : Trace independent, (Nat.card (tracePrefixSet independent T) : ℝ≥0∞) *
          ENNReal.ofReal (traceWeight independent z T) := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun T => by ring
    _ = Bδ * ENNReal.ofReal (tracePartition independent z) := by
        congr 1
        have hweight : ∀ T : Trace independent,
            ENNReal.ofReal (traceWeight independent z T) =
              ENNReal.ofReal (z ^ traceLen independent T) *
                ENNReal.ofReal (tracePartition independent z)⁻¹ := by
          intro T
          rw [traceWeight, div_eq_mul_inv, ENNReal.ofReal_mul (by positivity)]
        calc (∑' T : Trace independent, (Nat.card (tracePrefixSet independent T) : ℝ≥0∞) *
              ENNReal.ofReal (traceWeight independent z T))
            = ∑' T : Trace independent, ((Nat.card (tracePrefixSet independent T) : ℝ≥0∞) *
                ENNReal.ofReal (z ^ traceLen independent T)) *
                  ENNReal.ofReal (tracePartition independent z)⁻¹ := by
              exact tsum_congr fun T => by rw [hweight T, mul_assoc]
          _ = (∑' T : Trace independent, (Nat.card (tracePrefixSet independent T) : ℝ≥0∞) *
                ENNReal.ofReal (z ^ traceLen independent T)) *
                  ENNReal.ofReal (tracePartition independent z)⁻¹ := ENNReal.tsum_mul_right
          _ = (tracePartitionENN independent z * tracePartitionENN independent z) *
                ENNReal.ofReal (tracePartition independent z)⁻¹ := by
              rw [tsum_tracePrefixCount independent hsymm hz0]
          _ = ENNReal.ofReal (tracePartition independent z) := by
              rw [tracePartitionENN_eq_ofReal independent hsymm Δ hdegree hz0 hz,
                mul_assoc, ← ENNReal.ofReal_mul hZpos.le,
                mul_inv_cancel₀ (ne_of_gt hZpos), ENNReal.ofReal_one, mul_one]

end SoftCapacity

end GaloisForLFunctions.RHTower
