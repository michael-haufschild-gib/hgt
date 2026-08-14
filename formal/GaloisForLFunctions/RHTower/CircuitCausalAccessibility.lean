import GaloisForLFunctions.RHTower.CircuitTraceBoltzmann

/-!
# Concurrent causal accessibility of a circuit trace dictionary

A random circuit heap succeeds at a state when one of its causal prefixes already reaches the
target.  The Boltzmann probability of that union is the concurrent causal accessibility; its
negative logarithm is the preparation action.

The accessibility lies in the unit interval, has exact value one at a robust recurrence, is
bounded below by the geometric weight of the shortest successful trace and above by the mass of
the heaps at least that long.  Comparing two weights inside the convergence interval and
optimizing the comparison gives a two-sided calibration of the preparation action by the robust
circuit complexity.
-/

open MeasureTheory

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.RHTower

section CausalAccessibility

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
variable {X : Type*}

/-- The event that some causal prefix of a heap already succeeds at `x`. -/
def causalSuccessEvent (independent : α → α → Prop) (S : Trace independent → Set X) (x : X) :
    Set (Trace independent) := {T | ∃ u, TracePrefix independent u T ∧ x ∈ S u}

/-- Concurrent causal accessibility of a target dictionary at a state. -/
noncomputable def causalAccessibility (independent : α → α → Prop) (z : ℝ)
    (S : Trace independent → Set X) (x : X) : ℝ :=
  traceMass independent z (causalSuccessEvent independent S x)

/-- Preparation action of a target dictionary at a state. -/
noncomputable def preparationAction (independent : α → α → Prop) (z : ℝ)
    (S : Trace independent → Set X) (x : X) : ℝ :=
  -Real.log (causalAccessibility independent z S x)

theorem causalAccessibility_nonneg (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1)
    (S : Trace independent → Set X) (x : X) :
    0 ≤ causalAccessibility independent z S x :=
  traceMass_nonneg independent hz0 (tracePartition_pos independent hsymm Δ hdegree hz0 hz) _

theorem causalAccessibility_le_one (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1)
    (S : Trace independent → Set X) (x : X) :
    causalAccessibility independent z S x ≤ 1 :=
  traceMass_le_one independent hsymm Δ hdegree hz0 hz _

theorem traceCylinder_subset_causalSuccessEvent (independent : α → α → Prop)
    {S : Trace independent → Set X} {x : X}
    {u : Trace independent} (hu : x ∈ S u) :
    traceCylinder independent u ⊆ causalSuccessEvent independent S x :=
  fun _ hT => ⟨u, hT, hu⟩

/-- **Complexity lower calibration.**  Any successful trace gives its geometric weight as a lower
bound for the causal accessibility. -/
theorem pow_le_causalAccessibility (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1)
    {S : Trace independent → Set X} {x : X} {u : Trace independent} (hu : x ∈ S u) :
    z ^ traceLen independent u ≤ causalAccessibility independent z S x := by
  rw [← traceMass_traceCylinder independent hsymm Δ hdegree hz0 hz u]
  exact traceMass_mono independent hsymm Δ hdegree hz0 hz
    (traceCylinder_subset_causalSuccessEvent independent
      (S := S) (x := x) (u := u) hu)

/-- **Exact recurrence value.**  If the identity trace already succeeds, the causal accessibility
is one and the preparation action vanishes. -/
theorem causalAccessibility_eq_one (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1)
    {S : Trace independent → Set X} {x : X} (hx : x ∈ S 1) :
    causalAccessibility independent z S x = 1 := by
  refine le_antisymm (causalAccessibility_le_one independent hsymm Δ hdegree hz0 hz S x) ?_
  have h := pow_le_causalAccessibility independent hsymm Δ hdegree hz0 hz (u := 1) hx
  simpa using h

theorem preparationAction_eq_zero (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1)
    {S : Trace independent → Set X} {x : X} (hx : x ∈ S 1) :
    preparationAction independent z S x = 0 := by
  rw [preparationAction, causalAccessibility_eq_one independent hsymm Δ hdegree hz0 hz hx,
    Real.log_one, neg_zero]

/-- The success event is contained in the heaps at least as long as the shortest successful
trace. -/
theorem causalSuccessEvent_subset_longHeaps (independent : α → α → Prop)
    {S : Trace independent → Set X} {x : X} {c : ℕ}
    (hmin : ∀ u, x ∈ S u → c ≤ traceLen independent u) :
    causalSuccessEvent independent S x ⊆ {T | c ≤ traceLen independent T} := by
  rintro T ⟨u, hprefix, hu⟩
  exact le_trans (hmin u hu) (traceLen_of_mem_traceCylinder hprefix)

/-- **Complexity upper calibration.**  The causal accessibility is at most the Boltzmann mass of
the heaps at least as long as the shortest successful trace. -/
theorem causalAccessibility_le_longHeaps (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1)
    {S : Trace independent → Set X} {x : X} {c : ℕ}
    (hmin : ∀ u, x ∈ S u → c ≤ traceLen independent u) :
    causalAccessibility independent z S x ≤
      traceMass independent z {T | c ≤ traceLen independent T} :=
  traceMass_mono independent hsymm Δ hdegree hz0 hz
    (causalSuccessEvent_subset_longHeaps independent hmin)

/-- **Complexity calibration of the endpoint measure.**  The measure of the states reachable at
depth at most `s` is controlled by the integral of the causal accessibility. -/
theorem measure_heapAccessible_le_causalAccessibility [MeasurableSpace X] (ν : Measure X)
    (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) (hz : 2 ^ Δ * z < 1)
    {S : Trace independent → Set X} (hS : ∀ u, MeasurableSet (S u)) (s : ℕ) :
    ν (heapAccessible (traceLen independent) S s) ≤
      ENNReal.ofReal ((z ^ s)⁻¹) *
        ∫⁻ x, ENNReal.ofReal (causalAccessibility independent z S x) ∂ν := by
  have hpt : ∀ x : X, (heapAccessible (traceLen independent) S s).indicator 1 x ≤
      ENNReal.ofReal ((z ^ s)⁻¹) *
        ENNReal.ofReal (causalAccessibility independent z S x) := by
    intro x
    by_cases hx : x ∈ heapAccessible (traceLen independent) S s
    · rw [Set.indicator_of_mem hx, Pi.one_apply]
      obtain ⟨u, hu, hxu⟩ : ∃ u : Trace independent, traceLen independent u ≤ s ∧ x ∈ S u := by
        simpa only [heapAccessible, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] using hx
      have hlow : z ^ s ≤ causalAccessibility independent z S x :=
        le_trans (pow_le_pow_of_le_one hz0.le hz1 hu)
          (pow_le_causalAccessibility independent hsymm Δ hdegree hz0.le hz hxu)
      calc
        (1 : ℝ≥0∞) = ENNReal.ofReal ((z ^ s)⁻¹) * ENNReal.ofReal (z ^ s) := by
          rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity),
            ENNReal.ofReal_one]
        _ ≤ ENNReal.ofReal ((z ^ s)⁻¹) *
            ENNReal.ofReal (causalAccessibility independent z S x) :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal hlow) _
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  calc
    ν (heapAccessible (traceLen independent) S s)
        = ∫⁻ x, (heapAccessible (traceLen independent) S s).indicator 1 x ∂ν :=
      (lintegral_indicator_one (measurableSet_heapAccessible hS s)).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal ((z ^ s)⁻¹) *
          ENNReal.ofReal (causalAccessibility independent z S x) ∂ν := lintegral_mono hpt
    _ = ENNReal.ofReal ((z ^ s)⁻¹) *
          ∫⁻ x, ENNReal.ofReal (causalAccessibility independent z S x) ∂ν :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **Two-weight comparison.**  Comparing the Boltzmann weight against a larger weight inside the
convergence interval contracts the causal accessibility by the complexity power. -/
theorem causalAccessibility_le_ratio (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z y : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) (hy0 : 0 < y) (hy : 2 ^ Δ * y < 1)
    (hzy : z ≤ y) {S : Trace independent → Set X} {x : X} {c : ℕ}
    (hmin : ∀ u, x ∈ S u → c ≤ traceLen independent u) :
    causalAccessibility independent z S x ≤
      (z / y) ^ c * (tracePartition independent y / tracePartition independent z) := by
  have hzpos := tracePartition_pos independent hsymm Δ hdegree hz0 hz
  have hsumz := summable_tracePow independent hsymm Δ hdegree hz0 hz
  have hsumy := summable_tracePow independent hsymm Δ hdegree hy0.le hy
  have hratio0 : 0 ≤ z / y := by positivity
  have hratio1 : z / y ≤ 1 := (div_le_one hy0).mpr hzy
  have hterm : ∀ T : Trace independent,
      Set.indicator (causalSuccessEvent independent S x)
        (fun T => z ^ traceLen independent T) T ≤
        (z / y) ^ c * y ^ traceLen independent T := by
    intro T
    by_cases hT : T ∈ causalSuccessEvent independent S x
    · rw [Set.indicator_of_mem hT]
      obtain ⟨u, hprefix, hu⟩ := hT
      have hlen : c ≤ traceLen independent T :=
        le_trans (hmin u hu) (traceLen_of_mem_traceCylinder hprefix)
      have hsplit : z ^ traceLen independent T =
          (z / y) ^ traceLen independent T * y ^ traceLen independent T := by
        rw [div_pow, div_mul_cancel₀]
        exact pow_ne_zero _ (ne_of_gt hy0)
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one hratio0 hratio1 hlen) (by positivity)
    · rw [Set.indicator_of_notMem hT]
      positivity
  have hnum : (∑' T : causalSuccessEvent independent S x,
      z ^ traceLen independent (T : Trace independent)) ≤
      (z / y) ^ c * tracePartition independent y := by
    rw [tsum_subtype (causalSuccessEvent independent S x)
      (fun T : Trace independent => z ^ traceLen independent T)]
    calc
      (∑' T : Trace independent, Set.indicator (causalSuccessEvent independent S x)
          (fun T => z ^ traceLen independent T) T)
          ≤ ∑' T : Trace independent, (z / y) ^ c * y ^ traceLen independent T :=
        Summable.tsum_le_tsum hterm (hsumz.indicator _) (hsumy.mul_left _)
      _ = (z / y) ^ c * tracePartition independent y := by
        rw [tsum_mul_left, tracePartition]
  rw [causalAccessibility, traceMass, div_le_iff₀ hzpos]
  calc
    (∑' T : causalSuccessEvent independent S x,
        z ^ traceLen independent (T : Trace independent))
        ≤ (z / y) ^ c * tracePartition independent y := hnum
    _ = (z / y) ^ c * (tracePartition independent y / tracePartition independent z) *
          tracePartition independent z := by
      field_simp

/-- **Optimized two-weight comparison.**  At the optimal comparison weight the causal
accessibility is bounded by the complexity power times the profile factors. -/
theorem causalAccessibility_le_optimal (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) {S : Trace independent → Set X} {x : X} {c : ℕ} (hc : 1 ≤ c)
    (hzc : 2 ^ Δ * z < (c : ℝ) / ((Fintype.card α : ℝ) + c))
    (hmin : ∀ u, x ∈ S u → c ≤ traceLen independent u) :
    causalAccessibility independent z S x ≤
      (2 ^ Δ * z) ^ c * (1 + (Fintype.card α : ℝ) / c) ^ c *
        (1 + (c : ℝ) / Fintype.card α) ^ Fintype.card α := by
  set M : ℕ := Fintype.card α with hMdef
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Fintype.card_pos
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  have hpow : (0 : ℝ) < 2 ^ Δ := by positivity
  have hsum : (0 : ℝ) < (M : ℝ) + c := by linarith
  set y : ℝ := (c : ℝ) / (2 ^ Δ * ((M : ℝ) + c)) with hydef
  have hy0 : 0 < y := by rw [hydef]; positivity
  have hkey : 2 ^ Δ * y = (c : ℝ) / ((M : ℝ) + c) := by
    rw [hydef]; field_simp
  have hy : 2 ^ Δ * y < 1 := by
    rw [hkey, div_lt_one hsum]; linarith
  have hzy : z ≤ y := by
    have : 2 ^ Δ * z < 2 ^ Δ * y := by rw [hkey]; exact hzc
    nlinarith
  have hz : 2 ^ Δ * z < 1 := lt_of_lt_of_le (by rw [hkey] at hy; linarith [hzc]) (le_of_eq rfl)
  have hzpartition : 1 ≤ tracePartition independent z :=
    one_le_tracePartition independent hsymm Δ hdegree hz0 hz
  have hypartition : tracePartition independent y ≤ (1 + (c : ℝ) / M) ^ M := by
    have hle := tracePartition_le independent hsymm Δ hdegree hy0.le hy
    have hone : 1 - 2 ^ Δ * y = (M : ℝ) / ((M : ℝ) + c) := by
      rw [hkey]; field_simp; ring
    have hfac : 1 / (1 - 2 ^ Δ * y) ^ M = (1 + (c : ℝ) / M) ^ M := by
      rw [hone, div_pow, one_div_div, ← div_pow]
      congr 1
      field_simp
    rw [hfac] at hle
    exact hle
  have hratio := causalAccessibility_le_ratio independent hsymm Δ hdegree hz0 hz hy0 hy hzy hmin
  have hzpos : 0 < tracePartition independent z := lt_of_lt_of_le zero_lt_one hzpartition
  have hquot : tracePartition independent y / tracePartition independent z ≤
      (1 + (c : ℝ) / M) ^ M := by
    refine le_trans (div_le_self ?_ hzpartition) hypartition
    exact le_trans (by norm_num) (one_le_tracePartition independent hsymm Δ hdegree hy0.le hy)
  have hzyc : (z / y) ^ c = (2 ^ Δ * z) ^ c * (1 + (M : ℝ) / c) ^ c := by
    have hzyval : z / y = 2 ^ Δ * z * (1 + (M : ℝ) / c) := by
      rw [hydef]; field_simp; ring
    rw [hzyval, mul_pow]
  calc
    causalAccessibility independent z S x
        ≤ (z / y) ^ c * (tracePartition independent y / tracePartition independent z) := hratio
    _ ≤ (z / y) ^ c * (1 + (c : ℝ) / M) ^ M := by
        refine mul_le_mul_of_nonneg_left hquot ?_
        positivity
    _ = (2 ^ Δ * z) ^ c * (1 + (M : ℝ) / c) ^ c * (1 + (c : ℝ) / M) ^ M := by
        rw [hzyc]

/-- **Two-sided preparation-action calibration.**  The preparation action is sandwiched by the
robust complexity times the logarithmic weight, up to the profile corrections. -/
theorem preparationAction_sandwich (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 < z) {S : Trace independent → Set X} {x : X} {c : ℕ} (hc : 1 ≤ c)
    (hzc : 2 ^ Δ * z < (c : ℝ) / ((Fintype.card α : ℝ) + c))
    {u₀ : Trace independent} (hu₀ : x ∈ S u₀) (hlen₀ : traceLen independent u₀ = c)
    (hmin : ∀ u, x ∈ S u → c ≤ traceLen independent u) :
    c * Real.log (1 / (2 ^ Δ * z)) - c * Real.log (1 + (Fintype.card α : ℝ) / c) -
        Fintype.card α * Real.log (1 + (c : ℝ) / Fintype.card α) ≤
      preparationAction independent z S x ∧
      preparationAction independent z S x ≤ c * Real.log (1 / z) := by
  have hMpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  have hpow : (0 : ℝ) < 2 ^ Δ := by positivity
  have hsum : (0 : ℝ) < (Fintype.card α : ℝ) + c := by linarith
  have hz : 2 ^ Δ * z < 1 := by
    have : (c : ℝ) / ((Fintype.card α : ℝ) + c) < 1 := (div_lt_one hsum).mpr (by linarith)
    linarith
  have hlow : z ^ c ≤ causalAccessibility independent z S x := by
    have := pow_le_causalAccessibility independent hsymm Δ hdegree hz0.le hz hu₀
    rwa [hlen₀] at this
  have hFpos : 0 < causalAccessibility independent z S x :=
    lt_of_lt_of_le (by positivity) hlow
  have hupper := causalAccessibility_le_optimal independent hsymm Δ hdegree hz0.le hc hzc hmin
  have hlogdiv1 : Real.log (1 / (2 ^ Δ * z)) = -Real.log (2 ^ Δ * z) := by
    rw [one_div, Real.log_inv]
  have hlogdiv2 : Real.log (1 / z) = -Real.log z := by rw [one_div, Real.log_inv]
  have hbound : Real.log (causalAccessibility independent z S x) ≤
      c * Real.log (2 ^ Δ * z) + c * Real.log (1 + (Fintype.card α : ℝ) / c) +
        Fintype.card α * Real.log (1 + (c : ℝ) / Fintype.card α) := by
    refine le_trans (Real.log_le_log hFpos hupper) (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
  have hlogz : (c : ℝ) * Real.log z ≤ Real.log (causalAccessibility independent z S x) := by
    have := Real.log_le_log (by positivity : (0:ℝ) < z ^ c) hlow
    rwa [Real.log_pow] at this
  refine ⟨?_, ?_⟩
  · rw [preparationAction, hlogdiv1]
    linarith
  · rw [preparationAction, hlogdiv2]
    linarith

/-- **Causal heap-capacity law.**  With a target-uniform measure bound the causal accessibility
programme reproduces the completed-phase capacity exponent. -/
theorem measure_heapAccessible_le_capacity [MeasurableSpace X] (ν : Measure X)
    (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) (hz : 2 ^ Δ * z < 1)
    {S : Trace independent → Set X} (hS : ∀ u, MeasurableSet (S u)) (s : ℕ)
    {B : ℝ≥0∞} (hB : ∀ u, ν (S u) ≤ B) :
    ν (heapAccessible (traceLen independent) S s) ≤
      ENNReal.ofReal ((z ^ s)⁻¹) *
        (B * ENNReal.ofReal (1 / (1 - 2 ^ Δ * z) ^ Fintype.card α)) := by
  refine measure_heapAccessible_le_partition ν hz0 hz1 _ hS s hB ?_
  have hEq : (∑' T : Trace independent, ENNReal.ofReal (z ^ traceLen independent T)) =
      ENNReal.ofReal (tracePartition independent z) :=
    tracePartitionENN_eq_ofReal independent hsymm Δ hdegree hz0.le hz
  rw [hEq]
  exact ENNReal.ofReal_le_ofReal (tracePartition_le independent hsymm Δ hdegree hz0.le hz)

/-- **Optimized causal heap-capacity law.**  At the optimal weight the capacity bound is the
dependence-normalized profile exponent. -/
theorem measure_heapAccessible_le_capacity_optimal [MeasurableSpace X] (ν : Measure X)
    (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {S : Trace independent → Set X} (hS : ∀ u, MeasurableSet (S u)) {s : ℕ} (hs : 1 ≤ s)
    {B : ℝ≥0∞} (hB : ∀ u, ν (S u) ≤ B) :
    ν (heapAccessible (traceLen independent) S s) ≤
      B * ENNReal.ofReal (2 ^ (Δ * s) *
        (1 + (Fintype.card α : ℝ) / s) ^ s *
        (1 + (s : ℝ) / Fintype.card α) ^ Fintype.card α) := by
  have hlen : (fun p : CircuitTrace independent =>
      traceLen independent (traceGradeEquiv independent p)) = traceLength independent := by
    funext p
    exact traceLen_traceGradeEquiv independent p
  have hcongr := heapAccessible_congr_equiv (X := X) (traceGradeEquiv independent)
    (traceLen independent) S s
  rw [← hcongr, hlen]
  exact measure_traceHeapAccessible_le_optimal ν independent hsymm Δ hdegree
    (S := fun p => S (traceGradeEquiv independent p))
    (fun p => hS _) hs (fun p => hB _)

/-- The positive heap Green reporter of a trace dictionary. -/
noncomputable def traceGreenReporter (independent : α → α → Prop) (z : ℝ)
    (S : Trace independent → Set X) (x : X) : ℝ :=
  ∑' u : Trace independent,
    Set.indicator {u | x ∈ S u} (fun u => z ^ traceLen independent u) u

theorem traceGreenReporter_nonneg (independent : α → α → Prop) {z : ℝ} (hz0 : 0 ≤ z)
    (S : Trace independent → Set X) (x : X) :
    0 ≤ traceGreenReporter independent z S x := by
  refine tsum_nonneg fun u => ?_
  by_cases hu : u ∈ {u | x ∈ S u}
  · rw [Set.indicator_of_mem hu]; positivity
  · rw [Set.indicator_of_notMem hu]

/-- **Green relation.**  The concurrent causal accessibility never exceeds the expected number of
successful causal prefixes. -/
theorem causalAccessibility_le_traceGreenReporter (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1)
    (S : Trace independent → Set X) (x : X) :
    causalAccessibility independent z S x ≤ traceGreenReporter independent z S x := by
  classical
  have hsumz := summable_tracePow independent hsymm Δ hdegree hz0 hz
  have hzpos := tracePartition_pos independent hsymm Δ hdegree hz0 hz
  set w : Trace independent → ℝ := fun T => z ^ traceLen independent T with hwdef
  set h : Trace independent → Trace independent → ℝ≥0∞ := fun u T =>
    if x ∈ S u ∧ TracePrefix independent u T then ENNReal.ofReal (w T) else 0 with hhdef
  have hEventLe : ∀ T : Trace independent,
      Set.indicator (causalSuccessEvent independent S x)
        (fun T => ENNReal.ofReal (w T)) T ≤ ∑' u : Trace independent, h u T := by
    intro T
    by_cases hT : T ∈ causalSuccessEvent independent S x
    · rw [Set.indicator_of_mem hT]
      obtain ⟨u, hprefix, hu⟩ := hT
      refine le_trans (le_of_eq ?_) (ENNReal.le_tsum u)
      simp only [hhdef]
      exact (if_pos (show x ∈ S u ∧ TracePrefix independent u T from ⟨hu, hprefix⟩)).symm
    · rw [Set.indicator_of_notMem hT]
      exact bot_le
  have hInner : ∀ u : Trace independent,
      (∑' T : Trace independent, h u T) =
        (if x ∈ S u then ENNReal.ofReal (w u) else 0) * tracePartitionENN independent z := by
    intro u
    by_cases hu : x ∈ S u
    · have hterm : ∀ T : Trace independent, h u T =
          Set.indicator (traceCylinder independent u)
            (fun T => ENNReal.ofReal (w T)) T := by
        intro T
        by_cases hT : TracePrefix independent u T
        · simp only [hhdef]
          rw [if_pos (show x ∈ S u ∧ TracePrefix independent u T from ⟨hu, hT⟩),
            Set.indicator_of_mem (show T ∈ traceCylinder independent u from hT)]
        · simp only [hhdef]
          rw [if_neg (show ¬ (x ∈ S u ∧ TracePrefix independent u T) from
              fun hc : x ∈ S u ∧ TracePrefix independent u T => hT hc.2),
            Set.indicator_of_notMem (show T ∉ traceCylinder independent u from hT)]
      simp_rw [hterm]
      rw [← tsum_subtype (traceCylinder independent u)
        (fun T : Trace independent => ENNReal.ofReal (w T)),
        tsum_traceCylinderENN independent hsymm hz0 u, if_pos hu]
    · have hterm : ∀ T : Trace independent, h u T = 0 := by
        intro T
        simp only [hhdef]
        rw [if_neg (show ¬ (x ∈ S u ∧ TracePrefix independent u T) from
          fun hc : x ∈ S u ∧ TracePrefix independent u T => hu hc.1)]
      simp_rw [hterm]
      rw [if_neg hu, tsum_zero, zero_mul]
  have hEventENN : (∑' T : Trace independent, Set.indicator
      (causalSuccessEvent independent S x) (fun T => ENNReal.ofReal (w T)) T) ≤
      (∑' u : Trace independent, if x ∈ S u then ENNReal.ofReal (w u) else 0) *
        tracePartitionENN independent z := by
    calc
      (∑' T : Trace independent, Set.indicator (causalSuccessEvent independent S x)
          (fun T => ENNReal.ofReal (w T)) T)
          ≤ ∑' T : Trace independent, ∑' u : Trace independent, h u T :=
        ENNReal.tsum_le_tsum hEventLe
      _ = ∑' u : Trace independent, ∑' T : Trace independent, h u T := ENNReal.tsum_comm
      _ = ∑' u : Trace independent,
            (if x ∈ S u then ENNReal.ofReal (w u) else 0) * tracePartitionENN independent z := by
        exact tsum_congr hInner
      _ = (∑' u : Trace independent, if x ∈ S u then ENNReal.ofReal (w u) else 0) *
            tracePartitionENN independent z := ENNReal.tsum_mul_right
  have hGreenENN : (∑' u : Trace independent, if x ∈ S u then ENNReal.ofReal (w u) else 0) =
      ENNReal.ofReal (traceGreenReporter independent z S x) := by
    rw [traceGreenReporter, ENNReal.ofReal_tsum_of_nonneg
      (fun u => by by_cases h : x ∈ S u <;> simp [Set.indicator, h, hwdef, pow_nonneg hz0])
      (hsumz.indicator {u | x ∈ S u})]
    refine tsum_congr fun u => ?_
    by_cases hu : u ∈ {u | x ∈ S u}
    · rw [if_pos (show x ∈ S u from hu), Set.indicator_of_mem hu]
    · rw [if_neg (show ¬ (x ∈ S u) from hu), Set.indicator_of_notMem hu, ENNReal.ofReal_zero]
  have hEventReal : (∑' T : Trace independent, Set.indicator
      (causalSuccessEvent independent S x) (fun T => ENNReal.ofReal (w T)) T) =
      ENNReal.ofReal (∑' T : causalSuccessEvent independent S x, w (T : Trace independent)) := by
    rw [tsum_subtype (causalSuccessEvent independent S x) w,
      ENNReal.ofReal_tsum_of_nonneg
      (fun T => by
        by_cases h : T ∈ causalSuccessEvent independent S x <;>
          simp [Set.indicator, h, hwdef, pow_nonneg hz0])
      (hsumz.indicator (causalSuccessEvent independent S x))]
    refine tsum_congr fun T => ?_
    by_cases hT : T ∈ causalSuccessEvent independent S x
    · rw [Set.indicator_of_mem hT, Set.indicator_of_mem hT]
    · rw [Set.indicator_of_notMem hT, Set.indicator_of_notMem hT, ENNReal.ofReal_zero]
  rw [hEventReal, hGreenENN, tracePartitionENN_eq_ofReal independent hsymm Δ hdegree hz0 hz,
    ← ENNReal.ofReal_mul (traceGreenReporter_nonneg independent hz0 S x)] at hEventENN
  have hreal : (∑' T : causalSuccessEvent independent S x, w (T : Trace independent)) ≤
      traceGreenReporter independent z S x * tracePartition independent z := by
    have hnn : 0 ≤ traceGreenReporter independent z S x * tracePartition independent z := by
      exact mul_nonneg (traceGreenReporter_nonneg independent hz0 S x) hzpos.le
    exact (ENNReal.ofReal_le_ofReal_iff hnn).mp hEventENN
  rw [causalAccessibility, traceMass, div_le_iff₀ hzpos]
  exact hreal

end CausalAccessibility

end GaloisForLFunctions.RHTower
