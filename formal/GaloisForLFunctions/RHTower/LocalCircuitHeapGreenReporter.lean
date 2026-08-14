import Mathlib
import GaloisForLFunctions.RHTower.LocalCircuitTraceCapacity

/-!
# The heap Green reporter of a local circuit dictionary

A countable dictionary of target sets, weighted by a geometric factor in the length of its index,
defines one positive reporter on the state space.  Any state reachable within budget `s` already
contributes at least the `s`-th power of the weight, so the measure of the accessible set is
controlled by the reporter integral.  Integrating the reporter against a target-uniform bound
replaces it by the partition sum of the index family.

For a local circuit alphabet the index family is the set of partially commutative traces.  The
pair-projection capacity bound turns its partition sum into a negative-binomial series whose exact
value is `(1 - 2^Δ z)^{-M}`.  Optimizing the geometric weight gives the dependency-normalized
accessibility law: the accessible measure is at most `B · 2^{Δ s} (1 + M/s)^s (1 + s/M)^M`, in
which the alphabet size enters only through the subexponential profile factors.
-/

open MeasureTheory ENNReal

namespace GaloisForLFunctions.RHTower

section HeapReporter

variable {X : Type*} [MeasurableSpace X] {T : Type*} [Countable T]

/-- Positive heap Green reporter of a countable weighted dictionary of target sets. -/
noncomputable def heapGreenReporter (z : ℝ) (len : T → ℕ) (S : T → Set X) (x : X) : ℝ≥0∞ :=
  ∑' τ : T, ENNReal.ofReal (z ^ len τ) * (S τ).indicator 1 x

/-- States reachable from the dictionary within budget `s`. -/
def heapAccessible (len : T → ℕ) (S : T → Set X) (s : ℕ) : Set X :=
  ⋃ τ ∈ {τ : T | len τ ≤ s}, S τ

theorem measurableSet_heapAccessible {len : T → ℕ} {S : T → Set X}
    (hS : ∀ τ, MeasurableSet (S τ)) (s : ℕ) : MeasurableSet (heapAccessible len S s) :=
  MeasurableSet.biUnion (Set.to_countable _) fun τ _ => hS τ

theorem measurable_heapGreenReporter {z : ℝ} {len : T → ℕ} {S : T → Set X}
    (hS : ∀ τ, MeasurableSet (S τ)) : Measurable (heapGreenReporter z len S) :=
  Measurable.tsum fun τ => (measurable_one.indicator (hS τ)).const_mul _

omit [MeasurableSpace X] [Countable T] in
/-- Budget-`s` accessibility is dominated by the heap Green reporter. -/
theorem indicator_heapAccessible_le_reporter {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1)
    (len : T → ℕ) (S : T → Set X) (s : ℕ) (x : X) :
    (heapAccessible len S s).indicator 1 x ≤
      ENNReal.ofReal ((z ^ s)⁻¹) * heapGreenReporter z len S x := by
  by_cases hx : x ∈ heapAccessible len S s
  · rw [Set.indicator_of_mem hx]
    obtain ⟨τ, hτ, hxτ⟩ : ∃ τ : T, len τ ≤ s ∧ x ∈ S τ := by
      simpa only [heapAccessible, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] using hx
    have hterm : ENNReal.ofReal (z ^ s) ≤ heapGreenReporter z len S x := by
      refine le_trans ?_ (ENNReal.le_tsum τ)
      rw [Set.indicator_of_mem hxτ, Pi.one_apply, mul_one]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hz0.le hz1 hτ)
    calc
      (1 : ℝ≥0∞) = ENNReal.ofReal ((z ^ s)⁻¹) * ENNReal.ofReal (z ^ s) := by
        rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity),
          ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal ((z ^ s)⁻¹) * heapGreenReporter z len S x :=
        mul_le_mul_right hterm _
  · rw [Set.indicator_of_notMem hx]
    exact bot_le

/-- **Heap reporter accessibility bound.**  The measure of the states reachable within budget `s`
is at most the reciprocal geometric weight times the reporter integral. -/
theorem measure_heapAccessible_le_lintegral (ν : Measure X) {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1)
    (len : T → ℕ) {S : T → Set X} (hS : ∀ τ, MeasurableSet (S τ)) (s : ℕ) :
    ν (heapAccessible len S s) ≤
      ENNReal.ofReal ((z ^ s)⁻¹) * ∫⁻ x, heapGreenReporter z len S x ∂ν := by
  calc
    ν (heapAccessible len S s)
        = ∫⁻ x, (heapAccessible len S s).indicator 1 x ∂ν :=
      (lintegral_indicator_one (measurableSet_heapAccessible hS s)).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal ((z ^ s)⁻¹) * heapGreenReporter z len S x ∂ν :=
      lintegral_mono fun x => indicator_heapAccessible_le_reporter hz0 hz1 len S s x
    _ = ENNReal.ofReal ((z ^ s)⁻¹) * ∫⁻ x, heapGreenReporter z len S x ∂ν :=
      lintegral_const_mul _ (measurable_heapGreenReporter hS)

/-- The reporter integral is the weighted sum of the target measures. -/
theorem lintegral_heapGreenReporter (ν : Measure X) (z : ℝ) (len : T → ℕ) {S : T → Set X}
    (hS : ∀ τ, MeasurableSet (S τ)) :
    ∫⁻ x, heapGreenReporter z len S x ∂ν =
      ∑' τ : T, ENNReal.ofReal (z ^ len τ) * ν (S τ) := by
  simp only [heapGreenReporter]
  rw [lintegral_tsum fun τ =>
      ((measurable_one.indicator (hS τ)).const_mul
        (ENNReal.ofReal (z ^ len τ))).aemeasurable]
  refine tsum_congr fun τ => ?_
  rw [lintegral_const_mul _ (measurable_one.indicator (hS τ)), lintegral_indicator_one (hS τ)]

/-- Target-uniform measure bounds replace the reporter integral by the index partition sum. -/
theorem lintegral_heapGreenReporter_le (ν : Measure X) (z : ℝ) (len : T → ℕ) {S : T → Set X}
    (hS : ∀ τ, MeasurableSet (S τ)) {B : ℝ≥0∞} (hB : ∀ τ, ν (S τ) ≤ B) :
    ∫⁻ x, heapGreenReporter z len S x ∂ν ≤ B * ∑' τ : T, ENNReal.ofReal (z ^ len τ) := by
  rw [lintegral_heapGreenReporter ν z len hS]
  calc
    ∑' τ : T, ENNReal.ofReal (z ^ len τ) * ν (S τ)
        ≤ ∑' τ : T, ENNReal.ofReal (z ^ len τ) * B :=
      ENNReal.tsum_le_tsum fun τ => mul_le_mul_right (hB τ) _
    _ = (∑' τ : T, ENNReal.ofReal (z ^ len τ)) * B := ENNReal.tsum_mul_right
    _ = B * ∑' τ : T, ENNReal.ofReal (z ^ len τ) := mul_comm _ _

/-- **Dependency-normalized accessibility law.**  The reporter bound, a target-uniform measure
bound and a partition-sum bound combine into one accessibility estimate. -/
theorem measure_heapAccessible_le_partition (ν : Measure X) {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1)
    (len : T → ℕ) {S : T → Set X} (hS : ∀ τ, MeasurableSet (S τ)) (s : ℕ)
    {B Z : ℝ≥0∞} (hB : ∀ τ, ν (S τ) ≤ B)
    (hZ : ∑' τ : T, ENNReal.ofReal (z ^ len τ) ≤ Z) :
    ν (heapAccessible len S s) ≤ ENNReal.ofReal ((z ^ s)⁻¹) * (B * Z) :=
  le_trans (measure_heapAccessible_le_lintegral ν hz0 hz1 len hS s)
    (mul_le_mul_right (le_trans (lintegral_heapGreenReporter_le ν z len hS hB)
      (mul_le_mul_right hZ B)) _)

/-- Finite heap incidence of a weighted dictionary through budget `s`. -/
noncomputable def heapIncidence (ν : Measure X) (len : T → ℕ) (S : T → Set X) (s : ℕ) : ℝ≥0∞ :=
  ∑' τ : T, Set.indicator {τ : T | len τ ≤ s} (fun τ => ν (S τ)) τ

/-- **Finite heap-incidence bound.**  Budget-`s` accessibility is at most the finite heap
incidence, with no probability or spectral premise. -/
theorem measure_heapAccessible_le_heapIncidence (ν : Measure X) (len : T → ℕ) (S : T → Set X)
    (s : ℕ) : ν (heapAccessible len S s) ≤ heapIncidence ν len S s := by
  rw [heapAccessible, heapIncidence, ← tsum_subtype]
  exact measure_biUnion_le ν (Set.to_countable _) S

/-- Every dependence edge at `a` is determined by its other endpoint, so the incident-edge count is
one less than the size of any finite set of letters containing `a` and every letter dependent on
`a`. -/
theorem incidentEdgeCount_succ_le_of_dependentSubset {α : Type*} [Fintype α] [LinearOrder α]
    (independent : α → α → Prop) (hsymm : ∀ x y, independent x y → independent y x) (a : α)
    (t : Finset α) (ht : ∀ b, b ≠ a → ¬ independent a b → b ∈ t) (hat : a ∈ t) :
    incidentEdgeCount independent a + 1 ≤ t.card := by
  classical
  set E : Finset (DependenceEdge independent) :=
    (Finset.univ : Finset (DependenceEdge independent)).filter fun e => a = e.1.1 ∨ a = e.1.2
    with hE
  have hother : ∀ e ∈ E, (if a = e.1.1 then e.1.2 else e.1.1) ∈ t.erase a := by
    intro e he
    have hmem : a = e.1.1 ∨ a = e.1.2 := (Finset.mem_filter.mp he).2
    have hlt : e.1.1 < e.1.2 := e.2.1
    have hdep : ¬ independent e.1.1 e.1.2 := e.2.2
    rcases hmem with h1 | h2
    · rw [if_pos h1]
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · exact fun hcon => absurd (hcon ▸ h1 ▸ hlt) (lt_irrefl _)
      · refine ht _ (fun hcon => absurd (hcon ▸ h1 ▸ hlt) (lt_irrefl _)) ?_
        rw [h1]; exact hdep
    · have hne : a ≠ e.1.1 := fun hcon => absurd (hcon ▸ h2 ▸ hlt) (lt_irrefl _)
      rw [if_neg hne]
      refine Finset.mem_erase.mpr ⟨fun hcon => hne hcon.symm, ?_⟩
      refine ht _ (fun hcon => hne hcon.symm) ?_
      rw [h2]
      exact fun hcon => hdep (hsymm _ _ hcon)
  have hinj : Set.InjOn (fun e : DependenceEdge independent =>
      if a = e.1.1 then e.1.2 else e.1.1) (E : Set (DependenceEdge independent)) := by
    intro e he e' he' hEq
    dsimp only at hEq
    have hmem : a = e.1.1 ∨ a = e.1.2 := (Finset.mem_filter.mp he).2
    have hmem' : a = e'.1.1 ∨ a = e'.1.2 := (Finset.mem_filter.mp he').2
    have hlt : e.1.1 < e.1.2 := e.2.1
    have hlt' : e'.1.1 < e'.1.2 := e'.2.1
    have hpair : e.1 = e'.1 := by
      rcases hmem with h1 | h2 <;> rcases hmem' with h1' | h2'
      · rw [if_pos h1, if_pos h1'] at hEq
        exact Prod.ext (h1 ▸ h1'.symm ▸ rfl) hEq
      · have hne' : a ≠ e'.1.1 := fun hcon => absurd (hcon ▸ h2' ▸ hlt') (lt_irrefl _)
        rw [if_pos h1, if_neg hne'] at hEq
        have hgt : a < e.1.2 := h1 ▸ hlt
        have hlt2 : e'.1.1 < a := h2' ▸ hlt'
        exact absurd (hEq ▸ hgt) (not_lt.mpr hlt2.le)
      · have hne : a ≠ e.1.1 := fun hcon => absurd (hcon ▸ h2 ▸ hlt) (lt_irrefl _)
        rw [if_neg hne, if_pos h1'] at hEq
        have hgt : a < e'.1.2 := h1' ▸ hlt'
        have hlt2 : e.1.1 < a := h2 ▸ hlt
        exact absurd (hEq ▸ hlt2) (not_lt.mpr hgt.le)
      · have hne : a ≠ e.1.1 := fun hcon => absurd (hcon ▸ h2 ▸ hlt) (lt_irrefl _)
        have hne' : a ≠ e'.1.1 := fun hcon => absurd (hcon ▸ h2' ▸ hlt') (lt_irrefl _)
        rw [if_neg hne, if_neg hne'] at hEq
        exact Prod.ext hEq (h2 ▸ h2'.symm ▸ rfl)
    exact Subtype.ext hpair
  have hcard : E.card ≤ (t.erase a).card :=
    Finset.card_le_card_of_injOn _ hother hinj
  have hterase : (t.erase a).card = t.card - 1 := Finset.card_erase_of_mem hat
  have hpos : 1 ≤ t.card := Finset.card_pos.mpr ⟨a, hat⟩
  have : incidentEdgeCount independent a = E.card := by
    rw [incidentEdgeCount, hE]
  omega

/-- A finite family of `Fin`-indexed letters is bounded by any finite set of numerical labels
covering it. -/
theorem card_filter_fin_le {m : ℕ} (P : Fin m → Prop) [DecidablePred P] (t : Finset ℕ)
    (h : ∀ x : Fin m, P x → (x : ℕ) ∈ t) :
    ((Finset.univ : Finset (Fin m)).filter P).card ≤ t.card :=
  Finset.card_le_card_of_injOn Fin.val (fun x hx => h x (Finset.mem_filter.mp hx).2)
    (fun _ _ _ _ hxy => Fin.val_injective hxy)

end HeapReporter

section TracePartition

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]

/-- The countable family of all circuit traces of a local alphabet. -/
abbrev CircuitTrace (independent : α → α → Prop) : Type _ :=
  Σ ℓ : ℕ, FixedTraceClass independent ℓ

instance (independent : α → α → Prop) (ℓ : ℕ) : Finite (FixedTraceClass independent ℓ) :=
  Quotient.finite _

instance (independent : α → α → Prop) : Countable (CircuitTrace independent) :=
  inferInstanceAs (Countable (Σ ℓ : ℕ, FixedTraceClass independent ℓ))

/-- Length of a circuit trace. -/
def traceLength (independent : α → α → Prop) : CircuitTrace independent → ℕ := Sigma.fst

omit [DecidableEq α] [LinearOrder α] [Nonempty α] in
/-- The trace partition sum is the length-graded generating sum of the trace counts. -/
theorem tsum_ofReal_pow_traceLength (independent : α → α → Prop) (z : ℝ) :
    ∑' τ : CircuitTrace independent, ENNReal.ofReal (z ^ traceLength independent τ) =
      ∑' ℓ : ℕ, (Nat.card (FixedTraceClass independent ℓ) : ℝ≥0∞) * ENNReal.ofReal (z ^ ℓ) := by
  rw [ENNReal.tsum_sigma' (β := fun ℓ => FixedTraceClass independent ℓ)]
  refine tsum_congr fun ℓ => ?_
  have hconst : ∀ b : FixedTraceClass independent ℓ,
      ENNReal.ofReal (z ^ traceLength independent (⟨ℓ, b⟩ : CircuitTrace independent)) =
        ENNReal.ofReal (z ^ ℓ) := fun _ => rfl
  rw [tsum_congr hconst, ENNReal.tsum_const, ENat.card_eq_coe_natCard]
  rfl

omit [DecidableEq α] in
/-- The trace count is dominated termwise by the negative-binomial majorant. -/
theorem traceCount_pow_le (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (ℓ : ℕ) :
    (Nat.card (FixedTraceClass independent ℓ) : ℝ) * z ^ ℓ ≤
      ((ℓ + (Fintype.card α - 1)).choose (Fintype.card α - 1) : ℝ) * (2 ^ Δ * z) ^ ℓ := by
  have hM : 1 ≤ Fintype.card α := Fintype.card_pos
  have hidx : Fintype.card α + ℓ - 1 = ℓ + (Fintype.card α - 1) := by omega
  have hsub : ℓ + (Fintype.card α - 1) - (Fintype.card α - 1) = ℓ := by omega
  have hchoose : (ℓ + (Fintype.card α - 1)).choose (Fintype.card α - 1) =
      (Fintype.card α + ℓ - 1).choose ℓ := by
    rw [hidx, ← Nat.choose_symm (Nat.le_add_left (Fintype.card α - 1) ℓ), hsub]
  have hcount := natCard_fixedTraceClass_le_maxDegree independent hsymm ℓ Δ hdegree
  calc
    (Nat.card (FixedTraceClass independent ℓ) : ℝ) * z ^ ℓ
        ≤ (((Fintype.card α + ℓ - 1).choose ℓ * 2 ^ (Δ * ℓ) : ℕ) : ℝ) * z ^ ℓ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (by positivity)
    _ = ((ℓ + (Fintype.card α - 1)).choose (Fintype.card α - 1) : ℝ) * (2 ^ Δ * z) ^ ℓ := by
      rw [hchoose]
      push_cast
      rw [mul_pow, ← pow_mul, mul_assoc]

omit [DecidableEq α] in
theorem summable_traceCount_pow (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) :
    Summable fun ℓ : ℕ => (Nat.card (FixedTraceClass independent ℓ) : ℝ) * z ^ ℓ := by
  have hnorm : ‖(2 : ℝ) ^ Δ * z‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hz
  refine Summable.of_nonneg_of_le (fun ℓ => by positivity)
    (traceCount_pow_le independent hsymm Δ hdegree hz0)
    (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (Fintype.card α - 1) hnorm).summable

omit [DecidableEq α] in
/-- **Trace partition bound.**  The dependency-normalized trace generating sum is bounded by the
negative-binomial value `(1 - 2^Δ z)^{-M}`. -/
theorem tracePartitionSum_le (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) :
    ∑' ℓ : ℕ, (Nat.card (FixedTraceClass independent ℓ) : ℝ) * z ^ ℓ ≤
      1 / (1 - 2 ^ Δ * z) ^ Fintype.card α := by
  have hM : 1 ≤ Fintype.card α := Fintype.card_pos
  have hnorm : ‖(2 : ℝ) ^ Δ * z‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hz
  have hmaj := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (Fintype.card α - 1) hnorm
  have hexp : Fintype.card α - 1 + 1 = Fintype.card α := by omega
  calc
    ∑' ℓ : ℕ, (Nat.card (FixedTraceClass independent ℓ) : ℝ) * z ^ ℓ
        ≤ ∑' ℓ : ℕ,
          ((ℓ + (Fintype.card α - 1)).choose (Fintype.card α - 1) : ℝ) * (2 ^ Δ * z) ^ ℓ := by
      exact Summable.tsum_mono (summable_traceCount_pow independent hsymm Δ hdegree hz0 hz)
        hmaj.summable (traceCount_pow_le independent hsymm Δ hdegree hz0)
    _ = 1 / (1 - 2 ^ Δ * z) ^ Fintype.card α := by
      rw [hmaj.tsum_eq, hexp]

omit [DecidableEq α] in
/-- The trace partition sum in extended nonnegative reals. -/
theorem tsum_ofReal_pow_traceLength_le (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) :
    ∑' τ : CircuitTrace independent, ENNReal.ofReal (z ^ traceLength independent τ) ≤
      ENNReal.ofReal (1 / (1 - 2 ^ Δ * z) ^ Fintype.card α) := by
  rw [tsum_ofReal_pow_traceLength]
  have hterm : ∀ ℓ : ℕ, (Nat.card (FixedTraceClass independent ℓ) : ℝ≥0∞) *
      ENNReal.ofReal (z ^ ℓ) =
      ENNReal.ofReal ((Nat.card (FixedTraceClass independent ℓ) : ℝ) * z ^ ℓ) := by
    intro ℓ
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  rw [tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg (fun ℓ => by positivity)
    (summable_traceCount_pow independent hsymm Δ hdegree hz0 hz)]
  exact ENNReal.ofReal_le_ofReal (tracePartitionSum_le independent hsymm Δ hdegree hz0 hz)

omit [DecidableEq α] [LinearOrder α] [Nonempty α] in
/-- The finite heap incidence of a trace dictionary is paid at the cumulative trace count. -/
theorem heapIncidence_trace_le {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (independent : α → α → Prop) (S : CircuitTrace independent → Set X) (s : ℕ)
    {B : ℝ≥0∞} (hB : ∀ τ, ν (S τ) ≤ B) :
    heapIncidence ν (traceLength independent) S s ≤
      (cumulativeTraceCount independent s : ℝ≥0∞) * B := by
  classical
  have hsplit : ∀ ℓ : ℕ,
      (∑' b : FixedTraceClass independent ℓ,
        Set.indicator {τ : CircuitTrace independent | traceLength independent τ ≤ s}
          (fun τ => ν (S τ)) ⟨ℓ, b⟩) ≤
        (if ℓ ≤ s then (Nat.card (FixedTraceClass independent ℓ) : ℝ≥0∞) * B else 0) := by
    intro ℓ
    by_cases hℓ : ℓ ≤ s
    · rw [if_pos hℓ]
      calc (∑' b : FixedTraceClass independent ℓ,
              Set.indicator {τ : CircuitTrace independent | traceLength independent τ ≤ s}
                (fun τ => ν (S τ)) ⟨ℓ, b⟩)
            ≤ ∑' _b : FixedTraceClass independent ℓ, B := by
            refine ENNReal.tsum_le_tsum fun b => ?_
            rw [Set.indicator_of_mem (show (⟨ℓ, b⟩ : CircuitTrace independent) ∈
              {τ : CircuitTrace independent | traceLength independent τ ≤ s} from hℓ)]
            exact hB _
        _ = (Nat.card (FixedTraceClass independent ℓ) : ℝ≥0∞) * B := by
            rw [ENNReal.tsum_const, ENat.card_eq_coe_natCard]
            rfl
    · rw [if_neg hℓ]
      have hzero : ∀ b : FixedTraceClass independent ℓ,
          Set.indicator {τ : CircuitTrace independent | traceLength independent τ ≤ s}
            (fun τ => ν (S τ)) (⟨ℓ, b⟩ : CircuitTrace independent) = 0 :=
        fun b => Set.indicator_of_notMem
          (show (⟨ℓ, b⟩ : CircuitTrace independent) ∉
            {τ : CircuitTrace independent | traceLength independent τ ≤ s} from
              fun hcon => hℓ hcon) _
      simp [hzero]
  calc heapIncidence ν (traceLength independent) S s
      = ∑' ℓ : ℕ, ∑' b : FixedTraceClass independent ℓ,
          Set.indicator {τ : CircuitTrace independent | traceLength independent τ ≤ s}
            (fun τ => ν (S τ)) ⟨ℓ, b⟩ := by
        rw [heapIncidence, ENNReal.tsum_sigma' (β := fun ℓ => FixedTraceClass independent ℓ)]
    _ ≤ ∑' ℓ : ℕ, (if ℓ ≤ s then (Nat.card (FixedTraceClass independent ℓ) : ℝ≥0∞) * B else 0) :=
        ENNReal.tsum_le_tsum hsplit
    _ = ∑ ℓ ∈ Finset.range (s + 1),
          (Nat.card (FixedTraceClass independent ℓ) : ℝ≥0∞) * B := by
        rw [tsum_eq_sum (s := Finset.range (s + 1)) (fun ℓ hℓ => ?_)]
        · refine Finset.sum_congr rfl fun ℓ hℓ => ?_
          rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ))]
        · rw [if_neg]
          exact fun hcon => hℓ (Finset.mem_range.mpr (Nat.lt_succ_of_le hcon))
    _ = (cumulativeTraceCount independent s : ℝ≥0∞) * B := by
        rw [cumulativeTraceCount, ← Finset.sum_mul]
        push_cast
        rfl

omit [DecidableEq α] [LinearOrder α] [Nonempty α] in
/-- **Local-circuit plateau capacity bound.**  With a target-uniform measure bound `B`, the measure
of the states reachable by circuits of depth at most `s` is at most the cumulative heap capacity
times `B`. -/
theorem measure_traceHeapAccessible_le_cumulativeTraceCount {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (independent : α → α → Prop) (S : CircuitTrace independent → Set X) (s : ℕ)
    {B : ℝ≥0∞} (hB : ∀ τ, ν (S τ) ≤ B) :
    ν (heapAccessible (traceLength independent) S s) ≤
      (cumulativeTraceCount independent s : ℝ≥0∞) * B :=
  le_trans (measure_heapAccessible_le_heapIncidence ν _ S s)
    (heapIncidence_trace_le ν independent S s hB)

end TracePartition

section CircuitAccessibility

variable {X : Type*} [MeasurableSpace X]
variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]

omit [DecidableEq α] in
/-- **Local-circuit heap accessibility law.**  With a target-uniform measure bound `B`, the measure
of the states reachable by circuits of depth at most `s` is controlled by the geometric weight and
the dependency-normalized trace partition value. -/
theorem measure_traceHeapAccessible_le (ν : Measure X) (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) (hz : 2 ^ Δ * z < 1)
    {S : CircuitTrace independent → Set X} (hS : ∀ τ, MeasurableSet (S τ)) (s : ℕ)
    {B : ℝ≥0∞} (hB : ∀ τ, ν (S τ) ≤ B) :
    ν (heapAccessible (traceLength independent) S s) ≤
      ENNReal.ofReal ((z ^ s)⁻¹) *
        (B * ENNReal.ofReal (1 / (1 - 2 ^ Δ * z) ^ Fintype.card α)) :=
  measure_heapAccessible_le_partition ν hz0 hz1 _ hS s hB
    (tsum_ofReal_pow_traceLength_le independent hsymm Δ hdegree hz0.le hz)

omit [DecidableEq α] in
/-- **Optimized dependency-normalized accessibility law.**  At the optimal geometric weight
`z = s / (2^Δ (M + s))` the accessibility bound becomes
`B · 2^{Δ s} (1 + M/s)^s (1 + s/M)^M`. -/
theorem measure_traceHeapAccessible_le_optimal (ν : Measure X) (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {S : CircuitTrace independent → Set X} (hS : ∀ τ, MeasurableSet (S τ)) {s : ℕ} (hs : 1 ≤ s)
    {B : ℝ≥0∞} (hB : ∀ τ, ν (S τ) ≤ B) :
    ν (heapAccessible (traceLength independent) S s) ≤
      B * ENNReal.ofReal (2 ^ (Δ * s) *
        (1 + (Fintype.card α : ℝ) / s) ^ s * (1 + (s : ℝ) / Fintype.card α) ^ Fintype.card α) := by
  set M : ℕ := Fintype.card α with hMdef
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Fintype.card_pos
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hpow : (0 : ℝ) < 2 ^ Δ := by positivity
  set z : ℝ := (s : ℝ) / (2 ^ Δ * ((M : ℝ) + s)) with hzdef
  have hsum : (0 : ℝ) < (M : ℝ) + s := by linarith
  have hz0 : 0 < z := by rw [hzdef]; positivity
  have hkey : 2 ^ Δ * z = (s : ℝ) / ((M : ℝ) + s) := by
    rw [hzdef]
    field_simp
  have hz : 2 ^ Δ * z < 1 := by
    rw [hkey, div_lt_one hsum]
    linarith
  have hz1 : z ≤ 1 := by
    have h2 : (1 : ℝ) ≤ 2 ^ Δ := one_le_pow₀ (by norm_num)
    have : z ≤ 2 ^ Δ * z := le_mul_of_one_le_left hz0.le h2
    linarith [hz]
  have hone : 1 - 2 ^ Δ * z = (M : ℝ) / ((M : ℝ) + s) := by
    rw [hkey]
    field_simp
    ring
  have hinvz : z⁻¹ = 2 ^ Δ * (1 + (M : ℝ) / s) := by
    rw [hzdef]
    field_simp
    ring
  have hfactor1 : ((z ^ s)⁻¹) = 2 ^ (Δ * s) * (1 + (M : ℝ) / s) ^ s := by
    rw [← inv_pow, hinvz, mul_pow, pow_mul]
  have hfactor2 : 1 / (1 - 2 ^ Δ * z) ^ M = (1 + (s : ℝ) / M) ^ M := by
    rw [hone, div_pow, one_div_div, ← div_pow]
    congr 1
    field_simp
  refine le_trans (measure_traceHeapAccessible_le ν independent hsymm Δ hdegree hz0 hz1 hz hS s hB)
    (le_of_eq ?_)
  rw [hfactor1, hfactor2, ← mul_assoc, mul_comm (ENNReal.ofReal
    (2 ^ (Δ * s) * (1 + (M : ℝ) / s) ^ s)) B, mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

end CircuitAccessibility


section ChainAlphabet

/-! ### The one-dimensional local gate alphabet -/

variable (n K₁ K₂ : ℕ)

/-- Letters of a one-dimensional local gate alphabet on an open chain: `K₁` one-site types at each
of `n` sites and `K₂` nearest-neighbour types at each of the `n - 1` edges. -/
def ChainLetter : Type := (Fin n × Fin K₁) ⊕ (Fin (n - 1) × Fin K₂)

instance : Fintype (ChainLetter n K₁ K₂) :=
  inferInstanceAs (Fintype ((Fin n × Fin K₁) ⊕ (Fin (n - 1) × Fin K₂)))

instance : DecidableEq (ChainLetter n K₁ K₂) :=
  inferInstanceAs (DecidableEq ((Fin n × Fin K₁) ⊕ (Fin (n - 1) × Fin K₂)))

noncomputable instance : LinearOrder (ChainLetter n K₁ K₂) :=
  LinearOrder.lift' (fun a => (Fintype.equivFin (ChainLetter n K₁ K₂) a).val)
    fun _ _ h => (Fintype.equivFin (ChainLetter n K₁ K₂)).injective (Fin.val_injective h)

/-- The alphabet size of a one-dimensional local gate dictionary. -/
theorem card_chainLetter :
    Fintype.card (ChainLetter n K₁ K₂) = K₁ * n + K₂ * (n - 1) := by
  show Fintype.card ((Fin n × Fin K₁) ⊕ (Fin (n - 1) × Fin K₂)) = K₁ * n + K₂ * (n - 1)
  simp [mul_comm]

/-- Hardware support of a chain letter. -/
def chainSupport : ChainLetter n K₁ K₂ → Finset ℕ
  | Sum.inl p => {p.1.val}
  | Sum.inr p => {p.1.val, p.1.val + 1}

/-- Two chain letters commute exactly when their hardware supports are disjoint. -/
def chainIndependent (a b : ChainLetter n K₁ K₂) : Prop :=
  Disjoint (chainSupport n K₁ K₂ a) (chainSupport n K₁ K₂ b)

theorem chainIndependent_symm (a b : ChainLetter n K₁ K₂) :
    chainIndependent n K₁ K₂ a b → chainIndependent n K₁ K₂ b a :=
  fun h => h.symm

theorem not_chainIndependent_self (a : ChainLetter n K₁ K₂) :
    ¬ chainIndependent n K₁ K₂ a a := by
  cases a with
  | inl p => simp [chainIndependent, chainSupport]
  | inr p => simp [chainIndependent, chainSupport]

theorem card_le_two_filter_site (m c : ℕ) :
    ((Finset.univ : Finset (Fin m)).filter fun e => e.val = c ∨ e.val + 1 = c).card ≤ 2 := by
  refine le_trans (card_filter_fin_le _ ({c, c - 1} : Finset ℕ) ?_) ?_
  · rintro x (hx | hx)
    · simp [hx]
    · have : (x : ℕ) = c - 1 := by omega
      simp [this]
  · exact le_trans (Finset.card_insert_le _ _) (by simp)

theorem card_le_two_filter_edge (m c : ℕ) :
    ((Finset.univ : Finset (Fin m)).filter fun j => j.val = c ∨ j.val = c + 1).card ≤ 2 := by
  refine le_trans (card_filter_fin_le _ ({c, c + 1} : Finset ℕ) ?_) ?_
  · rintro x (hx | hx) <;> simp [hx]
  · exact le_trans (Finset.card_insert_le _ _) (by simp)

theorem card_le_three_filter_neighbourEdge (m c : ℕ) :
    ((Finset.univ : Finset (Fin m)).filter fun f =>
      f.val = c ∨ f.val = c + 1 ∨ f.val + 1 = c).card ≤ 3 := by
  refine le_trans (card_filter_fin_le _ ({c, c + 1, c - 1} : Finset ℕ) ?_) ?_
  · rintro x (hx | hx | hx)
    · simp [hx]
    · simp [hx]
    · have : (x : ℕ) = c - 1 := by omega
      simp [this]
  · refine le_trans (Finset.card_insert_le _ _) ?_
    have : ({c + 1, c - 1} : Finset ℕ).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    omega

/-- **Bounded-degree one-dimensional dictionary.**  The dependence degree of a one-dimensional
local gate alphabet is bounded independently of the chain length. -/
theorem chain_incidentEdgeCount_le (n K₁ K₂ : ℕ) (a : ChainLetter n K₁ K₂) :
    incidentEdgeCount (chainIndependent n K₁ K₂) a ≤
      max (K₁ - 1 + 2 * K₂) (2 * K₁ + 3 * K₂ - 1) := by
  classical
  cases a with
  | inl p =>
      obtain ⟨i, k⟩ := p
      have hK₁ : 0 < K₁ := k.pos
      set E : Finset (Fin (n - 1)) :=
        (Finset.univ : Finset (Fin (n - 1))).filter fun e => e.val = i.val ∨ e.val + 1 = i.val
        with hEdef
      set A : Finset (ChainLetter n K₁ K₂) :=
        (Finset.univ : Finset (Fin K₁)).image fun k' => (Sum.inl (i, k') : ChainLetter n K₁ K₂)
        with hAdef
      set Bset : Finset (ChainLetter n K₁ K₂) :=
        (E ×ˢ (Finset.univ : Finset (Fin K₂))).image fun q => (Sum.inr q : ChainLetter n K₁ K₂)
        with hBdef
      have hat : (Sum.inl (i, k) : ChainLetter n K₁ K₂) ∈ A ∪ Bset :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
      have ht : ∀ b : ChainLetter n K₁ K₂, b ≠ Sum.inl (i, k) →
          ¬ chainIndependent n K₁ K₂ (Sum.inl (i, k)) b → b ∈ A ∪ Bset := by
        rintro (⟨j, k'⟩ | ⟨c, k'⟩) _ hdep
        · have hij : i = j := by
            by_contra hne
            refine hdep ?_
            simp only [chainIndependent, chainSupport, Finset.disjoint_singleton]
            exact fun hcon => hne (Fin.val_injective hcon)
          subst hij
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k', Finset.mem_univ _, rfl⟩)
        · have hmem : c.val = i.val ∨ c.val + 1 = i.val := by
            by_contra hcon
            have h1 : c.val ≠ i.val := fun h => hcon (Or.inl h)
            have h2 : c.val + 1 ≠ i.val := fun h => hcon (Or.inr h)
            refine hdep ?_
            simp only [chainIndependent, chainSupport, Finset.disjoint_singleton_left,
              Finset.mem_insert, Finset.mem_singleton]
            exact fun hx => by rcases hx with hx | hx <;> omega
          refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(c, k'), ?_, rfl⟩)
          refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
          show c ∈ E
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
      have h1 : A.card ≤ K₁ := by
        refine le_trans Finset.card_image_le ?_
        simp
      have h2 : Bset.card ≤ 2 * K₂ := by
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_product]
        have hE2 : E.card ≤ 2 := card_le_two_filter_site (n - 1) i.val
        calc E.card * (Finset.univ : Finset (Fin K₂)).card
            ≤ 2 * (Finset.univ : Finset (Fin K₂)).card := Nat.mul_le_mul_right _ hE2
          _ = 2 * K₂ := by simp
      have hcard : (A ∪ Bset).card ≤ K₁ + 2 * K₂ :=
        le_trans (Finset.card_union_le _ _) (Nat.add_le_add h1 h2)
      have hmain := incidentEdgeCount_succ_le_of_dependentSubset
        (chainIndependent n K₁ K₂) (chainIndependent_symm n K₁ K₂) _ (A ∪ Bset) ht hat
      have hfinal : incidentEdgeCount (chainIndependent n K₁ K₂) (Sum.inl (i, k)) ≤
          K₁ - 1 + 2 * K₂ := by omega
      exact le_trans hfinal (le_max_left _ _)
  | inr p =>
      obtain ⟨e, k⟩ := p
      have hK₂ : 0 < K₂ := k.pos
      set J : Finset (Fin n) :=
        (Finset.univ : Finset (Fin n)).filter fun j => j.val = e.val ∨ j.val = e.val + 1 with hJdef
      set F : Finset (Fin (n - 1)) :=
        (Finset.univ : Finset (Fin (n - 1))).filter fun f =>
          f.val = e.val ∨ f.val = e.val + 1 ∨ f.val + 1 = e.val with hFdef
      set A : Finset (ChainLetter n K₁ K₂) :=
        (J ×ˢ (Finset.univ : Finset (Fin K₁))).image fun q => (Sum.inl q : ChainLetter n K₁ K₂)
        with hAdef
      set Bset : Finset (ChainLetter n K₁ K₂) :=
        (F ×ˢ (Finset.univ : Finset (Fin K₂))).image fun q => (Sum.inr q : ChainLetter n K₁ K₂)
        with hBdef
      have heF : e ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩
      have hat : (Sum.inr (e, k) : ChainLetter n K₁ K₂) ∈ A ∪ Bset :=
        Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨(e, k), Finset.mem_product.mpr ⟨heF, Finset.mem_univ _⟩, rfl⟩)
      have ht : ∀ b : ChainLetter n K₁ K₂, b ≠ Sum.inr (e, k) →
          ¬ chainIndependent n K₁ K₂ (Sum.inr (e, k)) b → b ∈ A ∪ Bset := by
        rintro (⟨j, k'⟩ | ⟨f, k'⟩) _ hdep
        · have hmem : j.val = e.val ∨ j.val = e.val + 1 := by
            by_contra hcon
            have h1 : j.val ≠ e.val := fun h => hcon (Or.inl h)
            have h2 : j.val ≠ e.val + 1 := fun h => hcon (Or.inr h)
            refine hdep ?_
            simp only [chainIndependent, chainSupport, Finset.disjoint_singleton_right,
              Finset.mem_insert, Finset.mem_singleton]
            exact fun hx => by rcases hx with hx | hx <;> omega
          refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(j, k'), ?_, rfl⟩)
          refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
          show j ∈ J
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
        · have hmem : f.val = e.val ∨ f.val = e.val + 1 ∨ f.val + 1 = e.val := by
            by_contra hcon
            have h1 : f.val ≠ e.val := fun h => hcon (Or.inl h)
            have h2 : f.val ≠ e.val + 1 := fun h => hcon (Or.inr (Or.inl h))
            have h3 : f.val + 1 ≠ e.val := fun h => hcon (Or.inr (Or.inr h))
            refine hdep ?_
            simp only [chainIndependent, chainSupport, Finset.disjoint_left,
              Finset.mem_insert, Finset.mem_singleton]
            rintro x (rfl | rfl) <;> rintro (hx | hx) <;> omega
          refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(f, k'), ?_, rfl⟩)
          refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
          show f ∈ F
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
      have h1 : A.card ≤ 2 * K₁ := by
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_product]
        have hJ2 : J.card ≤ 2 := card_le_two_filter_edge n e.val
        calc J.card * (Finset.univ : Finset (Fin K₁)).card
            ≤ 2 * (Finset.univ : Finset (Fin K₁)).card := Nat.mul_le_mul_right _ hJ2
          _ = 2 * K₁ := by simp
      have h2 : Bset.card ≤ 3 * K₂ := by
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_product]
        have hF3 : F.card ≤ 3 := card_le_three_filter_neighbourEdge (n - 1) e.val
        calc F.card * (Finset.univ : Finset (Fin K₂)).card
            ≤ 3 * (Finset.univ : Finset (Fin K₂)).card := Nat.mul_le_mul_right _ hF3
          _ = 3 * K₂ := by simp
      have hcard : (A ∪ Bset).card ≤ 2 * K₁ + 3 * K₂ :=
        le_trans (Finset.card_union_le _ _) (Nat.add_le_add h1 h2)
      have hmain := incidentEdgeCount_succ_le_of_dependentSubset
        (chainIndependent n K₁ K₂) (chainIndependent_symm n K₁ K₂) _ (A ∪ Bset) ht hat
      have hfinal : incidentEdgeCount (chainIndependent n K₁ K₂) (Sum.inr (e, k)) ≤
          2 * K₁ + 3 * K₂ - 1 := by omega
      exact le_trans hfinal (le_max_right _ _)

end ChainAlphabet

section ChainCapacity

/-- **One-dimensional local-circuit capacity law.**  For a one-dimensional local gate dictionary
with `K₁` one-site and `K₂` nearest-neighbour types, the measure of the states reachable at depth
at most `s` is bounded by the length-independent dependence-degree capacity times any
target-uniform measure bound. -/
theorem chain_measure_traceHeapAccessible_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) {n K₁ K₂ : ℕ} (hn : 0 < n) (hK : 0 < K₁)
    (S : CircuitTrace (chainIndependent n K₁ K₂) → Set X) (s : ℕ)
    {B : ℝ≥0∞} (hB : ∀ τ, ν (S τ) ≤ B) :
    ν (heapAccessible (traceLength (chainIndependent n K₁ K₂)) S s) ≤
      (((s + 1) * (K₁ * n + K₂ * (n - 1) + s - 1).choose s *
        2 ^ (max (K₁ - 1 + 2 * K₂) (2 * K₁ + 3 * K₂ - 1) * s) : ℕ) : ℝ≥0∞) * B := by
  haveI : Nonempty (ChainLetter n K₁ K₂) :=
    ⟨Sum.inl (⟨0, hn⟩, ⟨0, hK⟩)⟩
  refine le_trans (measure_traceHeapAccessible_le_cumulativeTraceCount ν _ S s hB) ?_
  refine mul_le_mul_left ?_ B
  have hcum := cumulativeTraceCount_le_maxDegree (chainIndependent n K₁ K₂)
    (chainIndependent_symm n K₁ K₂) s (max (K₁ - 1 + 2 * K₂) (2 * K₁ + 3 * K₂ - 1))
    (chain_incidentEdgeCount_le n K₁ K₂)
  rw [card_chainLetter] at hcum
  exact_mod_cast hcum

end ChainCapacity

section CapacityEntropy

/-- Explicit binomial profile bound: a `k`-subset count of an `n`-set is at most `(e n / k)^k`. -/
theorem choose_le_exp_mul_div_pow (n k : ℕ) (hk : 0 < k) :
    (n.choose k : ℝ) ≤ (Real.exp 1 * n / k) ^ k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have h1 : (n.choose k : ℝ) ≤ (n : ℝ) ^ k / (k.factorial : ℝ) := Nat.choose_le_pow_div k n
  have h2 : ((k : ℝ)) ^ k / (k.factorial : ℝ) ≤ Real.exp k :=
    Real.pow_div_factorial_le_exp k (by positivity) k
  have h3 : ((k : ℝ)) ^ k ≤ Real.exp k * (k.factorial : ℝ) := by
    rw [div_le_iff₀ hfac] at h2
    exact h2
  have hinv : (1 : ℝ) / (k.factorial : ℝ) ≤ Real.exp k / ((k : ℝ) ^ k) := by
    rw [div_le_div_iff₀ hfac (by positivity)]
    linarith
  calc (n.choose k : ℝ) ≤ (n : ℝ) ^ k / (k.factorial : ℝ) := h1
    _ = (n : ℝ) ^ k * (1 / (k.factorial : ℝ)) := by ring
    _ ≤ (n : ℝ) ^ k * (Real.exp k / ((k : ℝ) ^ k)) := by
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (Real.exp 1 * n / k) ^ k := by
        rw [div_pow, mul_pow, ← Real.exp_nat_mul, mul_one]
        field_simp

variable {α : Type*} [Fintype α] [LinearOrder α] [Nonempty α]

omit [LinearOrder α] in
/-- Multiplicity profiles at depth `s` are dominated by the `M`-subset profile count. -/
theorem choose_profile_le_choose_alphabet (s : ℕ) :
    (Fintype.card α + s - 1).choose s ≤ (Fintype.card α + s).choose (Fintype.card α) := by
  have hM : 1 ≤ Fintype.card α := Fintype.card_pos
  have hidx : Fintype.card α + s - 1 = s + (Fintype.card α - 1) := by omega
  have hsub : s + (Fintype.card α - 1) - (Fintype.card α - 1) = s := by omega
  have hchoose : (Fintype.card α + s - 1).choose s =
      (s + (Fintype.card α - 1)).choose (Fintype.card α - 1) := by
    rw [hidx, ← Nat.choose_symm (Nat.le_add_left (Fintype.card α - 1) s), hsub]
  have hpascal : (Fintype.card α + s).choose (Fintype.card α) =
      (s + (Fintype.card α - 1)).choose (Fintype.card α - 1) +
        (s + (Fintype.card α - 1)).choose (Fintype.card α) := by
    have h1 : Fintype.card α + s = (s + (Fintype.card α - 1)) + 1 := by omega
    have h2 : Fintype.card α = (Fintype.card α - 1) + 1 := by omega
    rw [h1, h2, Nat.choose_succ_succ]
    simp
  omega

/-- **Bounded-degree gate entropy.**  The logarithm of the cumulative heap capacity splits into an
extensive dependence term and a subleading multiplicity-profile term. -/
theorem log_cumulativeTraceCount_le (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (s Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ) :
    Real.log (cumulativeTraceCount independent s) ≤
      Δ * s * Real.log 2 +
        Fintype.card α * (1 + Real.log (1 + (s : ℝ) / Fintype.card α)) +
        Real.log (s + 1) := by
  classical
  have hM : 1 ≤ Fintype.card α := Fintype.card_pos
  have hMR : (0 : ℝ) < Fintype.card α := by exact_mod_cast hM
  have hcum := cumulativeTraceCount_le_maxDegree independent hsymm s Δ hdegree
  have hprofile : ((Fintype.card α + s - 1).choose s : ℝ) ≤
      (Real.exp 1 * (1 + (s : ℝ) / Fintype.card α)) ^ Fintype.card α := by
    have hstep : ((Fintype.card α + s - 1).choose s : ℝ) ≤
        ((Fintype.card α + s).choose (Fintype.card α) : ℝ) := by
      exact_mod_cast choose_profile_le_choose_alphabet (α := α) s
    refine le_trans hstep ?_
    refine le_trans (choose_le_exp_mul_div_pow (Fintype.card α + s) (Fintype.card α) hM) ?_
    apply le_of_eq
    congr 1
    push_cast
    field_simp
  have hbound : (cumulativeTraceCount independent s : ℝ) ≤
      ((s : ℝ) + 1) * (Real.exp 1 * (1 + (s : ℝ) / Fintype.card α)) ^ Fintype.card α *
        (2 : ℝ) ^ (Δ * s) := by
    have hcast : (cumulativeTraceCount independent s : ℝ) ≤
        ((s : ℝ) + 1) * ((Fintype.card α + s - 1).choose s : ℝ) * (2 : ℝ) ^ (Δ * s) := by
      exact_mod_cast hcum
    refine le_trans hcast ?_
    have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ (Δ * s) := by positivity
    refine mul_le_mul_of_nonneg_right ?_ h2pos
    exact mul_le_mul_of_nonneg_left hprofile (by positivity)
  have hprofpos : (0 : ℝ) < 1 + (s : ℝ) / Fintype.card α := by positivity
  have hpos : (0 : ℝ) < ((s : ℝ) + 1) *
      (Real.exp 1 * (1 + (s : ℝ) / Fintype.card α)) ^ Fintype.card α * (2 : ℝ) ^ (Δ * s) := by
    have h1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (Real.exp 1 * (1 + (s : ℝ) / Fintype.card α)) ^ Fintype.card α :=
      pow_pos (by positivity) _
    have h3 : (0 : ℝ) < (2 : ℝ) ^ (Δ * s) := by positivity
    exact mul_pos (mul_pos h1 h2) h3
  have hone : 0 < Nat.card (FixedTraceClass independent 0) := by
    haveI : Nonempty (FixedTraceClass independent 0) :=
      ⟨Quotient.mk (fixedTraceSetoid independent 0) List.Vector.nil⟩
    exact Nat.card_pos
  have hcumpos : (0 : ℝ) < (cumulativeTraceCount independent s : ℝ) := by
    have : 0 < cumulativeTraceCount independent s := by
      rw [cumulativeTraceCount]
      exact Finset.sum_pos' (fun i _ => Nat.zero_le _)
        ⟨0, Finset.mem_range.mpr (Nat.succ_pos s), hone⟩
    exact_mod_cast this
  refine le_trans (Real.log_le_log hcumpos hbound) ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
  push_cast
  ring_nf
  exact le_rfl

/-- **Subexponential gate profile.**  In the regime `M ≤ K n`, `s ≤ c 2^n`, the multiplicity-profile
and depth terms of the capacity logarithm are `o(2^n)`. -/
theorem tendsto_capacityProfile_div_pow_two (K c : ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c) :
    Filter.Tendsto
      (fun n : ℕ => (K * n * (1 + Real.log (1 + c * 2 ^ n)) + Real.log (c * 2 ^ n + 1)) / 2 ^ n)
      Filter.atTop (nhds 0) := by
  have hlogc : (0 : ℝ) < 1 + c := by linarith
  have hbound : ∀ n : ℕ, Real.log (1 + c * 2 ^ n) ≤ Real.log (1 + c) + n * Real.log 2 := by
    intro n
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hle : 1 + c * (2 : ℝ) ^ n ≤ (1 + c) * 2 ^ n := by nlinarith
    calc Real.log (1 + c * 2 ^ n) ≤ Real.log ((1 + c) * 2 ^ n) :=
          Real.log_le_log (by positivity) hle
      _ = Real.log (1 + c) + n * Real.log 2 := by
          rw [Real.log_mul (ne_of_gt hlogc) (by positivity), Real.log_pow]
  have hbound' : ∀ n : ℕ, Real.log (c * 2 ^ n + 1) ≤ Real.log (1 + c) + n * Real.log 2 := by
    intro n
    have := hbound n
    rwa [add_comm (c * (2:ℝ) ^ n) 1]
  have hnonneg : ∀ n : ℕ,
      0 ≤ (K * n * (1 + Real.log (1 + c * 2 ^ n)) + Real.log (c * 2 ^ n + 1)) / 2 ^ n := by
    intro n
    have h1 : 0 ≤ Real.log (1 + c * (2:ℝ) ^ n) :=
      Real.log_nonneg (by nlinarith [one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num) (n := n)])
    have h2 : 0 ≤ Real.log (c * (2:ℝ) ^ n + 1) :=
      Real.log_nonneg (by nlinarith [one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num) (n := n)])
    have : 0 ≤ K * n * (1 + Real.log (1 + c * (2:ℝ) ^ n)) := by positivity
    positivity
  have hupper : ∀ n : ℕ,
      (K * n * (1 + Real.log (1 + c * 2 ^ n)) + Real.log (c * 2 ^ n + 1)) / 2 ^ n ≤
        (K * Real.log 2) * ((n : ℝ) ^ 2 / 2 ^ n) +
          (K * (1 + Real.log (1 + c)) + Real.log 2) * ((n : ℝ) ^ 1 / 2 ^ n) +
          Real.log (1 + c) * ((n : ℝ) ^ 0 / 2 ^ n) := by
    intro n
    have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    rw [div_le_iff₀ hpow]
    have h1 := hbound n
    have h2 := hbound' n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hKn : 0 ≤ K * n := by positivity
    have hstep : K * n * (1 + Real.log (1 + c * 2 ^ n)) ≤
        K * n * (1 + Real.log (1 + c) + n * Real.log 2) := by
      refine mul_le_mul_of_nonneg_left ?_ hKn
      linarith
    have hfield : ((K * Real.log 2) * ((n : ℝ) ^ 2 / 2 ^ n) +
        (K * (1 + Real.log (1 + c)) + Real.log 2) * ((n : ℝ) ^ 1 / 2 ^ n) +
        Real.log (1 + c) * ((n : ℝ) ^ 0 / 2 ^ n)) * 2 ^ n =
        K * Real.log 2 * (n : ℝ) ^ 2 +
          (K * (1 + Real.log (1 + c)) + Real.log 2) * (n : ℝ) + Real.log (1 + c) := by
      field_simp
    rw [hfield]
    nlinarith [hstep, h2]
  have hzero : Filter.Tendsto
      (fun n : ℕ => (K * Real.log 2) * ((n : ℝ) ^ 2 / 2 ^ n) +
        (K * (1 + Real.log (1 + c)) + Real.log 2) * ((n : ℝ) ^ 1 / 2 ^ n) +
        Real.log (1 + c) * ((n : ℝ) ^ 0 / 2 ^ n)) Filter.atTop (nhds 0) := by
    have h2 := tendsto_pow_const_div_const_pow_of_one_lt 2 (r := (2 : ℝ)) (by norm_num)
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (r := (2 : ℝ)) (by norm_num)
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (r := (2 : ℝ)) (by norm_num)
    simpa using ((h2.const_mul (K * Real.log 2)).add
      (h1.const_mul (K * (1 + Real.log (1 + c)) + Real.log 2))).add
      (h0.const_mul (Real.log (1 + c)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
    hnonneg hupper

end CapacityEntropy

end GaloisForLFunctions.RHTower
