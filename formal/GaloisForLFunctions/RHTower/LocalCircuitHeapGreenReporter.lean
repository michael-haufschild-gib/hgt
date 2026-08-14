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

end GaloisForLFunctions.RHTower
