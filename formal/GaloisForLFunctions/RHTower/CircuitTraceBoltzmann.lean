import GaloisForLFunctions.RHTower.CircuitTraceMonoid
import GaloisForLFunctions.RHTower.LocalCircuitHeapGreenReporter

/-!
# The Boltzmann law of a circuit trace monoid

Below the dependence radius the geometric weight `z^{|T|}` is summable over the trace monoid, and
its total mass is the trace partition function.  Normalizing gives a probability law on finite
circuit heaps whose causal-cylinder masses are exact: cancellativity turns the cylinder above `u`
into a translate of the whole monoid, so its mass is exactly `z^{|u|}`.

The prefix set of a trace is finite, and pairing a prefix with its unique residual identifies the
expected prefix count with the partition function itself.
-/

namespace GaloisForLFunctions.RHTower

section Partition

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]

omit [DecidableEq α] in
/-- Below the dependence radius the geometric trace weight is summable. -/
theorem summable_tracePow (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) :
    Summable fun T : Trace independent => z ^ traceLen independent T := by
  have hgrade : ∀ ℓ : ℕ, (∑' _y : FixedTraceClass independent ℓ, z ^ ℓ) =
      (Nat.card (FixedTraceClass independent ℓ) : ℝ) * z ^ ℓ := by
    intro ℓ
    rw [tsum_const, nsmul_eq_mul]
  have hsig : Summable fun p : (ℓ : ℕ) × FixedTraceClass independent ℓ => z ^ p.1 := by
    rw [summable_sigma_of_nonneg fun p => by positivity]
    refine ⟨fun ℓ => Summable.of_finite, ?_⟩
    simp only [hgrade]
    exact summable_traceCount_pow independent hsymm Δ hdegree hz0 hz
  have hcomp : (fun p : (ℓ : ℕ) × FixedTraceClass independent ℓ =>
      z ^ traceLen independent (traceGradeEquiv independent p)) =
      fun p => z ^ p.1 := by
    funext p
    rw [traceLen_traceGradeEquiv]
  exact ((traceGradeEquiv independent).summable_iff).mp (by rw [Function.comp_def, hcomp]; exact hsig)

/-- The trace partition function. -/
noncomputable def tracePartition (independent : α → α → Prop) (z : ℝ) : ℝ :=
  ∑' T : Trace independent, z ^ traceLen independent T

omit [DecidableEq α] in
/-- The identity trace already contributes one to the partition function. -/
theorem one_le_tracePartition (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) :
    1 ≤ tracePartition independent z := by
  have hsum := summable_tracePow independent hsymm Δ hdegree hz0 hz
  have hterm : (1 : ℝ) = (fun T : Trace independent => z ^ traceLen independent T) 1 := by
    simp
  rw [hterm]
  exact hsum.le_tsum 1 fun j _ => by positivity

omit [DecidableEq α] in
theorem tracePartition_pos (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) :
    0 < tracePartition independent z :=
  lt_of_lt_of_le zero_lt_one (one_le_tracePartition independent hsymm Δ hdegree hz0 hz)

omit [DecidableEq α] in
/-- **Trace partition bound.**  The dependence radius controls the partition function by the exact
negative-binomial value. -/
theorem tracePartition_le (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) :
    tracePartition independent z ≤ 1 / (1 - 2 ^ Δ * z) ^ Fintype.card α := by
  have hgrade : ∀ ℓ : ℕ, (∑' _y : FixedTraceClass independent ℓ, z ^ ℓ) =
      (Nat.card (FixedTraceClass independent ℓ) : ℝ) * z ^ ℓ := by
    intro ℓ
    rw [tsum_const, nsmul_eq_mul]
  have hsig : Summable fun p : (ℓ : ℕ) × FixedTraceClass independent ℓ => z ^ p.1 := by
    rw [summable_sigma_of_nonneg fun p => by positivity]
    refine ⟨fun ℓ => Summable.of_finite, ?_⟩
    simp only [hgrade]
    exact summable_traceCount_pow independent hsymm Δ hdegree hz0 hz
  have hstep : tracePartition independent z =
      ∑' ℓ : ℕ, (Nat.card (FixedTraceClass independent ℓ) : ℝ) * z ^ ℓ := by
    rw [tracePartition]
    rw [← (traceGradeEquiv independent).tsum_eq
      (fun T : Trace independent => z ^ traceLen independent T)]
    have hcomp : (fun p : (ℓ : ℕ) × FixedTraceClass independent ℓ =>
        z ^ traceLen independent (traceGradeEquiv independent p)) = fun p => z ^ p.1 := by
      funext p
      rw [traceLen_traceGradeEquiv]
    rw [hcomp, hsig.tsum_sigma]
    exact tsum_congr hgrade
  rw [hstep]
  exact tracePartitionSum_le independent hsymm Δ hdegree hz0 hz

end Partition

section Cylinder

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]

omit [Fintype α] [LinearOrder α] [Nonempty α] in
/-- The geometric weight of a causal cylinder is its base weight times the partition function. -/
theorem tsum_traceCylinder (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (z : ℝ) (u : Trace independent) :
    (∑' T : traceCylinder independent u, z ^ traceLen independent (T : Trace independent)) =
      z ^ traceLen independent u * tracePartition independent z := by
  rw [← (traceCylinderEquiv hsymm u).tsum_eq
    (fun T : traceCylinder independent u => z ^ traceLen independent (T : Trace independent))]
  have hval : ∀ v : Trace independent,
      z ^ traceLen independent
        ((traceCylinderEquiv hsymm u v : traceCylinder independent u) : Trace independent) =
      z ^ traceLen independent u * z ^ traceLen independent v := by
    intro v
    show z ^ traceLen independent (u * v) = _
    rw [traceLen_mul, pow_add]
  simp_rw [hval]
  rw [tsum_mul_left, tracePartition]

/-- Normalized Boltzmann mass of a set of circuit heaps. -/
noncomputable def traceMass (independent : α → α → Prop) (z : ℝ)
    (S : Set (Trace independent)) : ℝ :=
  (∑' T : S, z ^ traceLen independent (T : Trace independent)) / tracePartition independent z

/-- **Exact causal-cylinder law.**  The Boltzmann mass of the cylinder above `u` is exactly the
geometric weight of `u`. -/
theorem traceMass_traceCylinder (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) (u : Trace independent) :
    traceMass independent z (traceCylinder independent u) = z ^ traceLen independent u := by
  have hpos := tracePartition_pos independent hsymm Δ hdegree hz0 hz
  rw [traceMass, tsum_traceCylinder independent hsymm z u,
    mul_div_assoc, div_self (ne_of_gt hpos), mul_one]

omit [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α] in
theorem traceMass_nonneg (independent : α → α → Prop) {z : ℝ} (hz0 : 0 ≤ z)
    (hpos : 0 < tracePartition independent z) (S : Set (Trace independent)) :
    0 ≤ traceMass independent z S := by
  refine div_nonneg (tsum_nonneg fun T => by positivity) hpos.le

omit [DecidableEq α] in
theorem traceMass_le_one (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) (S : Set (Trace independent)) :
    traceMass independent z S ≤ 1 := by
  have hsum := summable_tracePow independent hsymm Δ hdegree hz0 hz
  have hpos := tracePartition_pos independent hsymm Δ hdegree hz0 hz
  rw [traceMass, div_le_one hpos]
  exact Summable.tsum_subtype_le _ S (fun T => by positivity) hsum

omit [DecidableEq α] in
theorem traceMass_mono (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) {S S' : Set (Trace independent)} (hSS : S ⊆ S') :
    traceMass independent z S ≤ traceMass independent z S' := by
  have hsum := summable_tracePow independent hsymm Δ hdegree hz0 hz
  have hpos := tracePartition_pos independent hsymm Δ hdegree hz0 hz
  have hnum : (∑' T : S, z ^ traceLen independent (T : Trace independent)) ≤
      ∑' T : S', z ^ traceLen independent (T : Trace independent) := by
    rw [tsum_subtype S (fun T : Trace independent => z ^ traceLen independent T),
      tsum_subtype S' (fun T : Trace independent => z ^ traceLen independent T)]
    exact Summable.tsum_le_tsum
      (fun i => Set.indicator_le_indicator_of_subset hSS (fun a => by positivity) i)
      (hsum.indicator S) (hsum.indicator S')
  rw [traceMass, traceMass]
  gcongr

omit [DecidableEq α] in
/-- Boltzmann mass is modular: union plus intersection is the sum of the two masses. -/
theorem traceMass_union_add_inter (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) (S S' : Set (Trace independent)) :
    traceMass independent z (S ∪ S') + traceMass independent z (S ∩ S') =
      traceMass independent z S + traceMass independent z S' := by
  classical
  have hsum := summable_tracePow independent hsymm Δ hdegree hz0 hz
  set w : Trace independent → ℝ := fun T => z ^ traceLen independent T with hwdef
  have hpt : ∀ T : Trace independent,
      Set.indicator (S ∪ S') w T + Set.indicator (S ∩ S') w T =
        Set.indicator S w T + Set.indicator S' w T := by
    intro T
    by_cases hS : T ∈ S <;> by_cases hS' : T ∈ S' <;>
      simp [Set.indicator, hS, hS', Set.mem_union, Set.mem_inter_iff]
  have hkey : (∑' T : Trace independent, Set.indicator (S ∪ S') w T) +
      (∑' T : Trace independent, Set.indicator (S ∩ S') w T) =
      (∑' T : Trace independent, Set.indicator S w T) +
        ∑' T : Trace independent, Set.indicator S' w T := by
    rw [← (hsum.indicator (S ∪ S')).tsum_add (hsum.indicator (S ∩ S')),
      ← (hsum.indicator S).tsum_add (hsum.indicator S')]
    exact tsum_congr hpt
  rw [traceMass, traceMass, traceMass, traceMass,
    tsum_subtype (S ∪ S') w, tsum_subtype (S ∩ S') w, tsum_subtype S w, tsum_subtype S' w,
    ← add_div, ← add_div, hkey]

/-- **Concurrency falsifier.**  For two distinct independent letters the union of their causal
cylinders has mass `2z - z²`, strictly below the sum `2z` of the two cylinder masses. -/
theorem traceMass_union_cylinders_of_independent (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) {a b : α} (hab : a ≠ b)
    (hind : independent a b) :
    traceMass independent z (traceCylinder independent (traceMk independent [a]) ∪
        traceCylinder independent (traceMk independent [b])) = 2 * z - z ^ 2 := by
  have hmod := traceMass_union_add_inter independent hsymm Δ hdegree hz0 hz
    (traceCylinder independent (traceMk independent [a]))
    (traceCylinder independent (traceMk independent [b]))
  rw [traceCylinder_inter_of_independent hsymm hab hind] at hmod
  have hA : traceMass independent z (traceCylinder independent (traceMk independent [a])) = z := by
    rw [traceMass_traceCylinder independent hsymm Δ hdegree hz0 hz]
    simp
  have hB : traceMass independent z (traceCylinder independent (traceMk independent [b])) = z := by
    rw [traceMass_traceCylinder independent hsymm Δ hdegree hz0 hz]
    simp
  have hAB : traceMass independent z
      (traceCylinder independent (traceMk independent [a, b])) = z ^ 2 := by
    rw [traceMass_traceCylinder independent hsymm Δ hdegree hz0 hz]
    simp
  rw [hA, hB, hAB] at hmod
  linarith

/-- Normalized Boltzmann weight of a single circuit heap. -/
noncomputable def traceWeight (independent : α → α → Prop) (z : ℝ) (T : Trace independent) : ℝ :=
  z ^ traceLen independent T / tracePartition independent z

omit [DecidableEq α] in
omit [Fintype α] [LinearOrder α] [Nonempty α] in
theorem traceWeight_nonneg (independent : α → α → Prop) {z : ℝ} (hz0 : 0 ≤ z)
    (hpos : 0 < tracePartition independent z) (T : Trace independent) :
    0 ≤ traceWeight independent z T := by
  rw [traceWeight]
  positivity

omit [DecidableEq α] in
theorem summable_traceWeight (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) :
    Summable (traceWeight independent z) := by
  have h := (summable_tracePow independent hsymm Δ hdegree hz0 hz).mul_right
    (tracePartition independent z)⁻¹
  have heq : (fun T : Trace independent =>
      z ^ traceLen independent T * (tracePartition independent z)⁻¹) =
      traceWeight independent z := by
    funext T
    rw [traceWeight, div_eq_mul_inv]
  rwa [heq] at h

omit [DecidableEq α] in
/-- The Boltzmann weights form a probability law on circuit heaps. -/
theorem tsum_traceWeight (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) :
    (∑' T : Trace independent, traceWeight independent z T) = 1 := by
  have hpos := tracePartition_pos independent hsymm Δ hdegree hz0 hz
  simp only [traceWeight, div_eq_mul_inv]
  rw [tsum_mul_right, ← tracePartition, mul_inv_cancel₀ (ne_of_gt hpos)]

omit [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α] in
theorem traceMass_eq_tsum_traceWeight (independent : α → α → Prop) (z : ℝ)
    (S : Set (Trace independent)) :
    traceMass independent z S = ∑' T : S, traceWeight independent z (T : Trace independent) := by
  have heq : ∀ T : Trace independent,
      traceWeight independent z T =
        z ^ traceLen independent T * (tracePartition independent z)⁻¹ := by
    intro T
    rw [traceWeight, div_eq_mul_inv]
  rw [traceMass, tsum_congr fun T : S => heq (T : Trace independent), tsum_mul_right,
    div_eq_mul_inv]

end Cylinder

section PrefixCount

open scoped ENNReal

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]

omit [DecidableEq α] [LinearOrder α] [Nonempty α] in
/-- Traces of bounded length form a finite set. -/
theorem finite_setOf_traceLen_le (independent : α → α → Prop) (n : ℕ) :
    {u : Trace independent | traceLen independent u ≤ n}.Finite := by
  have hsub : {u : Trace independent | traceLen independent u ≤ n} ⊆
      ⋃ ℓ ∈ Finset.range (n + 1), Set.range (fixedTraceToTrace independent ℓ) := by
    intro u hu
    obtain ⟨p, rfl⟩ := (traceGradeEquiv independent).surjective u
    have hlen : p.1 ≤ n := by
      have := hu
      rw [Set.mem_setOf_eq, traceLen_traceGradeEquiv] at this
      exact this
    exact Set.mem_iUnion₂.mpr
      ⟨p.1, Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le hlen)), ⟨p.2, rfl⟩⟩
  refine Set.Finite.subset ?_ hsub
  exact Set.Finite.biUnion (Finset.range (n + 1)).finite_toSet fun ℓ _ => Set.finite_range _

/-- The causal prefixes of a trace. -/
def tracePrefixSet (independent : α → α → Prop) (T : Trace independent) :
    Set (Trace independent) := {u | TracePrefix independent u T}

omit [DecidableEq α] in
omit [LinearOrder α] [Nonempty α] in
theorem tracePrefixSet_finite (independent : α → α → Prop) (T : Trace independent) :
    (tracePrefixSet independent T).Finite :=
  (finite_setOf_traceLen_le independent (traceLen independent T)).subset fun u hu =>
    traceLen_of_mem_traceCylinder (u := u) (T := T) hu

noncomputable instance (independent : α → α → Prop) (T : Trace independent) :
    Finite (tracePrefixSet independent T) := (tracePrefixSet_finite independent T).to_subtype

/-- The trace partition function in extended nonnegative reals. -/
noncomputable def tracePartitionENN (independent : α → α → Prop) (z : ℝ) : ℝ≥0∞ :=
  ∑' T : Trace independent, ENNReal.ofReal (z ^ traceLen independent T)

omit [DecidableEq α] in
theorem tracePartitionENN_eq_ofReal (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) :
    tracePartitionENN independent z = ENNReal.ofReal (tracePartition independent z) := by
  rw [tracePartitionENN, tracePartition, ENNReal.ofReal_tsum_of_nonneg (fun T => by positivity)
    (summable_tracePow independent hsymm Δ hdegree hz0 hz)]

omit [Fintype α] [LinearOrder α] [Nonempty α] in
theorem tsum_traceCylinderENN (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) {z : ℝ} (hz0 : 0 ≤ z)
    (u : Trace independent) :
    (∑' T : traceCylinder independent u,
        ENNReal.ofReal (z ^ traceLen independent (T : Trace independent))) =
      ENNReal.ofReal (z ^ traceLen independent u) * tracePartitionENN independent z := by
  rw [← (traceCylinderEquiv hsymm u).tsum_eq
    (fun T : traceCylinder independent u =>
      ENNReal.ofReal (z ^ traceLen independent (T : Trace independent)))]
  have hval : ∀ v : Trace independent,
      ENNReal.ofReal (z ^ traceLen independent
        ((traceCylinderEquiv hsymm u v : traceCylinder independent u) : Trace independent)) =
      ENNReal.ofReal (z ^ traceLen independent u) *
        ENNReal.ofReal (z ^ traceLen independent v) := by
    intro v
    show ENNReal.ofReal (z ^ traceLen independent (u * v)) = _
    rw [traceLen_mul, pow_add, ENNReal.ofReal_mul (by positivity)]
  simp_rw [hval]
  rw [ENNReal.tsum_mul_left, tracePartitionENN]

omit [DecidableEq α] [Nonempty α] in
/-- **Exact expected causal-prefix count.**  Pairing every causal prefix with its unique residual
identifies the weighted prefix count with the square of the partition function. -/
theorem tsum_tracePrefixCount (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) {z : ℝ} (hz0 : 0 ≤ z) :
    (∑' T : Trace independent, (Nat.card (tracePrefixSet independent T) : ℝ≥0∞) *
        ENNReal.ofReal (z ^ traceLen independent T)) =
      tracePartitionENN independent z * tracePartitionENN independent z := by
  have hcount : ∀ T : Trace independent,
      (Nat.card (tracePrefixSet independent T) : ℝ≥0∞) *
          ENNReal.ofReal (z ^ traceLen independent T) =
        ∑' u : Trace independent, Set.indicator (tracePrefixSet independent T)
          (fun _ => ENNReal.ofReal (z ^ traceLen independent T)) u := by
    intro T
    rw [← tsum_subtype (tracePrefixSet independent T)
      (fun _ => ENNReal.ofReal (z ^ traceLen independent T)),
      ENNReal.tsum_const, ENat.card_eq_coe_natCard]
    rfl
  have hswap : (∑' T : Trace independent, ∑' u : Trace independent,
      Set.indicator (tracePrefixSet independent T)
        (fun _ => ENNReal.ofReal (z ^ traceLen independent T)) u) =
      ∑' u : Trace independent, ∑' T : Trace independent,
        Set.indicator (tracePrefixSet independent T)
          (fun _ => ENNReal.ofReal (z ^ traceLen independent T)) u := ENNReal.tsum_comm
  have hinner : ∀ u : Trace independent,
      (∑' T : Trace independent, Set.indicator (tracePrefixSet independent T)
          (fun _ => ENNReal.ofReal (z ^ traceLen independent T)) u) =
        ENNReal.ofReal (z ^ traceLen independent u) * tracePartitionENN independent z := by
    intro u
    have hrewrite : ∀ T : Trace independent,
        Set.indicator (tracePrefixSet independent T)
          (fun _ => ENNReal.ofReal (z ^ traceLen independent T)) u =
          Set.indicator (traceCylinder independent u)
            (fun T => ENNReal.ofReal (z ^ traceLen independent T)) T := by
      intro T
      by_cases h : TracePrefix independent u T
      · rw [Set.indicator_of_mem (show u ∈ tracePrefixSet independent T from h),
          Set.indicator_of_mem (show T ∈ traceCylinder independent u from h)]
      · rw [Set.indicator_of_notMem (show u ∉ tracePrefixSet independent T from h),
          Set.indicator_of_notMem (show T ∉ traceCylinder independent u from h)]
    simp_rw [hrewrite]
    rw [← tsum_subtype (traceCylinder independent u)
      (fun T : Trace independent => ENNReal.ofReal (z ^ traceLen independent T))]
    exact tsum_traceCylinderENN independent hsymm hz0 u
  simp_rw [hcount]
  rw [hswap]
  simp_rw [hinner]
  rw [ENNReal.tsum_mul_right, tracePartitionENN]

end PrefixCount

end GaloisForLFunctions.RHTower
