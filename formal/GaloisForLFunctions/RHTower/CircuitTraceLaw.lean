import GaloisForLFunctions.RHTower.CircuitCausalAccessibility

/-!
# The Boltzmann law of circuit heaps as a measure

The normalized Boltzmann weights of the trace monoid assemble into a probability measure on the
countable space of circuit heaps.  Its value on a set of heaps is the Boltzmann mass of that set,
so the concurrent causal accessibility of a state is exactly the probability of the causal success
event.
-/

open MeasureTheory

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.RHTower

section TraceLaw

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]

/-- The discrete measurable structure of the countable trace monoid. -/
instance instMeasurableSpaceTrace (independent : α → α → Prop) :
    MeasurableSpace (Trace independent) := ⊤

instance instMeasurableSingletonClassTrace (independent : α → α → Prop) :
    MeasurableSingletonClass (Trace independent) := ⟨fun _ => trivial⟩

theorem measurableSet_trace (independent : α → α → Prop) (S : Set (Trace independent)) :
    MeasurableSet S := trivial

/-- A trace has zero length exactly when it is the empty heap. -/
theorem traceLen_eq_zero_iff (independent : α → α → Prop) (u : Trace independent) :
    traceLen independent u = 0 ↔ u = 1 := by
  constructor
  · obtain ⟨w, rfl⟩ := traceMk_surjective independent u
    intro h
    rw [traceLen_traceMk] at h
    rw [List.eq_nil_of_length_eq_zero h]
    rfl
  · rintro rfl
    rfl

/-- Only the empty heap is a causal prefix of the empty heap. -/
theorem eq_one_of_tracePrefix_one (independent : α → α → Prop) {u : Trace independent}
    (h : TracePrefix independent u (1 : Trace independent)) : u = 1 := by
  obtain ⟨v, hv⟩ := h
  have hlen : traceLen independent u + traceLen independent v = 0 := by
    rw [← traceLen_mul, ← hv, traceLen_one]
  exact (traceLen_eq_zero_iff independent u).mp (Nat.eq_zero_of_add_eq_zero_right hlen)

/-- The Boltzmann law of circuit heaps. -/
noncomputable def traceLaw (independent : α → α → Prop) (z : ℝ) : Measure (Trace independent) :=
  Measure.sum fun T => ENNReal.ofReal (traceWeight independent z T) • Measure.dirac T

theorem traceLaw_apply (independent : α → α → Prop) (z : ℝ) (S : Set (Trace independent)) :
    traceLaw independent z S =
      ∑' T : S, ENNReal.ofReal (traceWeight independent z (T : Trace independent)) := by
  rw [traceLaw, Measure.sum_apply _ (measurableSet_trace independent S),
    tsum_subtype S fun T => ENNReal.ofReal (traceWeight independent z T)]
  refine tsum_congr fun T => ?_
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  by_cases hT : T ∈ S
  · rw [Set.indicator_of_mem hT, Set.indicator_of_mem hT, Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem hT, Set.indicator_of_notMem hT, mul_zero]

/-- **The Boltzmann law computes the Boltzmann mass.** -/
theorem traceLaw_apply_eq_ofReal_traceMass (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) (S : Set (Trace independent)) :
    traceLaw independent z S = ENNReal.ofReal (traceMass independent z S) := by
  have hpos := tracePartition_pos independent hsymm Δ hdegree hz0 hz
  rw [traceLaw_apply, traceMass_eq_tsum_traceWeight,
    ENNReal.ofReal_tsum_of_nonneg
      (fun T : S => traceWeight_nonneg independent hz0 hpos (T : Trace independent))
      ((summable_traceWeight independent hsymm Δ hdegree hz0 hz).subtype S)]

theorem traceLaw_univ (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) :
    traceLaw independent z Set.univ = 1 := by
  have hpos := tracePartition_pos independent hsymm Δ hdegree hz0 hz
  rw [traceLaw_apply]
  rw [tsum_subtype Set.univ fun T => ENNReal.ofReal (traceWeight independent z T)]
  have hind : ∀ T : Trace independent,
      Set.univ.indicator (fun T => ENNReal.ofReal (traceWeight independent z T)) T =
        ENNReal.ofReal (traceWeight independent z T) := fun T => by
    rw [Set.indicator_of_mem (Set.mem_univ T)]
  rw [tsum_congr hind, ← ENNReal.ofReal_tsum_of_nonneg
      (fun T => traceWeight_nonneg independent hz0 hpos T)
      (summable_traceWeight independent hsymm Δ hdegree hz0 hz),
    tsum_traceWeight independent hsymm Δ hdegree hz0 hz, ENNReal.ofReal_one]

theorem isProbabilityMeasure_traceLaw (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) :
    IsProbabilityMeasure (traceLaw independent z) :=
  ⟨traceLaw_univ independent hsymm Δ hdegree hz0 hz⟩

variable {X : Type*}

/-- **Causal accessibility is the probability of the causal success event.** -/
theorem traceLaw_causalSuccessEvent (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) (S : Trace independent → Set X) (x : X) :
    traceLaw independent z (causalSuccessEvent independent S x) =
      ENNReal.ofReal (causalAccessibility independent z S x) :=
  traceLaw_apply_eq_ofReal_traceMass independent hsymm Δ hdegree hz0 hz _

end TraceLaw

end GaloisForLFunctions.RHTower
