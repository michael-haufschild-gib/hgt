import GaloisForLFunctions.RHTower.CircuitCausalAccessibility

/-!
# The preparation action as a relative-entropy projection

The Boltzmann law of circuit heaps is strictly positive on every heap, so the discrete relative
entropy against it is well behaved.  Gibbs' inequality then identifies the preparation action of a
target dictionary with the least relative entropy of a law supported on the causal success event,
and the conditioned Boltzmann law attains it.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.RHTower

section Gibbs

variable {ι : Type*}

/-- Discrete relative entropy of one weight function against another. -/
noncomputable def discreteRelativeEntropy (Q R : ι → ℝ) : ℝ :=
  ∑' i, Q i * Real.log (Q i / R i)

/-- **Gibbs' inequality.**  Relative entropy between probability weights is nonnegative. -/
theorem discreteRelativeEntropy_nonneg (Q R : ι → ℝ) (hQ : ∀ i, 0 ≤ Q i) (hR : ∀ i, 0 < R i)
    (hQsum : Summable Q) (hRsum : Summable R) (hQtot : ∑' i, Q i = 1) (hRtot : ∑' i, R i = 1)
    (hDsum : Summable fun i => Q i * Real.log (Q i / R i)) :
    0 ≤ discreteRelativeEntropy Q R := by
  have hneg : ∀ i, Q i * Real.log (R i / Q i) = -(Q i * Real.log (Q i / R i)) := by
    intro i
    rcases eq_or_lt_of_le (hQ i) with h | h
    · rw [← h]; ring
    · have hlog : Real.log (R i / Q i) = -Real.log (Q i / R i) := by
        rw [← Real.log_inv, inv_div]
      rw [hlog]
      ring
  have hle : ∀ i, Q i * Real.log (R i / Q i) ≤ R i - Q i := by
    intro i
    rcases eq_or_lt_of_le (hQ i) with h | h
    · rw [← h]
      simp only [zero_mul, sub_zero]
      exact (hR i).le
    · have hlog : Real.log (R i / Q i) ≤ R i / Q i - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (hR i) h)
      have := mul_le_mul_of_nonneg_left hlog h.le
      calc Q i * Real.log (R i / Q i) ≤ Q i * (R i / Q i - 1) := this
        _ = R i - Q i := by field_simp
  have hsumneg : Summable fun i => Q i * Real.log (R i / Q i) := by
    simpa only [hneg] using hDsum.neg
  have hkey : (∑' i, Q i * Real.log (R i / Q i)) ≤ 0 := by
    calc (∑' i, Q i * Real.log (R i / Q i)) ≤ ∑' i, (R i - Q i) :=
        Summable.tsum_le_tsum hle hsumneg (hRsum.sub hQsum)
      _ = 0 := by rw [hRsum.tsum_sub hQsum, hRtot, hQtot, sub_self]
  have hrewrite : (∑' i, Q i * Real.log (R i / Q i)) =
      -discreteRelativeEntropy Q R := by
    rw [discreteRelativeEntropy, ← tsum_neg]
    exact tsum_congr hneg
  rw [hrewrite] at hkey
  linarith

end Gibbs

section PreparationEntropy

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
variable {X : Type*}

theorem traceWeight_pos (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 < z) (hz : 2 ^ Δ * z < 1) (T : Trace independent) :
    0 < traceWeight independent z T := by
  have hZ := tracePartition_pos independent hsymm Δ hdegree hz0.le hz
  rw [traceWeight]
  positivity

/-- The Boltzmann law conditioned on a positive-mass event. -/
noncomputable def conditionedTraceWeight (independent : α → α → Prop) (z : ℝ)
    (E : Set (Trace independent)) (T : Trace independent) : ℝ :=
  Set.indicator E (traceWeight independent z) T / traceMass independent z E

theorem conditionedTraceWeight_nonneg (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) (E : Set (Trace independent))
    (T : Trace independent) : 0 ≤ conditionedTraceWeight independent z E T := by
  have hZ := tracePartition_pos independent hsymm Δ hdegree hz0 hz
  rw [conditionedTraceWeight]
  refine div_nonneg ?_ (traceMass_nonneg independent hz0 hZ E)
  by_cases h : T ∈ E
  · rw [Set.indicator_of_mem h]
    exact traceWeight_nonneg independent hz0 hZ T
  · rw [Set.indicator_of_notMem h]

theorem summable_conditionedTraceWeight (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) (E : Set (Trace independent)) :
    Summable (conditionedTraceWeight independent z E) := by
  classical
  have hbase := summable_traceWeight independent hsymm Δ hdegree hz0 hz
  have heq : conditionedTraceWeight independent z E =
      fun T => Set.indicator E (traceWeight independent z) T *
        (traceMass independent z E)⁻¹ := by
    funext T
    rw [conditionedTraceWeight, div_eq_mul_inv]
  rw [heq]
  exact (hbase.indicator E).mul_right _

theorem tsum_conditionedTraceWeight (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) {E : Set (Trace independent)}
    (hE : 0 < traceMass independent z E) :
    (∑' T : Trace independent, conditionedTraceWeight independent z E T) = 1 := by
  classical
  have hbase := summable_traceWeight independent hsymm Δ hdegree hz0 hz
  have heq : conditionedTraceWeight independent z E =
      fun T => Set.indicator E (traceWeight independent z) T *
        (traceMass independent z E)⁻¹ := by
    funext T
    rw [conditionedTraceWeight, div_eq_mul_inv]
  rw [heq, tsum_mul_right, ← tsum_subtype E (traceWeight independent z),
    ← traceMass_eq_tsum_traceWeight independent z E, mul_inv_cancel₀ (ne_of_gt hE)]

theorem conditionedTraceWeight_pos (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 < z) (hz : 2 ^ Δ * z < 1) {E : Set (Trace independent)}
    (hE : 0 < traceMass independent z E) {T : Trace independent} (hT : T ∈ E) :
    0 < conditionedTraceWeight independent z E T := by
  rw [conditionedTraceWeight, Set.indicator_of_mem hT]
  exact div_pos (traceWeight_pos independent hsymm Δ hdegree hz0 hz T) hE

theorem conditionedTraceWeight_eq_zero (independent : α → α → Prop) (z : ℝ)
    {E : Set (Trace independent)} {T : Trace independent} (hT : T ∉ E) :
    conditionedTraceWeight independent z E T = 0 := by
  rw [conditionedTraceWeight, Set.indicator_of_notMem hT, zero_div]

/-- The conditioned Boltzmann law has relative entropy exactly the preparation action. -/
theorem discreteRelativeEntropy_conditionedTraceWeight (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 < z) (hz : 2 ^ Δ * z < 1) {E : Set (Trace independent)}
    (hE : 0 < traceMass independent z E) :
    discreteRelativeEntropy (conditionedTraceWeight independent z E)
        (traceWeight independent z) = -Real.log (traceMass independent z E) := by
  have hterm : ∀ T : Trace independent,
      conditionedTraceWeight independent z E T *
        Real.log (conditionedTraceWeight independent z E T / traceWeight independent z T) =
      conditionedTraceWeight independent z E T * -Real.log (traceMass independent z E) := by
    intro T
    by_cases hT : T ∈ E
    · congr 1
      have hw : traceWeight independent z T ≠ 0 :=
        ne_of_gt (traceWeight_pos independent hsymm Δ hdegree hz0 hz T)
      have hm : traceMass independent z E ≠ 0 := ne_of_gt hE
      rw [conditionedTraceWeight, Set.indicator_of_mem hT]
      have hval : traceWeight independent z T / traceMass independent z E /
          traceWeight independent z T = (traceMass independent z E)⁻¹ := by
        field_simp
      rw [hval, Real.log_inv]
    · rw [conditionedTraceWeight_eq_zero independent z hT, zero_mul, zero_mul]
  rw [discreteRelativeEntropy, tsum_congr hterm, tsum_mul_right,
    tsum_conditionedTraceWeight independent hsymm Δ hdegree hz0.le hz hE, one_mul]

/-- **Preparation action as an information projection.**  The preparation action is the least
relative entropy of a law supported on the causal success event, and the conditioned Boltzmann law
attains it. -/
theorem isLeast_preparationAction (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 < z) (hz : 2 ^ Δ * z < 1)
    (S : Trace independent → Set X) (x : X)
    (hpos : 0 < causalAccessibility independent z S x) :
    IsLeast {d : ℝ | ∃ Q : Trace independent → ℝ,
        (∀ T, 0 ≤ Q T) ∧ Summable Q ∧ (∑' T, Q T) = 1 ∧
        (∀ T, T ∉ causalSuccessEvent independent S x → Q T = 0) ∧
        Summable (fun T => Q T * Real.log (Q T / traceWeight independent z T)) ∧
        d = discreteRelativeEntropy Q (traceWeight independent z)}
      (preparationAction independent z S x) := by
  set E : Set (Trace independent) := causalSuccessEvent independent S x with hEdef
  have hE : 0 < traceMass independent z E := hpos
  have hcond := discreteRelativeEntropy_conditionedTraceWeight independent hsymm Δ hdegree
    hz0 hz hE
  have hcondTerm : ∀ T : Trace independent,
      conditionedTraceWeight independent z E T *
        Real.log (conditionedTraceWeight independent z E T / traceWeight independent z T) =
      conditionedTraceWeight independent z E T * -Real.log (traceMass independent z E) := by
    intro T
    by_cases hT : T ∈ E
    · congr 1
      have hw : traceWeight independent z T ≠ 0 :=
        ne_of_gt (traceWeight_pos independent hsymm Δ hdegree hz0 hz T)
      have hm : traceMass independent z E ≠ 0 := ne_of_gt hE
      rw [conditionedTraceWeight, Set.indicator_of_mem hT]
      have hval : traceWeight independent z T / traceMass independent z E /
          traceWeight independent z T = (traceMass independent z E)⁻¹ := by
        field_simp
      rw [hval, Real.log_inv]
    · rw [conditionedTraceWeight_eq_zero independent z hT, zero_mul, zero_mul]
  constructor
  · refine ⟨conditionedTraceWeight independent z E,
      conditionedTraceWeight_nonneg independent hsymm Δ hdegree hz0.le hz E,
      summable_conditionedTraceWeight independent hsymm Δ hdegree hz0.le hz E,
      tsum_conditionedTraceWeight independent hsymm Δ hdegree hz0.le hz hE,
      fun T hT => conditionedTraceWeight_eq_zero independent z hT, ?_, ?_⟩
    · have hbase := (summable_conditionedTraceWeight independent hsymm Δ hdegree hz0.le hz
        E).mul_right (-Real.log (traceMass independent z E))
      simpa only [hcondTerm] using hbase
    · rw [preparationAction, causalAccessibility, hcond]
  · rintro d ⟨Q, hQ0, hQsum, hQtot, hQsupp, hQD, rfl⟩
    have hsupp : Function.support Q ⊆ E := by
      intro T hT
      by_contra hTE
      exact hT (hQsupp T hTE)
    have hsuppD : Function.support
        (fun T => Q T * Real.log (Q T / traceWeight independent z T)) ⊆ E := by
      intro T hT
      by_contra hTE
      exact hT (by simp only [hQsupp T hTE, zero_mul])
    have hEqterm : ∀ T : E,
        Q (T : Trace independent) * Real.log (Q (T : Trace independent) /
            conditionedTraceWeight independent z E (T : Trace independent)) =
          Q (T : Trace independent) * Real.log (Q (T : Trace independent) /
            traceWeight independent z (T : Trace independent)) +
            Q (T : Trace independent) * Real.log (traceMass independent z E) := by
      intro T
      by_cases hQT : Q (T : Trace independent) = 0
      · rw [hQT]; ring
      · have hQpos : 0 < Q (T : Trace independent) :=
          lt_of_le_of_ne (hQ0 _) (Ne.symm hQT)
        have hcpos := conditionedTraceWeight_pos independent hsymm Δ hdegree hz0 hz hE T.2
        have hwe : traceWeight independent z (T : Trace independent) =
            conditionedTraceWeight independent z E (T : Trace independent) *
              traceMass independent z E := by
          rw [conditionedTraceWeight, Set.indicator_of_mem T.2,
            div_mul_cancel₀ _ (ne_of_gt hE)]
        rw [hwe, ← div_div,
          Real.log_div (ne_of_gt (div_pos hQpos hcpos)) (ne_of_gt hE)]
        ring
    have h1 : Summable fun T : E =>
        Q (T : Trace independent) * Real.log (Q (T : Trace independent) /
          traceWeight independent z (T : Trace independent)) :=
      hQD.subtype (fun T => T ∈ E)
    have h2 : Summable fun T : E =>
        Q (T : Trace independent) * Real.log (traceMass independent z E) :=
      (hQsum.subtype (fun T => T ∈ E)).mul_right _
    have hsummableG : Summable fun T : E =>
        Q (T : Trace independent) * Real.log (Q (T : Trace independent) /
          conditionedTraceWeight independent z E (T : Trace independent)) :=
      (h1.add h2).congr fun T => (hEqterm T).symm
    have hgibbs : 0 ≤ ∑' T : E, Q (T : Trace independent) *
        Real.log (Q (T : Trace independent) /
          conditionedTraceWeight independent z E (T : Trace independent)) := by
      refine discreteRelativeEntropy_nonneg
        (fun T : E => Q (T : Trace independent))
        (fun T : E => conditionedTraceWeight independent z E (T : Trace independent))
        (fun T => hQ0 _)
        (fun T => conditionedTraceWeight_pos independent hsymm Δ hdegree hz0 hz hE T.2)
        (hQsum.subtype _)
        ((summable_conditionedTraceWeight independent hsymm Δ hdegree hz0.le hz E).subtype _)
        ?_ ?_ hsummableG
      · rw [tsum_subtype_eq_of_support_subset hsupp, hQtot]
      · refine (tsum_subtype_eq_of_support_subset ?_).trans
          (tsum_conditionedTraceWeight independent hsymm Δ hdegree hz0.le hz hE)
        intro T hT
        by_contra hTE
        exact hT (conditionedTraceWeight_eq_zero independent z hTE)
    have hcongr : (∑' T : E, Q (T : Trace independent) *
          Real.log (Q (T : Trace independent) /
            conditionedTraceWeight independent z E (T : Trace independent))) =
        ∑' T : E, (Q (T : Trace independent) * Real.log (Q (T : Trace independent) /
            traceWeight independent z (T : Trace independent)) +
          Q (T : Trace independent) * Real.log (traceMass independent z E)) :=
      tsum_congr hEqterm
    have hadd : (∑' T : E, (Q (T : Trace independent) * Real.log (Q (T : Trace independent) /
            traceWeight independent z (T : Trace independent)) +
          Q (T : Trace independent) * Real.log (traceMass independent z E))) =
        (∑' T : E, Q (T : Trace independent) * Real.log (Q (T : Trace independent) /
            traceWeight independent z (T : Trace independent))) +
          ∑' T : E, Q (T : Trace independent) * Real.log (traceMass independent z E) :=
      h1.tsum_add h2
    have hconst : (∑' T : E, Q (T : Trace independent) *
        Real.log (traceMass independent z E)) = Real.log (traceMass independent z E) := by
      rw [tsum_mul_right, tsum_subtype_eq_of_support_subset hsupp, hQtot, one_mul]
    have hsplit : (∑' T : E, Q (T : Trace independent) *
        Real.log (Q (T : Trace independent) /
          traceWeight independent z (T : Trace independent))) =
        (∑' T : E, Q (T : Trace independent) * Real.log (Q (T : Trace independent) /
          conditionedTraceWeight independent z E (T : Trace independent))) -
          Real.log (traceMass independent z E) := by
      rw [hcongr, hadd, hconst]
      ring
    rw [preparationAction, causalAccessibility, discreteRelativeEntropy,
      ← tsum_subtype_eq_of_support_subset hsuppD, hsplit]
    linarith

end PreparationEntropy

end GaloisForLFunctions.RHTower
