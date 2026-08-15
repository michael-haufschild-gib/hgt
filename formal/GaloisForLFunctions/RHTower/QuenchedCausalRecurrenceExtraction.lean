import GaloisForLFunctions.RHTower.QuenchedCausalReplicaIncidence

/-!
# Exact extraction of the common recurrence sector

The empty circuit heap carries a positive Boltzmann mass, and it succeeds at a state exactly when
the state already lies in the robust target.  Hence the causal accessibility equals one precisely on
the target, and is bounded away from one by the mass of the empty heap everywhere else.

Consequently the quenched causal replica mass is squeezed between the source mass of the recurrence
sector and that mass plus a geometrically decaying remainder, so the replica limit is exactly the
recurrence mass.  Removing that one sector is therefore necessary and sufficient for the replica
mass to vanish in the replica limit.
-/

open MeasureTheory Filter Topology

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

section RecurrenceExtraction

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

theorem traceLaw_singleton (independent : α → α → Prop) (z : ℝ) (u : Trace independent) :
    traceLaw independent z {u} = ENNReal.ofReal (traceWeight independent z u) := by
  classical
  rw [traceLaw_apply, tsum_subtype ({u} : Set (Trace independent))
    fun T => ENNReal.ofReal (traceWeight independent z T),
    tsum_eq_single u fun T hT => Set.indicator_of_notMem (by simpa using hT) _,
    Set.indicator_of_mem (Set.mem_singleton u)]

theorem traceWeight_one_pos (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) :
    0 < traceWeight independent z (1 : Trace independent) := by
  rw [traceWeight, traceLen_one, pow_zero]
  exact div_pos one_pos (tracePartition_pos independent hsymm Δ hdegree hz0 hz)

theorem traceWeight_one_le_one (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) :
    traceWeight independent z (1 : Trace independent) ≤ 1 := by
  rw [traceWeight, traceLen_one, pow_zero,
    div_le_one (tracePartition_pos independent hsymm Δ hdegree hz0 hz)]
  exact one_le_tracePartition independent hsymm Δ hdegree hz0 hz

/-- **Isolation of the recurrence mass.**  Outside the robust target the causal accessibility loses
at least the Boltzmann mass of the empty heap. -/
theorem causalAccessibility_add_traceWeight_one_le_one (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1)
    {S : Trace independent → Set X} {y : X} (hy : y ∉ S 1) :
    causalAccessibility independent z S y + traceWeight independent z (1 : Trace independent)
      ≤ 1 := by
  haveI hprob : IsProbabilityMeasure (traceLaw independent z) :=
    isProbabilityMeasure_traceLaw independent hsymm Δ hdegree hz0 hz
  have hdisj : Disjoint (causalSuccessEvent independent S y)
      ({1} : Set (Trace independent)) := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨u, hu, hyu⟩
    exact hy (by rw [← eq_one_of_tracePrefix_one independent hu]; exact hyu)
  have hle : traceLaw independent z (causalSuccessEvent independent S y) +
      traceLaw independent z ({1} : Set (Trace independent)) ≤ 1 := by
    rw [← measure_union hdisj (measurableSet_trace independent _)]
    exact prob_le_one
  rw [traceLaw_causalSuccessEvent independent hsymm Δ hdegree hz0 hz, traceLaw_singleton,
    ← ENNReal.ofReal_add
      (causalAccessibility_nonneg independent hsymm Δ hdegree hz0 hz S y)
      (traceWeight_one_pos independent hsymm Δ hdegree hz0 hz).le] at hle
  exact ENNReal.ofReal_le_one.mp hle

/-- **Exact recurrence value.**  The causal accessibility equals one exactly at the robust
target. -/
theorem causalAccessibility_eq_one_iff (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1)
    (S : Trace independent → Set X) (y : X) :
    causalAccessibility independent z S y = 1 ↔ y ∈ S 1 := by
  refine ⟨fun h => ?_, causalAccessibility_eq_one independent hsymm Δ hdegree hz0 hz⟩
  by_contra hy
  have hb := causalAccessibility_add_traceWeight_one_le_one independent hsymm Δ hdegree hz0 hz hy
  have hp := traceWeight_one_pos independent hsymm Δ hdegree hz0 hz
  rw [h] at hb
  linarith

/-- **Recurrence lower bound.**  The quenched replica mass is at least the source mass of the
recurrence sector. -/
theorem measureReal_recurrent_le_quenchedActionReplicaMass (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1)
    {S : Trace independent → Set X} (hS : ∀ u, MeasurableSet (S u)) {x : Ω → X}
    (hx : Measurable x) (ρ : Measure Ω) [IsProbabilityMeasure ρ] (r : ℕ) :
    ρ.real (x ⁻¹' S 1) ≤
      quenchedActionReplicaMass ρ (fun H => causalAccessibility independent z S (x H)) r := by
  classical
  have hA : MeasurableSet (x ⁻¹' S 1) := hx (hS 1)
  have hpoint : ∀ H : Ω, Set.indicator (x ⁻¹' S 1) (1 : Ω → ℝ) H ≤
      causalAccessibility independent z S (x H) ^ r := by
    intro H
    by_cases hH : H ∈ x ⁻¹' S 1
    · rw [Set.indicator_of_mem hH, Pi.one_apply,
        causalAccessibility_eq_one independent hsymm Δ hdegree hz0 hz hH, one_pow]
    · rw [Set.indicator_of_notMem hH]
      exact pow_nonneg (causalAccessibility_nonneg independent hsymm Δ hdegree hz0 hz S (x H)) r
  have hindint : Integrable (Set.indicator (x ⁻¹' S 1) (1 : Ω → ℝ)) ρ := by
    rw [integrable_indicator_iff hA]
    exact integrableOn_const (by simp [measure_ne_top])
  have hmono := integral_mono hindint
    (integrable_causalAccessibility_pow independent hsymm Δ hdegree hz0 hz hS hx ρ r) hpoint
  rwa [integral_indicator_one hA] at hmono

/-- **Recurrence upper bound.**  Off the recurrence sector the replica mass decays geometrically in
the replica order. -/
theorem quenchedActionReplicaMass_le_recurrent_add (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1)
    {S : Trace independent → Set X} (hS : ∀ u, MeasurableSet (S u)) {x : Ω → X}
    (hx : Measurable x) (ρ : Measure Ω) [IsProbabilityMeasure ρ] (r : ℕ) :
    quenchedActionReplicaMass ρ (fun H => causalAccessibility independent z S (x H)) r ≤
      ρ.real (x ⁻¹' S 1) +
        ρ.real ((x ⁻¹' S 1)ᶜ) *
          (1 - traceWeight independent z (1 : Trace independent)) ^ r := by
  classical
  have hA : MeasurableSet (x ⁻¹' S 1) := hx (hS 1)
  have hp1 := traceWeight_one_le_one independent hsymm Δ hdegree hz0 hz
  have hpoint : ∀ H : Ω, causalAccessibility independent z S (x H) ^ r ≤
      Set.indicator (x ⁻¹' S 1) (1 : Ω → ℝ) H +
        (1 - traceWeight independent z (1 : Trace independent)) ^ r *
          Set.indicator ((x ⁻¹' S 1)ᶜ) (1 : Ω → ℝ) H := by
    intro H
    by_cases hH : H ∈ x ⁻¹' S 1
    · rw [Set.indicator_of_mem hH, Pi.one_apply, Set.indicator_of_notMem (by simpa using hH),
        mul_zero, add_zero]
      exact pow_le_one₀
        (causalAccessibility_nonneg independent hsymm Δ hdegree hz0 hz S (x H))
        (causalAccessibility_le_one independent hsymm Δ hdegree hz0 hz S (x H))
    · rw [Set.indicator_of_notMem hH, Set.indicator_of_mem (by simpa using hH), Pi.one_apply,
        mul_one, zero_add]
      have hb := causalAccessibility_add_traceWeight_one_le_one independent hsymm Δ hdegree hz0 hz
        (S := S) (y := x H) hH
      exact pow_le_pow_left₀
        (causalAccessibility_nonneg independent hsymm Δ hdegree hz0 hz S (x H))
        (by linarith) r
  have hind1 : Integrable (Set.indicator (x ⁻¹' S 1) (1 : Ω → ℝ)) ρ := by
    rw [integrable_indicator_iff hA]
    exact integrableOn_const (by simp [measure_ne_top])
  have hind2 : Integrable (Set.indicator ((x ⁻¹' S 1)ᶜ) (1 : Ω → ℝ)) ρ := by
    rw [integrable_indicator_iff hA.compl]
    exact integrableOn_const (by simp [measure_ne_top])
  have hmono := integral_mono
    (integrable_causalAccessibility_pow independent hsymm Δ hdegree hz0 hz hS hx ρ r)
    (hind1.add (hind2.const_mul _)) hpoint
  simp only [Pi.add_apply] at hmono
  rwa [integral_add hind1 (hind2.const_mul _), integral_const_mul, integral_indicator_one hA,
    integral_indicator_one hA.compl, mul_comm] at hmono

/-- **Exact replica limit.**  The quenched replica mass converges to the source mass of the
recurrence sector. -/
theorem tendsto_quenchedActionReplicaMass_recurrent (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1)
    {S : Trace independent → Set X} (hS : ∀ u, MeasurableSet (S u)) {x : Ω → X}
    (hx : Measurable x) (ρ : Measure Ω) [IsProbabilityMeasure ρ] :
    Tendsto
      (fun r : ℕ => quenchedActionReplicaMass ρ (fun H => causalAccessibility independent z S (x H)) r)
      atTop (𝓝 (ρ.real (x ⁻¹' S 1))) := by
  have hp0 := traceWeight_one_pos independent hsymm Δ hdegree hz0 hz
  have hp1 := traceWeight_one_le_one independent hsymm Δ hdegree hz0 hz
  have hgeom : Tendsto
      (fun r : ℕ => (1 - traceWeight independent z (1 : Trace independent)) ^ r) atTop (𝓝 0) := by
    refine tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have hupper : Tendsto
      (fun r : ℕ => ρ.real (x ⁻¹' S 1) +
        ρ.real ((x ⁻¹' S 1)ᶜ) *
          (1 - traceWeight independent z (1 : Trace independent)) ^ r)
      atTop (𝓝 (ρ.real (x ⁻¹' S 1))) := by
    have := (hgeom.const_mul (ρ.real ((x ⁻¹' S 1)ᶜ))).const_add (ρ.real (x ⁻¹' S 1))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun r => measureReal_recurrent_le_quenchedActionReplicaMass independent hsymm Δ hdegree hz0 hz
      hS hx ρ r)
    (fun r => quenchedActionReplicaMass_le_recurrent_add independent hsymm Δ hdegree hz0 hz hS hx ρ r)

end RecurrenceExtraction

end

end GaloisForLFunctions.RHTower
