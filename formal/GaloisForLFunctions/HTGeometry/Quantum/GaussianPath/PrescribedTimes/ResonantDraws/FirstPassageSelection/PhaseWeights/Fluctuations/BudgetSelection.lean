import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.BudgetLaw

/-! # Late circuit tests at a budget chosen from the original disorder -/
open MeasureTheory ProbabilityTheory Set Filter Topology Function
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
open private real_union_sum from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.SetwiseLimit
noncomputable section

/-- Apply a different late test on each of a countable collection of
disjoint prefix selections. The original probability is a common summable
bound, including when the chosen budgets have no uniform bound. -/
theorem disjoint_selected_limit {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (A : ℕ→Set X) (hA : ∀ j, MeasurableSet (A j)) (hd : Pairwise (Disjoint on A))
    (E : ℕ→ℝ→Set X) (hE : ∀ j t, MeasurableSet (E j t)) (p : ℕ→ℝ)
    (h : ∀ j, Tendsto (fun t => μ.real (A j ∩ E j t)) atTop (𝓝 (p j))) :
    Tendsto (fun t => μ.real (⋃ j, A j ∩ E j t)) atTop (𝓝 (∑' j, p j)) := by
  have hs := summable_measure_toReal (μ:=μ) hA hd
  have hbound (t : ℝ) (j : ℕ) : ‖μ.real (A j ∩ E j t)‖ ≤ μ.real (A j) := by
    rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
    exact measureReal_mono inter_subset_left
  have hh := tendsto_tsum_of_dominated_convergence hs h (Eventually.of_forall hbound)
  apply hh.congr
  intro t
  exact (real_union_sum μ _ (fun i j hij => (hd hij).mono inter_subset_left inter_subset_left)
    (fun j => (hA j).inter (hE j t))).symm

private theorem selected_index_limit {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (B : Set X) (hB : MeasurableSet B) (j : X→ℕ) (hj : Measurable j)
    (E : ℕ→ℝ→Set X) (hm : ∀ s t, MeasurableSet (E s t)) (W : ℕ→ℝ)
    (h : ∀ s, Tendsto (fun t => μ.real ((B ∩ j ⁻¹' {s}) ∩ E s t)) atTop (𝓝 (W s))) :
    Tendsto (fun t => μ.real (B ∩ {x | x∈E (j x) t})) atTop (𝓝 (∑' s, W s)) := by
  let A (s : ℕ) := B ∩ j ⁻¹' {s}
  have hA s : MeasurableSet (A s) := hB.inter ((measurableSet_singleton s).preimage hj)
  have hd : Pairwise (Disjoint on A) := fun i s hn => Set.disjoint_left.mpr fun _ hi hs =>
    hn (hi.2.symm.trans hs.2)
  apply (disjoint_selected_limit μ A hA hd E hm W h).congr
  intro t
  apply congrArg μ.real
  ext x
  constructor
  · intro hx
    obtain ⟨s,hs,ht⟩ := mem_iUnion.mp hx
    refine ⟨hs.1,?_⟩
    change x∈E (j x) t
    rwa [show j x=s from hs.2]
  · rintro ⟨hb,hx⟩
    exact mem_iUnion.mpr ⟨j x,⟨hb,rfl⟩,hx⟩

/-- Even the observed gate budget may be chosen from the same draw and
its first-excursion history. The limiting probability integrates the
draw's Haar affordable fraction separately on each budget level. -/
theorem selected_random_budget (k P r : ℕ) (ε : ℝ) (j : (PrefixIndex (k+1)→ℝ)→ℕ)
    (hj : Measurable j) (B : Set (PrefixIndex (k+1)→ℝ)) (hB : MeasurableSet B) :
    let n := k+1
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
    let σ := crossingOrigin n P (9/80)
    let Δ := crossingWait n P r
    let p := ∑' s : ℕ, ∫ ω in X ⁻¹' (B ∩ j ⁻¹' {s}), affordablePhaseMass k s ε ω ∂pathPauliDisorderLaw
    Tendsto (fun t => μ.real (B ∩ {x | pathGateDistance n (j x) x (σ x+t)≤ε})) atTop (𝓝 p) ∧
    Tendsto (fun t => μ.real (B ∩ {x | pathGateDistance n (j x) x (σ x+Δ x+t)≤ε})) atTop (𝓝 p) := by
  intro n μ X σ Δ p
  let A (s : ℕ) := B ∩ j ⁻¹' {s}
  have hA s : MeasurableSet (A s) := hB.inter ((measurableSet_singleton s).preimage hj)
  let W s := ∫ ω in X ⁻¹' A s, affordablePhaseMass k s ε ω ∂pathPauliDisorderLaw
  have hbase s := gaussian_selected_budget_distribution k P r s ε (A s) (hA s)
  have assemble (o : (PrefixIndex n→ℝ)→ℝ) (ho : Measurable o)
      (h : ∀ s, Tendsto (fun t => μ.real (A s ∩ {x | pathGateDistance n s x (o x+t)≤ε})) atTop (𝓝 (W s))) :
      Tendsto (fun t => μ.real (B ∩ {x | pathGateDistance n (j x) x (o x+t)≤ε})) atTop (𝓝 p) := by
    let E s t := {x | pathGateDistance n s x (o x+t)≤ε}
    exact selected_index_limit μ B hB j hj E (fun s t => measurable_origin_event n s ε t o ho) W h
  exact ⟨assemble σ (measurable_crossingOrigin ..) (fun s => (hbase s).1),
    assemble (fun x => σ x+Δ x) ((measurable_crossingOrigin ..).add (measurable_crossingWait ..))
      (fun s => (hbase s).2)⟩

#print axioms selected_random_budget
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
