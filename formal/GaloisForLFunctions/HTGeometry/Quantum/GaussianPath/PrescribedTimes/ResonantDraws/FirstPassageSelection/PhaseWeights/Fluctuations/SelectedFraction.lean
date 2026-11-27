import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.Fluctuations.PrefixMean
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.Fluctuations.BudgetSelection

/-! # A selected late test integrates the affordable fraction at its own budget -/
open Set MeasureTheory ProbabilityTheory Filter Topology Function
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
noncomputable section
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

/-- The Haar fraction at a measurable, prefix-dependent budget is an
integrable weight on the same Gaussian draw. -/
theorem integrable_selected_fraction (k : ℕ) (ε : ℝ) (j : (PrefixIndex (k+1)→ℝ)→ℕ) (hj : Measurable j) :
    let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
    Integrable (fun ω => prefixFraction k (j (X ω)) ε (X ω)) pathPauliDisorderLaw := by
  intro X
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  let f (p : (PrefixIndex (k+1)→ℝ)×ℕ) := prefixFraction k p.2 ε p.1
  have hf : Measurable f := measurable_from_prod_countable_left fun s => measurable_prefixFraction k s ε
  have hm := (hf.comp (measurable_id.prodMk hj)).comp (gaussian_pauli_prefix_coordinates_law (k+1)).measurable
  refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
  filter_upwards [ae_all_iff.mpr (fun s => prefixFraction_eq k s ε)] with ω hw
  change ‖prefixFraction k (j (X ω)) ε (X ω)‖≤1
  rw [hw _,Real.norm_of_nonneg (show 0 ≤ affordablePhaseMass k (j (X ω)) ε ω from measureReal_nonneg)]
  exact measureReal_le_one

/-- At either end of the first excursion, the limit for a budget
chosen from the draw is the selected integral of that draw's fraction.
A countable partition by budget also allows unbounded selectors. -/
theorem selected_fraction_limit (k P r : ℕ) (ε : ℝ) (j : (PrefixIndex (k+1)→ℝ)→ℕ)
    (hj : Measurable j) (B : Set (PrefixIndex (k+1)→ℝ)) (hB : MeasurableSet B) :
    let n := k+1
    let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let σ := crossingOrigin n P (9/80)
    let Δ := crossingWait n P r
    let p := ∫ ω in X ⁻¹' B, prefixFraction k (j (X ω)) ε (X ω) ∂pathPauliDisorderLaw
    Tendsto (fun t => μ.real (B ∩ {x | pathGateDistance n (j x) x (σ x+t)≤ε})) atTop (𝓝 p) ∧
      Tendsto (fun t => μ.real (B ∩ {x | pathGateDistance n (j x) x (σ x+Δ x+t)≤ε})) atTop (𝓝 p) := by
  intro n X μ σ Δ p
  let W := fun ω => prefixFraction k (j (X ω)) ε (X ω)
  let A (s : ℕ) := X ⁻¹' (B ∩ j ⁻¹' {s})
  have hX : Measurable X := (gaussian_pauli_prefix_coordinates_law n).measurable
  have hm s : MeasurableSet (A s) := (hB.inter ((measurableSet_singleton s).preimage hj)).preimage hX
  have hd : Pairwise (Disjoint on A) := fun s s' hn => Set.disjoint_left.mpr fun _ h₁ h₂ =>
    hn ((show j _=s from h₁.2).symm.trans h₂.2)
  have he : (⋃ s, A s) = X ⁻¹' B := by
    ext ω
    exact ⟨fun h => (mem_iUnion.mp h).elim fun _ hs => hs.1,
      fun h => mem_iUnion.mpr ⟨j (X ω),h,rfl⟩⟩
  have hp : p = ∑' s : ℕ, ∫ ω in A s, affordablePhaseMass k s ε ω ∂pathPauliDisorderLaw := by
    change (∫ ω in X ⁻¹' B, W ω ∂pathPauliDisorderLaw)=_
    rw [←he,integral_iUnion hm hd (integrable_selected_fraction k ε j hj).integrableOn]
    apply tsum_congr
    intro s
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ:=pathPauliDisorderLaw) (hm s),
      ae_restrict_of_ae (s:=A s) (prefixFraction_eq k s ε)] with ω hω hw
    change prefixFraction k (j (X ω)) ε (X ω)=affordablePhaseMass k s ε ω
    rw [show j (X ω)=s from hω.2]
    exact hw
  rw [hp]
  exact selected_random_budget k P r ε j hj B hB

#print axioms selected_fraction_limit
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
