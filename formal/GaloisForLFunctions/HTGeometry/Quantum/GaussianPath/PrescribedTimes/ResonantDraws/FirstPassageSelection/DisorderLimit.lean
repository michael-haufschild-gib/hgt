import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.SelectedLimit

/-! # Disorder limits after selecting samples by their first passages -/
open Set Filter MeasureTheory ProbabilityTheory Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
noncomputable section

/-- A radial occupation limit that is constant across draws remains
valid after selecting any expansion-closed measurable sample event. -/
theorem selected_snapshot_limit {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : Ω → (ι → ℝ))
    (hX : MeasurePreserving X P (Measure.pi fun _ : ι => gaussianReal 0 1))
    (B : Set (ι → ℝ)) (hB : MeasurableSet B) (hclosed : expansionClosed B)
    (E : ℝ → Set (ι → ℝ)) (hE : ∀ t, MeasurableSet (E t)) (p : ℝ)
    (h : ∀ b > (1:ℝ), ∀ᵐ ω ∂P, Tendsto (fun t => rayMass b (E t) (X ω)) atTop (𝓝 ((b-1)*p))) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    Tendsto (fun t => μ.real (B ∩ E t)) atTop (𝓝 (μ.real B*p)) := by
  intro μ
  have hw := weighted_selected_snapshot X hX B hB hclosed E hE (fun _ => p) h
  simpa only [setIntegral_const,smul_eq_mul,hX.measureReal_preimage hB.nullMeasurableSet] using hw

#print axioms selected_snapshot_limit
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
