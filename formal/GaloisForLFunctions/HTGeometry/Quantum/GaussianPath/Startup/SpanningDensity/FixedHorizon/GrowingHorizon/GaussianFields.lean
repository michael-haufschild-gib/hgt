import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GrowingHorizon.FieldBox
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GaussianFields

/-! # A geometric detection threshold for unrestricted Gaussian fields -/
open MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

/-- A fixed number of Gaussian coordinates preserves a threshold of the
form s^L on all but a prescribed fraction of coefficient vectors. -/
theorem geometric_gaussian_fields (n : ℕ) (a : ℝ) {h η : ℝ} (hh : 0 < h) (hη : 0 < η) :
    ∃ s > 0, ∀ L : ℕ, 0 < L → ∀ F : (Fin n → ℝ) → ℝ, Continuous F →
      (∀ i, EntireFieldSlice F (fun R => Real.exp (2*L*R)) i) →
      ∀ u : Fin n → ℝ, (∀ i, |u i| ≤ a) → h^L ≤ |F u| →
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) {x | |F x| ≤ s^L} ≤ ENNReal.ofReal η := by
  obtain ⟨b,δ,hb,ha,hδ,hbox⟩ := gaussian_box_tolerance n a hη
  obtain ⟨s,hs,hf⟩ := geometric_field_box n hb hh hδ
  exact ⟨s,hs,fun L hL F hc hslice u hu hcal =>
    hbox _ (hf L hL F hc hslice u (fun i => (hu i).trans ha) hcal)⟩

#print axioms geometric_gaussian_fields
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
