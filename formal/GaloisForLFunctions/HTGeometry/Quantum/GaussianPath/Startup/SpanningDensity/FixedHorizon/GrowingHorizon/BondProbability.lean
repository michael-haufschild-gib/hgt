import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GrowingHorizon.BondSections
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.BondProbability

/-! # Bond detection for a frozen path on increasing horizons -/
open MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

/-- One exponential threshold works for all prefixes and every date
from a fixed positive onset through the integer horizon. -/
theorem geometric_bond_probability {a η : ℝ} (ha : 0 < a) (hη : 0 < η) :
    ∃ b > 0, ∀ L : ℕ, 0 < L → ∀ (n : ℕ) (e : Fin (n+1)) (t : ℝ), t∈Icc a (L:ℝ) →
      pathPauliDisorderLaw {ω | |bondSignal e (pathPauliDisorderShell ω n) t| ≤ b^L} ≤ ENNReal.ofReal η := by
  obtain ⟨b,hb,hs⟩ := geometric_bond_sections ha hη
  exact ⟨b,hb,fun L hL n e t ht =>
    bond_probability_of_sections e t (b^L) η (fun u => hs L hL n e u t ht)⟩

#print axioms geometric_bond_probability
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
