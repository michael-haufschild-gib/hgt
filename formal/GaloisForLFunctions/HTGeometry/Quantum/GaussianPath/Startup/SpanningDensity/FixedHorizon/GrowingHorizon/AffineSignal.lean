import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GrowingHorizon.GaussianFields
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.AffineSignal

/-! # Detecting an affine physical signal through an increasing time horizon -/
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
private abbrev Op (κ : Type*) := Matrix κ κ ℂ

/-- A calibrated physical signal survives release of all local fields
at threshold s^L, uniformly over the exterior and the register size. -/
theorem geometric_affine_signal (m : ℕ) (a : ℝ) {h η : ℝ} (hh : 0 < h) (hη : 0 < η) :
    ∃ s > 0, ∀ L : ℕ, 0 < L → ∀ (κ : Type*) [Fintype κ] [DecidableEq κ] [Nonempty κ],
      ∀ (H Y B : Op κ) (P : Fin m → Op κ),
      IsSelfAdjoint H → Y.IsHermitian → B.IsHermitian → ‖Y‖ ≤ 1 → ‖B‖ ≤ 1 →
      (∀ i, IsSelfAdjoint (P i)) → (∀ i, ‖P i‖ ≤ 1) →
      ∀ t : ℝ, |t| ≤ L → ∀ u : Fin m → ℝ, (∀ i, |u i| ≤ a) →
      h^L ≤ |signal (affineHamiltonian H P u) Y B t| →
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1))
        {x | |signal (affineHamiltonian H P x) Y B t| ≤ s^L} ≤ ENNReal.ofReal η := by
  obtain ⟨s,hs,hf⟩ := geometric_gaussian_fields m a hh hη
  refine ⟨s,hs,?_⟩
  intro L hL κ _ _ _ H Y B P hH hY hB hYn hBn hP hPn t ht u hu hcal
  exact hf L hL _ (continuous_signal_fields H P Y B t)
    (entire_signal_fields H Y B P hH hY hB hYn hBn hP hPn ht) u hu hcal

#print axioms geometric_affine_signal
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
