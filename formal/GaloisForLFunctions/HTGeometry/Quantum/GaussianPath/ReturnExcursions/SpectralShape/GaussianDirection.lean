import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Forecasts.Sections

/-! # Gaussian sublevel bounds along a fixed physical direction -/

open MeasureTheory ProbabilityTheory WithLp Set
open scoped ENNReal InnerProductSpace
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
noncomputable section

/-- A uniform one-dimensional Gaussian price on the lines parallel to a unit
coupling direction also bounds the full disorder probability. Reflection sends
one resampled coordinate to the prescribed direction. -/
theorem gaussian_line_price {I : Type*} [Fintype I] [DecidableEq I] (i : I)
    (v : EuclideanSpace ℝ I) (hv : ‖v‖=1) (S : Set (EuclideanSpace ℝ I))
    (hS : MeasurableSet S) (b : ℝ≥0∞)
    (hline : ∀ y : EuclideanSpace ℝ I, gaussianReal 0 1 {x : ℝ | y+x • v∈S} ≤ b) :
    stdGaussian (EuclideanSpace ℝ I) S ≤ b := by
  obtain ⟨Y,hY⟩ := gaussian_sections i v hv
  rw [hY S hS]
  exact (lintegral_mono (fun h => hline (Y h))).trans_eq (by simp)

#print axioms gaussian_line_price
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
