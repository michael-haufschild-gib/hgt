import Mathlib.Probability.Moments.Variance

/-! For square-integrable observables, zero variance is precisely an almost-everywhere constant. -/

open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

theorem variance_eq_zero_iff_ae_const {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {f : X → ℝ} (hf : MemLp f 2 μ) :
    variance f μ = 0 ↔ ∃ c : ℝ, ∀ᵐ x ∂μ, f x = c := by
  constructor
  · intro h
    exact ⟨∫ x, f x ∂μ, ae_eq_integral_of_variance_eq_zero hf h⟩
  · rintro ⟨c, hc⟩
    rw [variance_congr hc, variance_eq_integral aemeasurable_const]
    simp

end GaloisForLFunctions.HTGeometry
