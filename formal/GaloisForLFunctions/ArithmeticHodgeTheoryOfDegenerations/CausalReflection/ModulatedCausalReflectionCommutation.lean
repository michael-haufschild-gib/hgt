import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ModulatedCausalReflectionEnergy

/-!
# Commutation of actual complex-rate reflections

Each reflection acts by a scalar Fourier multiplier. Fourier uniqueness
on actual L¹ profiles therefore makes two reflections commute almost everywhere.
-/

noncomputable section
open MeasureTheory Filter FourierTransform

namespace GaloisForLFunctions.HTGeometry
open _root_.RHTower

/-- The complex-rate reflection has the translated real-rate inner multiplier. -/
theorem fourier_modulatedCausalReflection {a : ℝ} (ha : 0 < a) (b : ℝ)
    {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    𝓕 (modulatedCausalReflection a b f) ξ =
      (((a : ℂ) - 2 * Complex.I * (ξ + b)) /
        ((a : ℂ) + 2 * Complex.I * (ξ + b))) * 𝓕 f ξ := by
  rw [modulatedCausalReflection_eq_conjugate, fourier_causalModulation,
    fourier_causalBlaschkeStep ha (integrable_causalModulation b hf),
    fourier_causalModulation, sub_neg_eq_add, add_sub_cancel_right]
  simp only [Complex.ofReal_add]

/-- Actual integrable reflections commute because their Fourier multipliers do. -/
theorem modulatedCausalReflections_commute_ae {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (b d : ℝ) {f : ℝ → ℂ} (hf : Integrable f) :
    modulatedCausalReflection a b (modulatedCausalReflection c d f) =ᵐ[volume]
      modulatedCausalReflection c d (modulatedCausalReflection a b f) := by
  apply _root_.HTGeometry.ae_eq_of_fourierIntegral_eq
    (integrable_modulatedCausalReflection ha b (integrable_modulatedCausalReflection hc d hf))
    (integrable_modulatedCausalReflection hc d (integrable_modulatedCausalReflection ha b hf))
  intro ξ
  rw [fourier_modulatedCausalReflection ha b (integrable_modulatedCausalReflection hc d hf),
    fourier_modulatedCausalReflection hc d hf,
    fourier_modulatedCausalReflection hc d (integrable_modulatedCausalReflection ha b hf),
    fourier_modulatedCausalReflection ha b hf]
  ring

end GaloisForLFunctions.HTGeometry
