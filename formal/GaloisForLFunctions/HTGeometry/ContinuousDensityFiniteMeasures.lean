import GaloisForLFunctions.HTGeometry.CompactMonoidMeasureAlgebra
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral

/-!
# Finite measures from continuous nonnegative densities

On a compact space a continuous density has finite mass. Nonnegative
densities preserve the expected weighted-integral and total-mass identities.
-/

open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- A continuous real density on a compact space defines a finite measure. -/
def continuousDensityFiniteMeasure (μ : FiniteMeasure X) (f : C(X, ℝ)) : FiniteMeasure X :=
  ⟨(μ : Measure X).withDensity (fun x => ENNReal.ofReal (f x)),
    isFiniteMeasure_withDensity_ofReal
      (f.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).hasFiniteIntegral⟩

/-- Integration against a nonnegative continuous density is weighted integration. -/
theorem integral_continuousDensityFiniteMeasure (μ : FiniteMeasure X)
    (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) (g : C(X, ℂ)) :
    (∫ x, g x ∂(continuousDensityFiniteMeasure μ f : Measure X)) =
      ∫ x, (f x : ℂ) * g x ∂(μ : Measure X) := by
  change (∫ x, g x ∂(μ : Measure X).withDensity (fun x => ENNReal.ofReal (f x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul f.continuous.measurable.ennreal_ofReal
    (by simp : ∀ᵐ x ∂(μ : Measure X), ENNReal.ofReal (f x) < ∞)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp only [ENNReal.toReal_ofReal (hf x), Complex.real_smul])

/-- The mass is the integral of the density. -/
theorem mass_continuousDensityFiniteMeasure (μ : FiniteMeasure X)
    (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    ((continuousDensityFiniteMeasure μ f).mass : ℝ) = ∫ x, f x ∂(μ : Measure X) := by
  rw [MeasureAlgebra.mass_eq_real]
  have h : (∫ _x, (1 : ℝ) ∂(continuousDensityFiniteMeasure μ f : Measure X)) =
      ∫ x, f x ∂(μ : Measure X) := by
    change (∫ _x, (1 : ℝ) ∂(μ : Measure X).withDensity (fun x => ENNReal.ofReal (f x))) = _
    rw [integral_withDensity_eq_integral_toReal_smul f.continuous.measurable.ennreal_ofReal
      (by simp : ∀ᵐ x ∂(μ : Measure X), ENNReal.ofReal (f x) < ∞)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [ENNReal.toReal_ofReal (hf x), smul_eq_mul, mul_one])
  simpa only [integral_const, smul_eq_mul, mul_one] using h

end

end GaloisForLFunctions.HTGeometry
