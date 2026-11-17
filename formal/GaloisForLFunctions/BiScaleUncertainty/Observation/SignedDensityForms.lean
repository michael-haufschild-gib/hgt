import GaloisForLFunctions.BiScaleUncertainty.Observation.BoundedCoordinateSignCone

/-!
# Positive carriers for signed density forms

An integrable signed density factors into a finite positive measure and a
bounded sign multiplier. The factorization preserves every quadratic integral.
-/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.Observation

/-- Positive measure carrying the absolute value of a real density. -/
def absoluteDensityMeasure (μ : Measure ℝ) (f : ℝ → ℝ) : Measure ℝ :=
  μ.withDensity (fun x => ENNReal.ofReal |f x|)

/-- The bounded sign multiplier of a real density; the zero set is assigned sign one. -/
def densitySign (f : ℝ → ℝ) (x : ℝ) : ℝ := if 0 ≤ f x then 1 else -1

/-- An integrable real density gives a finite positive carrier measure. -/
theorem absoluteDensityMeasure_finite {μ : Measure ℝ} {f : ℝ → ℝ} (hf : Integrable f μ) :
    IsFiniteMeasure (absoluteDensityMeasure μ f) :=
  isFiniteMeasure_withDensity_ofReal hf.abs.hasFiniteIntegral

/-- The sign multiplier is bounded in the absolute-density measure. -/
theorem densitySign_memLp (μ : Measure ℝ) {f : ℝ → ℝ} (hfm : Measurable f) :
    MemLp (densitySign f) ∞ (absoluteDensityMeasure μ f) := by
  have hm : Measurable (densitySign f) := Measurable.ite
    (measurableSet_le measurable_const hfm) measurable_const measurable_const
  apply memLp_top_of_bound hm.aestronglyMeasurable 1
  filter_upwards [] with x
  dsimp only [densitySign]
  split_ifs <;> norm_num

/-- The sign multiplier exactly restores the original signed density in every integral. -/
theorem integral_densitySign (μ : Measure ℝ) {f : ℝ → ℝ} (hfm : Measurable f) (g : ℝ → ℝ) :
    (∫ x, g x * densitySign f x ∂absoluteDensityMeasure μ f) = ∫ x, g x * f x ∂μ := by
  rw [absoluteDensityMeasure, integral_withDensity_eq_integral_toReal_smul (μ := μ)
    (show Measurable (fun x => ENNReal.ofReal |f x|) from ENNReal.measurable_ofReal.comp hfm.abs) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]
  dsimp only [densitySign]
  split_ifs with hx
  · rw [abs_of_nonneg hx]
    ring
  · rw [abs_of_neg (lt_of_not_ge hx)]
    ring

/-- Almost-everywhere coordinate bounds pass to the positive carrier measure. -/
theorem ae_absoluteDensityMeasure {μ : Measure ℝ} (f : ℝ → ℝ) {p : ℝ → Prop}
    (hp : ∀ᵐ x ∂μ, p x) : ∀ᵐ x ∂absoluteDensityMeasure μ f, p x :=
  (withDensity_absolutelyContinuous μ (fun x => ENNReal.ofReal |f x|)).ae_le hp

#print axioms integral_densitySign
end GaloisForLFunctions.BiScaleUncertainty.Observation
