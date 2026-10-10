import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Finite.Law
import GaloisForLFunctions.HTGeometry.CountableRelativeEntropyValue
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Finite observations as literal probability laws

A finite observation of an arbitrary probability measure gives a paper finite
law with the exact cell masses. Its expectations are the original integrals,
and coarsening the observation is exactly the finite-law pushforward.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory FourierLLogL
open scoped BigOperators

variable {Ω α β : Type*} [MeasurableSpace Ω]
  [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- The exact atom masses of a probability measure on a finite space. -/
def paperFiniteMeasureLaw (μ : ProbabilityMeasure α) : Law α :=
  ⟨fun a => (μ : Measure α).real {a}, fun _ => measureReal_nonneg, by
    simpa using (sum_measureReal_singleton (μ := (μ : Measure α)) Finset.univ)⟩

theorem paperFiniteMeasureLaw_apply (μ : ProbabilityMeasure α) (a : α) :
    paperFiniteMeasureLaw μ a = (μ : Measure α).real {a} := rfl

/-- Every finite-law expectation is exactly its measure-theoretic integral. -/
theorem paperFiniteMeasureLaw_Ex (μ : ProbabilityMeasure α) (g : α → ℝ) :
    (paperFiniteMeasureLaw μ).Ex g = ∫ a, g a ∂(μ : Measure α) := by
  have hi : Integrable g (μ : Measure α) :=
    integrable_of_summable_singleton_weighted g (hasSum_fintype _).summable
  simpa only [Law.Ex, paperFiniteMeasureLaw_apply, smul_eq_mul] using
    (integral_fintype hi).symm

/-- A finite measurable observation, retaining its actual source cell masses. -/
def paperFiniteObservationLaw (μ : ProbabilityMeasure Ω) (f : SimpleFunc Ω α) : Law α :=
  paperFiniteMeasureLaw (μ.map f.aemeasurable)

theorem paperFiniteObservationLaw_apply (μ : ProbabilityMeasure Ω) (f : SimpleFunc Ω α) (a : α) :
    paperFiniteObservationLaw μ f a = (μ : Measure Ω).real (f ⁻¹' {a}) := by
  change (((μ : Measure Ω).map f) {a}).toReal = _
  rw [Measure.map_apply f.measurable (measurableSet_singleton a)]
  rfl

theorem paperFiniteObservationLaw_Ex (μ : ProbabilityMeasure Ω) (f : SimpleFunc Ω α) (g : α → ℝ) :
    (paperFiniteObservationLaw μ f).Ex g = ∫ x, g (f x) ∂(μ : Measure Ω) := by
  rw [paperFiniteObservationLaw, paperFiniteMeasureLaw_Ex]
  exact integral_map f.aemeasurable (Measurable.of_discrete.aestronglyMeasurable)

/-- Coarsening observations commutes exactly with the paper's finite-law pushforward. -/
theorem paperFiniteObservationLaw_send (μ : ProbabilityMeasure Ω) (f : SimpleFunc Ω α) (g : α → β) :
    paperFiniteObservationLaw μ (f.map g) = (paperFiniteObservationLaw μ f).send g := by
  apply Law.ext_of_Ex
  intro v
  rw [Law.Ex_send, paperFiniteObservationLaw_Ex, paperFiniteObservationLaw_Ex]
  rfl

end
end GaloisForLFunctions.HTGeometry
