import GaloisForLFunctions.HTGeometry.GomesHausdorffReflection
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Uniform compact sources and endpoint-power integrability

A canonical atom-free finite source on the corpus's compact Hausdorff interval. Exact transport
between subtype volume and ordinary interval integration supplies the endpoint-power boundary.
This infrastructure tests the reconstruction obstructions in the arXiv:2607.24901 experiments
on genuinely diffuse sources, beyond finite atomic examples.
-/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- Lebesgue probability measure on the corpus's compact interval. -/
def gomesHausdorffUniformSource : FiniteMeasure HausdorffSourceSpace := ⟨volume, inferInstance⟩

/-- The canonical diffuse source has unit total mass. -/
theorem gomesHausdorffUniformSource_mass : gomesHausdorffUniformSource.mass = 1 := by
  change (volume (Set.univ : Set HausdorffSourceSpace)).toNNReal = 1
  simp

/-- Every singleton has zero mass, including both compactification endpoints. -/
theorem gomesHausdorffUniformSource_singleton (y : HausdorffSourceSpace) :
    gomesHausdorffUniformSource {y} = 0 := by
  change (volume ({y} : Set HausdorffSourceSpace)).toNNReal = 0
  simp

/-- The diffuse source is nonzero despite assigning zero mass to every point. -/
theorem gomesHausdorffUniformSource_ne_zero : gomesHausdorffUniformSource ≠ 0 := by
  intro h
  have hm := congrArg FiniteMeasure.mass h
  rw [gomesHausdorffUniformSource_mass] at hm
  simp at hm

/-- Embedding the compact source into the real line gives restricted Lebesgue measure. -/
theorem gomesHausdorffUniformSource_map_coe :
    Measure.map (fun y : HausdorffSourceSpace => (y : ℝ))
      (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) =
      volume.restrict (Set.Icc (0 : ℝ) 1) := unitInterval.measurePreserving_coe.map_eq

/-- Integrability on the compact corpus source is exactly real interval integrability. -/
theorem gomesHausdorffUniformSource_integrable_coe_iff (f : ℝ → ℝ) :
    Integrable (fun y : HausdorffSourceSpace => f y)
      (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) ↔
      IntegrableOn f (Set.Icc (0 : ℝ) 1) := by
  have h := unitInterval.measurableEmbedding_coe.integrable_map_iff
    (μ := (gomesHausdorffUniformSource : Measure HausdorffSourceSpace)) (g := f)
  rw [gomesHausdorffUniformSource_map_coe] at h
  exact h.symm

/-- Arbitrary real integrals transfer through the subtype embedding exactly. -/
theorem gomesHausdorffUniformSource_integral_coe (f : ℝ → ℝ) :
    (∫ y : HausdorffSourceSpace, f y ∂(gomesHausdorffUniformSource : Measure HausdorffSourceSpace)) =
      ∫ x in Set.Icc (0 : ℝ) 1, f x := by
  have h := unitInterval.measurableEmbedding_coe.integral_map
    (μ := (gomesHausdorffUniformSource : Measure HausdorffSourceSpace)) f
  rw [gomesHausdorffUniformSource_map_coe] at h
  exact h.symm

/-- The corpus's reflection preserves the uniform source measure. -/
theorem gomesHausdorffUniformSource_reflection_map :
    Measure.map gomesHausdorffReflection (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) =
      (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) := by
  have hf : (gomesHausdorffReflection : HausdorffSourceSpace → HausdorffSourceSpace) =
      unitInterval.symm := by
    funext y
    apply Subtype.ext
    rfl
  rw [hf]
  exact unitInterval.measurePreserving_symm.map_eq

/-- The source-level reflection fixes the canonical diffuse source. -/
theorem gomesHausdorffUniformSource_reflected :
    gomesHausdorffReflectSource gomesHausdorffUniformSource = gomesHausdorffUniformSource := by
  apply FiniteMeasure.toMeasure_injective
  exact gomesHausdorffUniformSource_reflection_map

/-- Reflection transports integrability without a measurability premise on the test. -/
theorem gomesHausdorffUniformSource_integrable_reflection_iff (f : HausdorffSourceSpace → ℝ) :
    Integrable (fun y => f (gomesHausdorffReflection y))
      (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) ↔
      Integrable f (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) := by
  have h := gomesHausdorffReflection.measurableEmbedding.integrable_map_iff
    (μ := (gomesHausdorffUniformSource : Measure HausdorffSourceSpace)) (g := f)
  rw [gomesHausdorffUniformSource_reflection_map] at h
  exact h.symm

/-- The complete power-integrability boundary at the zero endpoint. -/
theorem gomesHausdorffUniformSource_rpow_integrable_iff (a : ℝ) :
    Integrable (fun y : HausdorffSourceSpace => (y : ℝ) ^ a)
      (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) ↔ -1 < a := by
  rw [gomesHausdorffUniformSource_integrable_coe_iff (fun x : ℝ => x ^ a),
    integrableOn_Icc_iff_integrableOn_Ioo]
  exact intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one

/-- Reflection gives the complete power-integrability boundary at the Clark blind endpoint. -/
theorem gomesHausdorffUniformSource_complement_rpow_integrable_iff (a : ℝ) :
    Integrable (fun y : HausdorffSourceSpace => (1 - (y : ℝ)) ^ a)
      (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) ↔ -1 < a := by
  have h := gomesHausdorffUniformSource_integrable_reflection_iff
    (fun y : HausdorffSourceSpace => (y : ℝ) ^ a)
  change Integrable (fun y : HausdorffSourceSpace => (1 - (y : ℝ)) ^ a)
    (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) ↔ _ at h
  exact h.trans (gomesHausdorffUniformSource_rpow_integrable_iff a)

/-- The inverse coordinate is not integrable against the atom-free source. -/
theorem gomesHausdorffUniformSource_not_integrable_inverse :
    ¬ Integrable (fun y : HausdorffSourceSpace => (y : ℝ)⁻¹)
      (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) := by
  have h := gomesHausdorffUniformSource_rpow_integrable_iff (-1)
  simpa only [Real.rpow_neg_one, lt_self_iff_false, iff_false] using h

/-- The reciprocal distance to the blind endpoint is not integrable either. -/
theorem gomesHausdorffUniformSource_not_integrable_complement_inverse :
    ¬ Integrable (fun y : HausdorffSourceSpace => (1 - (y : ℝ))⁻¹)
      (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) := by
  have h := gomesHausdorffUniformSource_complement_rpow_integrable_iff (-1)
  simpa only [Real.rpow_neg_one, lt_self_iff_false, iff_false] using h

end GaloisForLFunctions.HTGeometry
