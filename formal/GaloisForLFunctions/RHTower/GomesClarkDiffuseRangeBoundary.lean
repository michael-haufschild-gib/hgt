import GaloisForLFunctions.RHTower.GomesClarkEndpointPowerSources
import GaloisForLFunctions.RHTower.GomesClarkSourceReweighting
import GaloisForLFunctions.RHTower.GomesClarkCollapsedReconstruction

/-!
# Sharp diffuse obstruction to collapsed-anchor reconstruction

Uniform source data are atom-free but have infinite canonical inverse mass. More generally,
finite endpoint-power sources with exponents `-1 < a ≤ 0` cannot be realized at the collapsed
anchor. Every nonzero anchor realizes all finite reciprocal sources. These closed classifications
locate the exact reconstruction boundary in the arXiv:2607.24901-inspired corpus experiments.
-/

noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

namespace RHTower

/-- The uniform source has no blind-endpoint atom. -/
theorem gomesClarkUniform_one :
    (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) {gomesHausdorffOne} = 0 := by
  change volume ({gomesHausdorffOne} : Set HausdorffSourceSpace) = 0
  simp

/-- Uniform data fail the inverse-moment condition despite having no atoms. -/
theorem gomesClarkUniform_inverse_not_integrable :
    ¬ Integrable gomesClarkCollapsedInverseWeight
      (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) := by
  rw [← gomesClarkEndpointPowerSource_zero, gomesClarkEndpointPowerSource_inverse_integrable_iff]
  exact lt_irrefl 0

/-- The atom-free uniform source is not the weighted image of any finite source at zero anchor. -/
theorem gomesClarkUniform_not_in_collapsed_range :
    gomesHausdorffUniformSource ∉ Set.range (gomesClarkWeightedSource 0) := by
  rw [gomesClarkCollapsed_range_iff]
  exact fun h => gomesClarkUniform_inverse_not_integrable h.2

/-- The unique canonical inverse of uniform data has genuinely infinite total mass. -/
theorem gomesClarkUniform_inverse_infinite_mass :
    gomesClarkCollapsedUnweight (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) Set.univ = ∞ := by
  apply not_isFiniteMeasure_iff.mp
  rw [gomesClarkCollapsedUnweight_finite_iff]
  exact gomesClarkUniform_inverse_not_integrable

/-- The range obstruction persists inside the class of atom-free probability sources. -/
theorem gomesClarkCollapsed_atomfree_probability_obstruction :
    ∃ ν : FiniteMeasure HausdorffSourceSpace, ν.mass = 1 ∧
      (∀ y : HausdorffSourceSpace, (ν : Measure HausdorffSourceSpace) {y} = 0) ∧
      ν ∉ Set.range (gomesClarkWeightedSource 0) := by
  refine ⟨gomesHausdorffUniformSource, gomesHausdorffUniformSource_mass, ?_,
    gomesClarkUniform_not_in_collapsed_range⟩
  intro y
  change volume ({y} : Set HausdorffSourceSpace) = 0
  simp

/-- An atom-free uniform reciprocal bank has no finite fixed-Clark realization. -/
theorem gomesClarkUniform_no_fixed_realization :
    ¬ ∃ μ : FiniteMeasure HausdorffSourceSpace,
      gomesClarkFixedRecord μ = gomesClarkReciprocalRecord gomesHausdorffUniformSource := by
  rw [gomesClarkFixed_reciprocal_realizable_iff]
  exact fun h => gomesClarkUniform_inverse_not_integrable h.2

/-- Arbitrarily local observations already witness the same non-realizability. -/
theorem gomesClarkUniform_no_local_fixed_realization (r : Set.Ioc (0 : ℝ) 1) :
    ¬ ∃ μ : FiniteMeasure HausdorffSourceSpace,
      gomesClarkGerm r (gomesClarkFixedRecord μ) =
        gomesClarkGerm r (gomesClarkReciprocalRecord gomesHausdorffUniformSource) := by
  rw [gomesClarkFixedGerm_reciprocal_realizable_iff]
  exact fun h => gomesClarkUniform_inverse_not_integrable h.2

/-- General realization boundary across all real anchors and finite target sources. -/
theorem gomesClarkAnchor_reciprocal_realizable_iff (c : ℝ)
    (ν : FiniteMeasure HausdorffSourceSpace) :
    (∃ μ : FiniteMeasure HausdorffSourceSpace,
      gomesClarkAnchorRecord c μ = gomesClarkReciprocalRecord ν) ↔
      c ≠ 0 ∨ ν ∈ Set.range (gomesClarkWeightedSource 0) := by
  have hn : c ≠ 0 → ∃ μ : FiniteMeasure HausdorffSourceSpace,
      gomesClarkAnchorRecord c μ = gomesClarkReciprocalRecord ν := by
    intro hc
    refine ⟨gomesClarkUnweightedSource ⟨c, hc⟩ ν, ?_⟩
    rw [gomesClarkAnchorRecord_weighted]
    exact congrArg gomesClarkReciprocalRecord (gomesClarkWeightedSource_unweighted ⟨c, hc⟩ ν)
  by_cases hc : c = 0
  · subst c
    simp only [ne_self_iff_false, false_or, gomesClarkAnchorRecord_zero]
    rw [gomesClarkFixed_reciprocal_realizable_iff, gomesClarkCollapsed_range_iff]
  · constructor
    · intro _
      exact Or.inl hc
    · intro _
      exact hn hc

/-- The entire diffuse power family has an exact joint anchor/exponent realization boundary. -/
theorem gomesClarkEndpointPowerSource_anchor_realizable_iff (c : ℝ) (a : Set.Ioi (-1 : ℝ)) :
    (∃ μ : FiniteMeasure HausdorffSourceSpace,
      gomesClarkAnchorRecord c μ = gomesClarkReciprocalRecord (gomesClarkEndpointPowerSource a)) ↔
      c ≠ 0 ∨ 0 < (a : ℝ) := by
  rw [gomesClarkAnchor_reciprocal_realizable_iff, gomesClarkEndpointPowerSource_range_iff]

/-- Uniform reciprocal data can be realized precisely at the nonzero anchors. -/
theorem gomesClarkUniform_anchor_realizable_iff (c : ℝ) :
    (∃ μ : FiniteMeasure HausdorffSourceSpace,
      gomesClarkAnchorRecord c μ = gomesClarkReciprocalRecord gomesHausdorffUniformSource) ↔ c ≠ 0 := by
  rw [gomesClarkAnchor_reciprocal_realizable_iff]
  simp only [gomesClarkUniform_not_in_collapsed_range, or_false]

/-- Local reciprocal realization has the same anchor/image boundary as the entire bank. -/
theorem gomesClarkAnchor_local_reciprocal_realizable_iff (r : Set.Ioc (0 : ℝ) 1) (c : ℝ)
    (ν : FiniteMeasure HausdorffSourceSpace) :
    (∃ μ : FiniteMeasure HausdorffSourceSpace,
      gomesClarkGerm r (gomesClarkAnchorRecord c μ) =
        gomesClarkGerm r (gomesClarkReciprocalRecord ν)) ↔
      c ≠ 0 ∨ ν ∈ Set.range (gomesClarkWeightedSource 0) := by
  rw [← gomesClarkAnchor_reciprocal_realizable_iff]
  constructor
  · rintro ⟨μ, h⟩
    refine ⟨μ, ?_⟩
    rw [gomesClarkAnchorRecord_weighted] at h ⊢
    have hw : gomesClarkWeightedSource c μ = ν := (gomesClarkReciprocalGerm_injective r) h
    rw [hw]
  · rintro ⟨μ, h⟩
    exact ⟨μ, congrArg (gomesClarkGerm r) h⟩

/-- Local observations see the same sharp exponent threshold throughout the diffuse family. -/
theorem gomesClarkEndpointPowerSource_local_anchor_realizable_iff (r : Set.Ioc (0 : ℝ) 1)
    (c : ℝ) (a : Set.Ioi (-1 : ℝ)) :
    (∃ μ : FiniteMeasure HausdorffSourceSpace,
      gomesClarkGerm r (gomesClarkAnchorRecord c μ) =
        gomesClarkGerm r (gomesClarkReciprocalRecord (gomesClarkEndpointPowerSource a))) ↔
      c ≠ 0 ∨ 0 < (a : ℝ) := by
  rw [gomesClarkAnchor_local_reciprocal_realizable_iff, gomesClarkEndpointPowerSource_range_iff]

/-- Nonpositive admissible exponents produce infinite inverse mass throughout the atom-free family. -/
theorem gomesClarkEndpointPowerSource_inverse_infinite_iff (a : Set.Ioi (-1 : ℝ)) :
    gomesClarkCollapsedUnweight (gomesClarkEndpointPowerSource a : Measure HausdorffSourceSpace)
        Set.univ = ∞ ↔ (a : ℝ) ≤ 0 := by
  rw [← not_isFiniteMeasure_iff, gomesClarkEndpointPowerSource_inverse_finite_iff, not_lt]

end RHTower
