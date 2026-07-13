import GaloisForLFunctions.HTGeometry.CompleteFrameTowerTopology
import GaloisForLFunctions.HTGeometry.InfiniteSupportCayleyGram

/-!
# The complete canonical frame tower on infinite-support carriers

Infinite support supplies strict positivity of every finite Cayley--Toeplitz section, so the
complete positive-diagonal inverse-Cholesky tower is defined without a separate matrix-positivity
hypothesis.  It is continuous and injective, and is a closed topological embedding on every
compact family of infinite-support probability measures.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ComplexOrder

noncomputable section

/-- Real probability measures with infinite topological support. -/
abbrev InfiniteSupportProbability :=
  {mu : ProbabilityMeasure ℝ // ((mu : ProbabilityMeasure ℝ) : Measure ℝ).support.Infinite}

/-- The complete canonical positive-diagonal inverse-Cholesky tower of an infinite-support
probability measure.  Finite-section positivity is derived from support rather than supplied as
extra data. -/
noncomputable def completeInfiniteSupportCanonicalFrameTower
    (mu : InfiniteSupportProbability) :
    ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun N => canonicalInverseCholeskyFactor
    ⟨circleToeplitzGram N
      (cayleyMomentZ ((mu.1 : ProbabilityMeasure ℝ) : Measure ℝ)),
      circleToeplitzGram_posDef_of_infiniteSupport
        ((mu.1 : ProbabilityMeasure ℝ) : Measure ℝ) mu.2 N⟩

/-- Every fixed frame level varies continuously in the weak measure topology on infinite-support
probabilities. -/
theorem continuous_completeInfiniteSupportCanonicalFrameTower_level (N : ℕ) :
    Continuous (fun mu : InfiniteSupportProbability =>
      completeInfiniteSupportCanonicalFrameTower mu N) := by
  apply continuous_canonicalInverseCholeskyFactor.comp
  apply Continuous.subtype_mk
  exact continuous_circleToeplitzGram_cayleyMomentZ N |>.comp continuous_subtype_val

/-- The complete frame tower is continuous in the product topology. -/
theorem continuous_completeInfiniteSupportCanonicalFrameTower :
    Continuous completeInfiniteSupportCanonicalFrameTower := by
  apply continuous_pi
  exact continuous_completeInfiniteSupportCanonicalFrameTower_level

/-- Equality of complete canonical towers selects the underlying infinite-support probability
measure, with finite-section positivity discharged internally. -/
theorem injective_completeInfiniteSupportCanonicalFrameTower :
    Function.Injective completeInfiniteSupportCanonicalFrameTower := by
  intro mu nu h
  apply Subtype.ext
  apply ProbabilityMeasure.toMeasure_injective
  let hmu := fun N => circleToeplitzGram_posDef_of_infiniteSupport
    ((mu.1 : ProbabilityMeasure ℝ) : Measure ℝ) mu.2 N
  let hnu := fun N => circleToeplitzGram_posDef_of_infiniteSupport
    ((nu.1 : ProbabilityMeasure ℝ) : Measure ℝ) nu.2 N
  exact measure_eq_of_completeCanonicalFrame_eq
    ((mu.1 : ProbabilityMeasure ℝ) : Measure ℝ)
    ((nu.1 : ProbabilityMeasure ℝ) : Measure ℝ)
    hmu hnu (fun N => by
      simpa [completeInfiniteSupportCanonicalFrameTower,
        canonicalInverseCholeskyFactor, hmu, hnu] using congrFun h N)

/-- **Paper-facing complete-frame selector.** On every compact family of infinite-support
probability measures, the complete inverse-Cholesky tower is a closed topological embedding. -/
theorem isClosedEmbedding_completeInfiniteSupportCanonicalFrameTower_restrict
    (K : Set InfiniteSupportProbability) (hK : IsCompact K) :
    Topology.IsClosedEmbedding
      (fun mu : K => completeInfiniteSupportCanonicalFrameTower
        (mu : InfiniteSupportProbability)) := by
  letI : CompactSpace K := ⟨by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    simpa using hK⟩
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
  · exact continuous_completeInfiniteSupportCanonicalFrameTower.comp continuous_subtype_val
  · exact injective_completeInfiniteSupportCanonicalFrameTower.comp Subtype.val_injective
  · exact (continuous_completeInfiniteSupportCanonicalFrameTower.comp
      continuous_subtype_val).isClosedMap

end
end GaloisForLFunctions.HTGeometry
