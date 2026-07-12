import GaloisForLFunctions.HTGeometry.CanonicalFrameContinuity
import GaloisForLFunctions.HTGeometry.CompleteGramTowerTopology

/-!
# Topological faithfulness of the complete inverse-Cholesky tower

This module proves the literal topological statement used in the cofinal Cholesky manuscript.
On the probability measures whose every finite Cayley--Toeplitz Gram section is positive definite,
the complete tower of canonical positive-diagonal inverse-Cholesky factors is continuous and
injective.  On every compact carrier family its restriction is therefore a closed topological
embedding.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ComplexOrder

noncomputable section

/-- Probability measures with positive-definite Cayley--Toeplitz Gram matrices at every finite
level.  Infinite-support carriers lie in this domain. -/
abbrev PositiveCayleyGramProbability :=
  {mu : ProbabilityMeasure ℝ //
    ∀ N : ℕ, (circleToeplitzGram N (cayleyMomentZ (mu : Measure ℝ))).PosDef}

/-- The complete canonical positive-diagonal inverse-Cholesky tower. -/
noncomputable def completeCanonicalFrameTower (mu : PositiveCayleyGramProbability) :
    ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun N => canonicalInverseCholeskyFactor
    ⟨circleToeplitzGram N (cayleyMomentZ ((mu.1 : ProbabilityMeasure ℝ) : Measure ℝ)),
      mu.2 N⟩

/-- Every fixed canonical frame level varies continuously in the weak measure topology. -/
theorem continuous_completeCanonicalFrameTower_level (N : ℕ) :
    Continuous (fun mu : PositiveCayleyGramProbability => completeCanonicalFrameTower mu N) := by
  apply continuous_canonicalInverseCholeskyFactor.comp
  apply Continuous.subtype_mk
  exact continuous_circleToeplitzGram_cayleyMomentZ N |>.comp continuous_subtype_val

/-- The complete canonical frame tower is continuous in the product topology. -/
theorem continuous_completeCanonicalFrameTower :
    Continuous completeCanonicalFrameTower := by
  apply continuous_pi
  exact continuous_completeCanonicalFrameTower_level

/-- Equality of complete canonical frame towers selects the underlying probability measure. -/
theorem injective_completeCanonicalFrameTower :
    Function.Injective completeCanonicalFrameTower := by
  intro mu nu h
  apply Subtype.ext
  apply ProbabilityMeasure.toMeasure_injective
  exact measure_eq_of_completeCanonicalFrame_eq
    ((mu.1 : ProbabilityMeasure ℝ) : Measure ℝ)
    ((nu.1 : ProbabilityMeasure ℝ) : Measure ℝ)
    mu.2 nu.2 (fun N => by
      simpa [completeCanonicalFrameTower, canonicalInverseCholeskyFactor] using congrFun h N)

/-- **Literal complete-frame topological selector.** On every compact carrier family, the
complete inverse-Cholesky tower is a closed topological embedding. -/
theorem isClosedEmbedding_completeCanonicalFrameTower_restrict
    (K : Set PositiveCayleyGramProbability) (hK : IsCompact K) :
    Topology.IsClosedEmbedding
      (fun mu : K => completeCanonicalFrameTower (mu : PositiveCayleyGramProbability)) := by
  letI : CompactSpace K := ⟨by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    simpa using hK⟩
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
  · exact continuous_completeCanonicalFrameTower.comp continuous_subtype_val
  · exact injective_completeCanonicalFrameTower.comp Subtype.val_injective
  · exact (continuous_completeCanonicalFrameTower.comp continuous_subtype_val).isClosedMap

end

end GaloisForLFunctions.HTGeometry
