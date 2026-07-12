import GaloisForLFunctions.HTGeometry.CofinalCholeskySelection

/-!
# Topological faithfulness of the complete Toeplitz Gram tower

The complete finite-section Gram coordinate is continuous and injective on real probability
measures.  Its restriction to any compact carrier family is therefore a closed topological
embedding.  This supplies the topological selector before the still-missing continuity theorem
for the positive-diagonal inverse-Cholesky factor itself.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- The complete tower of finite Toeplitz Gram sections of the Cayley pushforward. -/
noncomputable def completeToeplitzGramTower (mu : ProbabilityMeasure ℝ) :
    ∀ N : ℕ, Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun N => circleToeplitzGram N (cayleyMomentZ (mu : Measure ℝ))

/-- Every coordinate, hence the entire product-valued Gram tower, is weakly continuous. -/
theorem continuous_completeToeplitzGramTower :
    Continuous completeToeplitzGramTower := by
  apply continuous_pi
  intro N
  exact continuous_circleToeplitzGram_cayleyMomentZ N

/-- The complete Gram tower determines the probability measure. -/
theorem injective_completeToeplitzGramTower :
    Function.Injective completeToeplitzGramTower := by
  intro mu nu h
  apply ProbabilityMeasure.toMeasure_injective
  apply measure_eq_of_forall_cayleyMoment_eq
  intro n
  have hgram := congrFun h n
  exact (circleToeplitzGram_cayleyMomentZ_eq_iff
    (mu : Measure ℝ) (nu : Measure ℝ) n).mp hgram n le_rfl

/-- On any compact carrier family, the complete Gram tower is a closed topological embedding. -/
theorem isClosedEmbedding_completeToeplitzGramTower_restrict
    (K : Set (ProbabilityMeasure ℝ)) (hK : IsCompact K) :
    Topology.IsClosedEmbedding
      (fun mu : K => completeToeplitzGramTower (mu : ProbabilityMeasure ℝ)) := by
  letI : CompactSpace K := ⟨by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    simpa using hK⟩
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
  · exact continuous_completeToeplitzGramTower.comp continuous_subtype_val
  · exact injective_completeToeplitzGramTower.comp Subtype.val_injective
  · exact (continuous_completeToeplitzGramTower.comp continuous_subtype_val).isClosedMap

end

end GaloisForLFunctions.HTGeometry
