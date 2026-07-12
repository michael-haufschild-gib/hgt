import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Finite rationally independent real weights

Every finite vertex type embeds into a Hamel basis of `R` over `Q`, since that basis has continuum
cardinality.  The selected basis values give a canonical noncomputable family of real translation
weights with no nontrivial rational, hence no integral, relation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Embed a finite type into the chosen Hamel basis of `R` over `Q`. -/
def rationalBasisEmbedding (α : Type*) [Fintype α] :
    α ↪ Module.Free.ChooseBasisIndex ℚ ℝ := by
  apply Classical.choice
  rw [← Cardinal.lift_mk_le']
  rw [← Module.Free.rank_eq_card_chooseBasisIndex, Real.rank_rat_real,
    Cardinal.mk_fintype]
  simpa only [Cardinal.lift_natCast, Cardinal.lift_continuum] using
    (Cardinal.nat_lt_continuum (Fintype.card α)).le

/-- Real weights selected from distinct members of the chosen rational Hamel basis. -/
def rationalIndependentWeights (α : Type*) [Fintype α] : α → ℝ :=
  (Module.Free.chooseBasis ℚ ℝ) ∘ rationalBasisEmbedding α

/-- The selected finite real weight family is rationally linearly independent. -/
theorem rationalIndependentWeights_linearIndependent
    (α : Type*) [Fintype α] :
    LinearIndependent ℚ (rationalIndependentWeights α) := by
  exact (Module.Free.chooseBasis ℚ ℝ).linearIndependent.comp
    (rationalBasisEmbedding α) (rationalBasisEmbedding α).injective

end

end GaloisForLFunctions.HTGeometry
