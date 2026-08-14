import GaloisForLFunctions.HTGeometry.DifferentialIndependentTower

/-!
# The differential tower law is an equivalence

Additivity of differential independence along a tower holds in both directions: a family split into
two blocks is independent over the base exactly when the first block is independent over the base
and the second is independent over the differential field the first one generates.  The reverse
implication is what turns a *dependence* over a large base into a single-element differential
algebraicity statement, which is the form a coefficient-field descent consumes.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- The jets of a two-block family, reindexed as a sum of the blocks' jets. -/
theorem differentialJet_sumElim_comp {E : Type u} [CommRing E] [Differential E]
    {ι ι' : Type u} (x : ι → E) (y : ι' → E) :
    (Sum.elim (fun p : ι' × ℕ => differentialJet p.2 (y p.1))
        (fun p : ι × ℕ => differentialJet p.2 (x p.1)))
        ∘ (Equiv.sumProdDistrib ι' ι ℕ)
      = fun p : (ι' ⊕ ι) × ℕ => differentialJet p.2 (Sum.elim y x p.1) := by
  funext p
  obtain ⟨s, n⟩ := p
  cases s <;> rfl

/-- **The differential tower law, as an equivalence.** -/
theorem differentialIndependent_sumElim_iff
    {F E : Type u} [Field F] [Field E] [Algebra F E] [Differential E]
    {ι ι' : Type u} {x : ι → E} {y : ι' → E} :
    DifferentialIndependent F (Sum.elim y x) ↔
      DifferentialIndependent F x
        ∧ DifferentialIndependent ↥(differentialAdjoin F (Set.range x)) y := by
  unfold DifferentialIndependent
  rw [differentialAdjoin, IntermediateField.algebraicIndependent_adjoin_iff,
    differentialJetSet_range]
  rw [algebraicIndependent_equiv' (Equiv.sumProdDistrib ι' ι ℕ)
    (differentialJet_sumElim_comp x y)]
  exact AlgebraicIndependent.sumElim_iff

end

end GaloisForLFunctions.HTGeometry
