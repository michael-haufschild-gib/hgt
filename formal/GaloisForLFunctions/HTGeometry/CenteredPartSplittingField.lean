import GaloisForLFunctions.HTGeometry.GenericAverageSymmetric
import GaloisForLFunctions.HTGeometry.GenericRootSet

/-!
# The centered polynomial over the coefficient field splits in the rational function field

The centered polynomial is the shift of the generic one, so it factors into linear terms there and
its roots generate the same field.  Hence the rational function field is a splitting field for it
too, and its Galois group over the coefficient field is the symmetric group.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

theorem splits_centeredMonicPart :
    Polynomial.Splits ((centeredMonicPart K d).map
      (algebraMap (symmetricPart K d) (SymmetricRationalField K d))) := by
  rw [map_centeredMonicPart, centeredMonicF]
  exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _

theorem adjoin_rootSet_centeredMonicPart :
    IntermediateField.adjoin (symmetricPart K d)
        ((centeredMonicPart K d).rootSet (SymmetricRationalField K d)) =
      IntermediateField.adjoin (symmetricPart K d)
        ((genericMonic K d).rootSet (SymmetricRationalField K d)) :=
  adjoin_rootSet_taylor _ _ genericMonic_ne_zero

/-- **The rational function field is a splitting field of the centered polynomial over the
coefficient field.** -/
instance isSplittingField_centeredMonicPart (K : Type*) [Field K] [CharZero K] (d : ℕ) :
    Polynomial.IsSplittingField (symmetricPart K d) (SymmetricRationalField K d)
      (centeredMonicPart K d) where
  splits' := splits_centeredMonicPart
  adjoin_rootSet' := by
    have halg : ∀ x ∈ (centeredMonicPart K d).rootSet (SymmetricRationalField K d),
        IsAlgebraic (symmetricPart K d) x := by
      intro x hx
      refine ⟨centeredMonicPart K d, ?_, (Polynomial.mem_rootSet'.1 hx).2⟩
      exact taylor_ne_zero genericMonic_ne_zero
    have h := IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (F := symmetricPart K d) (E := SymmetricRationalField K d)
      (S := (centeredMonicPart K d).rootSet (SymmetricRationalField K d)) halg
    rw [← h, adjoin_rootSet_centeredMonicPart]
    have hgen : IntermediateField.adjoin (symmetricPart K d)
        ((genericMonic K d).rootSet (SymmetricRationalField K d)) = ⊤ := by
      refine le_antisymm le_top ?_
      rw [← IntermediateField.adjoin_univ, IntermediateField.adjoin_le_iff]
      intro z _
      have hz : z ∈ Algebra.adjoin (symmetricPart K d)
          ((genericMonic K d).rootSet (SymmetricRationalField K d)) := by
        rw [adjoin_rootSet_genericMonic]
        trivial
      exact IntermediateField.algebra_adjoin_le_adjoin _ _ hz
    rw [hgen, IntermediateField.top_toSubalgebra]

end GaloisForLFunctions.HTGeometry
