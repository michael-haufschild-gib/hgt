import GaloisForLFunctions.HTGeometry.CenteredRootFieldTop

/-!
# The centered field is a splitting field of the centered polynomial

The centered polynomial factors into linear terms over the centered field, and its roots generate
that field over the coefficient field.  So the centered field is a splitting field of the centered
polynomial over its coefficient field.

This is what lets the Galois group computed in the model be transported to any other ambient field
in which the polynomial splits, which is the form the base change step needs.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

theorem splits_centeredMonicE :
    Polynomial.Splits
      ((centeredMonicE K d).map (algebraMap (centeredCoeffField K d) (centeredField K d))) := by
  rw [map_centeredMonicE, centeredMonicL]
  exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _

theorem adjoin_rootSet_centeredMonicE :
    Algebra.adjoin (centeredCoeffField K d) ((centeredMonicE K d).rootSet (centeredField K d)) =
      ⊤ := by
  have halg : ∀ x ∈ (centeredMonicE K d).rootSet (centeredField K d),
      IsAlgebraic (centeredCoeffField K d) x := by
    intro x hx
    refine ⟨centeredMonicE K d, centeredMonicE_ne_zero, ?_⟩
    exact (Polynomial.mem_rootSet'.1 hx).2
  have h := IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (F := centeredCoeffField K d) (E := centeredField K d)
    (S := (centeredMonicE K d).rootSet (centeredField K d)) halg
  rw [← h, show IntermediateField.adjoin (centeredCoeffField K d)
      ((centeredMonicE K d).rootSet (centeredField K d)) = ⊤ from
    rootField_centeredMonicE_eq_top, IntermediateField.top_toSubalgebra]

/-- **The centered field is a splitting field of the centered polynomial.** -/
instance isSplittingField_centeredMonicE :
    Polynomial.IsSplittingField (centeredCoeffField K d) (centeredField K d)
      (centeredMonicE K d) where
  splits' := splits_centeredMonicE
  adjoin_rootSet' := adjoin_rootSet_centeredMonicE

end GaloisForLFunctions.HTGeometry
