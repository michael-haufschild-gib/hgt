import GaloisForLFunctions.HTGeometry.CrossRelationRankComparison

/-!
# The cross-relation cannot raise the order

The coefficient cross-relation is built from two polynomials over the base field by multiplying by
constants and subtracting.  Neither operation introduces a jet variable, so its order is bounded by the
larger of the two orders.

This is the structural half of the reverse comparison: whatever the two-block coefficients are, the
relation they produce is no higher in order than they are.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- **The cross-relation's order is at most the larger of its two entries' orders.** -/
theorem order_crossRelation_le (G : IntermediateField F E) (p q : G)
    (A B : DifferentialPolynomial Unit F) :
    scalarDifferentialPolynomialOrder
        (differentialCharacteristicCoefficientCrossRelation G p q A B)
      ≤ max (scalarDifferentialPolynomialOrder A) (scalarDifferentialPolynomialOrder B) := by
  classical
  have hinj : Function.Injective (algebraMap F G) := (algebraMap F G).injective
  have hsub : (differentialCharacteristicCoefficientCrossRelation G p q A B).vars
      ⊆ A.vars ∪ B.vars := by
    refine (MvPolynomial.vars_sub_subset _).trans ?_
    refine Finset.union_subset_union ?_ ?_
    · refine (MvPolynomial.vars_mul _ _).trans ?_
      rw [MvPolynomial.vars_C, MvPolynomial.vars_map_of_injective _ hinj]
      simp
    · refine (MvPolynomial.vars_mul _ _).trans ?_
      rw [MvPolynomial.vars_C, MvPolynomial.vars_map_of_injective _ hinj]
      simp
  refine Finset.sup_le fun j hj => ?_
  rcases Finset.mem_union.1 (hsub hj) with h | h
  · exact le_trans (Finset.le_sup (f := fun j : Unit × ℕ => j.2) h) (le_max_left _ _)
  · exact le_trans (Finset.le_sup (f := fun j : Unit × ℕ => j.2) h) (le_max_right _ _)

end

end GaloisForLFunctions
