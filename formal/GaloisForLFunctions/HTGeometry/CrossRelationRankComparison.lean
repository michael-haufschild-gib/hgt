import GaloisForLFunctions.HTGeometry.CrossRelationNonvanishing
import GaloisForLFunctions.HTGeometry.DifferentialLurothVariableSupport

/-!
# The characteristic's order is bounded by the coefficient cross-relation

Two characteristic coefficients with a ratio outside the base field carry a nonzero relation of the
free element over the small field they generate.  That relation is nonconstant, because a constant
would be a unit in a proper relation ideal.  Minimality of the characteristic over the larger field
therefore bounds its order by the order of the cross-relation.

This is the comparison a Lüroth argument runs; what it still needs is the reverse bound, which is the
degree count.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]

/-- **The characteristic's order is at most the cross-relation's order.** -/
theorem minimalRank_order_le_crossRelation (G : IntermediateField F E) {y : E}
    {P : DifferentialPolynomial Unit G}
    (hP : IsMinimalScalarDifferentialPolynomialRank
      (differentialIntermediateRelationIdeal G y : Set _) P)
    (p q : G) {A B : DifferentialPolynomial Unit F} (hB : B ≠ 0)
    (hratio : ∀ c : F, (p : E) ≠ algebraMap F E c * (q : E))
    (hle : IntermediateField.adjoin F ({(p : E), (q : E)} : Set E) ≤ G)
    (hmem : differentialCharacteristicCoefficientCrossRelation G p q A B
      ∈ differentialIntermediateRelationIdeal G y) :
    scalarDifferentialPolynomialOrder P
      ≤ scalarDifferentialPolynomialOrder
        (HTGeometry.descendCoefficients hle
          (differentialCharacteristicCoefficientCrossRelation G p q A B)
          (coeff_crossRelation_mem_adjoin G p q A B)) := by
  classical
  set S := HTGeometry.descendCoefficients hle
    (differentialCharacteristicCoefficientCrossRelation G p q A B)
    (coeff_crossRelation_mem_adjoin G p q A B) with hS
  have hSmem : S ∈ differentialIntermediateRelationIdeal
      (IntermediateField.adjoin F ({(p : E), (q : E)} : Set E)) y :=
    descend_crossRelation_mem_relationIdeal G p q A B hle hmem
  have hSne : S ≠ 0 := by
    intro h0
    have hcross : differentialCharacteristicCoefficientCrossRelation G p q A B = 0 := by
      rw [← crossRelation_descends G p q A B hle, ← hS, h0, map_zero]
    exact crossRelation_ne_zero (P := A) G p q hB hratio hcross
  have hSunit : ¬ IsUnit S := by
    intro hunit
    exact differentialIntermediateRelationIdeal_ne_top
      (IntermediateField.adjoin F ({(p : E), (q : E)} : Set E)) y
      (Ideal.eq_top_of_isUnit_mem _ hSmem hunit)
  have hSvars : (MvPolynomial.vars S).Nonempty :=
    mvPolynomial_vars_nonempty_of_ne_zero_of_not_isUnit hSne hSunit
  exact minimalRank_le_of_le hle y hSmem hSne hSvars hP

end

end GaloisForLFunctions
