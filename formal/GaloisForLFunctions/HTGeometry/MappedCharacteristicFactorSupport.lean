import GaloisForLFunctions.HTGeometry.TwoBlockIrreducibleFactor
import GaloisForLFunctions.HTGeometry.DifferentialLurothVariableSupport
import GaloisForLFunctions.HTGeometry.DifferentialRelationBaseChange

/-!
# An irreducible factor of the mapped characteristic has its full support

The corpus's factor-support theorem is stated along the structure map of an algebra.  The map into the
jet fraction field is an algebra map over the base field, not over the intermediate field, so it is
made into the structure map by declaring the fraction field an algebra over the intermediate field
through it.

With the supports equal, the orders are equal too, which is the comparison the divisibility bridge
asks for.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]

/-- **An irreducible factor of the mapped characteristic has exactly its variables.** -/
theorem irreducible_factor_mapped_vars_eq (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    {P : DifferentialPolynomial Unit G} (hPirr : Irreducible P)
    {A : DifferentialPolynomial Unit (FractionRing (DifferentialPolynomial Unit F))}
    (hAirr : Irreducible A)
    (hdiv : A ∣ MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom P) :
    A.vars = P.vars := by
  letI : Algebra G (FractionRing (DifferentialPolynomial Unit F)) :=
    (differentialIntermediateToJetFraction G hG hy).toRingHom.toAlgebra
  exact irreducible_map_factor_vars_eq hPirr hAirr hdiv

/-- **An irreducible factor of the mapped characteristic has its order.** -/
theorem irreducible_factor_mapped_order_eq (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    {P : DifferentialPolynomial Unit G} (hPirr : Irreducible P)
    {A : DifferentialPolynomial Unit (FractionRing (DifferentialPolynomial Unit F))}
    (hAirr : Irreducible A)
    (hdiv : A ∣ MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom P) :
    scalarDifferentialPolynomialOrder A = scalarDifferentialPolynomialOrder P := by
  rw [scalarDifferentialPolynomialOrder, scalarDifferentialPolynomialOrder,
    irreducible_factor_mapped_vars_eq G hG hy hPirr hAirr hdiv]

end

end GaloisForLFunctions
