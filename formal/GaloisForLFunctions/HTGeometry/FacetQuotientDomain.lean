import GaloisForLFunctions.HTGeometry.DomainLinearIndependentMul
import GaloisForLFunctions.HTGeometry.FacetPolynomialQuotient

/-!
# The facet quotient is a domain

The coordinate facet quotient is canonically the polynomial ring on the facet's own variables, so
over a domain it is a domain.  Transporting that along the corpus equivalence
`facetPolynomialQuotientEquiv` is all it takes.

The consequence is the freeness of a complete integral facet orbit: inside the facet quotient the
separator has nonzero class, and multiplying an independent family of monomials by a nonzero element
of a domain preserves independence.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The coordinate facet quotient of a domain is a domain.** -/
theorem isDomain_facetQuotient {R α : Type*} [CommRing R] [IsDomain R] [DecidableEq α]
    (F : Finset α) : IsDomain (MvPolynomial α R ⧸ facetIdeal R F) :=
  Function.Injective.isDomain
    ((facetPolynomialQuotientEquiv (R := R) F).toRingEquiv.toRingHom)
    (facetPolynomialQuotientEquiv (R := R) F).toRingEquiv.injective

/-- **Freeness of a facet orbit.**  An independent family in the facet quotient stays independent
after multiplication by a class with nonzero value; this is the complete integral facet orbit of the
separator. -/
theorem linearIndependent_facetOrbit_of_ne_zero {k α ι : Type*} [Field k] [DecidableEq α]
    (F : Finset α) {t : ι → MvPolynomial α k ⧸ facetIdeal k F} (ht : LinearIndependent k t)
    {q : MvPolynomial α k ⧸ facetIdeal k F} (hq : q ≠ 0) :
    LinearIndependent k fun i => t i * q := by
  haveI : IsDomain (MvPolynomial α k ⧸ facetIdeal k F) := isDomain_facetQuotient F
  exact linearIndependent_mul_const_of_ne_zero ht hq

end GaloisForLFunctions.HTGeometry
