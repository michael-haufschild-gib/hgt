import GaloisForLFunctions.HTGeometry.StanleyReisnerFacetIdeal
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Polynomial facet quotients

Setting every variable outside a facet to zero has kernel exactly the complementary coordinate
ideal.  Hence the facet quotient is canonically the polynomial ring on the variables of that
facet.  This supplies the finite numerator coefficient model before translation variables are
localized.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- Inclusion of the variables belonging to a facet. -/
def facetVariableInclusion {R α : Type*} [CommRing R]
    (F : Finset α) : F → α := Subtype.val

/-- Facet-variable inclusion is injective. -/
theorem facetVariableInclusion_injective
    {R α : Type*} [CommRing R] (F : Finset α) :
    Function.Injective (facetVariableInclusion (R := R) F) := Subtype.val_injective

/-- Set all variables outside a facet to zero and retain the facet variables. -/
def facetPolynomialRestriction
    {R α : Type*} [CommRing R] (F : Finset α) :
    MvPolynomial α R →ₐ[R] MvPolynomial F R :=
  MvPolynomial.killCompl (facetVariableInclusion_injective (R := R) F)

/-- Coefficients of facet restriction are the coefficients on embedded facet exponents. -/
theorem facetPolynomialRestriction_coeff
    {R α : Type*} [CommRing R] (F : Finset α)
    (P : MvPolynomial α R) (e : F →₀ ℕ) :
    (facetPolynomialRestriction F P).coeff e =
      P.coeff (e.mapDomain (facetVariableInclusion (R := R) F)) := by
  exact MvPolynomial.coeff_killCompl
    (facetVariableInclusion_injective (R := R) F)

/-- The kernel of polynomial facet restriction is exactly the complementary coordinate ideal. -/
theorem ker_facetPolynomialRestriction
    {R α : Type*} [CommRing R] [DecidableEq α] (F : Finset α) :
    RingHom.ker (facetPolynomialRestriction (R := R) F).toRingHom = facetIdeal R F := by
  ext P
  rw [RingHom.mem_ker, mem_facetIdeal_iff]
  constructor
  · intro h d hd hdF
    change facetPolynomialRestriction F P = 0 at h
    let e : F →₀ ℕ := d.comapDomain Subtype.val Subtype.val_injective.injOn
    have hmap : e.mapDomain (facetVariableInclusion (R := R) F) = d := by
      exact Finsupp.mapDomain_comapDomain Subtype.val Subtype.val_injective d (by
        intro a ha
        exact ⟨⟨a, hdF ha⟩, rfl⟩)
    have hc := congrArg (fun Q : MvPolynomial F R => Q.coeff e) h
    change (facetPolynomialRestriction F P).coeff e = 0 at hc
    rw [facetPolynomialRestriction_coeff, hmap] at hc
    exact (Finsupp.mem_support_iff.mp hd) hc
  · intro h
    apply MvPolynomial.ext
    intro e
    change (facetPolynomialRestriction F P).coeff e = 0
    rw [facetPolynomialRestriction_coeff]
    by_contra hcoeff
    have hd : e.mapDomain (facetVariableInclusion (R := R) F) ∈ P.support :=
      Finsupp.mem_support_iff.mpr hcoeff
    apply h _ hd
    intro a ha
    have himage := Finsupp.mapDomain_support (s := e) ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp himage
    exact b.2

/-- Every polynomial on a facet extends to the full vertex polynomial ring. -/
theorem facetPolynomialRestriction_surjective
    {R α : Type*} [CommRing R] (F : Finset α) :
    Function.Surjective (facetPolynomialRestriction (R := R) F) := by
  intro P
  refine ⟨MvPolynomial.rename (facetVariableInclusion (R := R) F) P, ?_⟩
  exact MvPolynomial.killCompl_rename_app
    (facetVariableInclusion_injective (R := R) F) P

/-- The coordinate facet quotient is canonically the polynomial ring on the facet variables. -/
def facetPolynomialQuotientEquiv
    {R α : Type*} [CommRing R] [DecidableEq α] (F : Finset α) :
    (MvPolynomial α R ⧸ facetIdeal R F) ≃ₐ[R] MvPolynomial F R := by
  let f : MvPolynomial α R →ₐ[R] MvPolynomial F R := facetPolynomialRestriction F
  let q : MvPolynomial α R ⧸ facetIdeal R F →ₐ[R] MvPolynomial F R :=
    Ideal.Quotient.liftₐ (facetIdeal R F) f (by
      intro P hP
      exact RingHom.mem_ker.mp
        ((ker_facetPolynomialRestriction (R := R) F).symm ▸ hP))
  apply AlgEquiv.ofBijective q
  constructor
  · intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    apply Ideal.Quotient.eq.mpr
    have hk : facetPolynomialRestriction F (a - b) = 0 := by
      change q (Ideal.Quotient.mk (facetIdeal R F) (a - b)) = 0
      simpa only [map_sub] using sub_eq_zero.mpr hab
    exact (ker_facetPolynomialRestriction (R := R) F).symm ▸
      (RingHom.mem_ker.mpr hk)
  · intro P
    obtain ⟨Q, hQ⟩ := facetPolynomialRestriction_surjective (R := R) F P
    exact ⟨Ideal.Quotient.mk (facetIdeal R F) Q, hQ⟩

end

end GaloisForLFunctions.HTGeometry
