import GaloisForLFunctions.HTGeometry.PencilFacetRestriction
import GaloisForLFunctions.HTGeometry.FacetTranslationCoordinates

/-!
# Translation coordinates of a facet restriction, and of a difference operator

Two coordinate identifications are needed to read a Stanley--Reisner Laurent row as a difference
operator acting on a pencil source.

The first is combinatorial: the facet coordinate of a Stanley--Reisner class, re-expanded in
translation variables, is the translation expansion of the facet restriction of any representative.

The second is the definition of the carrier itself: evaluating a polynomial at the difference
operators `T_v - 1` is the same as expanding it in translation variables and then reading each
monomial as one translation.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-! ### Facet coordinates in translation variables -/

variable {R α : Type*} [CommRing R] [DecidableEq α]

theorem rename_facetPolynomialRestriction (F : Finset α) (P : MvPolynomial α R) :
    MvPolynomial.rename (facetVariableInclusion (R := R) F)
        (facetPolynomialRestriction F P) = facetRestrict F P := by
  have hhom : (MvPolynomial.rename (facetVariableInclusion (R := R) F)).comp
      (facetPolynomialRestriction (R := R) F) = facetRestrict (R := R) F := by
    apply MvPolynomial.algHom_ext
    intro v
    by_cases hv : v ∈ F
    · have hval : (facetVariableInclusion (R := R) F) ⟨v, hv⟩ = v := rfl
      have hkill : facetPolynomialRestriction (R := R) F (MvPolynomial.X v)
          = MvPolynomial.X (⟨v, hv⟩ : F) := by
        have := MvPolynomial.killCompl_rename_app
          (facetVariableInclusion_injective (R := R) F)
          (MvPolynomial.X (⟨v, hv⟩ : F) : MvPolynomial F R)
        rwa [MvPolynomial.rename_X, hval] at this
      show MvPolynomial.rename _ (facetPolynomialRestriction F (MvPolynomial.X v)) = _
      rw [hkill, MvPolynomial.rename_X, hval, facetRestrict_X_mem hv]
    · have hmem : (MvPolynomial.X v : MvPolynomial α R) ∈ facetIdeal R F :=
        Ideal.subset_span ⟨v, hv, rfl⟩
      have hkill : facetPolynomialRestriction (R := R) F (MvPolynomial.X v) = 0 :=
        RingHom.mem_ker.mp ((ker_facetPolynomialRestriction (R := R) F).symm ▸ hmem)
      show MvPolynomial.rename _ (facetPolynomialRestriction F (MvPolynomial.X v)) = _
      rw [hkill, map_zero, facetRestrict_X_notMem hv]
  exact congrArg (fun f : MvPolynomial α R →ₐ[R] MvPolynomial α R => f P) hhom

omit [DecidableEq α] in
theorem rename_differenceToTranslationHom (F : Finset α) (Q : MvPolynomial F R) :
    MvPolynomial.rename (facetVariableInclusion (R := R) F) (differenceToTranslationHom Q)
      = differenceToTranslationHom
        (MvPolynomial.rename (facetVariableInclusion (R := R) F) Q) := by
  have hhom : (MvPolynomial.rename (facetVariableInclusion (R := R) F)).comp
        differenceToTranslationHom
      = (differenceToTranslationHom (R := R) (α := α)).comp
        (MvPolynomial.rename (facetVariableInclusion (R := R) F)) := by
    apply MvPolynomial.algHom_ext
    intro u
    show MvPolynomial.rename _ (differenceToTranslationHom (MvPolynomial.X u))
      = differenceToTranslationHom (MvPolynomial.rename _ (MvPolynomial.X u))
    simp only [differenceToTranslationHom, MvPolynomial.aeval_X, map_sub, MvPolynomial.rename_X,
      map_one]
  exact congrArg (fun f : MvPolynomial F R →ₐ[R] MvPolynomial α R => f Q) hhom

/-- **The facet translation coordinate is the translation expansion of the facet restriction.** -/
theorem facetTranslationPolynomialEmbedding_facetPolynomialRestriction
    (F : Finset α) (P : MvPolynomial α R) :
    facetTranslationPolynomialEmbedding (R := R) F (facetPolynomialRestriction F P)
      = differenceToTranslationHom (facetRestrict F P) := by
  show MvPolynomial.rename (facetVariableInclusion (R := R) F)
      (differenceToTranslationHom (facetPolynomialRestriction F P)) = _
  rw [rename_differenceToTranslationHom, rename_facetPolynomialRestriction]

theorem quotientFacetEmbedding_mk {k A σ : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (I : Ideal A) (J : σ → Ideal A) (hI : I = ⨅ s, J s) (P : A) (s : σ) :
    quotientFacetEmbedding (k := k) I J hI (Ideal.Quotient.mk I P) s
      = Ideal.Quotient.mk (J s) P := by
  subst hI
  rfl

set_option maxHeartbeats 2000000 in
theorem stanleyReisnerFacetPolynomialCoordinates_mk (facets : Finset (Finset α))
    (P : MvPolynomial α R) (F : facets) :
    stanleyReisnerFacetPolynomialCoordinates facets
        (Ideal.Quotient.mk (stanleyReisnerIdeal R facets) P) F
      = facetPolynomialRestriction F.1 P := by
  have hI : stanleyReisnerIdeal R facets = ⨅ G : facets, facetIdeal R G.1 := by
    rw [stanleyReisnerIdeal_eq_inf_facetIdeal]
    refine le_antisymm (le_iInf fun G => Finset.inf_le_of_le G.2 le_rfl)
      (Finset.le_inf fun G hG => iInf_le_of_le ⟨G, hG⟩ le_rfl)
  have hstep : quotientFacetEmbedding (k := R) (stanleyReisnerIdeal R facets)
      (fun G : facets => facetIdeal R G.1) hI
      (Ideal.Quotient.mk (stanleyReisnerIdeal R facets) P) F
      = Ideal.Quotient.mk (facetIdeal R F.1) P :=
    quotientFacetEmbedding_mk _ _ hI P F
  show facetPolynomialQuotientEquiv F.1
      (quotientFacetEmbedding (k := R) (stanleyReisnerIdeal R facets)
        (fun G : facets => facetIdeal R G.1) hI
        (Ideal.Quotient.mk (stanleyReisnerIdeal R facets) P) F) = _
  rw [hstep]
  rfl

/-- **The Stanley--Reisner facet translation coordinate of a class.** -/
theorem stanleyReisnerFacetTranslationCoordinates_mk (facets : Finset (Finset α))
    (P : MvPolynomial α R) (F : facets) :
    stanleyReisnerFacetTranslationCoordinates facets
        (Ideal.Quotient.mk (stanleyReisnerIdeal R facets) P) F
      = differenceToTranslationHom (facetRestrict F.1 P) := by
  show facetTranslationPolynomialEmbedding F.1
      (stanleyReisnerFacetPolynomialCoordinates facets
        (Ideal.Quotient.mk (stanleyReisnerIdeal R facets) P) F) = _
  rw [stanleyReisnerFacetPolynomialCoordinates_mk,
    facetTranslationPolynomialEmbedding_facetPolynomialRestriction]

end

end GaloisForLFunctions.HTGeometry
