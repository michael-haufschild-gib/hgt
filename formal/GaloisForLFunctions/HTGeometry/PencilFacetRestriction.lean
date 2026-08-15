import GaloisForLFunctions.HTGeometry.PencilGeneralSeed
import GaloisForLFunctions.HTGeometry.StanleyReisnerFacetIdeal

/-!
# Facet restriction of a difference operator

Setting the vertex variables outside a facet to zero is the coordinate form of the facet prime: its
kernel is exactly the facet ideal, and on the source of that facet the restricted operator has the
same carrier, because a variable outside the facet already annihilates that source.

Consequently the carrier of a difference operator on a general pencil source is the sum, over the
facets, of the carriers of its facet restrictions — the expansion `(20)` of the card.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R α : Type*} [CommRing R] [DecidableEq α]

/-- Setting the vertex variables outside a facet to zero. -/
def facetRestrict (A : Finset α) : MvPolynomial α R →ₐ[R] MvPolynomial α R :=
  MvPolynomial.aeval fun v => if v ∈ A then MvPolynomial.X v else 0

theorem facetRestrict_X_mem {A : Finset α} {v : α} (hv : v ∈ A) :
    facetRestrict (R := R) A (MvPolynomial.X v) = MvPolynomial.X v := by
  rw [facetRestrict, MvPolynomial.aeval_X, if_pos hv]

theorem facetRestrict_X_notMem {A : Finset α} {v : α} (hv : v ∉ A) :
    facetRestrict (R := R) A (MvPolynomial.X v) = 0 := by
  rw [facetRestrict, MvPolynomial.aeval_X, if_neg hv]

theorem facetRestrict_monomial (A : Finset α) (d : α →₀ ℕ) (c : R) :
    facetRestrict A (MvPolynomial.monomial d c) =
      if d.support ⊆ A then MvPolynomial.monomial d c else 0 := by
  classical
  rw [facetRestrict, MvPolynomial.aeval_monomial]
  by_cases hsub : d.support ⊆ A
  · rw [if_pos hsub]
    rw [MvPolynomial.monomial_eq, Finsupp.prod, Finsupp.prod]
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [if_pos (hsub hv)]
  · rw [if_neg hsub]
    obtain ⟨v, hvd, hvA⟩ := Finset.not_subset.mp hsub
    have hterm : (if v ∈ A then (MvPolynomial.X v : MvPolynomial α R) else 0) ^ (d v) = 0 := by
      rw [if_neg hvA]
      exact zero_pow (Finsupp.mem_support_iff.mp hvd)
    have hzero : (Finsupp.prod d fun v e =>
        (if v ∈ A then (MvPolynomial.X v : MvPolynomial α R) else 0) ^ e) = 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_eq_zero hvd hterm
    rw [hzero, mul_zero]

/-- **The kernel of facet restriction is the facet ideal.** -/
theorem facetRestrict_eq_zero_iff_mem_facetIdeal (A : Finset α) (P : MvPolynomial α R) :
    facetRestrict A P = 0 ↔ P ∈ facetIdeal R A := by
  classical
  rw [mem_facetIdeal_iff]
  constructor
  · intro h d hd hsub
    have hcoeff : MvPolynomial.coeff d (facetRestrict A P) = MvPolynomial.coeff d P := by
      conv_lhs => rw [MvPolynomial.as_sum P]
      rw [map_sum, MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single d]
      · rw [facetRestrict_monomial, if_pos hsub, MvPolynomial.coeff_monomial, if_pos rfl]
      · intro e _ hne
        rw [facetRestrict_monomial]
        by_cases hesub : e.support ⊆ A
        · rw [if_pos hesub, MvPolynomial.coeff_monomial, if_neg hne]
        · rw [if_neg hesub, MvPolynomial.coeff_zero]
      · intro hdnot
        rw [MvPolynomial.notMem_support_iff.mp hdnot, MvPolynomial.monomial_zero, map_zero,
          MvPolynomial.coeff_zero]
    rw [h, MvPolynomial.coeff_zero] at hcoeff
    exact (MvPolynomial.mem_support_iff.mp hd) hcoeff.symm
  · intro h
    conv_lhs => rw [MvPolynomial.as_sum P]
    rw [map_sum]
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [facetRestrict_monomial, if_neg (h d hd)]

variable {facets : Finset (Finset α)} {E : Type*} [AddCommMonoid E]

namespace PencilSeparation

/-- **On the source of a facet, only the facet variables act.** -/
theorem seedCarrierPoly_facetSource_facetRestrict
    (S : PencilSeparation facets E) (Ψ : Finset α → ℂ → ℂ) {A : Finset α} (hA : A ∈ facets)
    (P : MvPolynomial α ℂ) :
    seedCarrierPoly S.ω (S.facetSource Ψ A) P =
      seedCarrierPoly S.ω (S.facetSource Ψ A) (facetRestrict A P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [facetRestrict, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
      rw [seedCarrierPoly_add, hp, hq, map_add, seedCarrierPoly_add]
  | mul_X p v hp =>
      by_cases hv : v ∈ A
      · rw [map_mul, facetRestrict_X_mem hv]
        rw [show p * MvPolynomial.X v = MvPolynomial.X v * p from mul_comm _ _,
          show facetRestrict A p * MvPolynomial.X v
            = MvPolynomial.X v * facetRestrict A p from mul_comm _ _,
          seedCarrierPoly_X_mul, seedCarrierPoly_X_mul, hp]
      · rw [map_mul, facetRestrict_X_notMem hv, mul_zero]
        have hzero : seedCarrierPoly S.ω (S.facetSource Ψ A) (MvPolynomial.X v) = 0 := by
          show shiftAlgHom (polyShift S.ω (MvPolynomial.X v)) (S.facetSource Ψ A) = 0
          rw [polyShift_X]
          exact S.shiftAlgHom_stepVar_facetSource Ψ hA hv
        have hR : seedCarrierPoly S.ω (S.facetSource Ψ A) 0 = 0 :=
          map_zero (seedCarrierPolyₗ S.ω (S.facetSource Ψ A))
        rw [hR, seedCarrierPoly_mul, hzero, map_zero]

/-- **The expansion `(20)`.**  The carrier of a difference operator on a general pencil source is the
sum over facets of the carriers of its facet restrictions. -/
theorem seedCarrierPoly_genSeed_eq_sum_facetRestrict
    (S : PencilSeparation facets E) (Ψ : Finset α → ℂ → ℂ) (P : MvPolynomial α ℂ) :
    seedCarrierPoly S.ω (S.genSeed Ψ) P =
      ∑ A ∈ facets, seedCarrierPoly S.ω (S.facetSource Ψ A) (facetRestrict A P) := by
  funext z
  have hfun : S.genSeed Ψ = fun w => ∑ A ∈ facets, S.facetSource Ψ A w := rfl
  rw [hfun, seedCarrierPoly_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun A hA =>
    congrFun (S.seedCarrierPoly_facetSource_facetRestrict Ψ hA P) z

end PencilSeparation

end

end GaloisForLFunctions.HTGeometry
