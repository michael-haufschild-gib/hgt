/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.FacetRestrictionEmbedding

/-!
# Finite-facet polynomial Hasse principle

Pairwise-compatible quotient observations on a finite family of coordinate facets have a global
polynomial representative, unique modulo the Stanley--Reisner nonface ideal.  Equality and
vanishing of global quotient classes are therefore detected at every facet.  This is a finite
Čech-style geometric Hasse principle rather than an arithmetic ABHN sequence.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset MvPolynomial

noncomputable section

variable {R α : Type*} [CommRing R] [DecidableEq α]

/-- Two global polynomials define the same Stanley--Reisner class exactly when all facet-local
quotient observations agree. -/
theorem facetPolynomialHasse_eq_mod_stanleyReisner_iff_forall_local
    (s : Finset (Finset α)) (P Q : MvPolynomial α R) :
    P - Q ∈ stanleyReisnerIdeal R s ↔
      ∀ F ∈ s, (facetIdeal R F).mkQ P = (facetIdeal R F).mkQ Q := by
  constructor
  · intro h F hF
    apply (Submodule.Quotient.eq (facetIdeal R F)).2
    rw [stanleyReisnerIdeal_eq_inf_facetIdeal] at h
    have hle : s.inf (facetIdeal R) ≤ facetIdeal R F :=
      Finset.inf_le_of_le hF le_rfl
    exact hle h
  · exact commonFacetPolynomialRepresentative_sub_mem_stanleyReisnerIdeal s

/-- A global polynomial is zero modulo the Stanley--Reisner ideal exactly when every facet-local
observation is zero. -/
theorem facetPolynomialHasse_mem_stanleyReisner_iff_forall_local_zero
    (s : Finset (Finset α)) (P : MvPolynomial α R) :
    P ∈ stanleyReisnerIdeal R s ↔
      ∀ F ∈ s, (facetIdeal R F).mkQ P = 0 := by
  simpa using
    (facetPolynomialHasse_eq_mod_stanleyReisner_iff_forall_local
      (R := R) s P 0)

/-- Finite-facet Hasse principle: pairwise-compatible local observations have a global polynomial
representative, unique modulo the global Stanley--Reisner ideal. -/
theorem facetPolynomialHasse_exists_global_unique_mod_stanleyReisner_iff
    (s : Finset (Finset α))
    (x : (F : Finset α) → MvPolynomial α R ⧸ facetIdeal R F) :
    familyPairwiseCompatibleOn (facetIdeal R) s x ↔
      ∃ P : MvPolynomial α R,
        (∀ F ∈ s, (facetIdeal R F).mkQ P = x F) ∧
        ∀ Q : MvPolynomial α R,
          (∀ F ∈ s, (facetIdeal R F).mkQ Q = x F) →
            Q - P ∈ stanleyReisnerIdeal R s := by
  constructor
  · intro hx
    obtain ⟨P, hP⟩ :=
      (exists_commonFacetPolynomialRepresentative_iff (R := R) s x).2 hx
    refine ⟨P, hP, ?_⟩
    intro Q hQ
    apply commonFacetPolynomialRepresentative_sub_mem_stanleyReisnerIdeal s
    intro F hF
    exact (hQ F hF).trans (hP F hF).symm
  · rintro ⟨P, hP, _⟩
    exact (exists_commonFacetPolynomialRepresentative_iff (R := R) s x).1 ⟨P, hP⟩

end

end GaloisForLFunctions.HTGeometry
