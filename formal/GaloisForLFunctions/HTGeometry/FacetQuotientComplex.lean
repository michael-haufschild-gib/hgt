import GaloisForLFunctions.HTGeometry.FacetAugmentedComplex

/-!
# The facet complex in its quotient form

`FacetAugmentedComplex` proves the exactness of coordinate-facet descent in the truncation model,
where a term of the complex is a polynomial truncated to the multidegrees its facets carry.  This
module transports that result to the quotient form the descent statement is usually written in:
the term belonging to a set `T` of facets is the quotient of the polynomial ring by the sum of their
coordinate ideals, and the differential is the alternating sum of the canonical projections.

The transport is a choice of representatives: truncation is a section of the quotient map, so a
quotient cochain lifts to a truncated one, its differential vanishes exactly when the truncated one
does, and the primitive built in the truncation model projects to a primitive here.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable {ι α k : Type*} [DecidableEq ι] [LinearOrder ι] [DecidableEq α] [CommRing k]
variable (Fam : ι → Finset α)

omit [DecidableEq ι] [LinearOrder ι] [DecidableEq α] in
theorem capIdeal_mono {S T : Finset ι} (h : S ⊆ T) :
    capIdeal k Fam S ≤ capIdeal k Fam T :=
  Finset.sup_mono h

omit [DecidableEq ι] [LinearOrder ι] in
theorem capRestrict_idem (T : Finset ι) (p : MvPolynomial α k) :
    capRestrict k Fam T (capRestrict k Fam T p) = capRestrict k Fam T p := by
  rw [capRestrict_eq_self_iff]
  intro b hb
  by_contra hcon
  rw [coeff_capRestrict, if_neg hcon] at hb
  exact hb rfl

omit [DecidableEq ι] [LinearOrder ι] in
theorem sub_capRestrict_mem_capIdeal (T : Finset ι) (p : MvPolynomial α k) :
    p - capRestrict k Fam T p ∈ capIdeal k Fam T := by
  rw [mem_capIdeal_iff_coeff]
  intro b hb
  rw [coeff_sub, coeff_capRestrict, if_pos hb, sub_self]

/-- The term of the facet complex belonging to a set of facets. -/
abbrev facetQuot (k : Type*) [CommRing k] (Fam : ι → Finset α) (T : Finset ι) : Type _ :=
  MvPolynomial α k ⧸ capIdeal k Fam T

/-- The canonical projection between two terms of the facet complex. -/
def facetFactor (k : Type*) [CommRing k] (Fam : ι → Finset α) {S T : Finset ι} (h : S ⊆ T) :
    facetQuot k Fam S →+* facetQuot k Fam T :=
  Ideal.Quotient.factor (capIdeal_mono Fam h)

omit [DecidableEq ι] [LinearOrder ι] [DecidableEq α] in
@[simp]
theorem facetFactor_mk {S T : Finset ι} (h : S ⊆ T) (p : MvPolynomial α k) :
    facetFactor k Fam h (Ideal.Quotient.mk (capIdeal k Fam S) p)
      = Ideal.Quotient.mk (capIdeal k Fam T) p :=
  Ideal.Quotient.factor_mk _ p

/-- The differential of the facet complex in quotient form. -/
def quotCoboundary (k : Type*) [CommRing k] (Fam : ι → Finset α)
    (om : ∀ T : Finset ι, facetQuot k Fam T) (T : Finset ι) : facetQuot k Fam T :=
  ∑ i ∈ T, faceSign (facetQuot k Fam T) T i
    * facetFactor k Fam (Finset.erase_subset i T) (om (T.erase i))

omit [DecidableEq ι] [DecidableEq α] in
theorem mk_faceSign (T : Finset ι) (i : ι) :
    Ideal.Quotient.mk (capIdeal k Fam T) (faceSign (MvPolynomial α k) T i)
      = faceSign (facetQuot k Fam T) T i := by
  rw [faceSign, faceSign, map_pow, map_neg, map_one]

/-- **The two forms of the differential agree.** -/
theorem quotCoboundary_mk (om : Finset ι → MvPolynomial α k) (T : Finset ι) :
    quotCoboundary k Fam (fun S => Ideal.Quotient.mk (capIdeal k Fam S) (om S)) T
      = Ideal.Quotient.mk (capIdeal k Fam T) (facetCoboundary k Fam om T) := by
  rw [facetCoboundary, map_sum, quotCoboundary]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, mk_faceSign, facetFactor_mk]
  congr 1
  refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
  exact sub_capRestrict_mem_capIdeal Fam T (om (T.erase i))

omit [DecidableEq α] in
/-- The differential of a cochain given by representatives is represented by the plain alternating
sum of those representatives. -/
theorem quotCoboundary_mk_sum (om : Finset ι → MvPolynomial α k) (T : Finset ι) :
    quotCoboundary k Fam (fun S => Ideal.Quotient.mk (capIdeal k Fam S) (om S)) T
      = Ideal.Quotient.mk (capIdeal k Fam T)
        (∑ i ∈ T, faceSign (MvPolynomial α k) T i * om (T.erase i)) := by
  rw [quotCoboundary, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, mk_faceSign, facetFactor_mk]

/-- The differential is already truncated to what its facets carry. -/
theorem capRestrict_facetCoboundary (om : Finset ι → MvPolynomial α k) (T : Finset ι) :
    capRestrict k Fam T (facetCoboundary k Fam om T) = facetCoboundary k Fam om T := by
  rw [capRestrict_eq_self_iff]
  intro b hb
  by_contra hcon
  rw [coeff_facetCoboundary, if_neg hcon] at hb
  exact hb rfl

/-- **The augmented facet complex in quotient form is exact in every positive degree.**

A cochain assigning to every `c+1`-element set of facets a class modulo the sum of their coordinate
ideals, vanishing off the given facet family, and killed by the differential, is the differential of
a cochain one degree lower with the same vanishing properties. -/
theorem facetQuotientComplex_exact (facets : Finset ι) (c : ℕ)
    (om : ∀ T : Finset ι, facetQuot k Fam T)
    (hdeg : ∀ T : Finset ι, T.card ≠ c + 1 → om T = 0)
    (hsub : ∀ T : Finset ι, ¬ T ⊆ facets → om T = 0)
    (hcoc : ∀ T : Finset ι, T ⊆ facets → quotCoboundary k Fam om T = 0) :
    ∃ eta : ∀ T : Finset ι, facetQuot k Fam T,
      (∀ T : Finset ι, T.card ≠ c → eta T = 0) ∧ (∀ T : Finset ι, ¬ T ⊆ facets → eta T = 0)
        ∧ ∀ T : Finset ι, T ⊆ facets → quotCoboundary k Fam eta T = om T := by
  choose p hp using fun T : Finset ι => Ideal.Quotient.mk_surjective (I := capIdeal k Fam T) (om T)
  set q : Finset ι → MvPolynomial α k := fun T => capRestrict k Fam T (p T) with hq
  have hmk : ∀ T : Finset ι, Ideal.Quotient.mk (capIdeal k Fam T) (q T) = om T := by
    intro T
    rw [hq, ← hp T]
    refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
    have hn := neg_mem (sub_capRestrict_mem_capIdeal Fam T (p T))
    rw [neg_sub] at hn
    exact hn
  have hzeroT : ∀ T : Finset ι, om T = 0 → q T = 0 := by
    intro T hT
    rw [hq]
    refine (capRestrict_eq_zero_iff_mem Fam T (p T)).mpr ?_
    exact (Ideal.Quotient.eq_zero_iff_mem).mp (by rw [hp T, hT])
  have hdeg' : ∀ T : Finset ι, T.card ≠ c + 1 → q T = 0 := fun T h => hzeroT T (hdeg T h)
  have hsub' : ∀ T : Finset ι, ¬ T ⊆ facets → q T = 0 := fun T h => hzeroT T (hsub T h)
  have hcap' : ∀ T : Finset ι, capRestrict k Fam T (q T) = q T := fun T => capRestrict_idem Fam T _
  have hom : (fun S : Finset ι => Ideal.Quotient.mk (capIdeal k Fam S) (q S)) = om := funext hmk
  have hcoc' : ∀ T : Finset ι, T ⊆ facets → facetCoboundary k Fam q T = 0 := by
    intro T hT
    have hzero : Ideal.Quotient.mk (capIdeal k Fam T) (facetCoboundary k Fam q T) = 0 := by
      rw [← quotCoboundary_mk, hom]
      exact hcoc T hT
    have hmem : facetCoboundary k Fam q T ∈ capIdeal k Fam T :=
      Ideal.Quotient.eq_zero_iff_mem.mp hzero
    have hres := (capRestrict_eq_zero_iff_mem Fam T (facetCoboundary k Fam q T)).mpr hmem
    rwa [capRestrict_facetCoboundary] at hres
  obtain ⟨h1, h2, _, h4⟩ := facetComplex_exact Fam facets c q hdeg' hsub' hcap' hcoc'
  refine ⟨fun T => Ideal.Quotient.mk (capIdeal k Fam T) (coneAssemble k Fam facets q T), ?_, ?_, ?_⟩
  · intro T hT
    show Ideal.Quotient.mk (capIdeal k Fam T) (coneAssemble k Fam facets q T) = 0
    rw [h1 T hT, map_zero]
  · intro T hT
    show Ideal.Quotient.mk (capIdeal k Fam T) (coneAssemble k Fam facets q T) = 0
    rw [h2 T hT, map_zero]
  · intro T hT
    rw [quotCoboundary_mk, h4 T hT, hmk T]

end

end GaloisForLFunctions.HTGeometry
