import GaloisForLFunctions.HTGeometry.CubicFamilyAction

/-!
# Joint splitting groups of cubic families

The splitting field of the product acts faithfully on the union of all cubic
root sets. Independent discriminants force the full product of S3 groups,
and hence splitting degree six to the number of channels.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Polynomial
variable {F ι : Type*} [Field F] [Fintype ι]

/-- The polynomial whose splitting field is the finite cubic compositum. -/
def cubicFamilyPolynomial (P : ι → Cubic F) : F[X] := ∏ i, (P i).toPoly

theorem cubicFamilyPolynomial_ne_zero (P : ι → Cubic F)
    (hirr : ∀ i, Irreducible (P i).toPoly) : cubicFamilyPolynomial P ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => (hirr i).ne_zero)

theorem cubicFamily_member_splits (P : ι → Cubic F)
    (hirr : ∀ i, Irreducible (P i).toPoly) (i : ι) :
    ((P i).toPoly.map (algebraMap F (cubicFamilyPolynomial P).SplittingField)).Splits := by
  classical
  apply (SplittingField.splits (cubicFamilyPolynomial P)).of_dvd
    (Polynomial.map_ne_zero (cubicFamilyPolynomial_ne_zero P hirr))
  apply (Polynomial.map_dvd_map' _).mpr
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

/-- An ordering of each cubic's roots inside the one common splitting field. -/
def cubicFamilySplittingRootEquiv [CharZero F] (P : ι → Cubic F)
    (ha : ∀ i, (P i).a ≠ 0) (hirr : ∀ i, Irreducible (P i).toPoly) (i : ι) :
    (P i).toPoly.rootSet (cubicFamilyPolynomial P).SplittingField ≃ Fin 3 := by
  classical
  apply Fintype.equivFinOfCardEq
  rw [Polynomial.card_rootSet_eq_natDegree (hirr i).separable
    (cubicFamily_member_splits P hirr i)]
  exact Cubic.natDegree_of_a_ne_zero (ha i)

/-- Restriction to all ordered cubic root sets in their common splitting field. -/
def cubicFamilySplittingAction [CharZero F] (P : ι → Cubic F)
    (ha : ∀ i, (P i).a ≠ 0) (hirr : ∀ i, Irreducible (P i).toPoly) :
    (cubicFamilyPolynomial P).Gal →* (ι → Equiv.Perm (Fin 3)) := by
  letI : ∀ i, Fact (((P i).toPoly.map
      (algebraMap F (cubicFamilyPolynomial P).SplittingField)).Splits) :=
    fun i => ⟨cubicFamily_member_splits P hirr i⟩
  exact cubicFamilyRootAction P (cubicFamilySplittingRootEquiv P ha hirr)

theorem cubicFamilySplittingAction_injective [CharZero F] (P : ι → Cubic F)
    (ha : ∀ i, (P i).a ≠ 0) (hirr : ∀ i, Irreducible (P i).toPoly) :
    Function.Injective (cubicFamilySplittingAction P ha hirr) := by
  classical
  let L := (cubicFamilyPolynomial P).SplittingField
  letI : ∀ i, Fact (((P i).toPoly.map (algebraMap F L)).Splits) :=
    fun i => ⟨cubicFamily_member_splits P hirr i⟩
  let e := cubicFamilySplittingRootEquiv P ha hirr
  intro σ τ h
  apply Gal.ext
  intro x hx
  have hx0 := Polynomial.aeval_eq_zero_of_mem_rootSet hx
  change (aeval x) (∏ i, (P i).toPoly) = 0 at hx0
  rw [map_prod] at hx0
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hx0
  have hxi : x ∈ (P i).toPoly.rootSet L :=
    (Polynomial.mem_rootSet_of_ne (hirr i).ne_zero).mpr hi
  let z : (P i).toPoly.rootSet L := ⟨x, hxi⟩
  have hp := congrArg (fun f => f i (e i z)) h
  have he := congrArg (fun k => ((e i).symm k : L)) hp
  change ((e i).symm (cubicOrderedRootAction (P i) (e i) σ (e i z)) : L) =
    ((e i).symm (cubicOrderedRootAction (P i) (e i) τ (e i z)) : L) at he
  simp only [cubicOrderedRootAction_apply, Equiv.symm_apply_apply, z] at he
  exact he

/-- The exact finite joint S3 theorem for independent cubic discriminants. -/
def cubicFamilyGaloisEquiv [CharZero F] (P : ι → Cubic F)
    (ha : ∀ i, (P i).a ≠ 0) (hirr : ∀ i, Irreducible (P i).toPoly)
    (hind : ∀ T : Finset ι, T.Nonempty → ¬ IsSquare (∏ i ∈ T, (P i).discr)) :
    (cubicFamilyPolynomial P).Gal ≃* (ι → Equiv.Perm (Fin 3)) := by
  letI : ∀ i, Fact (((P i).toPoly.map
      (algebraMap F (cubicFamilyPolynomial P).SplittingField)).Splits) :=
    fun i => ⟨cubicFamily_member_splits P hirr i⟩
  exact MulEquiv.ofBijective (cubicFamilySplittingAction P ha hirr)
    ⟨cubicFamilySplittingAction_injective P ha hirr,
      cubicFamilyRootAction_surjective P ha hirr hind (cubicFamilySplittingRootEquiv P ha hirr)⟩

/-- Splitting degrees multiply even when no pairwise root-set disjointness is assumed. -/
theorem cubicFamily_splittingField_finrank [CharZero F] (P : ι → Cubic F)
    (ha : ∀ i, (P i).a ≠ 0) (hirr : ∀ i, Irreducible (P i).toPoly)
    (hind : ∀ T : Finset ι, T.Nonempty → ¬ IsSquare (∏ i ∈ T, (P i).discr)) :
    Module.finrank F (cubicFamilyPolynomial P).SplittingField = 6 ^ Fintype.card ι := by
  let L := (cubicFamilyPolynomial P).SplittingField
  letI : IsGalois F L := ⟨⟩
  rw [← IsGalois.card_aut_eq_finrank F L]
  change Nat.card (cubicFamilyPolynomial P).Gal = _
  rw [Nat.card_congr (cubicFamilyGaloisEquiv P ha hirr hind).toEquiv, Nat.card_fun,
    Nat.card_perm]
  norm_num

end GaloisForLFunctions.HTGeometry
