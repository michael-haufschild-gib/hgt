import GaloisForLFunctions.HTGeometry.StanleyReisnerVertexRelation
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.CoordinateArrangementCounts

/-!
# Rational points of Stanley–Reisner rings

A field-valued character of the quotient is determined by a word whose
nonzero support lies in a facet. The face strata in Andrusov's point-count
argument thus count two different spaces: nonzero supports give the affine
Stanley–Reisner scheme and zero supports give the arrangement complement.
-/

namespace GaloisForLFunctions.HTGeometry
open Finset MvPolynomial ArithmeticHarmonicAnalysis.Codes
open scoped Classical
noncomputable section

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

/-- All faces represented by the given facets, with overlaps counted only once. -/
def facetFaces (facets : Finset (Finset ι)) : Finset (Finset ι) :=
  facets.biUnion powerset

theorem mem_facetFaces (facets : Finset (Finset ι)) (s : Finset ι) :
    s ∈ facetFaces facets ↔ IsFaceOf (facets : Set (Finset ι)) s := by
  simp [facetFaces, IsFaceOf]

/-- An evaluation kills the nonface ideal exactly on the union of the facet
coordinate planes. The field assumption ensures a prime evaluation kernel. -/
theorem stanleyReisnerIdeal_le_eval_ker (facets : Finset (Finset ι)) (x : ι → F) :
    stanleyReisnerIdeal F facets ≤ RingHom.ker (eval x) ↔
      univ.filter (fun i => x i ≠ 0) ∈ facetFaces facets := by
  rw [stanleyReisnerIdeal_eq_inf_facetIdeal, (RingHom.ker_isPrime (eval x)).inf_le',
    mem_facetFaces]
  unfold IsFaceOf
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [facetIdeal, Ideal.span_le]
  constructor
  · intro h i hi
    by_contra hn
    have hzero := h (Set.mem_image_of_mem (MvPolynomial.X (R := F)) hn)
    exact (mem_filter.mp hi).2 (by simpa [RingHom.mem_ker] using hzero)
  · rintro h _ ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, eval_X]
    by_contra hn
    exact hi (h (mem_filter.mpr ⟨mem_univ _, hn⟩))

/-- Characters of the quotient are precisely the admitted coordinate evaluations. -/
def stanleyReisnerPointEquiv (facets : Finset (Finset ι)) :
    (stanleyReisnerRing F facets →ₐ[F] F) ≃
      {x : ι → F // univ.filter (fun i => x i ≠ 0) ∈ facetFaces facets} where
  toFun χ := ⟨fun i => χ (srVertexX F facets i), by
    apply (stanleyReisnerIdeal_le_eval_ker _ _).mp
    let I := stanleyReisnerIdeal F facets
    have hχ : aeval (fun i => χ (srVertexX F facets i)) =
        χ.comp (Ideal.Quotient.mkₐ F I) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [I, srVertexX]
    intro p hp
    change aeval (fun i => χ (srVertexX F facets i)) p = 0
    rw [hχ]
    change χ (Ideal.Quotient.mk I p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]⟩
  invFun x := Ideal.Quotient.liftₐ _ (aeval x.val) fun p hp => by
    have h := (stanleyReisnerIdeal_le_eval_ker facets x.val).mpr x.property hp
    exact h
  left_inv χ := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp [srVertexX, Ideal.Quotient.liftₐ_apply]
  right_inv x := by
    apply Subtype.ext
    funext i
    simp [srVertexX, Ideal.Quotient.liftₐ_apply]

/-- The affine quotient and the arrangement complement weight the same faces
by opposite dimensions of the coordinate torus. -/
theorem card_stanleyReisner_characters [Fintype F] (facets : Finset (Finset ι)) :
    Nat.card (stanleyReisnerRing F facets →ₐ[F] F) =
      ∑ s ∈ facetFaces facets, (Fintype.card F - 1) ^ s.card := by
  let D : ι → Finset F := fun _ => ({0} : Finset F)ᶜ
  have he (x : ι → F) : matchSet D x = univ.filter fun i => x i ≠ 0 := by
    ext i
    simp [matchSet, D]
  let e : {x : ι → F // univ.filter (fun i => x i ≠ 0) ∈ facetFaces facets} ≃
      ↥(arrangementWords D (facetFaces facets)) :=
    Equiv.subtypeEquivRight fun x => by simp [arrangementWords, he]
  rw [Nat.card_congr ((stanleyReisnerPointEquiv facets).trans e), Nat.card_eq_fintype_card,
    Fintype.card_coe, card_arrangementWords]
  have hF : Fintype.card F - (Fintype.card F - 1) = 1 := by
    have := Fintype.card_pos (α := F)
    omega
  refine sum_congr rfl fun s _ => ?_
  simp [D, card_compl, hF, Fintype.prod_ite_mem]

/-- The Alexander dual admits exactly the complements of nonfaces. -/
def dualFaceFamily (facets : Finset (Finset ι)) : Finset (Finset ι) :=
  univ.filter fun s => sᶜ ∉ facetFaces facets

/-- Alexander duality partitions affine space into Stanley–Reisner points
and the arrangement complement for the dual complex. -/
theorem stanleyReisner_add_dualArrangement [Fintype F] (facets : Finset (Finset ι)) :
    Nat.card (stanleyReisnerRing F facets →ₐ[F] F) +
      (arrangementWords (fun _ : ι => ({0} : Finset F)) (dualFaceFamily facets)).card =
      Fintype.card F ^ Fintype.card ι := by
  let S := univ.filter fun x : ι → F => univ.filter (fun i => x i ≠ 0) ∈ facetFaces facets
  have e : (stanleyReisnerRing F facets →ₐ[F] F) ≃ ↥S :=
    (stanleyReisnerPointEquiv facets).trans (Equiv.subtypeEquivRight fun _ => by simp [S])
  have he (x : ι → F) :
      (matchSet (fun _ : ι => ({0} : Finset F)) x)ᶜ = univ.filter (fun i => x i ≠ 0) := by
    ext i
    simp [matchSet]
  have hc : arrangementWords (fun _ : ι => ({0} : Finset F)) (dualFaceFamily facets) = Sᶜ := by
    ext x
    simp [arrangementWords, dualFaceFamily, he, S]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, hc, card_compl]
  simpa using Nat.add_sub_of_le S.card_le_univ

#print axioms card_stanleyReisner_characters
#print axioms stanleyReisner_add_dualArrangement

end
end GaloisForLFunctions.HTGeometry
