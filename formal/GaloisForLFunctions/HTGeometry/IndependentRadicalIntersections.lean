import GaloisForLFunctions.HTGeometry.MultiquadraticAdjoinDegree
import Mathlib.FieldTheory.LinearDisjoint

noncomputable section
namespace GaloisForLFunctions.HTGeometry
variable {F L : Type*} [Field F] [Field L] [Algebra F L]
variable {ι : Type*} (d : ι → F) (r : ι → L)
variable (h2 : (2 : L) ≠ 0) (hsq : ∀ i, r i * r i = algebraMap F L (d i))
variable (hind : ∀ T : Finset ι, T.Nonempty → ¬ IsSquare (∏ i ∈ T, d i))

include h2 hsq hind in
/-- Disjoint finite subsets of independent radicals generate linearly disjoint fields. -/
theorem independent_radical_finsets_linearDisjoint (S T : Finset ι) (hst : Disjoint S T) :
    (IntermediateField.adjoin F (r '' (S : Set ι))).LinearDisjoint
      (IntermediateField.adjoin F (r '' (T : Set ι))) := by
  classical
  have hd (U : Finset ι) := (multiquadratic_degree_and_twists d r h2 hsq hind U).1
  letI : FiniteDimensional F (IntermediateField.adjoin F (r '' (S : Set ι))) :=
    FiniteDimensional.of_finrank_pos (by rw [hd]; positivity)
  letI : FiniteDimensional F (IntermediateField.adjoin F (r '' (T : Set ι))) :=
    FiniteDimensional.of_finrank_pos (by rw [hd]; positivity)
  apply IntermediateField.LinearDisjoint.of_finrank_sup
  rw [← IntermediateField.adjoin_union, ← Set.image_union, ← Finset.coe_union,
    hd, hd, hd, Finset.card_union_of_disjoint hst, pow_add]

/-- Every element of an adjoin of an indexed family uses only finitely many labels. -/
theorem exists_finset_of_mem_adjoin_image {A : Set ι} {x : L}
    (hx : x ∈ IntermediateField.adjoin F (r '' A)) :
    ∃ S : Finset ι, (S : Set ι) ⊆ A ∧
      x ∈ IntermediateField.adjoin F (r '' (S : Set ι)) := by
  classical
  obtain ⟨X, hX, hx⟩ := IntermediateField.exists_finset_of_mem_adjoin hx
  have hl : ∀ y : X, ∃ i : ι, i ∈ A ∧ r i = (y : L) := fun y => hX y.property
  choose label hlabel hroot using hl
  refine ⟨Finset.univ.image label, ?_, ?_⟩
  · intro i hi
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hi
    exact hlabel y
  · apply (IntermediateField.adjoin_le_iff.mpr (show (X : Set L) ⊆
      IntermediateField.adjoin F (r '' ((Finset.univ.image label : Finset ι) : Set ι))
        from ?_)) hx
    intro y hy
    apply IntermediateField.subset_adjoin
    exact ⟨label ⟨y, hy⟩, Finset.mem_image.mpr ⟨⟨y, hy⟩, Finset.mem_univ _, rfl⟩,
      hroot ⟨y, hy⟩⟩

include h2 hsq hind in
/-- The intersection law extends to arbitrary, possibly infinite, disjoint label sets. -/
theorem independent_radical_sets_inf_eq_bot (A B : Set ι) (hab : Disjoint A B) :
    IntermediateField.adjoin F (r '' A) ⊓ IntermediateField.adjoin F (r '' B) = ⊥ := by
  classical
  apply le_antisymm
  · intro x hx
    obtain ⟨S, hSA, hxS⟩ := exists_finset_of_mem_adjoin_image r hx.1
    obtain ⟨T, hTB, hxT⟩ := exists_finset_of_mem_adjoin_image r hx.2
    have hst : Disjoint S T := Finset.disjoint_left.mpr fun i hi hj =>
      Set.disjoint_left.mp hab (hSA hi) (hTB hj)
    have he := (independent_radical_finsets_linearDisjoint d r h2 hsq hind S T hst).inf_eq_bot
    have hx' : x ∈ IntermediateField.adjoin F (r '' (S : Set ι)) ⊓
        IntermediateField.adjoin F (r '' (T : Set ι)) := ⟨hxS, hxT⟩
    rwa [he] at hx'
  · exact bot_le

end GaloisForLFunctions.HTGeometry
