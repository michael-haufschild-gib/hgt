import GaloisForLFunctions.HTGeometry.SimplicialConstraintTower

/-!
# The simplex boundary realizes purity and ridge thickness jointly

The `d`-subsets of a `(d+1)`-element vertex set form the boundary complex of a simplex.  It is pure of
card `d`, and it is ridge thick because the complement of a ridge has exactly two vertices, each of
which extends it to a facet.  Purity and ridge thickness are therefore jointly realized, so the
two-coface-direction theorem applies to an explicit complex.
-/

namespace GaloisForLFunctions

variable {α : Type*} [DecidableEq α]

/-- Facets of the boundary complex of a simplex on `V`: the `d`-element subsets of `V`. -/
def simplexBoundaryFacets (V : Finset α) (d : ℕ) : Set (Finset α) :=
  {F | F ⊆ V ∧ F.card = d}

omit [DecidableEq α] in
theorem pureOfCard_simplexBoundaryFacets (V : Finset α) (d : ℕ) :
    PureOfCard (simplexBoundaryFacets V d) d := fun _ hF => hF.2

omit [DecidableEq α] in
theorem simplexBoundaryFacets_nonempty {V : Finset α} {d : ℕ} (hd : d ≤ V.card) :
    (simplexBoundaryFacets V d).Nonempty := by
  obtain ⟨F, hFV, hFcard⟩ := Finset.exists_subset_card_eq hd
  exact ⟨F, hFV, hFcard⟩

omit [DecidableEq α] in
theorem isFaceOf_empty_simplexBoundaryFacets {V : Finset α} {d : ℕ} (hd : d ≤ V.card) :
    IsFaceOf (simplexBoundaryFacets V d) (∅ : Finset α) := by
  obtain ⟨F, hF⟩ := simplexBoundaryFacets_nonempty hd
  exact ⟨F, hF, Finset.empty_subset F⟩

/-- **Ridge thickness of the simplex boundary.**  The complement of a ridge has exactly two
vertices, and each extends the ridge to a facet. -/
theorem ridgeThick_simplexBoundaryFacets {V : Finset α} {d : ℕ} (hV : V.card = d + 1) :
    RidgeThick (simplexBoundaryFacets V d) d := by
  intro R hR hcard
  obtain ⟨F, ⟨hFV, _⟩, hRF⟩ := hR
  have hRV : R ⊆ V := hRF.trans hFV
  have hsdiff : (V \ R).card = 2 := by
    rw [Finset.card_sdiff_of_subset hRV, hV]
    omega
  obtain ⟨x, y, hxy, hxyeq⟩ := Finset.card_eq_two.mp hsdiff
  have hxmem : x ∈ V \ R := by rw [hxyeq]; simp
  have hymem : y ∈ V \ R := by rw [hxyeq]; simp
  have hxV : x ∈ V := (Finset.mem_sdiff.mp hxmem).1
  have hxR : x ∉ R := (Finset.mem_sdiff.mp hxmem).2
  have hyV : y ∈ V := (Finset.mem_sdiff.mp hymem).1
  have hyR : y ∉ R := (Finset.mem_sdiff.mp hymem).2
  refine ⟨insert x R, ⟨Finset.insert_subset hxV hRV, ?_⟩,
    insert y R, ⟨Finset.insert_subset hyV hRV, ?_⟩, ?_, Finset.subset_insert _ _,
    Finset.subset_insert _ _⟩
  · rw [Finset.card_insert_of_notMem hxR]
    omega
  · rw [Finset.card_insert_of_notMem hyR]
    omega
  · intro hEq
    have hx : x ∈ insert y R := by rw [← hEq]; simp
    rcases Finset.mem_insert.mp hx with h | h
    · exact hxy h
    · exact hxR h

/-- **Two coface directions on the simplex boundary.**  With no interface premise, the empty face of
the boundary complex of a positive-dimensional simplex has two distinct coface directions. -/
theorem exists_two_coface_directions_simplexBoundary {V : Finset α} {d : ℕ}
    (hV : V.card = d + 1) (hd : 0 < d) :
    ∃ q u : α, q ≠ u ∧ q ∉ (∅ : Finset α) ∧ u ∉ (∅ : Finset α) ∧
      IsFaceOf (simplexBoundaryFacets V d) (insert q ∅) ∧
      IsFaceOf (simplexBoundaryFacets V d) (insert u ∅) := by
  refine exists_two_coface_directions_of_pure_ridgeThick
    (pureOfCard_simplexBoundaryFacets V d) (ridgeThick_simplexBoundaryFacets hV)
    (isFaceOf_empty_simplexBoundaryFacets (by omega)) ?_
  simpa using hd

end GaloisForLFunctions
