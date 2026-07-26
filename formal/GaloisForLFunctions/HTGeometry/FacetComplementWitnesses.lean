import GaloisForLFunctions.HTGeometry.SimplicialConstraintTower

/-!
# Realizations of the rank-one facet-complement interface

The empty family, the full simplex, and the vertex-deletion family all have rank-one complements,
which are exactly the two cases separated by the simplex-or-deletion classification.
-/

namespace GaloisForLFunctions

variable {α : Type*} [DecidableEq α]

theorem facetComplementRankOne_empty (V : Finset α) :
    FacetComplementRankOne V (∅ : Set (Finset α)) := by
  intro F hF
  exact absurd hF (Set.notMem_empty F)

theorem facetComplementRankOne_singleton (V : Finset α) :
    FacetComplementRankOne V ({V} : Set (Finset α)) := by
  intro F hF
  rw [Set.mem_singleton_iff] at hF
  subst hF
  exact ⟨subset_rfl, by simp⟩

/-- The vertex-deletion family has rank-one complements. -/
theorem facetComplementRankOne_deletion (V : Finset α) :
    FacetComplementRankOne V ((fun v => V.erase v) '' (V : Set α)) := by
  rintro F ⟨v, hv, rfl⟩
  refine ⟨Finset.erase_subset _ _, ?_⟩
  rw [Finset.sdiff_erase (Finset.mem_coe.mp hv)]
  simp

end GaloisForLFunctions
