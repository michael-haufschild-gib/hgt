import GaloisForLFunctions.SimplicialConstraintTower

/-!
# The first nonpure two-thick HT relation geometry

This file certifies the finite simplicial geometry used by the facet-sewn realization theorem.  Its
seven facets form a six-vertex model of `S¹ ∨ S²`: a three-cycle and the boundary of a tetrahedron
meet at one vertex.  The formal conclusions needed by the analytic realization are exact facet
maximality, nonpurity, two-thickness, and the complete list of minimal nonfaces.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

/-- The six vertices of the wedge geometry. -/
abbrev WedgeVertex := Fin 6

/-- The three edges of a cycle and four triangles of a tetrahedral boundary, meeting at vertex `0`. -/
def wedgeFacets : Finset (Finset WedgeVertex) :=
  {{0, 1}, {1, 2}, {2, 0}, {0, 3, 4}, {0, 3, 5}, {0, 4, 5}, {3, 4, 5}}

/-- The facet family as a set, in the representation used by the constraint-tower API. -/
def wedgeFacetSet : Set (Finset WedgeVertex) := ↑wedgeFacets

local instance wedgeFacetMembership (J : Finset WedgeVertex) :
    Decidable (J ∈ wedgeFacetSet) := by
  change Decidable (J ∈ wedgeFacets)
  infer_instance

local instance wedgeFaceMembership (J : Finset WedgeVertex) :
    Decidable (IsFaceOf wedgeFacetSet J) := by
  unfold IsFaceOf
  infer_instance

/-- A nonface is minimal when every strict subface belongs to the complex. -/
def MinimalNonface {α : Type*} [DecidableEq α]
    (facets : Set (Finset α)) (J : Finset α) : Prop :=
  ¬ IsFaceOf facets J ∧ ∀ K, K ⊂ J → IsFaceOf facets K

local instance wedgeMinimalNonfaceDecidable (J : Finset WedgeVertex) :
    Decidable (MinimalNonface wedgeFacetSet J) := by
  unfold MinimalNonface
  infer_instance

/-- The eight minimal nonfaces: six cross-edges, the cycle triangle, and the tetrahedron. -/
def wedgeMinimalNonfaces : Finset (Finset WedgeVertex) :=
  {{1, 3}, {1, 4}, {1, 5}, {2, 3}, {2, 4}, {2, 5}, {0, 1, 2}, {0, 3, 4, 5}}

set_option maxRecDepth 100000 in
/-- The displayed facets are pairwise incomparable, hence are the actual maximal faces. -/
theorem wedge_facetAntichain : FacetAntichain wedgeFacetSet := by
  have h : ∀ F ∈ wedgeFacets, ∀ G ∈ wedgeFacets, F ⊆ G → F = G := by
    decide
  intro F hF G hG hFG
  change F ∈ wedgeFacets at hF
  change G ∈ wedgeFacets at hG
  exact h F hF G hG hFG

/-- The wedge geometry is nonpure: it has facets of cardinalities two and three. -/
theorem wedge_not_pure : ¬ ∃ d, PureOfCard wedgeFacetSet d := by
  rintro ⟨d, hd⟩
  have h01 : ({0, 1} : Finset WedgeVertex) ∈ wedgeFacetSet := by
    change ({0, 1} : Finset WedgeVertex) ∈ wedgeFacets
    decide
  have h034 : ({0, 3, 4} : Finset WedgeVertex) ∈ wedgeFacetSet := by
    change ({0, 3, 4} : Finset WedgeVertex) ∈ wedgeFacets
    decide
  have h2 := hd h01
  have h3 := hd h034
  have hc2 : ({0, 1} : Finset WedgeVertex).card = 2 := by decide
  have hc3 : ({0, 3, 4} : Finset WedgeVertex).card = 3 := by decide
  rw [hc2] at h2
  rw [hc3] at h3
  omega

/-- Every nonfacet face has two distinct immediate coface directions. -/
theorem wedge_twoThick : TwoThick wedgeFacetSet := by
  have h : ∀ J : Finset WedgeVertex,
      (∃ F ∈ wedgeFacets, J ⊆ F) → J ∉ wedgeFacets →
        ∃ q u : WedgeVertex, q ≠ u ∧ q ∉ J ∧ u ∉ J ∧
          (∃ F ∈ wedgeFacets, insert q J ⊆ F) ∧
          (∃ F ∈ wedgeFacets, insert u J ⊆ F) := by
    decide
  intro J hJface hJnot
  unfold IsFaceOf at hJface ⊢
  change J ∉ wedgeFacets at hJnot
  rcases h J hJface hJnot with ⟨q, u, hqu, hqJ, huJ, hq, hu⟩
  exact ⟨q, u, hqu, hqJ, huJ, hq, hu⟩

set_option maxRecDepth 100000 in
/-- The displayed eight sets are exactly the minimal nonfaces of the wedge geometry. -/
theorem wedge_minimalNonface_iff : ∀ J : Finset WedgeVertex,
    MinimalNonface wedgeFacetSet J ↔ J ∈ wedgeMinimalNonfaces := by
  decide

/-- Complete finite certificate for the nonpure two-thick wedge relation geometry. -/
theorem wedge_geometry_certificate :
    FacetAntichain wedgeFacetSet ∧
      (¬ ∃ d, PureOfCard wedgeFacetSet d) ∧
      TwoThick wedgeFacetSet ∧
      ∀ J : Finset WedgeVertex,
        MinimalNonface wedgeFacetSet J ↔ J ∈ wedgeMinimalNonfaces :=
  ⟨wedge_facetAntichain, wedge_not_pure, wedge_twoThick, wedge_minimalNonface_iff⟩

end GaloisForLFunctions.HTGeometry
