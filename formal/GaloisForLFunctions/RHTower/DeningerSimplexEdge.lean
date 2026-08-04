import GaloisForLFunctions.RHTower.DeningerEdgeCocycle

/-!
# Edges of a simplex of a classifying space

A simplex of a classifying space is a functor out of a linear order, so between any two of its
vertices there is a group element, and these compose.  Restricting the simplex along the edge
joining two vertices returns that element.

* `deningerSimplexEdge` : the element between two vertices of a simplex.
* `deningerSimplexEdge_comp` : the elements compose.
* `deningerSimplexEdge_restrict` : restricting along an edge returns the element.
-/

namespace RHTower

open CategoryTheory SSet SimplexCategory Opposite

universe u

/-- The group element of a simplex of a classifying space between two of its vertices. -/
def deningerSimplexEdge {G : Type u} [Group G] {m : ℕ}
    (F : (deningerClassifying G).obj (op (mk m))) {a b : Fin (m + 1)} (h : a ≤ b) : G :=
  F.map (homOfLE h)

/-- **The elements of a simplex compose.** -/
theorem deningerSimplexEdge_comp {G : Type u} [Group G] {m : ℕ}
    (F : (deningerClassifying G).obj (op (mk m))) {a b c : Fin (m + 1)} (hab : a ≤ b)
    (hbc : b ≤ c) :
    deningerSimplexEdge F (hab.trans hbc) =
      deningerSimplexEdge F hbc * deningerSimplexEdge F hab := by
  show F.map (homOfLE (hab.trans hbc)) = _
  rw [show homOfLE (hab.trans hbc) = homOfLE hab ≫ homOfLE hbc from rfl, F.map_comp]
  rfl

/-- **The element between two equal vertices is trivial.** -/
theorem deningerSimplexEdge_refl {G : Type u} [Group G] {m : ℕ}
    (F : (deningerClassifying G).obj (op (mk m))) (a : Fin (m + 1)) :
    deningerSimplexEdge F (le_refl a) = 1 := by
  show F.map (homOfLE (le_refl a)) = 1
  rw [show homOfLE (le_refl a) = 𝟙 a from rfl, F.map_id]
  rfl

/-- **Restricting a simplex along an edge returns the element of that edge.** -/
theorem deningerSimplexEdge_restrict {G : Type u} [Group G] {m : ℕ}
    (F : (deningerClassifying G).obj (op (mk m))) {a b : Fin (m + 1)} (h : a ≤ b) :
    deningerEdgeEquiv G ((deningerClassifying G).map (mkOfLe a b h).op F) =
      deningerSimplexEdge F h := rfl

end RHTower
