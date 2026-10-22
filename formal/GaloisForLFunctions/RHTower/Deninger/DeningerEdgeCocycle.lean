import GaloisForLFunctions.RHTower.Deninger.DeningerClassifyingHomExt

/-!
# The cocycle identity for edges

A map into a classifying space assigns a group element to every edge of the source.  A triangle of
the source is sent to a triangle of the classifying space, whose long edge is the composite of the
two short ones, so the assignment is a cocycle: the element of the long edge is the product of the
elements of the short ones.

* `deningerEdgeElt` : the element assigned to an edge.
* `deningerEdgeElt_comp` : the cocycle identity.
-/

namespace RHTower

open CategoryTheory SSet SimplexCategory Opposite

universe u

/-- The group element assigned to an edge by a map into a classifying space. -/
def deningerEdgeElt {Y : SSet.{u}} {G : Type u} [Group G] (u : Y ⟶ deningerClassifying G)
    (e : Y.obj (op (mk 1))) : G :=
  deningerEdgeEquiv G (u.app (op (mk 1)) e)

/-- The element assigned to an edge of a classifying space is the edge itself. -/
theorem deningerEdgeElt_id {G : Type u} [Group G]
    (e : (deningerClassifying G).obj (op (mk 1))) :
    deningerEdgeElt (𝟙 (deningerClassifying G)) e = deningerEdgeEquiv G e := rfl

/-- **The cocycle identity.**  The element of the long edge of a triangle is the product of the
elements of its two short edges. -/
theorem deningerEdgeElt_comp {Y : SSet.{u}} {G : Type u} [Group G]
    (u : Y ⟶ deningerClassifying G) (t : Y.obj (op (mk 2))) :
    deningerEdgeElt u (Y.map (SimplexCategory.δ 1).op t) =
      deningerEdgeElt u (Y.map (SimplexCategory.δ 0).op t) *
        deningerEdgeElt u (Y.map (SimplexCategory.δ 2).op t) := by
  have hnat : ∀ j : Fin 3, u.app (op (mk 1)) (Y.map (SimplexCategory.δ j).op t) =
      (deningerClassifying G).map (SimplexCategory.δ j).op (u.app (op (mk 2)) t) :=
    fun j => NatTrans.naturality_apply u (SimplexCategory.δ j).op t
  set F : ComposableArrows (DeningerPt G) 2 := u.app (op (mk 2)) t with hF
  have hface : ∀ j : Fin 3,
      deningerEdgeEquiv G ((deningerClassifying G).map (SimplexCategory.δ j).op F) =
        (F.whiskerLeft (toCat.map (SimplexCategory.δ j)).toFunctor).hom := by
    intro j
    rfl
  simp only [deningerEdgeElt, hnat, hface]
  show F.map' 0 2 = F.map' 1 2 * F.map' 0 1
  have hcomp : F.map' 0 2 = F.map' 0 1 ≫ F.map' 1 2 := F.map'_comp 0 1 2
  exact hcomp

end RHTower
