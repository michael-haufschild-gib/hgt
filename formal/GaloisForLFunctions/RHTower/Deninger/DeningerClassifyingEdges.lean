import GaloisForLFunctions.RHTower.Deninger.DeningerClassifyingSpace
import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal

/-!
# Simplices of a classifying space

The vertices of a classifying space are the single object, so they form a subsingleton, and its
edges are the elements of the group.  A map of classifying spaces acts on edges by the
homomorphism.  Together with the strict Segal property of a nerve, which recovers a simplex from its
spine, these are the coordinates in which the horn filling of a classifying space is computed.

* `deningerVertexSubsingleton` : the vertices form a subsingleton.
* `deningerEdgeEquiv` : the edges are the group.
* `deningerEdgeEquiv_map` : a map of classifying spaces acts by the homomorphism.
-/

namespace RHTower

open CategoryTheory SSet Opposite SimplexCategory

universe u

/-- **The vertices of a classifying space form a subsingleton.** -/
instance deningerVertexSubsingleton (G : Type u) [Group G] :
    Subsingleton ((deningerClassifying G).obj (op (SimplexCategory.mk 0))) := by
  constructor
  intro F K
  refine deningerPtHom_ext (fun {a b} x => ?_)
  have hab : a = b := Subsingleton.elim (α := Fin 1) a b
  subst hab
  have hx : x = 𝟙 a := Subsingleton.elim x (𝟙 a)
  rw [hx, F.map_id, K.map_id]

/-- **The edges of a classifying space are the elements of the group.** -/
def deningerEdgeEquiv (G : Type u) [Group G] :
    (deningerClassifying G).obj (op (SimplexCategory.mk 1)) ≃ G where
  toFun F := F.hom
  invFun g := ComposableArrows.mk₁ (X₀ := deningerPtStar G) (X₁ := deningerPtStar G) g
  left_inv F := by
    refine ComposableArrows.ext₁ rfl rfl ?_
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  right_inv g := rfl

/-- **A map of classifying spaces acts on edges by the homomorphism.** -/
theorem deningerEdgeEquiv_map {G H : Type u} [Group G] [Group H] (f : G →* H)
    (F : (deningerClassifying G).obj (op (SimplexCategory.mk 1))) :
    deningerEdgeEquiv H ((deningerClassifyingMap f).app (op (SimplexCategory.mk 1)) F) =
      f (deningerEdgeEquiv G F) := rfl

end RHTower
