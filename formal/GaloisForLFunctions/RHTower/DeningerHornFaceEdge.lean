import GaloisForLFunctions.RHTower.DeningerSimplexEdge
import GaloisForLFunctions.RHTower.DeningerHornEdges

/-!
# Edges of a face of a horn

An edge of the standard simplex joining two vertices lies in a horn as soon as some vertex avoids
its endpoints and the horn index.  Restricting a face of the horn along an edge of the face is the
edge of the standard simplex joining the images of its endpoints, so the elements a map assigns to
the edges of a face are the elements of the corresponding edges of the horn.

* `deningerStdEdgeOf`, `deningerEdgeOf_mem_horn` : the general edge and its membership.
* `deningerFace_edge` : the edges of a face are edges of the horn.
-/

namespace RHTower

open CategoryTheory SSet SimplexCategory Opposite

universe u

/-- The edge of the standard simplex joining two vertices. -/
def deningerStdEdgeOf {m : ℕ} {a b : Fin (m + 1)} (h : a ≤ b) :
    (stdSimplex.{u}.obj (mk m)).obj (op (mk 1)) :=
  stdSimplex.objEquiv.symm (mkOfLe a b h)

/-- **An edge lies in the horn** as soon as some vertex avoids its endpoints and the horn index. -/
theorem deningerEdgeOf_mem_horn {m : ℕ} (i : Fin (m + 1)) {a b : Fin (m + 1)} (h : a ≤ b)
    (j : Fin (m + 1)) (hji : j ≠ i) (hja : j ≠ a) (hjb : j ≠ b) :
    deningerStdEdgeOf.{u} h ∈ (horn.{u} m i).obj (op (mk 1)) := by
  rw [mem_horn_iff]
  intro hcon
  have hj : j ∈ Set.range (stdSimplex.asOrderHom (deningerStdEdgeOf.{u} h)) ∪ {i} := by
    rw [hcon]
    trivial
  rcases hj with ⟨t, ht⟩ | hj
  · fin_cases t
    · exact hja ht.symm
    · exact hjb ht.symm
  · exact hji hj

/-- The `k`-th spine edge is the edge joining `k` and its successor. -/
theorem deningerStdEdge_eq {m : ℕ} (k : Fin m) :
    deningerStdEdge.{u} k = deningerStdEdgeOf.{u} (Fin.castSucc_le_succ k) := by
  refine congrArg stdSimplex.objEquiv.symm ?_
  refine SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun t => ?_))
  fin_cases t <;> rfl

/-- **Restricting a simplex of the standard simplex along an edge** is the edge joining the images
of the endpoints. -/
theorem deningerStdEdge_restrict {m m' : ℕ} (g : mk m' ⟶ mk m) {a b : Fin (m' + 1)} (h : a ≤ b) :
    (stdSimplex.{u}.obj (mk m)).map (mkOfLe a b h).op (stdSimplex.objEquiv.symm g) =
      deningerStdEdgeOf.{u} (show g.toOrderHom a ≤ g.toOrderHom b from g.toOrderHom.monotone h) := by
  refine congrArg stdSimplex.objEquiv.symm ?_
  refine SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun t => ?_))
  fin_cases t <;> rfl

end RHTower
