import GaloisForLFunctions.RHTower.DeningerHornFillerFace

/-!
# Filling a horn of a large simplex

For a simplex with at least four vertices the filler built from the successive edges of the horn
solves the lifting problem: its faces are the faces of the horn, and its successive edges map to the
successive edges of the given simplex below, because the square commutes.

* `deningerEdgeElt_comp_map` : the element of an edge after a map of classifying spaces.
* `deningerEdgeElt_yoneda` : the element of an edge of a simplex.
* `deningerHornLift_large` : the lifting problem is solved.
-/

namespace RHTower

open CategoryTheory SSet SimplexCategory Opposite

universe u

variable {G H : Type u} [Group G] [Group H]

/-- **The element of an edge after a map of classifying spaces.** -/
theorem deningerEdgeElt_comp_map {Y : SSet.{u}} (u : Y ⟶ deningerClassifying G) (f : G →* H)
    (e : Y.obj (op (mk 1))) :
    deningerEdgeElt (u ≫ deningerClassifyingMap f) e = f (deningerEdgeElt u e) := rfl

/-- **The element of an edge of a simplex**, read through the map it corresponds to. -/
theorem deningerEdgeElt_yoneda {m : ℕ} (F : (deningerClassifying G).obj (op (mk m)))
    {a b : Fin (m + 1)} (h : a ≤ b) :
    deningerEdgeElt (SSet.yonedaEquiv.symm F) (deningerStdEdgeOf h) =
      deningerSimplexEdge F h := rfl

/-- **The lifting problem for a horn of a simplex with at least four vertices.** -/
theorem deningerHornLift_large {n : ℕ} (hm : 3 ≤ n + 1) (f : G →* H) (i : Fin (n + 2))
    (u : (horn.{u} (n + 1) i).toSSet ⟶ deningerClassifying G)
    (v : stdSimplex.{u}.obj (mk (n + 1)) ⟶ deningerClassifying H)
    (sq : CommSq u (horn.{u} (n + 1) i).ι (deningerClassifyingMap f) v) :
    ∃ l : stdSimplex.{u}.obj (mk (n + 1)) ⟶ deningerClassifying G,
      (horn.{u} (n + 1) i).ι ≫ l = u ∧ l ≫ deningerClassifyingMap f = v := by
  refine ⟨SSet.yonedaEquiv.symm (deningerHornFiller hm i u), ?_, ?_⟩
  · refine horn.hom_ext _ _ (fun j hj => ?_)
    show (SSet.yonedaEquiv.symm (deningerHornFiller hm i u)).app (op (mk n))
      ((horn.face i j hj) : (stdSimplex.obj (mk (n + 1))).obj (op (mk n))) = _
    rw [deningerYoneda_app]
    exact deningerHornFiller_face hm i u j hj
  · refine SSet.yonedaEquiv.injective ?_
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    refine deningerSimplex_ext (fun k => ?_)
    rw [deningerSimplexEdge_map, deningerHornFiller_spine]
    have hsq := congrArg (fun φ : (horn.{u} (n + 1) i).toSSet ⟶ deningerClassifying H =>
      φ.app (op (mk 1)) (⟨deningerStdEdgeOf (Fin.castSucc_le_succ k),
        deningerEdgeOf_mem_horn_of_three hm i (Fin.castSucc_le_succ k)⟩ :
        (horn.{u} (n + 1) i).toSSet.obj (op (mk 1)))) sq.w
    have hval := congrArg (deningerEdgeEquiv H) hsq
    refine hval.trans ?_
    show deningerEdgeElt v (deningerStdEdgeOf (Fin.castSucc_le_succ k)) = _
    rw [← Equiv.symm_apply_apply SSet.yonedaEquiv v]
    exact deningerEdgeElt_yoneda (SSet.yonedaEquiv v) (Fin.castSucc_le_succ k)

end RHTower
