import GaloisForLFunctions.RHTower.DeningerHornLiftLarge

/-!
# Filling a one dimensional horn

A one dimensional horn is a vertex, and the vertices of a classifying space are all equal, so the
only condition on a filler is the one below: its edge must map to the given edge, which is where
surjectivity of the homomorphism is used.

* `deningerHornLift_one` : the lifting problem for a one dimensional horn.
-/

namespace RHTower

open CategoryTheory SSet SimplexCategory Opposite

universe u

variable {G H : Type u} [Group G] [Group H]

/-- **The lifting problem for a one dimensional horn.** -/
theorem deningerHornLift_one (f : G →* H) (hf : Function.Surjective f) (i : Fin 2)
    (u : (horn.{u} 1 i).toSSet ⟶ deningerClassifying G)
    (v : stdSimplex.{u}.obj (mk 1) ⟶ deningerClassifying H)
    (_sq : CommSq u (horn.{u} 1 i).ι (deningerClassifyingMap f) v) :
    ∃ l : stdSimplex.{u}.obj (mk 1) ⟶ deningerClassifying G,
      (horn.{u} 1 i).ι ≫ l = u ∧ l ≫ deningerClassifyingMap f = v := by
  obtain ⟨g₀, hg₀⟩ := hf (deningerSimplexEdge (SSet.yonedaEquiv v)
    (Fin.castSucc_le_succ (0 : Fin 1)))
  refine ⟨SSet.yonedaEquiv.symm (deningerSimplexOfFun (fun _ : Fin 1 => g₀)), ?_, ?_⟩
  · refine horn.hom_ext _ _ (fun j hj => ?_)
    exact @Subsingleton.elim _ (deningerVertexSubsingleton G) _ _
  · refine SSet.yonedaEquiv.injective ?_
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    refine deningerSimplex_ext (fun k => ?_)
    rw [deningerSimplexEdge_map, deningerSimplexOfFun_edge]
    have hk : k = 0 := Subsingleton.elim k 0
    subst hk
    exact hg₀

end RHTower
