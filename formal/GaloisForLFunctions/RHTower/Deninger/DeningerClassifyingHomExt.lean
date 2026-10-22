import GaloisForLFunctions.RHTower.Deninger.DeningerClassifyingEdges

/-!
# Maps into a classifying space are determined by the edges

A classifying space is the nerve of a category, so a simplex is recovered from its spine, and it has
a single vertex.  Two maps of simplicial sets into a classifying space therefore agree as soon as
they agree on edges.

* `deningerClassifying_hom_ext` : the extensionality principle.
-/

namespace RHTower

open CategoryTheory SSet SimplexCategory Opposite

universe u

/-- **Two maps into a classifying space agree when they agree on edges.** -/
theorem deningerClassifying_hom_ext {X : SSet.{u}} {G : Type u} [Group G]
    {φ ψ : X ⟶ deningerClassifying G}
    (h : ∀ e : X.obj (op (mk 1)), φ.app (op (mk 1)) e = ψ.app (op (mk 1)) e) : φ = ψ := by
  ext m x
  obtain ⟨m⟩ := m
  induction m using SimplexCategory.rec with
  | _ m =>
    match m with
    | 0 => exact @Subsingleton.elim _ (deningerVertexSubsingleton G) _ _
    | (m + 1) =>
      refine (Nerve.strictSegal (DeningerPt G)).spineInjective ?_
      refine SSet.Path.ext ?_ ?_
      · funext k
        exact @Subsingleton.elim _ (deningerVertexSubsingleton G) _ _
      · funext k
        show ((deningerClassifying G).spine (m + 1) _).arrow k =
          ((deningerClassifying G).spine (m + 1) _).arrow k
        rw [spine_arrow, spine_arrow]
        exact ((NatTrans.naturality_apply φ (mkOfSucc k).op x).symm.trans
          (h (X.map (mkOfSucc k).op x))).trans
          (NatTrans.naturality_apply ψ (mkOfSucc k).op x)

end RHTower
