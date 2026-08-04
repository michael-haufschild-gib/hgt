import GaloisForLFunctions.RHTower.DeningerHornCocycle

/-!
# Simplices of a classifying space from prescribed edges

A simplex of a classifying space is determined by the elements of its successive edges, and any
family of elements occurs: the spine of a nerve determines the simplex, and the vertices of a
classifying space are all equal, so a family of edges assembles into a path and hence into a simplex.

* `deningerSimplexOfFun` : the simplex with prescribed successive edges.
* `deningerSimplexOfFun_edge` : its successive edges.
* `deningerSimplex_ext` : two simplices with the same successive edges agree.
* `deningerSimplexEdge_map` : a map of classifying spaces acts on edges by the homomorphism.
-/

namespace RHTower

open CategoryTheory SSet SimplexCategory Opposite

universe u

/-- The path of a classifying space with prescribed edges. -/
noncomputable def deningerPathOfFun {G : Type u} [Group G] {m : ℕ} (g : Fin m → G) :
    (deningerClassifying G).Path m where
  vertex _ := ComposableArrows.mk₀ (deningerPtStar G)
  arrow k := (deningerEdgeEquiv G).symm (g k)
  arrow_src _ := @Subsingleton.elim _ (deningerVertexSubsingleton G) _ _
  arrow_tgt _ := @Subsingleton.elim _ (deningerVertexSubsingleton G) _ _

/-- **The simplex of a classifying space with prescribed successive edges.** -/
noncomputable def deningerSimplexOfFun {G : Type u} [Group G] {m : ℕ} (g : Fin m → G) :
    (deningerClassifying G).obj (op (mk m)) :=
  (Nerve.strictSegal (DeningerPt G)).spineToSimplex (deningerPathOfFun g)

/-- The successive edge of a simplex, in the form the spine uses. -/
theorem deningerMkOfSucc_eq {m : ℕ} (k : Fin m) :
    mkOfSucc k = mkOfLe k.castSucc k.succ (Fin.castSucc_le_succ k) := by
  refine SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun t => ?_))
  fin_cases t <;> rfl

theorem deningerSimplexEdge_spine {G : Type u} [Group G] {m : ℕ}
    (F : (deningerClassifying G).obj (op (mk m))) (k : Fin m) :
    deningerEdgeEquiv G ((deningerClassifying G).map (mkOfSucc k).op F) =
      deningerSimplexEdge F (Fin.castSucc_le_succ k) := by
  rw [deningerMkOfSucc_eq k]
  exact deningerSimplexEdge_restrict F (Fin.castSucc_le_succ k)

/-- **The prescribed edges are the successive edges of the simplex.** -/
theorem deningerSimplexOfFun_edge {G : Type u} [Group G] {m : ℕ} (g : Fin m → G) (k : Fin m) :
    deningerSimplexEdge (deningerSimplexOfFun g) (Fin.castSucc_le_succ k) = g k := by
  rw [← deningerSimplexEdge_spine]
  have h := (Nerve.strictSegal (DeningerPt G)).spineToSimplex_arrow k (deningerPathOfFun g)
  rw [deningerSimplexOfFun, h]
  show deningerEdgeEquiv G ((deningerEdgeEquiv G).symm (g k)) = g k
  exact (deningerEdgeEquiv G).apply_symm_apply (g k)

/-- **Two simplices with the same successive edges agree.** -/
theorem deningerSimplex_ext {G : Type u} [Group G] {m : ℕ}
    {F K : (deningerClassifying G).obj (op (mk m))}
    (h : ∀ k : Fin m, deningerSimplexEdge F (Fin.castSucc_le_succ k) =
      deningerSimplexEdge K (Fin.castSucc_le_succ k)) : F = K := by
  refine (Nerve.strictSegal (DeningerPt G)).spineInjective ?_
  refine SSet.Path.ext ?_ ?_
  · funext k
    exact @Subsingleton.elim _ (deningerVertexSubsingleton G) _ _
  · funext k
    have hF := spine_arrow (deningerClassifying G) m F k
    have hK := spine_arrow (deningerClassifying G) m K k
    show ((deningerClassifying G).spine m F).arrow k = ((deningerClassifying G).spine m K).arrow k
    rw [hF, hK]
    refine (deningerEdgeEquiv G).injective ?_
    rw [deningerSimplexEdge_spine, deningerSimplexEdge_spine]
    exact h k

/-- **A map of classifying spaces acts on the edges of a simplex by the homomorphism.** -/
theorem deningerSimplexEdge_map {G H : Type u} [Group G] [Group H] (f : G →* H) {m : ℕ}
    (F : (deningerClassifying G).obj (op (mk m))) {a b : Fin (m + 1)} (h : a ≤ b) :
    deningerSimplexEdge ((deningerClassifyingMap f).app (op (mk m)) F) h =
      f (deningerSimplexEdge F h) := rfl

end RHTower
