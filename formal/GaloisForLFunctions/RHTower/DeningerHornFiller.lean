import GaloisForLFunctions.RHTower.DeningerHornAllEdges

/-!
# The filler of a horn of a large simplex

For a simplex with at least four vertices every edge lies in the horn, so the successive edges of a
map out of the horn prescribe a simplex, the filler.  The comparison of the filler with the horn is
carried out on edges, for which two computations are needed: the simplex a map out of the standard
simplex assigns to a simplex is the corresponding restriction, and the edges of a restriction are
the edges between the images of the endpoints.

* `deningerHornSpine`, `deningerHornFiller` : the successive edges and the filler.
* `deningerSimplexEdge_restrict_map` : the edges of a restriction.
* `deningerYoneda_app` : the simplex assigned by the map corresponding to a simplex.
-/

namespace RHTower

open CategoryTheory SSet SimplexCategory Opposite

universe u

variable {G : Type u} [Group G] {m : ℕ}

/-- The successive edges read off a map out of a horn. -/
noncomputable def deningerHornSpine (hm : 3 ≤ m) (i : Fin (m + 1))
    (u : (horn.{u} m i).toSSet ⟶ deningerClassifying G) (k : Fin m) : G :=
  deningerEdgeElt u ⟨deningerStdEdgeOf (Fin.castSucc_le_succ k),
    deningerEdgeOf_mem_horn_of_three hm i (Fin.castSucc_le_succ k)⟩

/-- **The filler of the horn**: the simplex with the successive edges of the horn. -/
noncomputable def deningerHornFiller (hm : 3 ≤ m) (i : Fin (m + 1))
    (u : (horn.{u} m i).toSSet ⟶ deningerClassifying G) :
    (deningerClassifying G).obj (op (mk m)) :=
  deningerSimplexOfFun (deningerHornSpine hm i u)

/-- **The successive edges of the filler are the successive edges of the horn.** -/
theorem deningerHornFiller_spine (hm : 3 ≤ m) (i : Fin (m + 1))
    (u : (horn.{u} m i).toSSet ⟶ deningerClassifying G) (k : Fin m) :
    deningerSimplexEdge (deningerHornFiller hm i u) (Fin.castSucc_le_succ k) =
      deningerEdgeElt u ⟨deningerStdEdgeOf (Fin.castSucc_le_succ k),
        deningerEdgeOf_mem_horn_of_three hm i (Fin.castSucc_le_succ k)⟩ :=
  deningerSimplexOfFun_edge (deningerHornSpine hm i u) k

/-- **The edges of a restriction** are the edges between the images of the endpoints. -/
theorem deningerSimplexEdge_restrict_map {m' : ℕ} (g : mk m' ⟶ mk m)
    (F : (deningerClassifying G).obj (op (mk m))) {r s : Fin (m' + 1)} (h : r ≤ s) :
    deningerSimplexEdge ((deningerClassifying G).map g.op F) h =
      deningerSimplexEdge F (g.toOrderHom.monotone h) := rfl

/-- **The simplex assigned by the map corresponding to a simplex** is the restriction. -/
theorem deningerYoneda_app (F : (deningerClassifying G).obj (op (mk m))) {m' : ℕ}
    (y : (stdSimplex.{u}.obj (mk m)).obj (op (mk m'))) :
    (SSet.yonedaEquiv.symm F).app (op (mk m')) y =
      (deningerClassifying G).map (stdSimplex.objEquiv y).op F := rfl

/-- **The filler agrees with the horn on a consecutive edge.** -/
theorem deningerHornFiller_spine' (hm : 3 ≤ m) (i : Fin (m + 1))
    (u : (horn.{u} m i).toSSet ⟶ deningerClassifying G) {x y : Fin (m + 1)} (h : x ≤ y)
    (hy : (y : ℕ) = (x : ℕ) + 1) :
    deningerSimplexEdge (deningerHornFiller hm i u) h =
      deningerEdgeElt u ⟨deningerStdEdgeOf h, deningerEdgeOf_mem_horn_of_three hm i h⟩ := by
  have hylt : (y : ℕ) < m + 1 := y.isLt
  obtain ⟨k, hkx, hky⟩ : ∃ k : Fin m, x = k.castSucc ∧ y = k.succ := by
    refine ⟨⟨(x : ℕ), by omega⟩, Fin.ext rfl, Fin.ext ?_⟩
    simp only [Fin.val_succ]
    omega
  subst hkx
  subst hky
  exact deningerHornFiller_spine hm i u k

/-- **The filler agrees with the horn on edges of length at most two.** -/
theorem deningerHornFiller_edge_step (hm : 3 ≤ m) (i : Fin (m + 1))
    (u : (horn.{u} m i).toSSet ⟶ deningerClassifying G) {a b : Fin (m + 1)} (h : a ≤ b)
    (hstep : (b : ℕ) ≤ (a : ℕ) + 2) :
    deningerSimplexEdge (deningerHornFiller hm i u) h =
      deningerEdgeElt u ⟨deningerStdEdgeOf h, deningerEdgeOf_mem_horn_of_three hm i h⟩ := by
  have hle : (a : ℕ) ≤ (b : ℕ) := h
  have hblt : (b : ℕ) < m + 1 := b.isLt
  rcases Nat.lt_or_ge (b : ℕ) ((a : ℕ) + 1) with hlt | hge1
  · have hab : a = b := Fin.ext (by omega)
    subst hab
    rw [deningerSimplexEdge_refl]
    exact (deningerHornEdgeElt_refl (by omega) u a _).symm
  rcases Nat.lt_or_ge (b : ℕ) ((a : ℕ) + 2) with hlt2 | hge2
  · exact deningerHornFiller_spine' hm i u h (by omega)
  · have hb2 : (b : ℕ) = (a : ℕ) + 2 := by omega
    have hcm : (a : ℕ) + 1 < m + 1 := by omega
    have hac : a ≤ (⟨(a : ℕ) + 1, hcm⟩ : Fin (m + 1)) := by
      simp only [Fin.le_def]
      omega
    have hcb : (⟨(a : ℕ) + 1, hcm⟩ : Fin (m + 1)) ≤ b := by
      simp only [Fin.le_def]
      omega
    rw [deningerSimplexEdge_comp _ hac hcb,
      deningerHornFiller_spine' hm i u hac (by simp),
      deningerHornFiller_spine' hm i u hcb (by simp; omega)]
    refine (deningerHornEdgeElt_comp_general hm u hac hcb ?_ ?_ ?_ _ _ _).symm
    · intro hc
      have := congrArg Fin.val hc
      simp only at this
      omega
    · intro hc
      have := congrArg Fin.val hc
      simp only at this
      omega
    · intro hc
      have := congrArg Fin.val hc
      omega

end RHTower
