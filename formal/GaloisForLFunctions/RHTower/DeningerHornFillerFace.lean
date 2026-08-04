import GaloisForLFunctions.RHTower.DeningerHornFiller

/-!
# The faces of the filler

The `j`-th face of the standard simplex takes consecutive vertices to vertices at distance one or
two, according to whether the omitted vertex lies between them.  So the successive edges of the
`j`-th face of the filler are edges of the horn of length at most two, on which the filler and the
horn already agree, and the two faces coincide.

* `deningerSuccAbove_step` : the distance between the images of consecutive vertices.
* `deningerSimplexEdge_of_map` : the edges of the image of a simplex.
* `deningerHornFiller_face` : the faces of the filler are the faces of the horn.
-/

namespace RHTower

open CategoryTheory SSet SimplexCategory Opposite

universe u

variable {G : Type u} [Group G]

/-- **Consecutive vertices go to vertices at distance one or two.** -/
theorem deningerSuccAbove_step {n : ℕ} (j : Fin (n + 2)) (r : Fin n) :
    ((j.succAbove r.succ : Fin (n + 2)) : ℕ) ≤
      ((j.succAbove r.castSucc : Fin (n + 2)) : ℕ) + 2 := by
  rcases Nat.lt_or_ge (r.castSucc : ℕ) (j : ℕ) with h1 | h1
  · rw [Fin.succAbove_of_castSucc_lt j r.castSucc (by simpa [Fin.lt_def] using h1)]
    rcases Nat.lt_or_ge (r.succ : ℕ) (j : ℕ) with h2 | h2
    · rw [Fin.succAbove_of_castSucc_lt j r.succ (by simpa [Fin.lt_def] using h2)]
      simp only [Fin.coe_castSucc, Fin.val_succ]
      omega
    · rw [Fin.succAbove_of_le_castSucc j r.succ (by simpa [Fin.le_def] using h2)]
      simp only [Fin.coe_castSucc, Fin.val_succ]
      omega
  · rw [Fin.succAbove_of_le_castSucc j r.castSucc (by simpa [Fin.le_def] using h1)]
    have h2 : (j : ℕ) ≤ (r.succ : ℕ) := by
      simp only [Fin.val_succ]
      simp only [Fin.coe_castSucc] at h1
      omega
    rw [Fin.succAbove_of_le_castSucc j r.succ (by simpa [Fin.le_def] using h2)]
    simp only [Fin.coe_castSucc, Fin.val_succ]
    omega

/-- **The edges of the image of a simplex** are the elements assigned to the corresponding edges. -/
theorem deningerSimplexEdge_of_map {Y : SSet.{u}} (u : Y ⟶ deningerClassifying G) {m' : ℕ}
    (y : Y.obj (op (mk m'))) {r s : Fin (m' + 1)} (h : r ≤ s) :
    deningerSimplexEdge (u.app (op (mk m')) y) h =
      deningerEdgeElt u (Y.map (mkOfLe r s h).op y) := by
  rw [← deningerSimplexEdge_restrict, deningerEdgeElt]
  exact congrArg (deningerEdgeEquiv G) (NatTrans.naturality_apply u (mkOfLe r s h).op y).symm

/-- **The faces of the filler are the faces of the horn.** -/
theorem deningerHornFiller_face {n : ℕ} (hm : 3 ≤ n + 1) (i : Fin (n + 2))
    (u : (horn.{u} (n + 1) i).toSSet ⟶ deningerClassifying G) (j : Fin (n + 2)) (hj : j ≠ i) :
    (deningerClassifying G).map (SimplexCategory.δ j).op (deningerHornFiller hm i u) =
      u.app (op (mk n)) (horn.face i j hj) := by
  refine deningerSimplex_ext (fun r => ?_)
  rw [deningerSimplexEdge_restrict_map, deningerSimplexEdge_of_map,
    deningerHornFiller_edge_step hm i u
      ((SimplexCategory.δ j).toOrderHom.monotone (Fin.castSucc_le_succ r))
      (deningerSuccAbove_step j r)]
  refine congrArg (deningerEdgeElt u) (Subtype.ext ?_)
  exact (deningerStdEdge_restrict (SimplexCategory.δ j) (Fin.castSucc_le_succ r)).symm

end RHTower
