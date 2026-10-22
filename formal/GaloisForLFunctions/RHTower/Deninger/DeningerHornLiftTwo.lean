import GaloisForLFunctions.RHTower.Deninger.DeningerHornLiftOne
import Mathlib.Tactic.Group

/-!
# Filling a two dimensional horn

A two dimensional horn has two of the three edges of a triangle, and the filler is the triangle they
span: for the inner horn the two edges are the two successive ones, and for an outer horn one
successive edge is missing and is recovered from the long edge by inverting the other, which is where
the group structure is used.

* `deningerStdEdge_eq_of` : every edge of the standard simplex joins its two vertices.
* `deningerHornFace_edgeElt` : the element of a face of a two dimensional horn.
* `deningerHornLift_two` : the lifting problem for a two dimensional horn.
-/

namespace RHTower

open CategoryTheory SSet SimplexCategory Opposite

universe u

variable {G H : Type u} [Group G] [Group H]

/-- **Every edge of the standard simplex joins its two vertices.** -/
theorem deningerStdEdge_eq_of {m : ℕ} (g : mk 1 ⟶ mk m) :
    (stdSimplex.objEquiv.symm g : (stdSimplex.{u}.obj (mk m)).obj (op (mk 1))) =
      deningerStdEdgeOf.{u} (g.toOrderHom.monotone (show (0 : Fin 2) ≤ 1 by decide)) := by
  refine congrArg stdSimplex.objEquiv.symm ?_
  refine SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun t => ?_))
  fin_cases t <;> rfl

/-- The element a map out of a two dimensional horn assigns to a face. -/
theorem deningerHornFace_edgeElt (i j : Fin 3) (hj : j ≠ i)
    (u : (horn.{u} 2 i).toSSet ⟶ deningerClassifying G) :
    deningerSimplexEdge (u.app (op (mk 1)) (horn.face i j hj))
        (show (0 : Fin 2) ≤ 1 by decide) =
      deningerEdgeElt u (horn.face i j hj) := rfl

/-- The element the simplex below assigns to a face of a two dimensional horn. -/
theorem deningerHornFace_base (i j : Fin 3) (hj : j ≠ i)
    (v : stdSimplex.{u}.obj (mk 2) ⟶ deningerClassifying H) :
    deningerEdgeElt v ((horn.face i j hj : (horn.{u} 2 i).toSSet.obj (op (mk 1))) :
        (stdSimplex.{u}.obj (mk 2)).obj (op (mk 1))) =
      deningerSimplexEdge (SSet.yonedaEquiv v)
        ((SimplexCategory.δ j).toOrderHom.monotone (show (0 : Fin 2) ≤ 1 by decide)) := by
  have hval : ((horn.face i j hj : (horn.{u} 2 i).toSSet.obj (op (mk 1))) :
      (stdSimplex.{u}.obj (mk 2)).obj (op (mk 1))) =
      deningerStdEdgeOf ((SimplexCategory.δ j).toOrderHom.monotone
        (show (0 : Fin 2) ≤ 1 by decide)) := deningerStdEdge_eq_of (SimplexCategory.δ j)
  rw [hval, ← Equiv.symm_apply_apply SSet.yonedaEquiv v]
  exact deningerEdgeElt_yoneda (SSet.yonedaEquiv v) _

/-- The edges of a two dimensional simplex of a classifying space. -/
theorem deningerSimplexTwo_edge01 (g : Fin 2 → G) :
    deningerSimplexEdge (deningerSimplexOfFun g) (show (0 : Fin 3) ≤ 1 by decide) = g 0 :=
  deningerSimplexOfFun_edge g 0

theorem deningerSimplexTwo_edge12 (g : Fin 2 → G) :
    deningerSimplexEdge (deningerSimplexOfFun g) (show (1 : Fin 3) ≤ 2 by decide) = g 1 :=
  deningerSimplexOfFun_edge g 1

theorem deningerSimplexTwo_edge02 (g : Fin 2 → G) :
    deningerSimplexEdge (deningerSimplexOfFun g) (show (0 : Fin 3) ≤ 2 by decide) =
      g 1 * g 0 := by
  have h := deningerSimplexEdge_comp (deningerSimplexOfFun g)
    (show (0 : Fin 3) ≤ 1 by decide) (show (1 : Fin 3) ≤ 2 by decide)
  rw [deningerSimplexTwo_edge01, deningerSimplexTwo_edge12] at h
  exact h

/-- The three vertices of a triangle. -/
theorem deningerFin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  have hx := x.isLt
  rcases (show (x : ℕ) = 0 ∨ (x : ℕ) = 1 ∨ (x : ℕ) = 2 by omega) with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

/-- The two edges of a triangle. -/
theorem deningerFin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  have hx := x.isLt
  rcases (show (x : ℕ) = 0 ∨ (x : ℕ) = 1 by omega) with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

/-- **The lifting problem for a two dimensional horn.** -/
theorem deningerHornLift_two (f : G →* H) (i : Fin 3)
    (u : (horn.{u} 2 i).toSSet ⟶ deningerClassifying G)
    (v : stdSimplex.{u}.obj (mk 2) ⟶ deningerClassifying H)
    (sq : CommSq u (horn.{u} 2 i).ι (deningerClassifyingMap f) v) :
    ∃ l : stdSimplex.{u}.obj (mk 2) ⟶ deningerClassifying G,
      (horn.{u} 2 i).ι ≫ l = u ∧ l ≫ deningerClassifyingMap f = v := by
  have hsq : ∀ (j : Fin 3) (hj : j ≠ i),
      f (deningerEdgeElt u (horn.face i j hj)) =
        deningerSimplexEdge (SSet.yonedaEquiv v)
          ((SimplexCategory.δ j).toOrderHom.monotone (show (0 : Fin 2) ≤ 1 by decide)) := by
    intro j hj
    have h := congrArg (fun φ : (horn.{u} 2 i).toSSet ⟶ deningerClassifying H =>
      φ.app (op (mk 1)) (horn.face i j hj)) sq.w
    exact (congrArg (deningerEdgeEquiv H) h).trans (deningerHornFace_base i j hj v)
  have hleft : ∀ g : Fin 2 → G,
      (∀ (j : Fin 3) (hj : j ≠ i),
        deningerSimplexEdge (deningerSimplexOfFun g)
            ((SimplexCategory.δ j).toOrderHom.monotone (show (0 : Fin 2) ≤ 1 by decide)) =
          deningerEdgeElt u (horn.face i j hj)) →
      (horn.{u} 2 i).ι ≫ SSet.yonedaEquiv.symm (deningerSimplexOfFun g) = u := by
    intro g hg
    refine horn.hom_ext _ _ (fun j hj => ?_)
    show (SSet.yonedaEquiv.symm (deningerSimplexOfFun g)).app (op (mk 1))
      ((horn.face i j hj : (horn.{u} 2 i).toSSet.obj (op (mk 1))) :
        (stdSimplex.{u}.obj (mk 2)).obj (op (mk 1))) = _
    rw [deningerYoneda_app]
    refine deningerSimplex_ext (fun k => ?_)
    have hk : k = 0 := Subsingleton.elim k 0
    subst hk
    rw [deningerSimplexEdge_restrict_map]
    exact (hg j hj).trans (deningerHornFace_edgeElt i j hj u).symm
  have hright : ∀ g : Fin 2 → G,
      (∀ k : Fin 2, f (g k) =
        deningerSimplexEdge (SSet.yonedaEquiv v) (Fin.castSucc_le_succ k)) →
      SSet.yonedaEquiv.symm (deningerSimplexOfFun g) ≫ deningerClassifyingMap f = v := by
    intro g hg
    refine SSet.yonedaEquiv.injective ?_
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    refine deningerSimplex_ext (fun k => ?_)
    rw [deningerSimplexEdge_map, deningerSimplexOfFun_edge]
    exact hg k
  have hV02 : deningerSimplexEdge (SSet.yonedaEquiv v) (show (0 : Fin 3) ≤ 2 by decide) =
      deningerSimplexEdge (SSet.yonedaEquiv v) (show (1 : Fin 3) ≤ 2 by decide) *
        deningerSimplexEdge (SSet.yonedaEquiv v) (show (0 : Fin 3) ≤ 1 by decide) :=
    deningerSimplexEdge_comp (SSet.yonedaEquiv v) (show (0 : Fin 3) ≤ 1 by decide)
      (show (1 : Fin 3) ≤ 2 by decide)
  rcases deningerFin3_cases i with rfl | rfl | rfl
  · refine ⟨SSet.yonedaEquiv.symm (deningerSimplexOfFun
      ![deningerEdgeElt u (horn.face 0 2 (by decide)),
        deningerEdgeElt u (horn.face 0 1 (by decide)) *
          (deningerEdgeElt u (horn.face 0 2 (by decide)))⁻¹]), hleft _ ?_, hright _ ?_⟩
    · intro j hj
      rcases deningerFin3_cases j with rfl | rfl | rfl
      · exact absurd rfl hj
      · show deningerSimplexEdge _ (show (0 : Fin 3) ≤ 2 by decide) = _
        rw [deningerSimplexTwo_edge02]
        show deningerEdgeElt u (horn.face 0 1 (by decide)) *
          (deningerEdgeElt u (horn.face 0 2 (by decide)))⁻¹ *
          deningerEdgeElt u (horn.face 0 2 (by decide)) = _
        group
      · show deningerSimplexEdge _ (show (0 : Fin 3) ≤ 1 by decide) = _
        rw [deningerSimplexTwo_edge01]
        rfl
    · intro k
      rcases deningerFin2_cases k with rfl | rfl
      · exact hsq 2 (by decide)
      · show f (deningerEdgeElt u (horn.face 0 1 (by decide)) *
          (deningerEdgeElt u (horn.face 0 2 (by decide)))⁻¹) = _
        rw [map_mul, map_inv, hsq 1 (by decide), hsq 2 (by decide)]
        show deningerSimplexEdge (SSet.yonedaEquiv v) (show (0 : Fin 3) ≤ 2 by decide) *
          (deningerSimplexEdge (SSet.yonedaEquiv v) (show (0 : Fin 3) ≤ 1 by decide))⁻¹ = _
        rw [hV02]
        group
        rfl
  · refine ⟨SSet.yonedaEquiv.symm (deningerSimplexOfFun
      ![deningerEdgeElt u (horn.face 1 2 (by decide)),
        deningerEdgeElt u (horn.face 1 0 (by decide))]), hleft _ ?_, hright _ ?_⟩
    · intro j hj
      rcases deningerFin3_cases j with rfl | rfl | rfl
      · show deningerSimplexEdge _ (show (1 : Fin 3) ≤ 2 by decide) = _
        rw [deningerSimplexTwo_edge12]
        rfl
      · exact absurd rfl hj
      · show deningerSimplexEdge _ (show (0 : Fin 3) ≤ 1 by decide) = _
        rw [deningerSimplexTwo_edge01]
        rfl
    · intro k
      rcases deningerFin2_cases k with rfl | rfl
      · exact hsq 2 (by decide)
      · exact hsq 0 (by decide)
  · refine ⟨SSet.yonedaEquiv.symm (deningerSimplexOfFun
      ![(deningerEdgeElt u (horn.face 2 0 (by decide)))⁻¹ *
          deningerEdgeElt u (horn.face 2 1 (by decide)),
        deningerEdgeElt u (horn.face 2 0 (by decide))]), hleft _ ?_, hright _ ?_⟩
    · intro j hj
      rcases deningerFin3_cases j with rfl | rfl | rfl
      · show deningerSimplexEdge _ (show (1 : Fin 3) ≤ 2 by decide) = _
        rw [deningerSimplexTwo_edge12]
        rfl
      · show deningerSimplexEdge _ (show (0 : Fin 3) ≤ 2 by decide) = _
        rw [deningerSimplexTwo_edge02]
        show deningerEdgeElt u (horn.face 2 0 (by decide)) *
          ((deningerEdgeElt u (horn.face 2 0 (by decide)))⁻¹ *
            deningerEdgeElt u (horn.face 2 1 (by decide))) = _
        group
      · exact absurd rfl hj
    · intro k
      rcases deningerFin2_cases k with rfl | rfl
      · show f ((deningerEdgeElt u (horn.face 2 0 (by decide)))⁻¹ *
          deningerEdgeElt u (horn.face 2 1 (by decide))) = _
        rw [map_mul, map_inv, hsq 0 (by decide), hsq 1 (by decide)]
        show (deningerSimplexEdge (SSet.yonedaEquiv v) (show (1 : Fin 3) ≤ 2 by decide))⁻¹ *
          deningerSimplexEdge (SSet.yonedaEquiv v) (show (0 : Fin 3) ≤ 2 by decide) = _
        rw [hV02]
        group
        rfl
      · exact hsq 0 (by decide)

end RHTower
