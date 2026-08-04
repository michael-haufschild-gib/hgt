import GaloisForLFunctions.RHTower.DeningerHornFaceEdge

/-!
# The cocycle identity inside a horn

Three vertices of the standard simplex span a triangle, whose three faces are the edges they
determine.  The triangle lies in a horn as soon as some vertex avoids the three and the horn index,
and then the elements a map out of the horn assigns to the three edges satisfy the cocycle identity.

* `deningerStdTriangle` : the triangle spanned by three vertices.
* `deningerTriangle_mem_horn` : its membership criterion.
* `deningerHornEdgeElt_comp` : the cocycle identity inside a horn.
-/

namespace RHTower

open CategoryTheory SSet SimplexCategory Opposite

universe u

/-- The triangle of the standard simplex spanned by three vertices. -/
def deningerStdTriangle {m : ℕ} {a b c : Fin (m + 1)} (hab : a ≤ b) (hbc : b ≤ c) :
    (stdSimplex.{u}.obj (mk m)).obj (op (mk 2)) :=
  stdSimplex.objEquiv.symm (SimplexCategory.mkHom
    ⟨![a, b, c], by
      rw [Fin.monotone_iff_le_succ]
      intro t
      fin_cases t
      · exact hab
      · exact hbc⟩)

/-- **The triangle lies in the horn** as soon as some vertex avoids its vertices and the horn
index. -/
theorem deningerTriangle_mem_horn {m : ℕ} (i : Fin (m + 1)) {a b c : Fin (m + 1)} (hab : a ≤ b)
    (hbc : b ≤ c) (j : Fin (m + 1)) (hji : j ≠ i) (hja : j ≠ a) (hjb : j ≠ b) (hjc : j ≠ c) :
    deningerStdTriangle.{u} hab hbc ∈ (horn.{u} m i).obj (op (mk 2)) := by
  rw [mem_horn_iff]
  intro hcon
  have hj : j ∈ Set.range (stdSimplex.asOrderHom (deningerStdTriangle.{u} hab hbc)) ∪ {i} := by
    rw [hcon]
    trivial
  rcases hj with ⟨t, ht⟩ | hj
  · fin_cases t
    · exact hja ht.symm
    · exact hjb ht.symm
    · exact hjc ht.symm
  · exact hji hj

/-- The three faces of the triangle are the three edges. -/
theorem deningerTriangle_face_zero {m : ℕ} {a b c : Fin (m + 1)} (hab : a ≤ b) (hbc : b ≤ c) :
    (stdSimplex.{u}.obj (mk m)).map (SimplexCategory.δ 0).op (deningerStdTriangle.{u} hab hbc) =
      deningerStdEdgeOf.{u} hbc := by
  refine congrArg stdSimplex.objEquiv.symm ?_
  refine SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun t => ?_))
  fin_cases t <;> rfl

theorem deningerTriangle_face_one {m : ℕ} {a b c : Fin (m + 1)} (hab : a ≤ b) (hbc : b ≤ c) :
    (stdSimplex.{u}.obj (mk m)).map (SimplexCategory.δ 1).op (deningerStdTriangle.{u} hab hbc) =
      deningerStdEdgeOf.{u} (hab.trans hbc) := by
  refine congrArg stdSimplex.objEquiv.symm ?_
  refine SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun t => ?_))
  fin_cases t <;> rfl

theorem deningerTriangle_face_two {m : ℕ} {a b c : Fin (m + 1)} (hab : a ≤ b) (hbc : b ≤ c) :
    (stdSimplex.{u}.obj (mk m)).map (SimplexCategory.δ 2).op (deningerStdTriangle.{u} hab hbc) =
      deningerStdEdgeOf.{u} hab := by
  refine congrArg stdSimplex.objEquiv.symm ?_
  refine SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun t => ?_))
  fin_cases t <;> rfl

/-- **The cocycle identity inside a horn.**  If a vertex avoids three vertices and the horn index,
the elements a map out of the horn assigns to the three edges they span compose. -/
theorem deningerHornEdgeElt_comp {G : Type u} [Group G] {m : ℕ} {i : Fin (m + 1)}
    (u : (horn.{u} m i).toSSet ⟶ deningerClassifying G) {a b c : Fin (m + 1)} (hab : a ≤ b)
    (hbc : b ≤ c) (j : Fin (m + 1)) (hji : j ≠ i) (hja : j ≠ a) (hjb : j ≠ b) (hjc : j ≠ c) :
    deningerEdgeElt u ⟨deningerStdEdgeOf (hab.trans hbc),
        deningerEdgeOf_mem_horn i (hab.trans hbc) j hji hja hjc⟩ =
      deningerEdgeElt u ⟨deningerStdEdgeOf hbc, deningerEdgeOf_mem_horn i hbc j hji hjb hjc⟩ *
        deningerEdgeElt u ⟨deningerStdEdgeOf hab,
          deningerEdgeOf_mem_horn i hab j hji hja hjb⟩ := by
  set t : (horn.{u} m i).toSSet.obj (op (mk 2)) :=
    ⟨deningerStdTriangle.{u} hab hbc, deningerTriangle_mem_horn i hab hbc j hji hja hjb hjc⟩
    with hts
  have ht := deningerEdgeElt_comp u t
  have h0 : (horn.{u} m i).toSSet.map (SimplexCategory.δ 0).op t =
      ⟨deningerStdEdgeOf hbc, deningerEdgeOf_mem_horn i hbc j hji hjb hjc⟩ :=
    Subtype.ext (deningerTriangle_face_zero hab hbc)
  have h1 : (horn.{u} m i).toSSet.map (SimplexCategory.δ 1).op t =
      ⟨deningerStdEdgeOf (hab.trans hbc),
        deningerEdgeOf_mem_horn i (hab.trans hbc) j hji hja hjc⟩ :=
    Subtype.ext (deningerTriangle_face_one hab hbc)
  have h2 : (horn.{u} m i).toSSet.map (SimplexCategory.δ 2).op t =
      ⟨deningerStdEdgeOf hab, deningerEdgeOf_mem_horn i hab j hji hja hjb⟩ :=
    Subtype.ext (deningerTriangle_face_two hab hbc)
  rw [h0, h1, h2] at ht
  exact ht

end RHTower
