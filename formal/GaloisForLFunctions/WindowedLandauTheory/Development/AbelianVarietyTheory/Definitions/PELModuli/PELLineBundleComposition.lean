import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.StructureSheafUnits

/-! Isomorphisms of line bundles compose by gluing the products of their local generators. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace ReciprocityTheory.ChartRestriction.G.Semi.LB

universe u

variable {X : Scheme.{u}} {A B C : LB X}

/-- The transition law on any smaller open contained in both charts. -/
theorem Gen.IsGen.restrict {L : LB X} {t : L.Gen} (ht : t.IsGen)
    {i j : L.ι} {U : X.Opens} (hi : U ≤ L.U i) (hj : U ≤ L.U j) :
    res hi (t.s i) = res (le_inf hi hj) (L.g i j) * res hj (t.s j) := by
  have e := congrArg (res (le_inf hi hj)) (ht i j)
  simpa only [map_mul, res_res] using e

private theorem restrict_self {L : LB X} (hL : L.IsLB) {i : L.ι} {U : X.Opens}
    (hi : U ≤ L.U i) : res (le_inf hi hi) (L.g i i) = 1 := by
  have e := congrArg (res hi) (hL.g_self i)
  simpa only [res_res, map_one] using e

private def productOn {s : Iso A B} {t : Iso B C}
    {i : A.ι} {j : B.ι} {k : C.ι} {U : X.Opens}
    (hi : U ≤ A.U i) (hj : U ≤ B.U j) (hk : U ≤ C.U k) : Γ(X, U)ˣ :=
  res (le_inf hk hj) (t.s (k, j)) * res (le_inf hj hi) (s.s (j, i))

private theorem productOn_transition {s : Iso A B} {t : Iso B C} (hs : s.IsGen) (ht : t.IsGen)
    {i i' : A.ι} {j j' : B.ι} {k k' : C.ι} {U : X.Opens}
    (hi : U ≤ A.U i) (hj : U ≤ B.U j) (hk : U ≤ C.U k)
    (hi' : U ≤ A.U i') (hj' : U ≤ B.U j') (hk' : U ≤ C.U k') :
    productOn (s := s) (t := t) hi hj hk =
      (res (le_inf hk hk') (C.g k k') * (res (le_inf hi hi') (A.g i i'))⁻¹) *
        productOn (s := s) (t := t) hi' hj' hk' := by
  have a := hs.restrict (i := (j, i)) (j := (j', i')) (le_inf hj hi) (le_inf hj' hi')
  have b := ht.restrict (i := (k, j)) (j := (k', j')) (le_inf hk hj) (le_inf hk' hj')
  simp only [div, map_mul, map_inv, res_res] at a b
  rw [productOn, productOn, a, b, mul_mul_mul_comm]
  simp only [mul_assoc, inv_mul_cancel_left]

private theorem cover_inf (hB : B.IsLB) (U : X.Opens) : U ≤ ⨆ j, U ⊓ B.U j := by
  intro x hx
  have hx' : x ∈ ⨆ j, B.U j := by rw [hB.cover]; trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx'
  exact Opens.mem_iSup.mpr ⟨j, hx, hj⟩

/-- Gluing over the middle bundle gives the composition of its local isomorphisms. -/
theorem Gen.IsGen.comp {s : Iso A B} {t : Iso B C} (hs : s.IsGen) (ht : t.IsGen)
    (hA : A.IsLB) (hB : B.IsLB) (hC : C.IsLB) : ∃ u : Iso A C, u.IsGen := by
  let V (a : C.ι × A.ι) (j : B.ι) : X.Opens := (C.U a.1 ⊓ A.U a.2) ⊓ B.U j
  let v (a : C.ι × A.ι) (j : B.ι) : Γ(X, V a j)ˣ :=
    productOn (s := s) (t := t) (inf_le_left.trans inf_le_right) inf_le_right
      (inf_le_left.trans inf_le_left)
  have hcompat (a : C.ι × A.ι) (j j' : B.ι) :
      res (inf_le_left : V a j ⊓ V a j' ≤ V a j) (v a j) =
        res (inf_le_right : V a j ⊓ V a j' ≤ V a j') (v a j') := by
    let W := V a j ⊓ V a j'
    have hl : W ≤ C.U a.1 ⊓ A.U a.2 := inf_le_left.trans inf_le_left
    have hj : W ≤ B.U j := inf_le_left.trans inf_le_right
    have hj' : W ≤ B.U j' := inf_le_right.trans inf_le_right
    have e := productOn_transition (i := a.2) (i' := a.2) (j := j) (j' := j')
      (k := a.1) (k' := a.1) hs ht (hl.trans inf_le_right) hj (hl.trans inf_le_left)
      (hl.trans inf_le_right) hj' (hl.trans inf_le_left)
    rw [restrict_self hC, restrict_self hA, inv_one, one_mul, one_mul] at e
    simpa only [v, productOn, map_mul, res_res] using e
  have hex (a : C.ι × A.ι) : ∃ z : Γ(X, (C.div A).U a)ˣ, ∀ j,
      res (inf_le_left : V a j ≤ (C.div A).U a) z = v a j :=
    (existsUnique_glueUnits (V a) (fun _ => inf_le_left) (cover_inf hB _) (v a) (hcompat a)).exists
  choose u hu using hex
  refine ⟨⟨u⟩, fun a b => ?_⟩
  let W : X.Opens := (C.div A).U a ⊓ (C.div A).U b
  apply units_ext_on_cover (fun j => W ⊓ B.U j) (fun _ => inf_le_left) (cover_inf hB W)
  intro j
  let D : X.Opens := W ⊓ B.U j
  have ea : D ≤ V a j := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have eb : D ≤ V b j := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have ha := congrArg (res ea) (hu a j)
  have hb := congrArg (res eb) (hu b j)
  simp only [res_res, v, productOn, map_mul] at ha hb
  simp only [map_mul, map_inv, div, res_res]
  rw [ha, hb]
  simpa only [productOn] using productOn_transition hs ht
    (i := a.2) (i' := b.2) (j := j) (j' := j) (k := a.1) (k' := b.1)
    (ea.trans (inf_le_left.trans inf_le_right)) inf_le_right
    (ea.trans (inf_le_left.trans inf_le_left)) (eb.trans (inf_le_left.trans inf_le_right))
    inf_le_right (eb.trans (inf_le_left.trans inf_le_left))

end ReciprocityTheory.ChartRestriction.G.Semi.LB
