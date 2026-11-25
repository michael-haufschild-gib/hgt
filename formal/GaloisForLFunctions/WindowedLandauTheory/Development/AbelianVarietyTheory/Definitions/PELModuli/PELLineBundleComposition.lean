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
  let h := le_inf hi hj
  exact (res_res inf_le_left h _).symm.trans ((congrArg (res h) (ht i j)).trans
    ((map_mul _ _ _).trans (congrArg (_ * ·) (res_res inf_le_right h _))))

private theorem Gen.IsGen.restrict_div {s : Iso A B} (hs : s.IsGen)
    {i j : (B.div A).ι} {U : X.Opens} (hi : U ≤ (B.div A).U i) (hj : U ≤ (B.div A).U j) :
    res hi (s.s i) =
      (res (le_inf (hi.trans inf_le_left) (hj.trans inf_le_left)) (B.g i.1 j.1) *
        (res (le_inf (hi.trans inf_le_right) (hj.trans inf_le_right)) (A.g i.2 j.2))⁻¹) *
        res hj (s.s j) :=
  (hs.restrict hi hj).trans (congrArg (· * res hj (s.s j)) (res_div_g A B hi hj))

/-- Inverting the local generators exchanges the two line bundles. -/
theorem Gen.IsGen.symm {s : Iso A B} (hs : s.IsGen) : ∃ t : Iso B A, t.IsGen := by
  let invGen (i : (A.div B).ι) : Γ(X, (A.div B).U i)ˣ :=
    (res (le_inf inf_le_right inf_le_left) (s.s (i.2, i.1)))⁻¹
  refine ⟨⟨invGen⟩, fun i j => ?_⟩
  let U := (A.div B).U i ⊓ (A.div B).U j
  have hi : U ≤ (B.div A).U (i.2, i.1) :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)
  have hj : U ≤ (B.div A).U (j.2, j.1) :=
    le_inf (inf_le_right.trans inf_le_right) (inf_le_right.trans inf_le_left)
  let a := res (le_inf (hi.trans inf_le_right) (hj.trans inf_le_right)) (A.g i.1 j.1)
  let b := res (le_inf (hi.trans inf_le_left) (hj.trans inf_le_left)) (B.g i.2 j.2)
  let q := res hj (s.s (j.2, j.1))
  have e : res hi (s.s (i.2, i.1)) = (b * a⁻¹) * q := hs.restrict_div hi hj
  have ei : res (inf_le_left : U ≤ (A.div B).U i) (invGen i) = (res hi (s.s (i.2, i.1)))⁻¹ :=
    (map_inv _ _).trans (congrArg Inv.inv (res_res _ _ _))
  have ej : res (inf_le_right : U ≤ (A.div B).U j) (invGen j) = q⁻¹ :=
    (map_inv _ _).trans (congrArg Inv.inv (res_res _ _ _))
  have eg : (A.div B).g i j = a * b⁻¹ :=
    (res_refl _).symm.trans (res_div_g B A (i := i) (j := j) inf_le_left inf_le_right)
  have eq : ((b * a⁻¹) * q)⁻¹ = (a * b⁻¹) * q⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_comm]
  exact ei.trans ((congrArg Inv.inv e).trans (eq.trans (congrArg₂ (· * ·) eg.symm ej.symm)))

private theorem restrict_self {L : LB X} (hL : L.IsLB) {i : L.ι} {U : X.Opens}
    (hi : U ≤ L.U i) : res (le_inf hi hi) (L.g i i) = 1 := by
  have e := congrArg (res hi) (hL.g_self i)
  simpa only [res_res, map_one] using e

private def productOn {s : Iso A B} {t : Iso B C}
    {i : A.ι} {j : B.ι} {k : C.ι} {U : X.Opens}
    (hi : U ≤ A.U i) (hj : U ≤ B.U j) (hk : U ≤ C.U k) : Γ(X, U)ˣ :=
  res (le_inf hk hj) (t.s (k, j)) * res (le_inf hj hi) (s.s (j, i))

private theorem res_productOn {s : Iso A B} {t : Iso B C}
    {i : A.ι} {j : B.ι} {k : C.ι} {U V : X.Opens}
    (h : V ≤ U) (hi : U ≤ A.U i) (hj : U ≤ B.U j) (hk : U ≤ C.U k) :
    res h (productOn (s := s) (t := t) hi hj hk) =
      productOn (s := s) (t := t) (h.trans hi) (h.trans hj) (h.trans hk) :=
  (map_mul (res h) _ _).trans (congrArg₂ (· * ·) (res_res _ h _) (res_res _ h _))

private theorem productOn_transition {s : Iso A B} {t : Iso B C} (hs : s.IsGen) (ht : t.IsGen)
    {i i' : A.ι} {j j' : B.ι} {k k' : C.ι} {U : X.Opens}
    (hi : U ≤ A.U i) (hj : U ≤ B.U j) (hk : U ≤ C.U k)
    (hi' : U ≤ A.U i') (hj' : U ≤ B.U j') (hk' : U ≤ C.U k') :
    productOn (s := s) (t := t) hi hj hk =
      (res (le_inf hk hk') (C.g k k') * (res (le_inf hi hi') (A.g i i'))⁻¹) *
        productOn (s := s) (t := t) hi' hj' hk' := by
  let a := res (le_inf hi hi') (A.g i i')
  let b := res (le_inf hj hj') (B.g j j')
  let c := res (le_inf hk hk') (C.g k k')
  let q := res (le_inf hj' hi') (s.s (j', i'))
  let r := res (le_inf hk' hj') (t.s (k', j'))
  have es : res (le_inf hj hi) (s.s (j, i)) = (b * a⁻¹) * q :=
    hs.restrict_div (i := (j, i)) (j := (j', i')) (le_inf hj hi) (le_inf hj' hi')
  have et : res (le_inf hk hj) (t.s (k, j)) = (c * b⁻¹) * r :=
    ht.restrict_div (i := (k, j)) (j := (k', j')) (le_inf hk hj) (le_inf hk' hj')
  calc
    _ = ((c * b⁻¹) * r) * ((b * a⁻¹) * q) := congrArg₂ (· * ·) et es
    _ = ((c * b⁻¹) * (b * a⁻¹)) * (r * q) := mul_mul_mul_comm _ _ _ _
    _ = _ := by
      change ((c * b⁻¹) * (b * a⁻¹)) * (r * q) = (c * a⁻¹) * (r * q)
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
    let l : W ≤ V a j := inf_le_left
    let r : W ≤ V a j' := inf_le_right
    have hl : W ≤ C.U a.1 ⊓ A.U a.2 := inf_le_left.trans inf_le_left
    have hj : W ≤ B.U j := inf_le_left.trans inf_le_right
    have hj' : W ≤ B.U j' := inf_le_right.trans inf_le_right
    let hi : W ≤ A.U a.2 := hl.trans inf_le_right
    let hk : W ≤ C.U a.1 := hl.trans inf_le_left
    have e := productOn_transition (i := a.2) (i' := a.2) (j := j) (j' := j')
      (k := a.1) (k' := a.1) hs ht hi hj hk hi hj' hk
    have hself : res (le_inf hk hk) (C.g a.1 a.1) * (res (le_inf hi hi) (A.g a.2 a.2))⁻¹ = 1 :=
      (congrArg₂ (· * ·) (restrict_self hC hk) (congrArg Inv.inv (restrict_self hA hi))).trans (by simp)
    have e' : productOn (s := s) (t := t) hi hj hk =
        productOn (s := s) (t := t) hi hj' hk :=
      e.trans ((congrArg (· * productOn (s := s) (t := t) hi hj' hk) hself).trans (_root_.one_mul _))
    have hl' : res l (v a j) = productOn (s := s) (t := t) hi hj hk := res_productOn l _ _ _
    have hr' : res r (v a j') = productOn (s := s) (t := t) hi hj' hk := res_productOn r _ _ _
    exact hl'.trans (e'.trans hr'.symm)
  have hex (a : C.ι × A.ι) : ∃ z : Γ(X, (C.div A).U a)ˣ, ∀ j,
      res (inf_le_left : V a j ≤ (C.div A).U a) z = v a j :=
    (existsUnique_glueUnits (V a) (fun _ => inf_le_left) (cover_inf hB _) (v a) (hcompat a)).exists
  choose u hu using hex
  refine ⟨⟨u⟩, fun a b => ?_⟩
  let W : X.Opens := (C.div A).U a ⊓ (C.div A).U b
  apply units_ext_on_cover (fun j => W ⊓ B.U j) (fun _ => inf_le_left) (cover_inf hB W)
  intro j
  let D : X.Opens := W ⊓ B.U j
  let hD : D ≤ W := inf_le_left
  let hWa : W ≤ (C.div A).U a := inf_le_left
  let hWb : W ≤ (C.div A).U b := inf_le_right
  have ea : D ≤ V a j := le_inf (hD.trans hWa) inf_le_right
  have eb : D ≤ V b j := le_inf (hD.trans hWb) inf_le_right
  let hi : D ≤ A.U a.2 := ea.trans (inf_le_left.trans inf_le_right)
  let hi' : D ≤ A.U b.2 := eb.trans (inf_le_left.trans inf_le_right)
  let hk : D ≤ C.U a.1 := ea.trans (inf_le_left.trans inf_le_left)
  let hk' : D ≤ C.U b.1 := eb.trans (inf_le_left.trans inf_le_left)
  let hj : D ≤ B.U j := inf_le_right
  have ha : res hD (res hWa (u a)) = productOn (s := s) (t := t) hi hj hk := by
    exact (res_res hWa hD _).trans ((res_res inf_le_left ea _).symm.trans
      ((congrArg (res ea) (hu a j)).trans (res_productOn ea _ _ _)))
  have hb : res hD (res hWb (u b)) = productOn (s := s) (t := t) hi' hj hk' := by
    exact (res_res hWb hD _).trans ((res_res inf_le_left eb _).symm.trans
      ((congrArg (res eb) (hu b j)).trans (res_productOn eb _ _ _)))
  have e := productOn_transition (i := a.2) (i' := b.2) (j := j) (j' := j) (k := a.1)
    (k' := b.1) hs ht hi hj hk hi' hj hk'
  have hg : res hD ((C.div A).g a b) =
      res (le_inf hk hk') (C.g a.1 b.1) * (res (le_inf hi hi') (A.g a.2 b.2))⁻¹ :=
    res_div_g A C (hD.trans hWa) (hD.trans hWb)
  exact ha.trans (e.trans ((congrArg₂ (· * ·) hg.symm hb.symm).trans (map_mul _ _ _).symm))

end ReciprocityTheory.ChartRestriction.G.Semi.LB
