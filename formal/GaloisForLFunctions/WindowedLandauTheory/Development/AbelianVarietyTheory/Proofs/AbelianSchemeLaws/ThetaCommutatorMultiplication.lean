import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ThetaProductOfLifts

/-! The theta commutator multiplies along products of lifts and inverts when the lifts are exchanged. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
  {L : LB A.left} {T : Over S} {k : ℤ}

private theorem translT_comm (x y : T ⟶ A) :
    (translT A x).left ≫ (translT A y).left = (translT A y).left ≫ (translT A x).left := by
  rw [← Over.comp_left, ← Over.comp_left, translT_mul, translT_mul, mul_comm x y]

theorem commIsOf_swap (hL : L.IsLB) {x y : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ}
    (h : CommIsOf A L k x y c) : CommIsOf A L k y x c⁻¹ := by
  apply (commIsOf_iff hL y x _).2
  intro Z r z j hj
  rw [map_inv, (commIsOf_iff hL x y c).1 h Z r z j hj, mul_inv_cancel_right]

/-- Multiplying two lifts multiplies their scalar commutators with a third lift. -/
theorem exists_commIsOf_mul_left (hL : L.IsLB) {x y u : ThetaGrp A L k T}
    {c d : Γ(T.left, ⊤)ˣ} (hc : CommIsOf A L k x u c) (hd : CommIsOf A L k y u d) :
    ∃ v : ThetaGrp A L k T, v.pt = x.pt * y.pt ∧ CommIsOf A L k v u (c * d) := by
  obtain ⟨v, hv, hval⟩ := exists_theta_mul hL x y
  refine ⟨v, hv, (commIsOf_iff hL v u (c * d)).2 (fun Z r z j hj => ?_)⟩
  let X := (translT A x.pt).left
  let Y := (translT A y.pt).left
  let U := (translT A u.pt).left
  let F := (fst T A).left
  have ev : r ≫ (translT A v.pt).left = (r ≫ X) ≫ Y := by
    rw [hv, ← translT_mul, Over.comp_left, Category.assoc]
  have eX : (r ≫ X) ≫ U = (r ≫ U) ≫ X := by
    rw [Category.assoc, Category.assoc]
    exact congrArg (r ≫ ·) (translT_comm x.pt u.pt)
  have eF : (r ≫ X) ≫ F = r ≫ F :=
    (Category.assoc r X F).trans (congrArg (r ≫ ·) (translT_fst x.pt))
  have b := (commIsOf_iff hL y u d).1 hd Z (r ≫ X) z j hj
  change tval y (r ≫ X) z j * tval u ((r ≫ X) ≫ Y) z j =
    tval u (r ≫ X) z j * tval y ((r ≫ X) ≫ U) z j * gm ((r ≫ X) ≫ F) z ⊤ d at b
  rw [eX, eF] at b
  have a := (commIsOf_iff hL x u c).1 hc Z r z j hj
  rw [hval Z r z j hj, hval Z (r ≫ U) z j hj, ev, map_mul]
  calc
    _ = tval x r z j * (tval y (r ≫ X) z j * tval u ((r ≫ X) ≫ Y) z j) := _root_.mul_assoc _ _ _
    _ = tval x r z j *
        ((tval u (r ≫ X) z j * tval y ((r ≫ U) ≫ X) z j) * gm (r ≫ F) z ⊤ d) :=
      congrArg (_ * ·) b
    _ = (tval x r z j * tval u (r ≫ X) z j) *
        (tval y ((r ≫ U) ≫ X) z j * gm (r ≫ F) z ⊤ d) := by simp only [_root_.mul_assoc]
    _ = _ := by
      change _ = _
      rw [a]
      apply Additive.ofMul.injective
      simp only [ofMul_mul]
      abel

end GlobalTheory.CommPairing
