import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ThetaCommutatorScalar

/-! Multiplication of theta lifts through composition of translations. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
  {L : LB A.left} {T : Over S} {k : ℤ}

theorem translT_translPt (x y : T ⟶ A) :
    translT A x ≫ translPt A y = translPt A (x * y) := by
  have e (q : T ⟶ A) : translPt A q = (fst T A ≫ q) * snd T A := rfl
  rw [e y, e (x * y), MonObj.comp_mul, ← Category.assoc, translT, lift_fst, lift_snd,
    e x, MonObj.comp_mul, ← _root_.mul_assoc, mul_comm (fst T A ≫ y) (fst T A ≫ x)]

theorem translT_mul (x y : T ⟶ A) :
    translT A x ≫ translT A y = translT A (x * y) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [translT, Category.assoc, lift_fst]
  · exact (Category.assoc _ _ _).trans
      ((congrArg (translT A x ≫ ·) (lift_snd (fst T A) (translPt A y))).trans
        ((translT_translPt x y).trans (lift_snd (fst T A) (translPt A (x * y))).symm))

/-- The product of the two lifts evaluates as a product with the second factor translated. -/
theorem exists_theta_mul (hL : L.IsLB) (x y : ThetaGrp A L k T) :
    ∃ xy : ThetaGrp A L k T, xy.pt = x.pt * y.pt ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) j, Good L z j →
        tval xy r z j = tval x r z j * tval y (r ≫ (translT A x.pt).left) z j := by
  let f (q : T ⟶ A) : Fin 2 → ((T ⊗ A).left ⟶ A.left) :=
    ![(snd T A).left, (translPt A q).left]
  let e : Fin 2 → ℤ := ![k, -k]
  let g (i : Fin 2) := (translT A x.pt).left ≫ f y.pt i
  have e₀ : g 0 = (translPt A x.pt).left := congrArg Over.Hom.left (lift_snd (fst T A) (translPt A x.pt))
  have e₁ : g 1 = (translPt A (x.pt * y.pt)).left := congrArg Over.Hom.left (translT_translPt x.pt y.pt)
  have h : FormEq (Sum.elim (f x.pt) g) (Sum.elim e e) (f (x.pt * y.pt)) e := by
    intro U _ a
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
      e₀, e₁, f, e, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]
    rw [_root_.mul_assoc, inv_mul_cancel_left]
  let s := LB.mulGen L (f x.pt) e g e x.φ (LB.pullGen L (f y.pt) e y.φ (translT A x.pt).left)
  have hs : s.IsGen := mulGen_isGen x.isGen (y.isGen.pullGen _ _ _)
  obtain ⟨a, ha, hb⟩ := exists_gen_of_formEq hL h s hs
  refine ⟨⟨x.pt * y.pt, a, ha⟩, rfl, fun Z r z j hj => ?_⟩
  exact (hb Z r z j hj).trans ((val_mul hj _ _ _).trans (congrArg (_ * ·) (val_pull hj _ _ _)))

end GlobalTheory.CommPairing
