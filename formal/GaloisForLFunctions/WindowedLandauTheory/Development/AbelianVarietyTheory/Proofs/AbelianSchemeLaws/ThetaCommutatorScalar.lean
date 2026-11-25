import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.AbelianSchemeGlobalSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ThetaScalarRatio
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.ThetaCommutatorValues
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundlePullback
import Mathlib.Tactic.Abel

/-! A theta commutator is a scalar and is independent of the lifts. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ}

theorem translT_fst (x : T ⟶ A) :
    (translT A x).left ≫ (fst T A).left = (fst T A).left :=
  congrArg Over.Hom.left (lift_fst (fst T A) (translPt A x))

private theorem translT_snd (x : T ⟶ A) :
    (translT A x).left ≫ (snd T A).left = (translPt A x).left :=
  congrArg Over.Hom.left (lift_snd (fst T A) (translPt A x))

/-- A pair of theta lifts gives a commutator scalar by cancellation of the translated factors. -/
theorem exists_commIsOf (hA : IsAbelianScheme A) (hL : L.IsLB) (x y : ThetaGrp A L k T) :
    ∃ c, CommIsOf A L k x y c := by
  haveI := hA.comm
  haveI := hA.isIso_fst_appTop T
  let f (q : T ⟶ A) : Fin 2 → ((T ⊗ A).left ⟶ A.left) :=
    ![(snd T A).left, (translPt A q).left]
  let e : Fin 2 → ℤ := ![k, -k]
  let g (q q' : T ⟶ A) (i : Fin 2) := (translT A q).left ≫ f q' i
  let sx := LB.mulGen L (f x.pt) e (g x.pt y.pt) e x.φ
    (LB.pullGen L (f y.pt) e y.φ (translT A x.pt).left)
  let sy := LB.mulGen L (f y.pt) e (g y.pt x.pt) e y.φ
    (LB.pullGen L (f x.pt) e x.φ (translT A y.pt).left)
  have hx : sx.IsGen := mulGen_isGen x.isGen (y.isGen.pullGen _ _ _)
  have hy : sy.IsGen := mulGen_isGen y.isGen (x.isGen.pullGen _ _ _)
  have eform : FormEq (Sum.elim (f x.pt) (g x.pt y.pt)) (Sum.elim e e)
      (Sum.elim (f y.pt) (g y.pt x.pt)) (Sum.elim e e) := by
    intro U _ a
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, f, e, g,
      Matrix.cons_val_zero, Matrix.cons_val_one, translT_snd,
      GlobalTheory.WeilPull.transl_commute (mul_comm x.pt y.pt)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, zpow_neg, ofMul_inv]
    abel
  obtain ⟨c, hc⟩ := exists_ratio hL eform (fst T A).left hx hy
  refine ⟨c, (commIsOf_iff hL x y c).2 (fun Z r z j hj => ?_)⟩
  have he := hc Z r z j hj
  simp only [sx, sy, val_mul hj, val_pull hj] at he
  exact he

private theorem theta_ratio (hA : IsAbelianScheme A) (hL : L.IsLB)
    (x x' : ThetaGrp A L k T) (h : x.pt = x'.pt) :
    ∃ c : Γ(T.left, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) j,
      Good L z j → tval x r z j = tval x' r z j * gm (r ≫ (fst T A).left) z ⊤ c := by
  haveI := hA.isIso_fst_appTop T
  obtain ⟨x, s, hs⟩ := x
  obtain ⟨x', s', hs'⟩ := x'
  change x = x' at h
  subst x'
  exact exists_ratio hL (fun _ _ _ => rfl) (fst T A).left hs hs'

/-- Changing either lift multiplies the two products by the same factors from the base. -/
theorem commIsOf_of_same_points (hA : IsAbelianScheme A) (hL : L.IsLB)
    {x y x' y' : ThetaGrp A L k T} (hx : x'.pt = x.pt) (hy : y'.pt = y.pt)
    {c : Γ(T.left, ⊤)ˣ} (hc : CommIsOf A L k x y c) : CommIsOf A L k x' y' c := by
  obtain ⟨a, ha⟩ := theta_ratio hA hL x' x hx
  obtain ⟨b, hb⟩ := theta_ratio hA hL y' y hy
  apply (commIsOf_iff hL x' y' c).2
  intro Z r z j hj
  have h := (commIsOf_iff hL x y c).1 hc Z r z j hj
  rw [hx, hy, ha Z r z j hj, hb Z r z j hj, hb Z _ z j hj, ha Z _ z j hj,
    Category.assoc, Category.assoc, translT_fst, translT_fst, _root_.mul_mul_mul_comm, h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul]
  abel

end GlobalTheory.CommPairing
