import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalPullbackGenerators
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.ThetaCommutatorValues

/-! Pullback in the parameter scheme preserves theta lifts and their scalar commutators. -/

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CommPairing

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

private theorem whiskerRight_translPt (a : T' ⟶ T) (x : T ⟶ A) :
    (a ▷ A) ≫ translPt A x = translPt A (a ≫ x) := by
  simp [translPt, comp_lift_assoc]

private theorem translT_whiskerRight (a : T' ⟶ T) (x : T ⟶ A) :
    translT A (a ≫ x) ≫ (a ▷ A) = (a ▷ A) ≫ translT A x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, whiskerRight_fst, translT, lift_fst, lift_fst_assoc]
  · simp only [Category.assoc, whiskerRight_snd, translT, lift_snd, whiskerRight_translPt]

/-- Restriction of a lift preserves its value on the induced test points. -/
theorem exists_theta_restrict (hL : L.IsLB) (a : T' ⟶ T) (x : ThetaGrp A L k T) :
    ∃ x' : ThetaGrp A L k T', x'.pt = a ≫ x.pt ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J), Good L z J →
        tval x' r z J = tval x (r ≫ (a ▷ A).left) z J := by
  let p := (a ▷ A).left
  let f : Fin 2 → ((T ⊗ A).left ⟶ A.left) := ![(snd T A).left, (translPt A x.pt).left]
  let g : Fin 2 → ((T' ⊗ A).left ⟶ A.left) := ![(snd T' A).left, (translPt A (a ≫ x.pt)).left]
  have e (i : Fin 2) : p ≫ f i = g i := by
    fin_cases i
    · exact congrArg Over.Hom.left (whiskerRight_snd a A)
    · exact congrArg Over.Hom.left (whiskerRight_translPt a x.pt)
  obtain ⟨u, hu, hv⟩ := exists_gen_of_formEq hL (g := g) (d := ![k, -k])
    (fun U _ c => Finset.prod_congr rfl fun i _ => congrArg (fun q => c q ^ (![k, -k] : Fin 2 → ℤ) i)
      (e i)) (LB.pullGen L f ![k, -k] x.φ p) (x.isGen.pullGen f ![k, -k] p)
  refine ⟨⟨a ≫ x.pt, u, hu⟩, rfl, fun Z r z J hJ => ?_⟩
  exact (hv Z r z J hJ).trans (val_pull hJ x.φ p r)

/-- The commutator of restricted lifts is the pullback of the original scalar. -/
theorem commIsOf_of_restrict (hL : L.IsLB) (a : T' ⟶ T)
    {x y : ThetaGrp A L k T} {x' y' : ThetaGrp A L k T'}
    (hx : x'.pt = a ≫ x.pt) (hy : y'.pt = a ≫ y.pt)
    (vx : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J), Good L z J →
      tval x' r z J = tval x (r ≫ (a ▷ A).left) z J)
    (vy : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J), Good L z J →
      tval y' r z J = tval y (r ≫ (a ▷ A).left) z J)
    {c : Γ(T.left, ⊤)ˣ} (hc : CommIsOf A L k x y c) :
    CommIsOf A L k x' y' (Units.map a.left.appTop.hom c) := by
  apply (commIsOf_iff hL _ _ _).2
  intro Z r z J hJ
  let p := (a ▷ A).left
  have et (v' : T' ⟶ A) (v : T ⟶ A) (h : v' = a ≫ v) :
      (r ≫ (translT A v').left) ≫ p = (r ≫ p) ≫ (translT A v).left := by
    rw [h]
    exact (Category.assoc _ _ _).trans
      ((congrArg (r ≫ ·) (congrArg Over.Hom.left (translT_whiskerRight a v))).trans
        (Category.assoc _ _ _).symm)
  have ep : (r ≫ p) ≫ (fst T A).left = (r ≫ (fst T' A).left) ≫ a.left :=
    (Category.assoc _ _ _).trans
      ((congrArg (r ≫ ·) (congrArg Over.Hom.left (whiskerRight_fst a A))).trans
        (Category.assoc _ _ _).symm)
  have eg : gm (r ≫ (fst T' A).left) z ⊤ (Units.map a.left.appTop.hom c) =
      gm ((r ≫ p) ≫ (fst T A).left) z ⊤ c :=
    (gm_pull (r ≫ (fst T' A).left) a.left z ⊤ trivial c).trans
      (congrArg (fun q => gm q z ⊤ c) ep.symm)
  rw [vx Z r z J hJ, vy Z r z J hJ, vx Z _ z J hJ, vy Z _ z J hJ, et _ _ hx, et _ _ hy, eg]
  exact (commIsOf_iff hL _ _ _).1 hc Z (r ≫ p) z J hJ

end GlobalTheory.CommPairing
