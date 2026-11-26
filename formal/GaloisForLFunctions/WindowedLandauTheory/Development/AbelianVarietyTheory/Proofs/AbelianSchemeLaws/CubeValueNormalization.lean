import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeAssembly
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeProductFormula
import Mathlib.Tactic.Abel

/-! A cube generator normalized at the identity triple evaluates to one on every
identity triple of test points. -/

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.AbLaw.Cube

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

/-- The germ of a cube generator at a triple of test points in coherent charts. -/
noncomputable def cubeValue (s : (cubeBundle A L).Gen) {T : Over S} (a b c : T ⟶ A)
    (z : T.left) (J : (T.left ⟶ A.left) → L.ι) : (T.left.presheaf.stalk z)ˣ :=
  val s (lift a (lift b c)).left z J

/-- A cube generator is normalized if its value on the identity triple is one. -/
def NormalizedCube (s : (cubeBundle A L).Gen) : Prop :=
  ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ A.left) → L.ι),
    Good L z J → cubeValue s (1 : T ⟶ A) 1 1 z J = 1

/-- Dividing any cube generator by its pullback along the identity triple normalizes it. -/
theorem exists_normalized_cube (hL : L.IsLB) {s : (cubeBundle A L).Gen} (hs : s.IsGen) :
    ∃ t : (cubeBundle A L).Gen, t.IsGen ∧ NormalizedCube t := by
  let B := A ⊗ (A ⊗ A)
  let r : B ⟶ B := lift (1 : B ⟶ A) (lift 1 1)
  let f := cubeMorphism A
  let d := cubeExponent
  have hcancel (U : Type) [CommGroup U] (k : (B.left ⟶ A.left) → U) :
      ∏ i, k (r.left ≫ f i) ^ d i = 1 := by
    refine (prod_cube (1 : B ⟶ A) 1 1 k).trans ?_
    apply Additive.ofMul.injective
    simp only [_root_.one_mul, ofMul_mul, ofMul_inv, ofMul_one]
    abel
  let sf := LB.pullGen L f d s r.left
  have hf : sf.IsGen := hs.pullGen f d r.left
  have hform : FormEq (Sum.elim f (fun i => r.left ≫ f i)) (Sum.elim d (fun i => -d i)) f d := by
    intro U _ k
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib,
      hcancel U k, inv_one, _root_.mul_one]
  obtain ⟨t, ht, hv⟩ := exists_gen_of_formEq hL hform
    (LB.mulGen L f d _ _ s (LB.invGen L _ _ sf)) (mulGen_isGen hs (invGen_isGen hf))
  refine ⟨t, ht, fun T z J hJ => ?_⟩
  let e : T ⟶ B := lift (1 : T ⟶ A) (lift 1 1)
  have he : e ≫ r = e := by
    change e ≫ lift (1 : B ⟶ A) (lift 1 1) = _
    simp only [comp_lift, MonObj.comp_one]
    rfl
  have he' : e.left ≫ r.left = e.left := congrArg Over.Hom.left he
  change val t e.left z J = 1
  rw [hv T.left e.left z J hJ, val_mul hJ, val_inv]
  have hv' : val sf e.left z J = val s e.left z J :=
    (val_pull hJ s r.left e.left).trans (congrArg (fun a => val s a z J) he')
  exact mul_inv_eq_one.mpr hv'.symm

end GlobalTheory.AbLaw.Cube
