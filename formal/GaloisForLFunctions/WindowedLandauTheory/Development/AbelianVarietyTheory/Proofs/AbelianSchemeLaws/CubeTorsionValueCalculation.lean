import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubePowerValueGenerators
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeSquare
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.ThetaCommutatorValues

/-! Cubical products express the values of torsion theta lifts and generators of
the pullback of a translation difference by multiplication. -/

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.AbLaw.Cube

open CommPairing (tval)

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

private theorem exists_gen_of_subsingleton {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB)
    [Subsingleton Y] [Nonempty Y] {I : Type} [Fintype I] (f : I → (Y ⟶ X)) (d : I → ℤ) :
    ∃ t : (LB.LinComb M f d).Gen, t.IsGen := by
  obtain ⟨p⟩ : Nonempty Y := inferInstance
  choose i hi using fun j => exists_chart hM (f j p)
  exact exists_gen_of_chart hM f d i fun y =>
    Set.mem_iInter.2 fun j => (Subsingleton.elim y p).symm ▸ hi j

/-- A torsion theta lift whose values are the cubical product up to a scalar on the parameter scheme. -/
theorem exists_theta_with_cube_values [Subsingleton T.left] [Nonempty T.left]
    (hL : L.IsLB) {s : (cubeBundle A L).Gen} (hs : s.IsGen)
    (y : T ⟶ A) (n : ℕ) (hy : y ^ n = 1) :
    ∃ θ : ThetaGrp A L (n : ℤ) T, θ.pt = y ∧
      ∀ (Z : Over S) (t : Z ⟶ T) (z : Z.left) (J : (Z.left ⟶ A.left) → L.ι),
        Good L z J → ∃ c : (Z.left.presheaf.stalk z)ˣ, ∀ x : Z ⟶ A,
          tval θ (lift t x).left z J =
            cubicalProduct (fun b d e => cubeValue s b d e z J) n 1 (t ≫ y) x * c := by
  let Q := T ⊗ A
  let p : Q ⟶ T := fst T A
  let m : Q ⟶ A := p ≫ y
  let a : Q ⟶ A := snd T A
  let f : Fin 2 → (T.left ⟶ A.left) := ![(1 : T ⟶ A).left, y.left]
  let d : Fin 2 → ℤ := ![(n : ℤ), -(n : ℤ)]
  obtain ⟨u, hu⟩ := exists_gen_of_subsingleton hL f d
  obtain ⟨v, hv, he⟩ := exists_cube_power_generator hL hs (1 : Q ⟶ A) m a n
  have hm : m ^ n = 1 := (MonObj.comp_pow y n p).symm.trans
    ((congrArg (p ≫ ·) hy).trans (MonObj.comp_one p))
  have e₁ : p.left ≫ (1 : T ⟶ A).left = (1 : Q ⟶ A).left := congrArg Over.Hom.left (MonObj.comp_one p)
  let g : Fin 2 → (Q.left ⟶ A.left) := ![a.left, (m * a).left]
  obtain ⟨w, hw, hval⟩ := exists_gen_of_formEq hL (g := g) (d := d)
    (fun U _ k => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, cubePowerFactors, cubePowerExponents, hm, f, d, g,
        Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        e₁, show p.left ≫ y.left = m.left from rfl, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      module) _ (mulGen_isGen hv (hu.pullGen f d p.left))
  refine ⟨⟨y, w, hw⟩, rfl, fun Z t z J hJ => ⟨val u t.left z J, fun x => ?_⟩⟩
  have et : (lift t x).left ≫ p.left = t.left := congrArg Over.Hom.left (lift_fst t x)
  have em : lift t x ≫ m = t ≫ y := lift_fst_assoc _ _ _
  have ea : lift t x ≫ a = x := lift_snd t x
  change val w (lift t x).left z J = _
  rw [hval Z.left (lift t x).left z J hJ, val_mul hJ, he Z (lift t x) z J hJ, val_pull hJ,
    et, em, ea, MonObj.comp_one]

/-- Pullback of the translation difference by multiplication has the cube-product
value divided by the theta lift, up to a scalar on the parameter scheme. -/
theorem exists_translation_generator_with_cube_values [Subsingleton T.left] [Nonempty T.left]
    (hL : L.IsLB) {s : (cubeBundle A L).Gen} (hs : s.IsGen) (n : ℕ) (θ : ThetaGrp A L (n : ℤ) T) :
    ∃ u : (LB.LinComb L (K := Fin 2)
        ![((snd T A ^ n) * (fst T A ≫ θ.pt)).left, (snd T A ^ n).left] ![1, -1]).Gen, u.IsGen ∧
      ∀ (Z : Over S) (t : Z ⟶ T) (z : Z.left) (J : (Z.left ⟶ A.left) → L.ι),
        Good L z J → ∃ c : (Z.left.presheaf.stalk z)ˣ, ∀ x : Z ⟶ A,
          val u (lift t x).left z J = cubicalProduct (fun b d e => cubeValue s b d e z J)
            n 1 x (t ≫ θ.pt) * ((tval θ (lift t x).left z J)⁻¹ * c) := by
  let Q := T ⊗ A
  let p : Q ⟶ T := fst T A
  let a : Q ⟶ A := snd T A
  let m : Q ⟶ A := p ≫ θ.pt
  let f : Fin 2 → (T.left ⟶ A.left) := ![(1 : T ⟶ A).left, θ.pt.left]
  let d : Fin 2 → ℤ := ![(n : ℤ) - 1, 1 - (n : ℤ)]
  let g : Fin 2 → (Q.left ⟶ A.left) := ![a.left, (m * a).left]
  let b : Fin 2 → ℤ := ![(n : ℤ), -(n : ℤ)]
  obtain ⟨u, hu⟩ := exists_gen_of_subsingleton hL f d
  obtain ⟨v, hv, he⟩ := exists_cube_power_generator hL hs (1 : Q ⟶ A) a m n
  have e₁ : p.left ≫ (1 : T ⟶ A).left = (1 : Q ⟶ A).left := congrArg Over.Hom.left (MonObj.comp_one p)
  obtain ⟨w, hw, hval⟩ := exists_gen_of_formEq hL (g := ![(a ^ n * m).left, (a ^ n).left]) (d := ![1, -1])
    (fun U _ k => by
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, cubePowerFactors, cubePowerExponents, f, d, g, b,
        Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        e₁, show p.left ≫ θ.pt.left = m.left from rfl, _root_.one_mul, show m * a = a * m from mul_comm m a]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      module)
    (LB.mulGen L _ _ _ _ v (LB.mulGen L _ _ _ _ (LB.invGen L g b θ.φ) (LB.pullGen L f d u p.left)))
    (mulGen_isGen hv (mulGen_isGen (invGen_isGen θ.isGen) (hu.pullGen f d p.left)))
  refine ⟨w, hw, fun Z t z J hJ => ⟨val u t.left z J, fun x => ?_⟩⟩
  have et : (lift t x).left ≫ p.left = t.left := congrArg Over.Hom.left (lift_fst t x)
  have em : lift t x ≫ m = t ≫ θ.pt := lift_fst_assoc _ _ _
  have ea : lift t x ≫ a = x := lift_snd t x
  rw [hval Z.left (lift t x).left z J hJ, val_mul hJ, val_mul hJ, he Z (lift t x) z J hJ,
    val_inv, val_pull hJ, et, em, ea, MonObj.comp_one]
  rfl

end GlobalTheory.AbLaw.Cube
