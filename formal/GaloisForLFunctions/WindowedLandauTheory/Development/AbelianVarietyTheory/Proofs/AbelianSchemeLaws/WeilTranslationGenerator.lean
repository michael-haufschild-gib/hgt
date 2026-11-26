import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeTorsionValueCalculation
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.WeilPairingLocalLifts
import Mathlib.Tactic.LinearCombination

/-! Translation by a torsion point acts on the multiplication pullback generator
through the Weil scalar. -/

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CommPairing

open AbLaw.Cube

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A] {L : LB A.left}

/-- When global lifts are given, their scalar commutator equals the Weil scalar. -/
theorem commIsOf_of_weilIs (hA : IsAbelianScheme A) (hL : L.IsLB) {k : ℤ}
    (x y : ThetaGrp A L k T) {c : Γ(T.left, ⊤)ˣ} (hc : WeilIs A L k x.pt y.pt c) :
    CommIsOf A L k x y c := by
  obtain ⟨d, hd⟩ := exists_commIsOf hA hL x y
  have e : c = d := weilIs_unique_of_local_lifts hA hL hc (weilIs_of_commIsOf hA hL hd)
  exact e.symm ▸ hd

/-- A generator of the translation difference pulled back along multiplication
transforms under torsion translation by the Weil scalar. -/
theorem exists_translation_generator_with_weil [Subsingleton T.left] [Nonempty T.left]
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L)
    (n : ℕ) (x : T ⟶ A) (hx : x ^ n = 1) :
    ∃ u : (LB.LinComb L (K := Fin 2)
        ![((snd T A ^ n) * (fst T A ≫ x)).left, (snd T A ^ n).left] ![1, -1]).Gen,
      u.IsGen ∧ ∀ (y : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), y ^ n = 1 → WeilIs A L (n : ℤ) x y c →
        LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (translT A y).left)
          (LB.mulGen L _ _ _ _ u (constGen A L c)) := by
  letI := hA.comm
  obtain ⟨q, hq⟩ := cube_gen_of_relAmple hA hL hAmp hL
  obtain ⟨s, hs, hn⟩ := exists_normalized_cube hL hq
  obtain ⟨θx, rfl, -⟩ := exists_theta_with_cube_values hL hs x n hx
  obtain ⟨u, hu, hval⟩ := exists_translation_generator_with_cube_values hL hs n θx
  refine ⟨u, hu, fun y c hy hc => ?_⟩
  obtain ⟨θy, rfl, hθy⟩ := exists_theta_with_cube_values hL hs y n hy
  have hcomm := commIsOf_of_weilIs hA hL θx θy hc
  apply corr_of_val hL
  intro z J hJ
  let Q := T ⊗ A
  let p : Q ⟶ T := fst T A
  let a : Q ⟶ A := snd T A
  let b : Q ⟶ A := p ≫ θx.pt
  let d : Q ⟶ A := p ≫ θy.pt
  let tx : Q.left ⟶ Q.left := (translT A θx.pt).left
  let ty : Q.left ⟶ Q.left := (translT A θy.pt).left
  let idQ : Q.left ⟶ Q.left := 𝟙 _
  let P := cubicalProduct (fun v w x : Q ⟶ A => cubeValue s v w x z J) n 1
  have e₀ : (lift p a).left = idQ :=
    congrArg Over.Hom.left (show lift p a = 𝟙 Q from lift_fst_snd)
  have ex : (lift p (b * a)).left = tx := rfl
  have ey : (lift p (d * a)).left = ty := rfl
  have hdn : d ^ n = 1 := (MonObj.comp_pow θy.pt n p).symm.trans
    ((congrArg (p ≫ ·) hy).trans (MonObj.comp_one p))
  obtain ⟨c₀, h₀⟩ := hval Q p z J hJ
  obtain ⟨c₁, h₁⟩ := hθy Q p z J hJ
  have hU₀ : val u idQ z J = P a b * ((tval θx idQ z J)⁻¹ * c₀) := by
    simpa only [e₀] using h₀ a
  have hU₁ : val u ty z J = P (d * a) b * ((tval θx ty z J)⁻¹ * c₀) := by
    simpa only [ey] using h₀ (d * a)
  have hY₀ : tval θy idQ z J = P d a * c₁ := by simpa only [e₀] using h₁ a
  have hY₁ : tval θy tx z J = P d (b * a) * c₁ := by simpa only [ex] using h₁ (b * a)
  have hP : P (d * a) b * P d a = P a b * P d (b * a) :=
    cubicalProduct_translate_of_pow_eq_one (isCubicalCocycle_cubeValue hA hL hs hn z J hJ) n d a b hdn
  have hC : tval θx idQ z J * tval θy tx z J =
      tval θy idQ z J * tval θx ty z J * gm p.left z ⊤ c := by
    simpa only [idQ, Category.id_comp] using (commIsOf_iff hL _ _ c).1 hcomm Q.left idQ z J hJ
  have hv : val u ty z J = val u idQ z J * gm p.left z ⊤ c := by
    apply Additive.ofMul.injective
    have eU₀ := congrArg Additive.ofMul hU₀
    have eU₁ := congrArg Additive.ofMul hU₁
    have eY₀ := congrArg Additive.ofMul hY₀
    have eY₁ := congrArg Additive.ofMul hY₁
    have eP := congrArg Additive.ofMul hP
    have eC := congrArg Additive.ofMul hC
    simp only [ofMul_mul, ofMul_inv] at eU₀ eU₁ eY₀ eY₁ eP eC ⊢
    linear_combination (norm := abel) eU₁ - eU₀ + eP + eY₀ - eY₁ + eC
  refine (val_pull hJ u _ _).trans ?_
  rw [Category.id_comp, val_mul hJ, val_constGen, Category.id_comp]
  exact hv

end GlobalTheory.CommPairing
