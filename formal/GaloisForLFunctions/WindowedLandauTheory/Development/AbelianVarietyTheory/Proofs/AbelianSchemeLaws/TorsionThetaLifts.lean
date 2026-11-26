import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeSquare
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.LocalGeneratorsOfFormalProducts
import Mathlib.Tactic.Module

/-! The theorem of the square gives local theta lifts of points killed by the tensor exponent. -/

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

namespace GlobalTheory.AbLaw.Cube

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A] {L : LB A.left}

private theorem translPt_one : translPt A (1 : T ⟶ A) = snd T A := by
  change (fst T A ≫ (1 : T ⟶ A)) * snd T A = snd T A
  rw [MonObj.comp_one, _root_.one_mul]

private theorem locallyGenerated_translate_pow (hA : IsAbelianScheme A) (hL : L.IsLB)
    (hAmp : RelAmple A L) (x : T ⟶ A) (n : ℕ) :
    LocallyGenerated L (I := Fin 3) (fst T A).left
      ![(translPt A (x ^ n)).left, (snd T A).left, (translPt A x).left] ![-1, 1 - (n : ℤ), (n : ℤ)] := by
  induction n with
  | zero =>
    apply locallyGenerated_of_cancellation hL
    intro U _ k
    rw [pow_zero, translPt_one, Fin.prod_univ_three]
    simp
  | succ n ih =>
    have hsq := (locallyGenerated_iff hL _ _ _).2
      (square_local_of_relAmple hA hL hAmp (x ^ n) x)
    refine LocallyGenerated.div hL ih hsq fun U _ k => ?_
    rw [pow_succ x n, Fin.prod_univ_three, Fin.prod_univ_three, Fin.prod_univ_four]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    simp
    module

/-- An n-torsion point lifts locally to the theta group of the n-th power
of a relatively ample line bundle. -/
theorem exists_local_theta_lift_of_pow_eq_one (hA : IsAbelianScheme A) (hL : L.IsLB)
    (hAmp : RelAmple A L) (x : T ⟶ A) (n : ℕ) (hx : x ^ n = 1) (p : T.left) :
    ∃ U : T.left.Opens, p ∈ U ∧ ∃ θ : ThetaGrp A L (n : ℤ) (overRes U),
      θ.pt = overResι U ≫ x := by
  have hpow := locallyGenerated_translate_pow hA hL hAmp x n
  rw [hx, translPt_one] at hpow
  have hone : LocallyGenerated L (I := Fin 0) (fst T A).left ![] ![] :=
    locallyGenerated_of_cancellation hL _ _ _ (fun U _ k => by simp)
  have hgen : LocallyGenerated L (I := Fin 2) (fst T A).left
      ![(snd T A).left, (translPt A x).left] ![(n : ℤ), -(n : ℤ)] := by
    refine LocallyGenerated.div hL hone hpow fun U _ k => ?_
    rw [Fin.prod_univ_three, Fin.prod_univ_two]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    simp
    module
  obtain ⟨U, hp, s, hs⟩ := hgen p
  let Z := overRes (T := T) U
  let r : Z ⊗ A ⟶ T ⊗ A := overResι U ▷ A
  let W := (fst T A).left ⁻¹ᵁ U
  have hr : Set.range r.left ⊆ W := by
    rintro _ ⟨z, rfl⟩
    exact (congrArg (fun f : Z ⊗ A ⟶ T => f.left z ∈ U)
      (whiskerRight_fst (overResι U) A)).mpr ((fst Z A).left z).2
  let q : (Z ⊗ A).left ⟶ W.toScheme := IsOpenImmersion.lift W.ι r.left (by rwa [Scheme.Opens.range_ι])
  have hq : q ≫ W.ι = r.left := IsOpenImmersion.lift_fac _ _ _
  have ht : r ≫ translPt A x = translPt A (overResι U ≫ x) := by
    simp [r, translPt, comp_lift_assoc]
  let f : Fin 2 → ((T ⊗ A).left ⟶ A.left) := ![(snd T A).left, (translPt A x).left]
  let g : Fin 2 → ((Z ⊗ A).left ⟶ A.left) := ![(snd Z A).left, (translPt A (overResι U ≫ x)).left]
  have e (i : Fin 2) : q ≫ W.ι ≫ f i = g i := by
    rw [← Category.assoc, hq]
    fin_cases i
    · exact congrArg Over.Hom.left (whiskerRight_snd (overResι U) A)
    · exact congrArg Over.Hom.left ht
  have hg : ∃ t : (LB.LinComb L (fun i => q ≫ W.ι ≫ f i) ![(n : ℤ), -(n : ℤ)]).Gen,
      t.IsGen := ⟨_, hs.pullGen (fun i => W.ι ≫ f i) _ q⟩
  rw [funext e] at hg
  obtain ⟨t, hu⟩ := hg
  exact ⟨U, hp, ⟨overResι U ≫ x, t, hu⟩, rfl⟩

end GlobalTheory.AbLaw.Cube
