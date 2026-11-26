import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeAssembly
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeProductFormula
import Mathlib.Tactic.Abel

/-! The translation quotient in the theorem of the square is locally trivial on the
parameter scheme. Pull back the cube and trivialize its factors from the parameter scheme. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.AbLaw.Cube

attribute [local instance] Over.cartesianMonoidalCategory

/-- A single chart containing the image of every factor gives a generator of the formal product. -/
theorem exists_gen_of_chart {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {I : Type} [Fintype I] (f : I → (Y ⟶ X)) (e : I → ℤ)
    (i : I → L.ι) (hi : ∀ y : Y, y ∈ LB.wchart L f i) :
    ∃ s : (LB.LinComb L f e).Gen, s.IsGen := by
  let P := LB.LinComb L f e
  have hle (j : I → L.ι) : P.U j ≤ P.U j ⊓ P.U i := fun y hy => ⟨hy, hi y⟩
  let s : P.Gen := ⟨fun j => res (hle j) (P.g j i)⟩
  have hs (y : Y) (j : I → L.ι) (hy : y ∈ P.U j) :
      gm (𝟙 Y) y (P.U j) (s.s j) = trF f e (𝟙 Y) y j i :=
    (gm_res (𝟙 Y) y (hle j) hy _).trans (gm_linComb L f e (𝟙 Y) y j i hy (hi y))
  refine ⟨s, isGen_of_gm (fun y j k hj hk => ?_)⟩
  rw [hs y j hj, hs y k hk]
  exact (trF_trans hL f e (𝟙 Y) y hj hk (hi y)).symm

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

private theorem exists_gen_square [IsCommMonObj A] (hL : L.IsLB)
    {s : (cubeBundle A L).Gen} (hs : s.IsGen) {T : Over S} (a b c : T ⟶ A)
    (i : Fin 4 → L.ι)
    (hi : ∀ y : T.left, y ∈ LB.wchart L ![(a * b).left, a.left, b.left, (1 : T ⟶ A).left] i) :
    ∃ t : (LB.LinComb L (K := Fin 4) ![(a * b * c).left, c.left, (a * c).left, (b * c).left]
      ![1, 1, -1, -1]).Gen, t.IsGen := by
  let f : Fin 4 → (T.left ⟶ A.left) := ![(a * b).left, a.left, b.left, (1 : T ⟶ A).left]
  let d : Fin 4 → ℤ := ![1, -1, -1, 1]
  obtain ⟨u, hu⟩ := exists_gen_of_chart hL f d i hi
  let r := (lift a (lift b c)).left
  have ht := hs.pullGen (cubeMorphism A) cubeExponent r
  obtain ⟨v, hv, -⟩ := exists_gen_of_formEq hL
    (g := ![(a * b * c).left, c.left, (a * c).left, (b * c).left]) (d := ![1, 1, -1, -1])
    (fun U _ k => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      have hp := prod_cube a b c k
      change (∏ I, k (r ≫ cubeMorphism A I) ^ cubeExponent I) = _ at hp
      rw [hp]
      apply Additive.ofMul.injective
      simp only [f, d, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, zpow_one, zpow_neg_one, _root_.mul_one, ofMul_inv, ofMul_mul]
      abel) _ (mulGen_isGen hu ht)
  exact ⟨v, hv⟩

/-- The square quotient for two translations is trivial over a neighbourhood of each
point of the parameter scheme. -/
theorem square_local_of_relAmple (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L)
    {T : Over S} (x y : T ⟶ A) (p : T.left) :
    ∃ V : T.left.Opens, p ∈ V ∧ ∃ t : ((LB.LinComb L (K := Fin 4)
      ![(translPt A (x * y)).left, (snd T A).left, (translPt A x).left, (translPt A y).left]
      ![1, 1, -1, -1]).pull ((fst T A).left ⁻¹ᵁ V).ι).Gen, t.IsGen := by
  letI := hA.comm
  obtain ⟨s, hs⟩ := cube_gen_of_relAmple hA hL hAmp hL
  let f : Fin 4 → (T.left ⟶ A.left) := ![(x * y).left, x.left, y.left, (1 : T ⟶ A).left]
  choose i hi using fun j => exists_chart hL (f j p)
  let V := LB.wchart L f i
  refine ⟨V, Set.mem_iInter.2 hi, ?_⟩
  let W := (fst T A).left ⁻¹ᵁ V
  let r : overRes (T := T ⊗ A) W ⟶ T ⊗ A := overResι W
  let a := r ≫ fst T A ≫ x
  let b := r ≫ fst T A ≫ y
  let c := r ≫ snd T A
  have e (j : Fin 4) : (![(a * b).left, a.left, b.left, (1 : overRes (T := T ⊗ A) W ⟶ A).left] j) =
      W.ι ≫ (fst T A).left ≫ f j := by
    fin_cases j
    · change (a * b).left = ((r ≫ fst T A) ≫ (x * y)).left
      rw [MonObj.comp_mul]
      simp only [a, b, Category.assoc]
    · rfl
    · rfl
    · change (1 : overRes (T := T ⊗ A) W ⟶ A).left =
        ((r ≫ fst T A) ≫ (1 : T ⟶ A)).left
      rw [MonObj.comp_one]
  obtain ⟨t, ht⟩ := exists_gen_square hL hs a b c i (fun z => Set.mem_iInter.2 fun j => by
    rw [e j]
    exact Set.mem_iInter.1 z.2 j)
  apply (trivial_pull_linComb L hL _ _ W.ι).2
  have h₁ : a * b * c = r ≫ translPt A (x * y) := by
    change _ = r ≫ ((fst T A ≫ (x * y)) * snd T A)
    simp only [a, b, c, MonObj.comp_mul]
  have h₂ (z : T ⟶ A) : (r ≫ fst T A ≫ z) * c = r ≫ translPt A z := by
    change _ = r ≫ ((fst T A ≫ z) * snd T A)
    simp only [c, MonObj.comp_mul]
  obtain ⟨u, hu, -⟩ := exists_gen_of_formEq hL
    (g := fun j => W.ι ≫ (![(translPt A (x * y)).left, (snd T A).left,
      (translPt A x).left, (translPt A y).left] : Fin 4 → ((T ⊗ A).left ⟶ A.left)) j)
    (d := ![1, 1, -1, -1])
    (fun U _ k => by
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, h₁, show a * c = _ from h₂ x, show b * c = _ from h₂ y]
      rfl) t ht
  exact ⟨u, hu⟩

end GlobalTheory.AbLaw.Cube
