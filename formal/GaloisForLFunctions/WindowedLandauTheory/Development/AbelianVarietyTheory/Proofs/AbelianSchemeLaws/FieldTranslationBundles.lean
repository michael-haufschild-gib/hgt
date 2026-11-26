import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.AbelianMultiplicationIsogeny
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeSquare
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.GeometricPointDivision

/-! On an abelian variety over an algebraically closed field, the theorem of
the square identifies a translated twist with a translate of the whole power. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TwistTranslate

attribute [local instance] Over.cartesianMonoidalCategory

variable {K : Type} [Field K] {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}

/-- Translation by a point on the base field. -/
def translate (A : Over (Spec (.of K))) [GrpObj A] (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) : A ⟶ A :=
  (toUnit A ≫ x) * 𝟙 A

@[simp] theorem translate_one : translate A 1 = 𝟙 A := by
  rw [translate, MonObj.comp_one, _root_.one_mul]

theorem translate_comp (x y : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    translate A x ≫ translate A y = translate A (y * x) := by
  change translate A x ≫ ((toUnit A ≫ y) * 𝟙 A) = _
  rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
  rw [translate, translate, MonObj.comp_mul, _root_.mul_assoc]

theorem translate_comp_mulN [IsCommMonObj A] (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) (n : ℕ) :
    translate A x ≫ GrpTangent.mulN A n = GrpTangent.mulN A n ≫ translate A (x ^ n) := by
  rw [GrpTangent.comp_mulN]
  change ((toUnit A ≫ x) * 𝟙 A) ^ n = GrpTangent.mulN A n ≫ ((toUnit A ≫ x ^ n) * 𝟙 A)
  rw [mul_pow, MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id]
  exact congrArg (· * GrpTangent.mulN A n) (MonObj.comp_pow x n (toUnit A)).symm

private abbrev HasGen {I : Type} [Fintype I] (f : I → (A.left ⟶ A.left)) (d : I → ℤ) :=
  ∃ s : (LB.LinComb L f d).Gen, s.IsGen

private theorem square_gen (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L)
    (x y : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    HasGen (L := L) ![(translate A (x * y)).left, 𝟙 A.left,
      (translate A x).left, (translate A y).left] ![1, 1, -1, -1] := by
  let T := 𝟙_ (Over (Spec (.of K)))
  let S := Spec (.of K)
  letI : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let p : S := IsLocalRing.closedPoint K
  obtain ⟨V, hp, s, hs⟩ := AbLaw.Cube.square_local_of_relAmple hA hL hAmp x y p
  let W := (fst T A).left ⁻¹ᵁ V
  let σ : A ⟶ T ⊗ A := lift (toUnit A) (𝟙 A)
  have hW : Set.range σ.left ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change (fst T A).left (σ.left z) ∈ V
    rwa [Subsingleton.elim ((fst T A).left (σ.left z)) p]
  let r : A.left ⟶ W.toScheme := IsOpenImmersion.lift W.ι σ.left hW
  have hr : r ≫ W.ι = σ.left := IsOpenImmersion.lift_fac _ _ _
  let f : Fin 4 → ((T ⊗ A).left ⟶ A.left) :=
    ![(translPt A (x * y)).left, (snd T A).left, (translPt A x).left, (translPt A y).left]
  let g : Fin 4 → (A.left ⟶ A.left) :=
    ![(translate A (x * y)).left, 𝟙 A.left, (translate A x).left, (translate A y).left]
  let d : Fin 4 → ℤ := ![1, 1, -1, -1]
  obtain ⟨t, ht⟩ := (AbLaw.Cube.trivial_pull_linComb L hL f d W.ι).1 ⟨s, hs⟩
  have htr (z : T ⟶ A) : σ ≫ translPt A z = translate A z := by
    change σ ≫ ((fst T A ≫ z) * snd T A) = _
    rw [MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd]
    rfl
  have he (i : Fin 4) : r ≫ W.ι ≫ f i = g i := by
    rw [← Category.assoc, hr]
    fin_cases i
    · exact congrArg Over.Hom.left (htr (x * y))
    · exact congrArg Over.Hom.left (lift_snd (toUnit A) (𝟙 A))
    · exact congrArg Over.Hom.left (htr x)
    · exact congrArg Over.Hom.left (htr y)
  obtain ⟨w, hw, -⟩ := exists_gen_of_formEq hL (g := g) (d := d)
    (fun U _ k => Finset.prod_congr rfl fun i _ => congrArg (fun v => k v ^ d i) (he i))
    (LB.pullGen L (fun i => W.ι ≫ f i) d t r) (ht.pullGen _ _ r)
  exact ⟨w, hw⟩

private theorem gen_power_translate (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L)
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) (m : ℕ) :
    HasGen (L := L) ![𝟙 A.left, (translate A (x ^ (m + 1))).left, (translate A x).left]
      ![(m : ℤ), 1, -((m : ℤ) + 1)] := by
  induction m with
  | zero =>
    obtain ⟨t, ht⟩ := square_gen hA hL hAmp x x
    let f : Fin 4 → (A.left ⟶ A.left) :=
      ![(translate A (x * x)).left, 𝟙 A.left, (translate A x).left, (translate A x).left]
    let d : Fin 4 → ℤ := ![1, 1, -1, -1]
    obtain ⟨u, hu, -⟩ := exists_gen_of_formEq hL
      (g := ![𝟙 A.left, (translate A (x ^ ((0 : ℕ) + 1))).left, (translate A x).left])
      (d := ![(0 : ℤ), 1, -((0 : ℤ) + 1)])
      (fun U _ k => by
        simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, ← Finset.prod_mul_distrib, ← zpow_add]
        simp [Fin.prod_univ_succ])
      (LB.mulGen L f d f (fun i => -d i) t (LB.invGen L f d t))
      (mulGen_isGen ht (invGen_isGen ht))
    exact ⟨u, hu⟩
  | succ m ih =>
    obtain ⟨s, hs⟩ := ih
    obtain ⟨t, ht⟩ := square_gen hA hL hAmp (x ^ (m + 1)) x
    obtain ⟨u, hu, -⟩ := exists_gen_of_formEq hL
      (g := ![𝟙 A.left, (translate A (x ^ (m + 1 + 1))).left, (translate A x).left])
      (d := ![((m + 1 : ℕ) : ℤ), 1, -(((m + 1 : ℕ) : ℤ) + 1)])
      (fun U _ k => by
        apply Additive.ofMul.injective
        simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ,
          Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, _root_.mul_one,
          ofMul_mul, ofMul_zpow, Nat.cast_succ, pow_succ x (m + 1)]
        module)
      _ (mulGen_isGen hs ht)
    exact ⟨u, hu⟩

/-- A positive power with a single translated factor is a translate of the whole power,
using division of the translation point and the theorem of the square. -/
theorem exists_gen_twisted_pow_translate [IsAlgClosed K]
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L)
    (hrig : ∃ t : (L.pull η[A].left).Gen, t.IsGen)
    (hsym : ∀ s : Spec (.of K), ∃ U : (Spec (.of K)).Opens, s ∈ U ∧
      ∃ t : (LB.LinComb L (K := Fin 2)
        ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]).Gen, t.IsGen)
    (n : ℕ) (hn : n ≠ 0) (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    ∃ y : 𝟙_ (Over (Spec (.of K))) ⟶ A, y ^ n = x ∧
      HasGen (L := L) ![𝟙 A.left, (translate A x).left, (translate A y).left]
        ![(n : ℤ) - 1, 1, -(n : ℤ)] := by
  let q := GrpTangent.mulN A n
  have hq := MulFinite.finite_flat_surjective_mulN_of_rigidified_symmetric hA hL hAmp hrig hsym n hn
  letI : IsFinite q.left := hq.1
  letI : Surjective q.left := hq.2.2.1
  obtain ⟨y, hy⟩ := GrpTangent.exists_lift_geometric_point
    (x := 𝟙 (Spec (.of K))) q x
  have he : y ^ n = x := (GrpTangent.comp_mulN y n).symm.trans hy
  refine ⟨y, he, ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [← he]
  let f : Fin 3 → (A.left ⟶ A.left) :=
    ![𝟙 A.left, (translate A (y ^ (m + 1))).left, (translate A y).left]
  let d₁ : Fin 3 → ℤ := ![((m + 1 : ℕ) : ℤ) - 1, 1, -((m + 1 : ℕ) : ℤ)]
  let d₂ : Fin 3 → ℤ := ![(m : ℤ), 1, -((m : ℤ) + 1)]
  change HasGen (L := L) f d₁
  have e₀ : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := Nat.cast_succ m
  have e (i : Fin 3) : d₁ i = d₂ i := by
    fin_cases i
    · exact (congrArg (· - 1) e₀).trans (add_sub_cancel_right _ _)
    · rfl
    · exact congrArg Neg.neg e₀
  exact (congrArg (HasGen (L := L) f) (funext e)).mpr (gen_power_translate hA hL hAmp y m)

end GlobalTheory.TwistTranslate
