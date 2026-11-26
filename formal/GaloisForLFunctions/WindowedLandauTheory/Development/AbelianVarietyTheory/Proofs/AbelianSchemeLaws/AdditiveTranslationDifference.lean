import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeSquare

/-! The translation difference of a line bundle is additive. The cube identity
leaves two factors from the field, which have constant trivializations. -/

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TranslateAdditive

attribute [local instance] Over.cartesianMonoidalCategory

variable {K : Type} [Field K] {A T : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}

private theorem constant_inverse_difference (hL : L.IsLB)
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    ∃ s : (LB.LinComb L (K := Fin 2) ![(toUnit T ≫ x).left, (1 : T ⟶ A).left] ![-1, 1]).Gen,
      s.IsGen := by
  let S := Spec (.of K)
  let E := 𝟙_ (Over S)
  letI : Subsingleton E.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let p : E.left := IsLocalRing.closedPoint K
  let a : T ⟶ A := toUnit T ≫ x
  let g : Fin 2 → (E.left ⟶ A.left) := ![x.left, (1 : E ⟶ A).left]
  let f : Fin 2 → (T.left ⟶ A.left) := ![a.left, (1 : T ⟶ A).left]
  let e : Fin 2 → ℤ := ![-1, 1]
  choose i hi using fun k => exists_chart hL (g k p)
  have hc (k : Fin 2) : f k = (toUnit T).left ≫ g k := by
    fin_cases k
    · rfl
    · exact congrArg Over.Hom.left (MonObj.comp_one (toUnit T)).symm
  exact AbLaw.Cube.exists_gen_of_chart hL f e i (fun y =>
    Set.mem_iInter.2 fun k => by
      have h : f k y = g k p :=
        (congrArg (fun m : T.left ⟶ A.left => m y) (hc k)).trans
          (congrArg (g k) (Subsingleton.elim ((toUnit T).left y) p))
      exact (congrArg (· ∈ L.U (i k)) h).mpr (hi k))

/-- The cube identity with one constant coordinate trivializes the additive
relation between the translation differences at `b`, `c`, and `b * c`. -/
theorem exists_gen_additive_of_constant
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L)
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) (b c : T ⟶ A) :
    let a := toUnit T ≫ x
    ∃ s : (LB.LinComb L (K := Fin 6)
      ![(a * b * c).left, (b * c).left, (a * b).left, b.left, (a * c).left, c.left]
      ![1, -1, -1, 1, -1, 1]).Gen, s.IsGen := by
  letI := hA.comm
  let a := toUnit T ≫ x
  let f : Fin 2 → (T.left ⟶ A.left) := ![a.left, (1 : T ⟶ A).left]
  let e : Fin 2 → ℤ := ![-1, 1]
  obtain ⟨v, hv⟩ := constant_inverse_difference (T := T) hL x
  obtain ⟨u, hu⟩ := AbLaw.Cube.cube_gen_of_relAmple hA hL hAmp hL
  let r := (lift a (lift b c)).left
  obtain ⟨w, hw, -⟩ := exists_gen_of_formEq hL
    (g := ![(a * b * c).left, (b * c).left, (a * b).left, b.left, (a * c).left, c.left])
    (d := ![1, -1, -1, 1, -1, 1])
    (fun U _ k => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      have hp := AbLaw.Cube.prod_cube a b c k
      change (∏ j, k (r ≫ AbLaw.Cube.cubeMorphism A j) ^ AbLaw.Cube.cubeExponent j) = _ at hp
      rw [hp]
      apply Additive.ofMul.injective
      simp only [f, e, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, zpow_one, zpow_neg_one, _root_.mul_one, ofMul_inv, ofMul_mul]
      abel) _ (mulGen_isGen hv (hu.pullGen (AbLaw.Cube.cubeMorphism A) AbLaw.Cube.cubeExponent r))
  exact ⟨w, hw⟩

/-- The translation difference tensored with its pullback along inversion is trivial. -/
theorem exists_gen_inverse_product (hA : IsAbelianScheme A) (hL : L.IsLB)
    (hAmp : RelAmple A L) (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) :
    let ν : A ⟶ A := GrpObj.inv
    let τ : A ⟶ A := (toUnit A ≫ x) * 𝟙 A
    ∃ s : (LB.LinComb L (K := Fin 4)
      ![τ.left, 𝟙 A.left, ν.left ≫ τ.left, ν.left] ![1, -1, 1, -1]).Gen, s.IsGen := by
  let a : A ⟶ A := toUnit A ≫ x
  let ν : A ⟶ A := GrpObj.inv
  let τ : A ⟶ A := a * 𝟙 A
  let f : Fin 6 → (A.left ⟶ A.left) :=
    ![(a * 𝟙 A * ν).left, ((𝟙 A : A ⟶ A) * ν).left, τ.left, 𝟙 A.left, (a * ν).left, ν.left]
  let g : Fin 2 → (A.left ⟶ A.left) := ![a.left, (1 : A ⟶ A).left]
  let d : Fin 6 → ℤ := ![1, -1, -1, 1, -1, 1]
  let e : Fin 2 → ℤ := ![-1, 1]
  obtain ⟨v, hv⟩ := exists_gen_additive_of_constant hA hL hAmp x (𝟙 A) ν
  obtain ⟨w, hw⟩ := constant_inverse_difference (T := A) hL x
  have hν : (𝟙 A : A ⟶ A) * ν = 1 := by
    change (𝟙 A : A ⟶ A) * GrpObj.inv = 1
    rw [GrpObj.inv_eq_inv, mul_inv_cancel]
  have ha : a * 𝟙 A * ν = a := (_root_.mul_assoc _ _ _).trans
    ((congrArg (a * ·) hν).trans (_root_.mul_one _))
  have hτ : ν ≫ τ = a * ν := by
    change ν ≫ ((toUnit A ≫ x) * 𝟙 A) = _
    rw [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id]
  let u := LB.mulGen L f d g e v w
  have hu := mulGen_isGen hv hw
  obtain ⟨s, hs, -⟩ := exists_gen_of_formEq hL (g := ![τ.left, 𝟙 A.left, ν.left ≫ τ.left, ν.left])
    (d := ![1, -1, 1, -1]) (fun U _ k => by
      rw [Fintype.prod_sum_type]
      apply Additive.ofMul.injective
      simp only [f, g, d, e, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ, ha, hν, hτ, zpow_one, zpow_neg_one, neg_neg,
        _root_.mul_one, ofMul_inv, ofMul_mul]
      abel) (LB.invGen L (Sum.elim f g) (Sum.elim d e) u) (invGen_isGen hu)
  exact ⟨s, hs⟩

end GlobalTheory.TranslateAdditive
