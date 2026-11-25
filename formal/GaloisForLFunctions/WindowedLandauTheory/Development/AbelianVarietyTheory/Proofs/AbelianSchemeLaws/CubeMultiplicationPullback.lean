import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeProductFormula
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeAssembly
import Mathlib.Tactic.Module

/-! The cube identity gives the quadratic pullback law for a rigidified symmetric line bundle. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators CategoryTheory.Obj

namespace GlobalTheory.AbLaw.Cube

attribute [local instance] Over.cartesianMonoidalCategory

private abbrev HasGen {X Y : Scheme.{0}} (L : LB X) {I : Type} [Fintype I]
    (f : I → (Y ⟶ X)) (d : I → ℤ) : Prop :=
  ∃ s : (LB.LinComb L f d).Gen, s.IsGen

section

variable {X Y Z : Scheme.{0}} {L : LB X} {I J : Type} [Fintype I] [Fintype J]
  {f : I → (Y ⟶ X)} {d : I → ℤ} {g : J → (Y ⟶ X)} {e : J → ℤ}

private theorem HasGen.mul (hf : HasGen L f d) (hg : HasGen L g e) :
    HasGen L (Sum.elim f g) (Sum.elim d e) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  exact ⟨_, mulGen_isGen hs ht⟩

private theorem HasGen.inv (h : HasGen L f d) : HasGen L f (fun i => -d i) := by
  obtain ⟨s, hs⟩ := h
  exact ⟨_, invGen_isGen hs⟩

private theorem HasGen.pull (h : HasGen L f d) (r : Z ⟶ Y) :
    HasGen L (fun i => r ≫ f i) d := by
  obtain ⟨s, hs⟩ := h
  exact ⟨_, hs.pullGen f d r⟩

private theorem HasGen.of_formEq (h : HasGen L f d) (hL : L.IsLB) (eq : FormEq f d g e) :
    HasGen L g e := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨t, ht, -⟩ := exists_gen_of_formEq hL eq s hs
  exact ⟨t, ht⟩

end

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

/-- A cube generator, a generator at the identity, and symmetry give
the quadratic pullback law on every point of the group. -/
theorem gen_quadratic_pullback (hL : L.IsLB) (hcube : ∃ s : (cubeBundle A L).Gen, s.IsGen)
    (x : T ⟶ A)
    (hone : ∃ s : (LB.LinComb L (K := Fin 1) ![(1 : T ⟶ A).left] ![1]).Gen, s.IsGen)
    (hsym : ∃ s : (LB.LinComb L (K := Fin 2) ![x.left, (x⁻¹).left] ![1, -1]).Gen, s.IsGen)
    (n : ℕ) :
    ∃ s : (LB.LinComb L (K := Fin 2) ![x.left, (x ^ n).left] ![(n : ℤ) ^ 2, -1]).Gen, s.IsGen := by
  have hC : HasGen L (cubeMorphism A) cubeExponent := hcube
  have h₁ : HasGen L ![(1 : T ⟶ A).left] ![1] := hone
  have hS : HasGen L ![x.left, (x⁻¹).left] ![1, -1] := hsym
  change HasGen L ![x.left, (x ^ n).left] ![(n : ℤ) ^ 2, -1]
  induction n using Nat.twoStepInduction with
  | zero =>
    exact h₁.inv.of_formEq hL (fun U _ k => by simp [Fin.prod_univ_succ])
  | one =>
    exact (h₁.mul h₁.inv).of_formEq hL (fun U _ k => by
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type])
  | more n ih₀ ih₁ =>
    -- The triple (x^(n+1), x, x⁻¹) gives the second difference of the exponent.
    let r := (lift (x ^ (n + 1)) (lift x x⁻¹)).left
    refine ((hC.pull r).mul ((ih₁.mul ih₁).mul (ih₀.inv.mul ((h₁.mul h₁).mul hS)))).of_formEq hL ?_
    intro U _ k
    have hprod := prod_cube (x ^ (n + 1)) x x⁻¹ k
    change (∏ I, k (r ≫ cubeMorphism A I) ^ cubeExponent I) = _ at hprod
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hprod]
    have e₁ : x ^ (n + 1) * x * x⁻¹ = x ^ (n + 1) := mul_inv_cancel_right _ _
    have e₂ : x ^ (n + 1) * x = x ^ (n + 2) := (pow_succ x (n + 1)).symm
    have e₃ : x ^ (n + 1) * x⁻¹ = x ^ n := by rw [pow_succ, mul_inv_cancel_right]
    rw [e₁, e₂, e₃, mul_inv_cancel]
    apply Additive.ofMul.injective
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
    push_cast
    module

private theorem gen_symmetry_of_local (hA : IsAbelianScheme A) (hL : L.IsLB)
    (h : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ t : (LB.LinComb L (K := Fin 2)
      ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]).Gen, t.IsGen) :
    HasGen L ![(𝟙 A.left), ((𝟙 A : A ⟶ A)⁻¹).left] ![1, -1] := by
  letI := hA.smooth
  letI := hA.proper
  letI := hA.geomConnected
  let f : Fin 2 → (A.left ⟶ A.left) := ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left]
  have he : η[A].left ≫ (GrpObj.inv : A ⟶ A).left = η[A].left :=
    congrArg Over.Hom.left (GrpObj.one_inv (G := A))
  have hf : HasGen L f ![1, -1] := by
    apply exists_gen_of_local_triviality hL f ![1, -1] A.hom η[A].left (Over.w (η[A]))
    · intro Z b U _ k
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, f, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Category.assoc, Category.comp_id,
        zpow_one, zpow_neg_one, _root_.mul_one]
      exact (congrArg (fun q : Z ⟶ A.left => k q * (k (b ≫ η[A].left))⁻¹)
        (congrArg (b ≫ ·) he)).trans (mul_inv_cancel _)
    · intro s
      obtain ⟨U, hs, t, ht⟩ := h s
      refine ⟨U, hs, ?_⟩
      have e : (fun i => (A.hom ⁻¹ᵁ U).ι ≫ f i) =
          ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] := by
        funext i
        fin_cases i <;> simp [f]
      rw [e]
      exact ⟨t, ht⟩
  apply hf.inv.of_formEq hL
  intro U _ k
  rw [← GrpObj.inv_eq_inv]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, f, Matrix.cons_val_zero,
    Matrix.cons_val_succ, neg_neg, zpow_one, zpow_neg_one, _root_.mul_one]
  exact _root_.mul_comm _ _

omit [IsCommMonObj A] in
/-- Multiplication by `n` pulls a rigidified symmetric relatively ample line bundle back
to its `n²`-th power. -/
theorem gen_mul_pullback_of_relAmple (hA : IsAbelianScheme A) (hL : L.IsLB)
    (hAmp : ReciprocityTheory.ChartRestriction.G.Out.RelAmple A L)
    (hrig : ∃ t : (L.pull η[A].left).Gen, t.IsGen)
    (hsym : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ t : (LB.LinComb L (K := Fin 2)
      ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]).Gen, t.IsGen)
    (n : ℕ) :
    ∃ t : (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ((𝟙 A : A ⟶ A) ^ n).left]
      ![(n : ℤ) ^ 2, -1]).Gen, t.IsGen := by
  letI := hA.comm
  have hre : HasGen L (fun _ : PUnit => η[A].left) (fun _ => 1) := hrig
  refine gen_quadratic_pullback hL (cube_gen_of_relAmple hA hL hAmp hL) (𝟙 A) ?_
    (gen_symmetry_of_local hA hL hsym) n
  apply (hre.pull (toUnit A).left).of_formEq hL
  intro U _ k
  simp only [Finset.univ_unique, Finset.prod_singleton, zpow_one]
  change k ((toUnit A).left ≫ η[A].left) = k (1 : A ⟶ A).left ^ (1 : ℤ)
  rw [zpow_one]
  rfl

end GlobalTheory.AbLaw.Cube
