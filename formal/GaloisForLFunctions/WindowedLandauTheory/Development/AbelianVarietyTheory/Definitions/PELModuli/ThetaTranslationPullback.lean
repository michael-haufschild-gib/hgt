import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELGroupPullbacks

/-! Base change identifies the fibre products on which theta translations act. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.WeilPull

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)

/-- Map of test-scheme products induced by the cartesian group map. -/
def psiO : Over.mk ((T ⊗ A).hom ≫ f) ⟶ T₀ ⊗ G :=
  lift (Over.homMk ((fst T A).left ≫ τ) (by
      show ((fst T A).left ≫ τ) ≫ T₀.hom = (T ⊗ A).hom ≫ f
      rw [Category.assoc, hτ, ← Category.assoc, Over.w (fst T A)]))
    (GlobalTheory.LiePull.pushHom hp (T ⊗ A) (snd T A))

theorem psi_fst : (psiO hp τ hτ).left ≫ (fst T₀ G).left = (fst T A).left ≫ τ := by
  rw [← Over.comp_left, psiO, lift_fst]; rfl

theorem psi_snd : (psiO hp τ hτ).left ≫ (snd T₀ G).left = (snd T A).left ≫ φ := by
  rw [← Over.comp_left, psiO, lift_snd]; rfl

theorem psi_tr (x : T ⟶ A) (x₀ : T₀ ⟶ G) (hx : τ ≫ x₀.left = x.left ≫ φ) :
    (psiO hp τ hτ).left ≫ (translPt G x₀).left = (translPt A x).left ≫ φ := by
  have e₁ : translPt G x₀ = (fst T₀ G ≫ x₀) * snd T₀ G := rfl
  have e₂ : translPt A x = (fst T A ≫ x) * snd T A := rfl
  rw [← Over.comp_left, e₁, MonObj.comp_mul, e₂]
  refine hp.2 _ _ _ _ _ ?_ ?_
  · rw [Over.comp_left, Over.comp_left, ← Category.assoc, psi_fst]
    let a : (T ⊗ A).left ⟶ T.left := (fst T A).left
    exact (Category.assoc a τ x₀.left).trans
      ((congrArg (a ≫ ·) hx).trans (Category.assoc a x.left φ).symm)
  · rw [Over.comp_left, psi_snd]

theorem psi_transl (x : T ⟶ A) (x₀ : T₀ ⟶ G) (hx : τ ≫ x₀.left = x.left ≫ φ) :
    (translT A x).left ≫ (psiO hp τ hτ).left = (psiO hp τ hτ).left ≫ (translT G x₀).left := by
  let m : Over.mk ((T ⊗ A).hom ≫ f) ⟶ Over.mk ((T ⊗ A).hom ≫ f) :=
    Over.homMk (translT A x).left (by
      show (translT A x).left ≫ (T ⊗ A).hom ≫ f = (T ⊗ A).hom ≫ f
      rw [← Category.assoc, Over.w (translT A x)])
  have key : m ≫ psiO hp τ hτ = psiO hp τ hτ ≫ translT G x₀ := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      have e1 : (m ≫ psiO hp τ hτ ≫ fst T₀ G).left = (fst T A).left ≫ τ := by
        rw [psiO, lift_fst]
        show (translT A x).left ≫ (fst T A).left ≫ τ = _
        rw [← Category.assoc, ← Over.comp_left, translT, lift_fst]
      have e2 : (psiO hp τ hτ ≫ translT G x₀ ≫ fst T₀ G).left = (fst T A).left ≫ τ := by
        rw [translT, lift_fst, Over.comp_left, psi_fst]
      simpa only [Category.assoc] using e1.trans e2.symm
    · apply Over.OverMorphism.ext
      have e1 : (m ≫ psiO hp τ hτ ≫ snd T₀ G).left = (translPt A x).left ≫ φ := by
        rw [psiO, lift_snd]
        show (translT A x).left ≫ (snd T A).left ≫ φ = _
        rw [← Category.assoc, ← Over.comp_left, translT, lift_snd]
      have e2 : (psiO hp τ hτ ≫ translT G x₀ ≫ snd T₀ G).left = (translPt A x).left ≫ φ := by
        rw [translT, lift_snd, Over.comp_left, psi_tr hp τ hτ x x₀ hx]
      simpa only [Category.assoc] using e1.trans e2.symm
  exact congrArg CommaMorphism.left key

/-- An isomorphism between the test schemes induces an isomorphism of the products. -/
theorem exists_psi_inv [IsIso τ] : ∃ χ : (T₀ ⊗ G).left ⟶ (T ⊗ A).left,
    (psiO hp τ hτ).left ≫ χ = 𝟙 (T ⊗ A).left ∧ χ ≫ (psiO hp τ hτ).left = 𝟙 _ := by
  have w₁ : (snd T₀ G).left ≫ G.hom = ((fst T₀ G).left ≫ inv τ ≫ T.hom) ≫ f := by
    rw [Over.w, Category.assoc, Category.assoc, ← hτ, IsIso.inv_hom_id_assoc, Over.w]
  let a : (T₀ ⊗ G).left ⟶ A.left := hp.1.lift _ _ w₁
  have a₁ : a ≫ φ = (snd T₀ G).left := hp.1.lift_fst _ _ _
  have a₂ : a ≫ A.hom = (fst T₀ G).left ≫ inv τ ≫ T.hom := hp.1.lift_snd _ _ _
  let χ : (T₀ ⊗ G).left ⟶ (T ⊗ A).left :=
    pullback.lift ((fst T₀ G).left ≫ inv τ) a (by rw [a₂, Category.assoc])
  have c₁ : χ ≫ (fst T A).left = (fst T₀ G).left ≫ inv τ := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd T A).left = a := pullback.lift_snd _ _ _
  let ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left := (psiO hp τ hτ).left
  have p₁ : ψ ≫ (fst T₀ G).left = (fst T A).left ≫ τ := psi_fst hp τ hτ
  have p₂ : ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ := psi_snd hp τ hτ
  refine ⟨χ, ?_, ?_⟩
  · change ψ ≫ χ = 𝟙 _
    refine pullback.hom_ext (f := T.hom) (g := A.hom) ?_ ?_
    · show (ψ ≫ χ) ≫ (fst T A).left = 𝟙 _ ≫ (fst T A).left
      rw [Category.assoc, c₁, ← Category.assoc, p₁, Category.assoc, IsIso.hom_inv_id, Category.id_comp,
        Category.comp_id]
    · show (ψ ≫ χ) ≫ (snd T A).left = 𝟙 _ ≫ (snd T A).left
      rw [Category.assoc, c₂, Category.id_comp]
      refine hp.1.hom_ext ?_ ?_
      · rw [Category.assoc, a₁, p₂]
      · rw [Category.assoc, a₂, ← Category.assoc, p₁, Category.assoc, IsIso.hom_inv_id_assoc, Over.w, Over.w]
  · change χ ≫ ψ = 𝟙 _
    refine pullback.hom_ext (f := T₀.hom) (g := G.hom) ?_ ?_
    · show (χ ≫ ψ) ≫ (fst T₀ G).left = 𝟙 _ ≫ (fst T₀ G).left
      rw [Category.assoc, p₁, ← Category.assoc, c₁, Category.assoc, IsIso.inv_hom_id, Category.id_comp,
        Category.comp_id]
    · show (χ ≫ ψ) ≫ (snd T₀ G).left = 𝟙 _ ≫ (snd T₀ G).left
      rw [Category.assoc, p₂, ← Category.assoc, c₂, a₁, Category.id_comp]

/-- Commuting points give commuting translations on the test-scheme product. -/
theorem transl_commute {x y : T ⟶ A} (h : x * y = y * x) :
    (translT A x).left ≫ (translPt A y).left = (translT A y).left ≫ (translPt A x).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  show translT A x ≫ ((fst T A ≫ y) * snd T A) = translT A y ≫ ((fst T A ≫ x) * snd T A)
  rw [MonObj.comp_mul, MonObj.comp_mul, translT, translT, lift_snd, lift_snd, ← Category.assoc, ← Category.assoc,
    lift_fst, lift_fst]
  show (fst T A ≫ y) * ((fst T A ≫ x) * snd T A) = (fst T A ≫ x) * ((fst T A ≫ y) * snd T A)
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← MonObj.comp_mul, ← MonObj.comp_mul, h]

end GlobalTheory.WeilPull
