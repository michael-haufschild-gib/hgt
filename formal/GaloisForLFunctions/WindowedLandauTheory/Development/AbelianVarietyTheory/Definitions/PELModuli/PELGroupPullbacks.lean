import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.GenericPELModuli
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.GroupTangentCriteria

/-! Base change of an abelian scheme, its order action and its fibre square. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S)

theorem pullback_map_left_fst' {A B : Over S} (g : A ⟶ B) :
    ((Over.pullback f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left := by
  simp
  exact pullback.lift_fst _ _ _

/-- Projection from the base-changed scheme. -/
abbrev pφ : ((Over.pullback f).obj G).left ⟶ G.left := pullback.fst G.hom f

/-- Projection from the base-changed fibre square. -/
def pφ₂ : (G2 ((Over.pullback f).obj G)).left ⟶ (G2 G).left :=
  (Functor.LaxMonoidal.μ (Over.pullback f) G G).left ≫ pullback.fst (G ⊗ G).hom f

theorem pφ₂_fst : pφ₂ f G ≫ (fst G G).left =
    (fst ((Over.pullback f).obj G) ((Over.pullback f).obj G)).left ≫ pφ f G := by
  let i := Functor.LaxMonoidal.μ (Over.pullback f) G G
  let a := (Over.pullback f).map (fst G G)
  calc
    _ = i.left ≫ (pullback.fst (G ⊗ G).hom f ≫ (fst G G).left) := Category.assoc _ _ _
    _ = i.left ≫ (a.left ≫ pullback.fst G.hom f) :=
      congrArg (i.left ≫ ·) (pullback_map_left_fst' f (fst G G)).symm
    _ = (i ≫ a).left ≫ pullback.fst G.hom f := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun h => h.left ≫ pullback.fst G.hom f)
      (Functor.Monoidal.μ_fst (Over.pullback f) G G)

theorem pφ₂_snd : pφ₂ f G ≫ (snd G G).left =
    (snd ((Over.pullback f).obj G) ((Over.pullback f).obj G)).left ≫ pφ f G := by
  let i := Functor.LaxMonoidal.μ (Over.pullback f) G G
  let a := (Over.pullback f).map (snd G G)
  calc
    _ = i.left ≫ (pullback.fst (G ⊗ G).hom f ≫ (snd G G).left) := Category.assoc _ _ _
    _ = i.left ≫ (a.left ≫ pullback.fst G.hom f) :=
      congrArg (i.left ≫ ·) (pullback_map_left_fst' f (snd G G)).symm
    _ = (i ≫ a).left ≫ pullback.fst G.hom f := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun h => h.left ≫ pullback.fst G.hom f)
      (Functor.Monoidal.μ_snd (Over.pullback f) G G)

theorem isSquare : IsSquare (pφ f G) (pφ₂ f G) := ⟨pφ₂_fst f G, pφ₂_snd f G⟩

theorem fibreSquare_hom_ext {R : Scheme.{0}} {a b : R ⟶ (G2 G).left}
    (h₁ : a ≫ (fst G G).left = b ≫ (fst G G).left)
    (h₂ : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b :=
  pullback.hom_ext h₁ h₂

variable [GrpObj G]

theorem one_left_pφ :
    (1 : (Over.pullback f).obj G ⟶ (Over.pullback f).obj G).left ≫ pφ f G =
      pφ f G ≫ (1 : G ⟶ G).left := by
  let u := η[(Over.pullback f).obj G].left
  let v := η[G].left
  have e : u ≫ pφ f G = f ≫ v := GlobalTheory.GrpTangent.one_pullback_left_fst f G
  calc
    _ = pullback.snd G.hom f ≫ (u ≫ pφ f G) := Category.assoc _ _ _
    _ = pullback.snd G.hom f ≫ (f ≫ v) := congrArg (pullback.snd G.hom f ≫ ·) e
    _ = (pullback.snd G.hom f ≫ f) ≫ v := (Category.assoc _ _ _).symm
    _ = (pφ f G ≫ G.hom) ≫ v := congrArg (· ≫ v) pullback.condition.symm
    _ = _ := Category.assoc _ _ _

theorem mul_left_pφ :
    (MonObj.mul : (Over.pullback f).obj G ⊗ (Over.pullback f).obj G ⟶ (Over.pullback f).obj G).left ≫ pφ f G =
      pφ₂ f G ≫ (MonObj.mul : G ⊗ G ⟶ G).left := by
  rw [Functor.obj.μ_def, Over.comp_left, Category.assoc, show pφ f G = pullback.fst G.hom f from rfl,
    pullback_map_left_fst', pφ₂, Category.assoc]
  rfl

/-- The cartesian projection preserves the group law on points. -/
theorem isGrpPullback : IsGrpPullback ((Over.pullback f).obj G) G f (pφ f G) := by
  refine ⟨IsPullback.of_hasPullback G.hom f, ?_⟩
  intro T x y x₀ y₀ hx hy
  let G' := (Over.pullback f).obj G
  let l : T.left ⟶ (G2 G).left := (lift x₀ y₀).left
  let l' : T.left ⟶ (G2 G').left := (lift x y).left
  have hl : l = l' ≫ pφ₂ f G := by
    apply fibreSquare_hom_ext (G := G)
    · have e₁ : l ≫ (fst G G).left = x₀.left :=
        congrArg Over.Hom.left (lift_fst x₀ y₀)
      have e₂ : l' ≫ (fst G' G').left = x.left :=
        congrArg Over.Hom.left (lift_fst x y)
      calc
        _ = _ := e₁
        _ = _ := hx
        _ = (l' ≫ (fst G' G').left) ≫ pφ f G := congrArg (· ≫ pφ f G) e₂.symm
        _ = l' ≫ ((fst G' G').left ≫ pφ f G) := Category.assoc _ _ _
        _ = l' ≫ (pφ₂ f G ≫ (fst G G).left) := congrArg (l' ≫ ·) (pφ₂_fst f G).symm
        _ = _ := (Category.assoc _ _ _).symm
    · have e₁ : l ≫ (snd G G).left = y₀.left :=
        congrArg Over.Hom.left (lift_snd x₀ y₀)
      have e₂ : l' ≫ (snd G' G').left = y.left :=
        congrArg Over.Hom.left (lift_snd x y)
      calc
        _ = _ := e₁
        _ = _ := hy
        _ = (l' ≫ (snd G' G').left) ≫ pφ f G := congrArg (· ≫ pφ f G) e₂.symm
        _ = l' ≫ ((snd G' G').left ≫ pφ f G) := Category.assoc _ _ _
        _ = l' ≫ (pφ₂ f G ≫ (snd G G).left) := congrArg (l' ≫ ·) (pφ₂_snd f G).symm
        _ = _ := (Category.assoc _ _ _).symm
  calc
    _ = l ≫ (μ[G]).left := rfl
    _ = (l' ≫ pφ₂ f G) ≫ (μ[G]).left := congrArg (· ≫ (μ[G]).left) hl
    _ = l' ≫ (pφ₂ f G ≫ (μ[G]).left) := Category.assoc _ _ _
    _ = l' ≫ ((μ[G']).left ≫ pφ f G) := congrArg (l' ≫ ·) (mul_left_pφ f G).symm
    _ = _ := (Category.assoc _ _ _).symm

end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

namespace ReciprocityTheory.ChartRestriction.G.Semi

/-- The defining properties of an abelian scheme are preserved by base change. -/
theorem IsAbelianScheme.pullback {S S' : Scheme.{0}} {A : Over S} [GrpObj A]
    (h : IsAbelianScheme A) (f : S' ⟶ S) : IsAbelianScheme ((Over.pullback f).obj A) := by
  letI := h.comm
  have hp := IsPullback.of_hasPullback A.hom f
  exact ⟨inferInstance, MorphismProperty.of_isPullback hp h.smooth,
    MorphismProperty.of_isPullback hp h.proper, MorphismProperty.of_isPullback hp h.geomConnected⟩

end ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.UPel.HT

variable {S S' : Scheme.{0}} {A : Over S} [GrpObj A]

/-- The base change of the order action uses the pullback functor on group morphisms. -/
def OActN.pullback {O : Type} [Ring O] (act : OActN O A) (f : S' ⟶ S) :
    OActN O ((Over.pullback f).obj A) where
  act b := (Over.pullback f).map (act.act b)
  hom b := by
    letI := act.hom b
    infer_instance
  one := by rw [act.one]; exact (Over.pullback f).map_id A
  mul b c := by rw [act.mul, Functor.map_comp]
  add b c := by
    rw [act.add]
    exact (Over.pullback f).map_mul (act.act b) (act.act c)

end GlobalTheory.UPel.HT

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

/-- The identity map is a cartesian map of group schemes. -/
theorem IsGrpPullback.refl {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    IsGrpPullback A A (𝟙 S) (𝟙 A.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, ?_⟩
  intro T x y x₀ y₀ hx hy
  let e : Over.mk (T.hom ≫ 𝟙 S) ⟶ T :=
    Over.homMk (𝟙 T.left) ((Category.id_comp T.hom).trans (Category.comp_id T.hom).symm)
  have h₁ : x₀ = e ≫ x := Over.OverMorphism.ext
    (hx.trans ((Category.comp_id x.left).trans (Category.id_comp x.left).symm))
  have h₂ : y₀ = e ≫ y := Over.OverMorphism.ext
    (hy.trans ((Category.comp_id y.left).trans (Category.id_comp y.left).symm))
  rw [h₁, h₂, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Cartesian group maps compose, with multiplication checked on points. -/
theorem IsGrpPullback.comp {S S' T : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {P : Over T} [GrpObj P] {f : S' ⟶ S} {t : T ⟶ S'} {φ : G'.left ⟶ G.left} {ψ : P.left ⟶ G'.left}
    (h₁ : IsGrpPullback P G' t ψ) (h₂ : IsGrpPullback G' G f φ) :
    IsGrpPullback P G (t ≫ f) (ψ ≫ φ) := by
  refine ⟨h₁.1.paste_horiz h₂.1, fun T₀ x y x₀ y₀ hx hy => ?_⟩
  have wx : ∀ z : T₀ ⟶ P, (z.left ≫ ψ) ≫ G'.hom = (Over.mk (T₀.hom ≫ t)).hom := fun z => by
    rw [Category.assoc, h₁.1.w, ← Category.assoc, Over.w z]; rfl
  let x' : Over.mk (T₀.hom ≫ t) ⟶ G' := Over.homMk (x.left ≫ ψ) (wx x)
  let y' : Over.mk (T₀.hom ≫ t) ⟶ G' := Over.homMk (y.left ≫ ψ) (wx y)
  have e₁ : (x' * y').left = (x * y).left ≫ ψ := h₁.2 T₀ x y x' y' rfl rfl
  let e : Over.mk ((Over.mk (T₀.hom ≫ t)).hom ≫ f) ⟶ Over.mk (T₀.hom ≫ t ≫ f) :=
    Over.homMk (𝟙 T₀.left) ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  have ex : (e ≫ x₀).left = x'.left ≫ φ := (Category.id_comp x₀.left).trans hx
  have ey : (e ≫ y₀).left = y'.left ≫ φ := (Category.id_comp y₀.left).trans hy
  have e₂ : (((e ≫ x₀) * (e ≫ y₀)).left : T₀.left ⟶ G.left) = (x' * y').left ≫ φ :=
    h₂.2 _ x' y' (e ≫ x₀) (e ≫ y₀) ex ey
  have e₃ : ((x₀ * y₀).left : T₀.left ⟶ G.left) = ((e ≫ x₀) * (e ≫ y₀)).left :=
    (Category.id_comp (show T₀.left ⟶ G.left from (x₀ * y₀).left)).symm.trans
      (congrArg (fun m => (m.left : T₀.left ⟶ G.left)) (MonObj.comp_mul e x₀ y₀))
  exact e₃.trans (e₂.trans ((congrArg (· ≫ φ) e₁).trans (Category.assoc _ _ _)))

/-- A pair of maps on fibre squares composes compatibly with both projections. -/
theorem IsSquare.comp {S S' S'' : Scheme.{0}} {A : Over S} {A' : Over S'} {A'' : Over S''}
    {f : A''.left ⟶ A'.left} {g : A'.left ⟶ A.left}
    {F : (A'' ⊗ A'').left ⟶ (A' ⊗ A').left} {G : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    (hF : IsSquare f F) (hG : IsSquare g G) : IsSquare (f ≫ g) (F ≫ G) := by
  constructor
  · rw [Category.assoc, hG.1, ← Category.assoc, hF.1, Category.assoc]
  · rw [Category.assoc, hG.2, ← Category.assoc, hF.2, Category.assoc]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LiePull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {f : S' ⟶ S} {φ : A'.left ⟶ A.left}

/-- A group pullback identifies points over the smaller base with points
of the original group over the composed base map. -/
def pushHom (h : IsGrpPullback A' A f φ) (T : Over S') :
    (T ⟶ A') →* (Over.mk (T.hom ≫ f) ⟶ A) := by
  let p (a : T ⟶ A') : Over.mk (T.hom ≫ f) ⟶ A :=
    Over.homMk (a.left ≫ φ) ((Category.assoc _ _ _).trans
      ((congrArg (a.left ≫ ·) h.1.w).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) (Over.w a)))))
  have hmul (a b : T ⟶ A') : p (a * b) = p a * p b :=
    Over.OverMorphism.ext ((h.2 T a b (p a) (p b) rfl rfl).symm)
  exact { toFun := p
          map_one' := mul_left_cancel ((hmul 1 1).symm.trans (by rw [_root_.one_mul, _root_.mul_one]))
          map_mul' := hmul }

/-- The point map of a group pullback is bijective by the pullback universal property. -/
theorem exists_pushEquiv (h : IsGrpPullback A' A f φ) (T : Over S') (g : T.left ⟶ S)
    (hg : g = T.hom ≫ f) : ∃ e : (T ⟶ A') ≃* (Over.mk g ⟶ A), ∀ a, (e a).left = a.left ≫ φ := by
  subst g
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨?_, ?_⟩, fun a => rfl⟩
  · intro a b e
    exact Over.OverMorphism.ext (h.1.hom_ext (congrArg Over.Hom.left e)
      ((Over.w a).trans (Over.w b).symm))
  · intro b
    exact ⟨Over.homMk (h.1.lift b.left T.hom (Over.w b)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

end GlobalTheory.LiePull
