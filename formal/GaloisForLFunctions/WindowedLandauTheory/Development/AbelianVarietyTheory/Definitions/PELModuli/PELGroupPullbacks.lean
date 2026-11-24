import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.GenericPELModuli
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.GroupTangentCriteria

/-! Base change of an abelian scheme, its order action and its fibre square. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem pullback_map_left_fst' {A B : Over S} (g : A ⟶ B) :
    ((Over.pullback f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left := by
  simp
  exact pullback.lift_fst _ _ _

/-- Projection from the base-changed scheme. -/
abbrev pφ : ((Over.pullback f).obj G).left ⟶ G.left := pullback.fst G.hom f

/-- Projection from the base-changed fibre square. -/
def pφ₂ : (G2 ((Over.pullback f).obj G)).left ⟶ (G2 G).left :=
  (Functor.LaxMonoidal.μ (Over.pullback f) G G).left ≫ pullback.fst (G ⊗ G).hom f

theorem pφ₂_fst : pφ₂ f G ≫ (fst G G).left = (fst ((Over.pullback f).obj G) ((Over.pullback f).obj G)).left ≫ pφ f G := by
  rw [show pφ f G = pullback.fst G.hom f from rfl, pφ₂, Category.assoc, ← pullback_map_left_fst',
    ← Category.assoc, ← Over.comp_left, Functor.Monoidal.μ_fst]

theorem pφ₂_snd : pφ₂ f G ≫ (snd G G).left = (snd ((Over.pullback f).obj G) ((Over.pullback f).obj G)).left ≫ pφ f G := by
  rw [show pφ f G = pullback.fst G.hom f from rfl, pφ₂, Category.assoc, ← pullback_map_left_fst',
    ← Category.assoc, ← Over.comp_left, Functor.Monoidal.μ_snd]

theorem isSquare : IsSquare (pφ f G) (pφ₂ f G) := And.intro (pφ₂_fst f G) (pφ₂_snd f G)

theorem fibreSquare_hom_ext {R : Scheme.{0}} (a b : R ⟶ (G2 G).left)
    (h1 : a ≫ (fst G G).left = b ≫ (fst G G).left) (h2 : a ≫ (snd G G).left = b ≫ (snd G G).left) :
    a = b := by
  have hab : a ≫ (G ⊗ G).hom = b ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), reassoc_of% h1]
  have key : (Over.homMk a : Over.mk (a ≫ (G ⊗ G).hom) ⟶ G ⊗ G) = Over.homMk b hab.symm := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      simpa using h1
    · ext
      simpa using h2
  exact congrArg Over.Hom.left key

theorem one_left_pφ :
    (1 : (Over.pullback f).obj G ⟶ (Over.pullback f).obj G).left ≫ pφ f G =
      pφ f G ≫ (1 : G ⟶ G).left := by
  change (pullback.snd G.hom f ≫ η[(Over.pullback f).obj G].left) ≫ pφ f G =
    pφ f G ≫ G.hom ≫ η[G].left
  rw [Category.assoc, GlobalTheory.GrpTangent.one_pullback_left_fst,
    ← Category.assoc, ← pullback.condition, Category.assoc]

theorem mul_left_pφ :
    (MonObj.mul : (Over.pullback f).obj G ⊗ (Over.pullback f).obj G ⟶ (Over.pullback f).obj G).left ≫ pφ f G =
      pφ₂ f G ≫ (MonObj.mul : G ⊗ G ⟶ G).left := by
  rw [Functor.obj.μ_def, Over.comp_left, Category.assoc, show pφ f G = pullback.fst G.hom f from rfl,
    pullback_map_left_fst', pφ₂, Category.assoc]

/-- The cartesian projection preserves the group law on points. -/
theorem isGrpPullback : IsGrpPullback ((Over.pullback f).obj G) G f (pφ f G) := by
  refine ⟨IsPullback.of_hasPullback G.hom f, ?_⟩
  intro T x y x₀ y₀ hx hy
  have hl : (lift x₀ y₀).left = (lift x y).left ≫ pφ₂ f G := by
    apply fibreSquare_hom_ext
    · have e1 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst x₀ y₀)
      have e2 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst x y)
      rw [Over.comp_left] at e1 e2
      rw [e1, Category.assoc, pφ₂_fst, reassoc_of% e2, hx]
    · have e1 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd x₀ y₀)
      have e2 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd x y)
      rw [Over.comp_left] at e1 e2
      rw [e1, Category.assoc, pφ₂_snd, reassoc_of% e2, hy]
  rw [Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, Category.assoc, mul_left_pφ f G,
    ← Category.assoc, ← hl]


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
  one := by rw [act.one, Functor.map_id]
  mul b c := by rw [act.mul, Functor.map_comp]
  add b c := by
    rw [act.add]
    exact map_mul ((Over.pullback f).homMonoidHom A A) (act.act b) (act.act c)

end GlobalTheory.UPel.HT

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

/-- The identity map is a cartesian map of group schemes. -/
theorem IsGrpPullback.refl {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    IsGrpPullback A A (𝟙 S) (𝟙 A.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, ?_⟩
  intro T x y x₀ y₀ hx hy
  let e : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 _) (by simp)
  have h₁ : x₀ = e ≫ x := Over.OverMorphism.ext (by simpa [e] using hx)
  have h₂ : y₀ = e ≫ y := Over.OverMorphism.ext (by simpa [e] using hy)
  rw [h₁, h₂, ← MonObj.comp_mul, Over.comp_left]
  simp [e]

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
    Over.homMk (𝟙 _) (by simp)
  have e₂ : ((e ≫ x₀) * (e ≫ y₀)).left = (x' * y').left ≫ φ :=
    h₂.2 _ x' y' (e ≫ x₀) (e ≫ y₀) (by simp [e, x', hx]) (by simp [e, y', hy])
  rw [← MonObj.comp_mul, Over.comp_left] at e₂
  simp only [e, Over.homMk_left, Category.id_comp] at e₂
  rw [e₂, e₁, Category.assoc]

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
          map_one' := mul_left_cancel ((hmul 1 1).symm.trans (by rw [one_mul, mul_one]))
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
