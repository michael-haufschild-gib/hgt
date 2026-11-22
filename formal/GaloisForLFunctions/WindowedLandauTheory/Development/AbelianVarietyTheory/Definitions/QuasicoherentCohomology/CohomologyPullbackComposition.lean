import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PushforwardComparison

/-! Pullback of sheaf cohomology commutes with composition. The degree-zero
identity on sections extends to higher degrees by the connecting maps. -/

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace

namespace GlobalTheory.SchemeCohomology

private abbrev AbSheaf (X : TopCat.{0}) := TopCat.Sheaf AddCommGrpCat.{0} X
private abbrev pull {X Y : TopCat.{0}} (f : Y ⟶ X) := TopCat.Sheaf.pullback AddCommGrpCat.{0} f
private abbrev push {X Y : TopCat.{0}} (f : Y ⟶ X) := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f
private abbrev adj {X Y : TopCat.{0}} (f : Y ⟶ X) :=
  TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f

local instance (X : TopCat.{0}) : HasExt.{0} (AbSheaf X) := hasExt_of_enoughInjectives _

variable {X Y Z : TopCat.{0}} (f : Y ⟶ X)

local instance : PreservesFiniteLimits (pull f) := RHTower.deningerSheafPullback_preservesFiniteLimits f

local instance : (pull f).Additive := by
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts (pull f)
  exact Functor.additive_of_preservesBinaryBiproducts _

local instance : (push f).Additive where
  map_add := rfl

local instance : (push f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (adj f)

private theorem extZero_mk₀ {T : TopCat.{0}} {A B : AbSheaf T} (a : A ⟶ B) :
    Ext.homEquiv₀ (Ext.mk₀ a) = a :=
  Ext.homEquiv₀.right_inv a

private theorem pullbackSection_zero {F : AbSheaf X} {G : AbSheaf Y}
    (φ : F ⟶ (push f).obj G) (U : Opens X) (x : Ext (openFree U) F 0) :
    openFreeHomEquiv ((Opens.map f).obj U) G (Ext.homEquiv₀ (abelianCohomologyPullback f φ U 0 x)) =
      φ.hom.app (op U) (openFreeHomEquiv U F (Ext.homEquiv₀ x)) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
  let V := (Opens.map f).obj U
  let b := ((adj f).homEquiv F G).symm φ
  let c := (pull f).map a ≫ b
  change openFreeHomEquiv V G (Ext.homEquiv₀
      (((Ext.mk₀ (pullbackOpenFree f U)).comp ((Ext.mk₀ a).mapExactFunctor (pull f)) rfl).comp
        (Ext.mk₀ b) rfl)) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, extZero_mk₀, extZero_mk₀]
  change openFreeHomEquiv V G (pullbackOpenFree f U ≫ c) =
    φ.hom.app (op U) (openFreeHomEquiv U F a)
  rw [openFreeHomEquiv_natural]
  have hfree : openFreeHomEquiv V ((pull f).obj (openFree U)) (pullbackOpenFree f U) =
      openFreeHomEquiv U _ ((adj f).homEquiv (openFree U) _ (𝟙 _)) :=
    Equiv.apply_symm_apply _ _
  rw [hfree]
  have hc := (adj f).homEquiv_naturality_right (𝟙 ((pull f).obj (openFree U))) c
  rw [Category.id_comp] at hc
  have ha := (adj f).homEquiv_naturality_left a b
  have hh : (adj f).homEquiv (openFree U) G c = a ≫ φ := by
    change (adj f).homEquiv (openFree U) G ((pull f).map a ≫ b) = _
    exact ha.trans (congrArg (a ≫ ·) (Equiv.apply_symm_apply _ _))
  have e := openFreeHomEquiv_natural U ((adj f).homEquiv (openFree U) _ (𝟙 _)) ((push f).map c)
  exact e.symm.trans ((congrArg (openFreeHomEquiv U ((push f).obj G)) (hc.symm.trans hh)).trans
    (openFreeHomEquiv_natural U a φ))

private def adjointShortComplexMap {S : ShortComplex (AbSheaf X)} {T : ShortComplex (AbSheaf Y)}
    (a : S ⟶ T.map (push f)) : S.map (pull f) ⟶ T where
  τ₁ := ((adj f).homEquiv _ _).symm a.τ₁
  τ₂ := ((adj f).homEquiv _ _).symm a.τ₂
  τ₃ := ((adj f).homEquiv _ _).symm a.τ₃
  comm₁₂ := by
    change ((adj f).homEquiv _ _).symm a.τ₁ ≫ T.f =
      (pull f).map S.f ≫ ((adj f).homEquiv _ _).symm a.τ₂
    rw [← Adjunction.homEquiv_naturality_right_symm, ← Adjunction.homEquiv_naturality_left_symm]
    exact congrArg ((adj f).homEquiv S.X₁ T.X₂).symm a.comm₁₂
  comm₂₃ := by
    change ((adj f).homEquiv _ _).symm a.τ₂ ≫ T.g =
      (pull f).map S.g ≫ ((adj f).homEquiv _ _).symm a.τ₃
    rw [← Adjunction.homEquiv_naturality_right_symm, ← Adjunction.homEquiv_naturality_left_symm]
    exact congrArg ((adj f).homEquiv S.X₂ T.X₃).symm a.comm₂₃

private theorem pullback_boundary {S : ShortComplex (AbSheaf X)} {T : ShortComplex (AbSheaf Y)}
    (hS : S.ShortExact) (hT : T.ShortExact) (a : S ⟶ T.map (push f))
    (U : Opens X) (n : ℕ) (x : Ext (openFree U) S.X₃ n) :
    abelianCohomologyPullback f a.τ₁ U (n + 1) (x.comp hS.extClass rfl) =
      (abelianCohomologyPullback f a.τ₃ U n x).comp hT.extClass rfl := by
  let c := adjointShortComplexMap f a
  let b := Ext.mk₀ (pullbackOpenFree f U)
  let y := x.mapExactFunctor (pull f)
  let d := (hS.map_of_exact (pull f)).extClass
  let z := b.comp y (zero_add n)
  have h := (hS.map_of_exact (pull f)).extClass_naturality hT c
  change (b.comp ((x.comp hS.extClass rfl).mapExactFunctor (pull f)) (zero_add (n + 1))).comp
      (Ext.mk₀ c.τ₁) (add_zero (n + 1)) = (z.comp (Ext.mk₀ c.τ₃) (add_zero n)).comp hT.extClass rfl
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  change (b.comp (y.comp d rfl) (zero_add (n + 1))).comp (Ext.mk₀ c.τ₁) (add_zero (n + 1)) = _
  rw [← Ext.comp_assoc b y d (zero_add n) rfl (by simp : 0 + n + 1 = n + 1),
    Ext.comp_assoc_of_third_deg_zero]
  exact (congrArg (fun η : Ext ((pull f).obj S.X₃) T.X₁ 1 => z.comp η rfl) h).trans
    (Ext.comp_assoc_of_second_deg_zero z (Ext.mk₀ c.τ₃) hT.extClass rfl).symm

private abbrev I {X : TopCat.{0}} (F : AbSheaf X) := RHTower.deningerInjectiveEmbedding F

private theorem extendPullbackMap {F : AbSheaf X} {G : AbSheaf Y} (φ : F ⟶ (push f).obj G) :
    ∃ a : I F ⟶ (I G).map (push f), a.τ₁ = φ := by
  haveI : Injective ((push f).obj (Injective.under G)) :=
    Functor.injective_obj _ _
  let a₂ := Injective.factorThru (φ ≫ (push f).map (I G).f) (I F).f
  have ha : (I F).f ≫ a₂ = φ ≫ (push f).map (I G).f :=
    Injective.comp_factorThru _ _
  have hzero : (I F).f ≫ a₂ ≫ (push f).map (I G).g = 0 := by
    rw [← Category.assoc, ha, Category.assoc, ← Functor.map_comp, (I G).zero,
      Functor.map_zero, comp_zero]
  refine ⟨{ τ₁ := φ, τ₂ := a₂, τ₃ := cokernel.desc (I F).f _ hzero
            comm₁₂ := ha.symm
            comm₂₃ := (cokernel.π_desc _ _ _).symm }, rfl⟩

/-- Pullback on cohomology along a composite is successive pullback. -/
theorem abelianCohomologyPullback_comp (g : Z ⟶ Y) {F : AbSheaf X} {G : AbSheaf Y} {L : AbSheaf Z}
    (φ : F ⟶ (push f).obj G) (ψ : G ⟶ (push g).obj L) (U : Opens X) (n : ℕ)
    (x : Ext (openFree U) F n) :
    abelianCohomologyPullback g ψ ((Opens.map f).obj U) n (abelianCohomologyPullback f φ U n x) =
      abelianCohomologyPullback (g ≫ f) (φ ≫ (push f).map ψ) U n x := by
  induction n generalizing F G L with
  | zero =>
    apply Ext.homEquiv₀.injective
    apply (openFreeHomEquiv _ L).injective
    rw [pullbackSection_zero, pullbackSection_zero]
    exact (pullbackSection_zero (g ≫ f) (φ ≫ (push f).map ψ) U x).symm
  | succ n ih =>
    let V := (Opens.map f).obj U
    have hF := RHTower.deningerInjectiveEmbedding_shortExact F
    have hG := RHTower.deningerInjectiveEmbedding_shortExact G
    have hL := RHTower.deningerInjectiveEmbedding_shortExact L
    obtain ⟨a, rfl⟩ := extendPullbackMap f φ
    obtain ⟨b, rfl⟩ := extendPullbackMap g ψ
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ (openFree U) hF x
      (Ext.eq_zero_of_injective _) rfl
    let c : I F ⟶ (I L).map (push (g ≫ f)) := a ≫ (push f).mapShortComplex.map b
    calc
      _ = (abelianCohomologyPullback g b.τ₃ V n
          (abelianCohomologyPullback f a.τ₃ U n y)).comp hL.extClass rfl := by
        rw [pullback_boundary f hF hG a, pullback_boundary g hG hL b]
      _ = (abelianCohomologyPullback (g ≫ f) c.τ₃ U n y).comp hL.extClass rfl :=
        congrArg (fun w => w.comp hL.extClass rfl) (ih a.τ₃ b.τ₃ y)
      _ = _ := (pullback_boundary (g ≫ f) hF hL c U n y).symm

end GlobalTheory.SchemeCohomology
