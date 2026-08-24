import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Functoriality of exact functors on derived categories

Natural isomorphisms and composition of exact additive functors descend through the
quasi-isomorphism localization to their induced functors on unbounded derived categories.
-/

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]

/-- The derived functor induced by the identity is the identity functor. -/
noncomputable def mapDerivedCategoryIdIso :
    (𝟭 C₁).mapDerivedCategory ≅ 𝟭 (DerivedCategory C₁) :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    ((𝟭 C₁).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    DerivedCategory.Q
    (𝟭 C₁).mapDerivedCategory (𝟭 (DerivedCategory C₁))
    (isoWhiskerRight (Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ))
      DerivedCategory.Q ≪≫ Functor.leftUnitor DerivedCategory.Q)

/-- Naturally isomorphic exact additive functors induce isomorphic derived functors. -/
noncomputable def mapDerivedCategoryNatIso
    {F G : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))
      DerivedCategory.Q)

variable {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-- Successive derived functors of exact additive functors agree with the derived functor of their
composite. The composite exactness instances make the chosen target derived functor explicit. -/
noncomputable def mapDerivedCategoryCompIso
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)] :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ (F ⋙ G).mapDerivedCategory := by
  let c := ComplexShape.up ℤ
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ c)
      ((F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c) ⋙ DerivedCategory.Q)
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm⟩
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ c)
    ((F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c) ⋙ DerivedCategory.Q)
    ((F ⋙ G).mapHomologicalComplex c ⋙ DerivedCategory.Q)
    (F.mapDerivedCategory ⋙ G.mapDerivedCategory) (F ⋙ G).mapDerivedCategory
    (isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c)
      DerivedCategory.Q)

end CategoryTheory.Functor
