import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.Induced

/-!
# Exact functors on bounded derived categories

An exact additive functor preserves the canonical lower and upper cohomological bounds on derived
objects. Its unbounded derived functor therefore restricts to bounded derived categories, with the
expected comparison to the full inclusions.
-/

open CategoryTheory Category Limits

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

noncomputable section

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor preserves canonical lower cohomological bounds. -/
theorem mapDerivedCategory_isGE (X : DerivedCategory C₁) (n : ℤ) [X.IsGE n] :
    (F.mapDerivedCategory.obj X).IsGE n := by
  obtain ⟨K, _, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isGE n
  haveI : CochainComplex.IsStrictlyGE
      ((F.mapHomologicalComplex (.up ℤ)).obj K) n := by infer_instance
  letI : (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj K)).IsGE n := by infer_instance
  let e' : F.mapDerivedCategory.obj X ≅ DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj K) :=
    F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app K
  exact DerivedCategory.TStructure.t.isGE_of_iso e'.symm n

/-- An exact functor preserves canonical upper cohomological bounds. -/
theorem mapDerivedCategory_isLE (X : DerivedCategory C₁) (n : ℤ) [X.IsLE n] :
    (F.mapDerivedCategory.obj X).IsLE n := by
  obtain ⟨K, _, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isLE n
  haveI : CochainComplex.IsStrictlyLE
      ((F.mapHomologicalComplex (.up ℤ)).obj K) n := by infer_instance
  letI : (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj K)).IsLE n := by infer_instance
  let e' : F.mapDerivedCategory.obj X ≅ DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj K) :=
    F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app K
  exact DerivedCategory.TStructure.t.isLE_of_iso e'.symm n

/-- An exact functor sends canonically bounded derived objects to bounded derived objects. -/
theorem mapDerivedCategory_bounded (X : DerivedCategory C₁)
    (hX : DerivedCategory.TStructure.t.bounded X) :
    DerivedCategory.TStructure.t.bounded (F.mapDerivedCategory.obj X) := by
  rcases hX with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  letI := ha
  letI := hb
  exact ⟨⟨a, F.mapDerivedCategory_isGE X a⟩, ⟨b, F.mapDerivedCategory_isLE X b⟩⟩

/-- Restriction of an exact functor's derived functor to bounded derived categories. -/
noncomputable abbrev mapBoundedDerivedCategory :
    DerivedCategory.Bounded C₁ ⥤ DerivedCategory.Bounded C₂ :=
  ObjectProperty.lift DerivedCategory.TStructure.t.bounded
    (DerivedCategory.Bounded.ι ⋙ F.mapDerivedCategory)
    (fun X ↦ F.mapDerivedCategory_bounded X.obj X.property)

/-- After inclusion, bounded derived mapping agrees with the unbounded derived functor. -/
noncomputable abbrev mapBoundedDerivedCategoryCompInclusionIso :
    F.mapBoundedDerivedCategory ⋙ DerivedCategory.Bounded.ι ≅
      DerivedCategory.Bounded.ι ⋙ F.mapDerivedCategory :=
  ObjectProperty.liftCompιIso _ _ _

end


end CategoryTheory.Functor
