import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Grothendieck's composition law for right derived functors

Let `F : C ⥤ D` and `G : D ⥤ E` be additive functors between abelian categories, let `C` and `D`
have enough injectives, and let `F` send injective objects to injective objects.  Then the right
derived functor of the composite is the composite of the right derived functors,
`R(G ∘ F) ≅ RG ∘ RF`, as functors between the bounded below derived categories.

This is the qualitative half of Grothendieck's theorem on the composition of derived functors —
the statement that underlies every Leray-type comparison — and mathlib has the derived functor
`Functor.rightDerivedFunctorPlus` but not this composition law.

The proof is the standard one, run through mathlib's injective derivability structure.  Both
`R(G ∘ F)` and `RG ∘ RF` are equipped with a natural transformation out of
`(G ∘ F)_* : K⁺(C) ⥤ D⁺(E)`, and by
`LocalizerMorphism.Derives.isRightDerivedFunctor_of_isIso` a functor equipped with such a
transformation is *the* right derived functor exactly when the transformation is invertible on
complexes of injectives.  For the composite transformation that is the conjunction of two facts:
the unit of `RF` is invertible on a complex of injectives, and the unit of `RG` is invertible on
its image, which is a complex of injectives precisely because `F` preserves injectivity.

* `HTGeometry.derivedCompUnit` : the comparison `(G ∘ F)_* ⟶ Q ∘ (RF ⋙ RG)`.
* `HTGeometry.derivedCompUnit_app_isIso` : it is invertible on complexes of injectives.
* `HTGeometry.rightDerivedFunctorPlusCompIso` : `R(G ∘ F) ≅ RF ⋙ RG`.
* `HTGeometry.rightDerivedFunctorPlusCompObjIso` : the same isomorphism, evaluated at an object.
-/

open CategoryTheory Limits

namespace HTGeometry

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D] [HasDerivedCategory.{w₃} E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [EnoughInjectives C] [EnoughInjectives D] [F.PreservesInjectiveObjects]

/-- A functor preserving injective objects carries a bounded below complex of injectives to a
bounded below complex of injectives. -/
instance mapHomotopyCategoryPlus_injective (K : HomotopyCategory.Plus C) (n : ℤ)
    [Injective (K.obj.as.X n)] :
    Injective ((F.mapHomotopyCategoryPlus.obj K).obj.as.X n) :=
  inferInstanceAs (Injective (F.obj (K.obj.as.X n)))

/-- The comparison natural transformation exhibiting `RF ⋙ RG` as a candidate right derived
functor of the composite `G ∘ F`.  It is the unit of `RG` at the `F`-image, followed by `RG`
applied to the unit of `RF`. -/
noncomputable def derivedCompUnit :
    (F ⋙ G).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerLeft F.mapHomotopyCategoryPlus G.rightDerivedFunctorPlusUnit ≫
    Functor.whiskerRight F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlus

/-- **The comparison is invertible on a bounded below complex of injectives.**  Its first factor is
the image of an isomorphism, its second is the unit of `RG` at a complex of injectives — which is
where preservation of injectivity by `F` is used — and its third is `RG` applied to the unit of
`RF` at a complex of injectives. -/
lemma derivedCompUnit_app_isIso (X : HomotopyCategory.Plus (InjectiveObject C)) :
    IsIso ((derivedCompUnit F G).app
      ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X)) := by
  have h1 : IsIso (DerivedCategory.Plus.Qh.map
      ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv.app
        ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X))) := inferInstance
  have h2 : IsIso (G.rightDerivedFunctorPlusUnit.app
      (F.mapHomotopyCategoryPlus.obj
        ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X))) := inferInstance
  have h3 : IsIso (G.rightDerivedFunctorPlus.map
      (F.rightDerivedFunctorPlusUnit.app
        ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X))) := inferInstance
  exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 h3)

/-- **`RF ⋙ RG` is a right derived functor of the composite.** -/
instance isRightDerivedFunctor_comp :
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (derivedCompUnit F G) (HomotopyCategory.Plus.quasiIso C) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      ((F ⋙ G).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh)).isRightDerivedFunctor_of_isIso _
    (fun X => derivedCompUnit_app_isIso F G X)

/-- **Grothendieck's composition law for right derived functors.**  If `F` preserves injective
objects, the right derived functor of `G ∘ F` on the bounded below derived category is the
composite of the right derived functors of `F` and of `G`. -/
noncomputable def rightDerivedFunctorPlusCompIso :
    (F ⋙ G).rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  Functor.rightDerivedUnique _ _ (F ⋙ G).rightDerivedFunctorPlusUnit
    (derivedCompUnit F G) (HomotopyCategory.Plus.quasiIso C)

/-- The composition law evaluated at an object of the bounded below derived category. -/
noncomputable def rightDerivedFunctorPlusCompObjIso (X : DerivedCategory.Plus C) :
    (F ⋙ G).rightDerivedFunctorPlus.obj X ≅
      G.rightDerivedFunctorPlus.obj (F.rightDerivedFunctorPlus.obj X) :=
  (rightDerivedFunctorPlusCompIso F G).app X

end HTGeometry
