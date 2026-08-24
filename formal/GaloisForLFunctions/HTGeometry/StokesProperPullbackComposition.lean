import GaloisForLFunctions.HTGeometry.StokesProperPullbackExact
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Composition of proper compact-support pullback

Sheaf inverse image composes contravariantly by uniqueness of left adjoints. For proper maps, the
comparison restricts to compactly supported sheaves by cancelling their fully faithful inclusion
into all sheaves.
-/

namespace GaloisForLFunctions.IrregularStokes.CompactIndSheaf

open CategoryTheory
open OrdinaryConvolution ExactSheafification

/-- Successive sheaf inverse images agree with inverse image along the composite. -/
noncomputable def sheafPullbackCompIso {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pullback IntModuleCat.{0} g ⋙
        TopCat.Sheaf.pullback IntModuleCat.{0} f ≅
      TopCat.Sheaf.pullback IntModuleCat.{0} (f ≫ g) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction IntModuleCat.{0} g).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction IntModuleCat.{0} f)).leftAdjointUniq
      (TopCat.Sheaf.pullbackPushforwardAdjunction IntModuleCat.{0} (f ≫ g))

/-- Sheaf inverse image along the identity is the identity functor. -/
noncomputable def sheafPullbackIdIso (X : TopCat.{0}) :
    TopCat.Sheaf.pullback IntModuleCat.{0} (𝟙 X) ≅ 𝟭 (Sh X) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction IntModuleCat.{0} (𝟙 X)).leftAdjointUniq
    (Adjunction.id : (𝟭 (Sh X)) ⊣ 𝟭 (Sh X))

/-- Proper pullback on compactly supported sheaves composes contravariantly. -/
noncomputable def properPullbackCompIso {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsProperMap f) (hg : IsProperMap g) :
    properPullback g hg ⋙ properPullback f hf ≅
      properPullback (f ≫ g) (by simpa using hg.comp hf) :=
  Functor.fullyFaithfulCancelRight (HasCompactSupport X).ι
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (properPullbackCompιIso f hf) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (properPullbackCompιIso g hg)
        (TopCat.Sheaf.pullback IntModuleCat.{0} f) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (sheafPullbackCompIso f g) ≪≫
      (properPullbackCompιIso (f ≫ g) (by simpa using hg.comp hf)).symm)

/-- Proper pullback along the identity is the identity on compactly supported sheaves. -/
noncomputable def properPullbackIdIso (X : TopCat.{0}) :
    properPullback (𝟙 X) isProperMap_id ≅ 𝟭 (CompactlySupportedSheaf X) :=
  Functor.fullyFaithfulCancelRight (HasCompactSupport X).ι
    (properPullbackCompιIso (𝟙 X) isProperMap_id ≪≫
      Functor.isoWhiskerLeft (HasCompactSupport X).ι (sheafPullbackIdIso X) ≪≫
      Functor.rightUnitor (HasCompactSupport X).ι ≪≫
      (Functor.leftUnitor (HasCompactSupport X).ι).symm)

end GaloisForLFunctions.IrregularStokes.CompactIndSheaf
