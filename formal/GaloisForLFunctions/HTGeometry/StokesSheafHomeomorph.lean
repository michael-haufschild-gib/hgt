import GaloisForLFunctions.HTGeometry.StokesProperPullbackComposition
import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Sheaf transport along homeomorphisms

Direct image of integer-module sheaves along a topological isomorphism is an equivalence. Hence
inverse image along the isomorphism agrees with direct image along its inverse. Constant sheaves
are preserved, with the comparison obtained from their global-sections adjunction.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace GaloisForLFunctions.IrregularStokes.SheafHomeomorph

open OrdinaryConvolution

/-- Direct images of integer-module sheaves compose canonically. -/
noncomputable def sheafPushforwardCompIso {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pushforward IntModuleCat (f ≫ g) ≅
      TopCat.Sheaf.pushforward IntModuleCat f ⋙
        TopCat.Sheaf.pushforward IntModuleCat g := by
  change (Opens.map (f ≫ g)).sheafPushforwardContinuous IntModuleCat _ _ ≅
    (Opens.map f).sheafPushforwardContinuous IntModuleCat _ _ ⋙
      (Opens.map g).sheafPushforwardContinuous IntModuleCat _ _
  exact (CategoryTheory.Functor.sheafPushforwardContinuousComp
    (Opens.map g) (Opens.map f) IntModuleCat _ _ _).symm

/-- Direct image along the identity is the identity functor. -/
noncomputable def sheafPushforwardIdIso (X : TopCat.{0}) :
    TopCat.Sheaf.pushforward IntModuleCat (𝟙 X) ≅
      𝟭 (TopCat.Sheaf IntModuleCat X) := by
  change (Opens.map (𝟙 X)).sheafPushforwardContinuous IntModuleCat _ _ ≅ _
  exact CategoryTheory.Functor.sheafPushforwardContinuousId IntModuleCat _

/-- Equal continuous maps induce isomorphic direct-image functors. -/
noncomputable def sheafPushforwardEqIso {X Y : TopCat.{0}}
    {f g : X ⟶ Y} (h : f = g) :
    TopCat.Sheaf.pushforward IntModuleCat f ≅
      TopCat.Sheaf.pushforward IntModuleCat g := by
  subst g
  exact Iso.refl _

/-- Direct image along a topological isomorphism is an equivalence of sheaf categories. -/
noncomputable def sheafPushforwardEquivalence {X Y : TopCat.{0}} (H : X ≅ Y) :
    TopCat.Sheaf IntModuleCat X ≌ TopCat.Sheaf IntModuleCat Y :=
  CategoryTheory.Equivalence.mk
    (TopCat.Sheaf.pushforward IntModuleCat H.hom)
    (TopCat.Sheaf.pushforward IntModuleCat H.inv)
    ((sheafPushforwardIdIso X).symm ≪≫
      sheafPushforwardEqIso H.hom_inv_id.symm ≪≫
      sheafPushforwardCompIso H.hom H.inv)
    ((sheafPushforwardCompIso H.inv H.hom).symm ≪≫
      sheafPushforwardEqIso H.inv_hom_id ≪≫
      sheafPushforwardIdIso Y)

/-- Inverse image along a topological isomorphism agrees with direct image along its inverse. -/
noncomputable def sheafPullbackIsoPushforwardInv {X Y : TopCat.{0}} (H : X ≅ Y) :
    TopCat.Sheaf.pullback IntModuleCat H.hom ≅
      TopCat.Sheaf.pushforward IntModuleCat H.inv :=
  CategoryTheory.Adjunction.leftAdjointUniq
    (TopCat.Sheaf.pullbackPushforwardAdjunction IntModuleCat H.hom)
    (sheafPushforwardEquivalence H.symm).toAdjunction

/-- Global sections after direct image along the inverse homeomorphism are unchanged. -/
noncomputable def sheafSectionsPushforwardInvIso {X Y : TopCat.{0}} (H : X ≅ Y) :
    TopCat.Sheaf.pushforward IntModuleCat H.inv ⋙
        (CategoryTheory.sheafSections (Opens.grothendieckTopology X) IntModuleCat).obj
          (Opposite.op (⊤ : Opens X)) ≅
      (CategoryTheory.sheafSections (Opens.grothendieckTopology Y) IntModuleCat).obj
        (Opposite.op (⊤ : Opens Y)) := by
  exact Iso.refl _

/-- Direct image along a topological isomorphism preserves constant integer-module sheaves. -/
noncomputable def constantSheafPushforwardIso {X Y : TopCat.{0}} (H : X ≅ Y) :
    CategoryTheory.constantSheaf (Opens.grothendieckTopology X) IntModuleCat ⋙
        TopCat.Sheaf.pushforward IntModuleCat H.hom ≅
      CategoryTheory.constantSheaf (Opens.grothendieckTopology Y) IntModuleCat :=
  (((CategoryTheory.constantSheafAdj (Opens.grothendieckTopology X) IntModuleCat
      isTerminalTop).comp
        (sheafPushforwardEquivalence H).toAdjunction).ofNatIsoRight
          (sheafSectionsPushforwardInvIso H)).leftAdjointUniq
    (CategoryTheory.constantSheafAdj (Opens.grothendieckTopology Y) IntModuleCat
      isTerminalTop)

end GaloisForLFunctions.IrregularStokes.SheafHomeomorph
