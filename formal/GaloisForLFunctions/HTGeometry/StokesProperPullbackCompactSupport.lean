import GaloisForLFunctions.HTGeometry.StokesCompactIndSheaf
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Proper pullback preserves compact support

For a proper continuous map, sheaf inverse image carries stalkwise compactly supported
integer-module sheaves to stalkwise compactly supported sheaves. This restricts ordinary sheaf
pullback to the compact-support category whose indization models ind-sheaves.

This module does not yet extend the restricted functor to ind-objects or derived categories.
-/

namespace GaloisForLFunctions.IrregularStokes.CompactIndSheaf

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat
open OrdinaryConvolution ExactSheafification

/-- Stalk of inverse image equals stalk over the image point. -/
noncomputable def sheafPullbackStalkIso {X Y : TopCat.{0}} (f : X ⟶ Y)
    (F : Sh Y) (x : X) :
    TopCat.Presheaf.stalk
        ((TopCat.Sheaf.pullback IntModuleCat.{0} f).obj F).1 x ≅
      TopCat.Presheaf.stalk F.1 ((ConcreteCategory.hom f) x) := by
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x IntModuleCat.{0}
    ((TopCat.Presheaf.pullback IntModuleCat.{0} f).obj F.1)
  exact (TopCat.Presheaf.stalkFunctor IntModuleCat.{0} x).mapIso
      ((TopCat.Sheaf.forget IntModuleCat.{0} X).mapIso
        ((TopCat.Sheaf.pullbackIso IntModuleCat.{0} f).app F)) ≪≫
    (asIso ((TopCat.Presheaf.stalkFunctor IntModuleCat.{0} x).map
      (toSheafify (Opens.grothendieckTopology X)
        ((TopCat.Presheaf.pullback IntModuleCat.{0} f).obj F.1)))).symm ≪≫
    (TopCat.Presheaf.stalkPullbackIso IntModuleCat.{0} f F.1 x).symm

/-- Proper inverse image preserves stalkwise compact support. -/
theorem pullback_hasCompactSupport {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hf : IsProperMap f) (F : Sh Y) (hF : HasCompactSupport Y F) :
    HasCompactSupport X ((TopCat.Sheaf.pullback IntModuleCat.{0} f).obj F) := by
  rcases hF with ⟨K, hK, hzero⟩
  refine ⟨f ⁻¹' K, hf.isCompact_preimage hK, fun x hx => ?_⟩
  refine IsZero.of_iso (hzero ((ConcreteCategory.hom f) x) ?_)
    (sheafPullbackStalkIso f F x)
  simpa using hx

/-- Sheaf inverse image restricted to compactly supported sheaves along a proper map. -/
noncomputable def properPullback {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hf : IsProperMap f) :
    CompactlySupportedSheaf Y ⥤ CompactlySupportedSheaf X :=
  (HasCompactSupport X).lift
    ((HasCompactSupport Y).ι ⋙ TopCat.Sheaf.pullback IntModuleCat.{0} f)
    (fun F => pullback_hasCompactSupport f hf F.1 F.2)

/-- Forgetting compact-support witnesses recovers ordinary sheaf inverse image. -/
noncomputable def properPullbackCompιIso {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hf : IsProperMap f) :
    properPullback f hf ⋙ (HasCompactSupport X).ι ≅
      (HasCompactSupport Y).ι ⋙ TopCat.Sheaf.pullback IntModuleCat.{0} f :=
  (HasCompactSupport X).liftCompιIso _ _

end GaloisForLFunctions.IrregularStokes.CompactIndSheaf
