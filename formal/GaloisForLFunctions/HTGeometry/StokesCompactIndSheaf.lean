import GaloisForLFunctions.HTGeometry.StokesExactSheafification
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Indization
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Abelian.Subcategory

/-!
# Compactly supported sheaves and ind-sheaves

Compact support for integer-module sheaves is defined by stalkwise vanishing outside a compact
set. Exactness of stalks makes this a Serre property. The corresponding full subcategory is
abelian, and its universe-small indization is Grothendieck abelian.

This is the correct coefficient-category construction `Ind(Modᶜ(ℤ_Y))`; it does not yet provide
the six operations, ordinary-sheaf embedding, bordered-space localization, or enhanced quotient.
-/

open CategoryTheory Limits TopologicalSpace ZeroObject

namespace GaloisForLFunctions.IrregularStokes.CompactIndSheaf

open OrdinaryConvolution ExactSheafification

abbrev Sh (Y : TopCat.{0}) := TopCat.Sheaf (IntModuleCat.{0}) Y

/-- Stalk functor on integer-module sheaves. -/
noncomputable abbrev stalkFunctor (Y : TopCat.{0}) (x : Y) :
    Sh Y ⥤ IntModuleCat.{0} :=
  TopCat.Sheaf.forget (IntModuleCat.{0}) Y ⋙
    TopCat.Presheaf.stalkFunctor (IntModuleCat.{0}) x

/-- A sheaf has compact support when all stalks outside some compact set are zero. -/
def HasCompactSupport (Y : TopCat.{0}) : ObjectProperty (Sh Y) :=
  fun F => ∃ K : Set Y, IsCompact K ∧
    ∀ x : Y, x ∉ K → IsZero ((stalkFunctor Y x).obj F)

instance hasCompactSupport_containsZero (Y : TopCat.{0}) :
    (HasCompactSupport Y).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, ∅, isCompact_empty, fun x _ =>
    (stalkFunctor Y x).map_isZero (isZero_zero _)⟩

instance hasCompactSupport_closedUnderSubobjects (Y : TopCat.{0}) :
    (HasCompactSupport Y).IsClosedUnderSubobjects where
  prop_of_mono {F G} f _ := by
    rintro ⟨K, hK, hG⟩
    refine ⟨K, hK, fun x hx => ?_⟩
    haveI : Mono ((stalkFunctor Y x).map f) := Functor.map_mono _ f
    exact IsZero.of_mono ((stalkFunctor Y x).map f) (hG x hx)

instance hasCompactSupport_closedUnderQuotients (Y : TopCat.{0}) :
    (HasCompactSupport Y).IsClosedUnderQuotients where
  prop_of_epi {F G} f _ := by
    rintro ⟨K, hK, hF⟩
    refine ⟨K, hK, fun x hx => ?_⟩
    haveI : Epi ((stalkFunctor Y x).map f) := Functor.map_epi _ f
    exact IsZero.of_epi ((stalkFunctor Y x).map f) (hF x hx)

instance hasCompactSupport_closedUnderExtensions (Y : TopCat.{0}) :
    (HasCompactSupport Y).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS := by
    rintro ⟨K₁, hK₁, h₁⟩ ⟨K₃, hK₃, h₃⟩
    refine ⟨K₁ ∪ K₃, hK₁.union hK₃, fun x hx => ?_⟩
    rw [Set.mem_union, not_or] at hx
    let T := S.map (stalkFunctor Y x)
    have hT : T.Exact :=
      (((Functor.exact_tfae (stalkFunctor Y x)).out 2 1 rfl rfl).mp
        inferInstance) S hS.exact
    exact hT.isZero_of_both_isZero (h₁ x hx.1) (h₃ x hx.2)

/-- Compact support is a Serre property of integer-module sheaves. -/
instance hasCompactSupport_isSerreClass (Y : TopCat.{0}) :
    (HasCompactSupport Y).IsSerreClass where

noncomputable instance hasCompactSupport_closedUnderBinaryProducts
    (Y : TopCat.{0}) :
    (HasCompactSupport Y).IsClosedUnderBinaryProducts := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro X ⟨F, hF⟩
  refine (HasCompactSupport Y).prop_of_iso ?_
    ((HasCompactSupport Y).prop_biprod
      (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩))
  exact biprod.isoProd _ _ ≪≫
    IsLimit.conePointUniqueUpToIso (prodIsProd _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair F) _).2 (limit.isLimit F))

noncomputable instance hasCompactSupport_closedUnderFiniteProducts
    (Y : TopCat.{0}) :
    (HasCompactSupport Y).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- Compactly supported integer-module sheaves. -/
abbrev CompactlySupportedSheaf (Y : TopCat.{0}) :=
  (HasCompactSupport Y).FullSubcategory

/-- Compactly supported integer-module sheaves form an abelian category. -/
noncomputable instance compactlySupportedSheafAbelian (Y : TopCat.{0}) :
    Abelian (CompactlySupportedSheaf Y) := by infer_instance

/-- Universe-small model of compactly supported integer-module sheaves. -/
abbrev SmallCompactlySupportedSheaf (Y : TopCat.{0}) :=
  AsSmall.{1} (CompactlySupportedSheaf Y)

/-- Integer-coefficient ind-sheaves: ind-objects of compactly supported sheaves. -/
abbrev IndSheaf (Y : TopCat.{0}) := Ind (SmallCompactlySupportedSheaf Y)

/-- Integer-coefficient ind-sheaves form an abelian category. -/
noncomputable instance indSheafAbelian (Y : TopCat.{0}) :
    Abelian (IndSheaf Y) := by infer_instance

/-- Integer-coefficient ind-sheaves form a Grothendieck abelian category. -/
instance indSheafGrothendieckAbelian (Y : TopCat.{0}) :
    IsGrothendieckAbelian.{1} (IndSheaf Y) := by infer_instance

/-- The standard derived category of integer-coefficient ind-sheaves exists. -/
theorem indSheaf_hasDerivedCategory (Y : TopCat.{0}) :
    Nonempty (HasDerivedCategory.{2} (IndSheaf Y)) :=
  ⟨HasDerivedCategory.standard _⟩

end GaloisForLFunctions.IrregularStokes.CompactIndSheaf
