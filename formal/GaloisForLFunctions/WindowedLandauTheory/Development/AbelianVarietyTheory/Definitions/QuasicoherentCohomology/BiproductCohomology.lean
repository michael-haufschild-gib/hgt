import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.CohomologyOn
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BiproductSections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! Cohomology commutes with finite direct sums as modules over global sections. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
  Opposite
open scoped GlobalTheory.SchemeCohomology

namespace GlobalTheory.SchemeCohomology

universe u

local instance biproductCohomologyHasExt (T : TopCat.{u}) :
    HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} T) := hasExt_of_enoughInjectives _

variable {X : Scheme.{u}} {I : Type} [Fintype I]

/-- The cohomology of a finite biproduct identifies with the product via the
cohomology maps of the individual projections. -/
def CohomologyOn.biproductEquiv (F : I → X.Modules) (V : X.Opens) (n : ℕ) :
    CohomologyOn (⨁ F) V n ≃ₗ[Γ(X, ⊤)] ∀ i, CohomologyOn (F i) V n := by
  let A : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    SheafOfModules.toSheaf X.ringCatSheaf
  letI : HasZeroMorphisms X.Modules :=
    inferInstanceAs (HasZeroMorphisms (SheafOfModules.{u} X.ringCatSheaf))
  letI : A.PreservesZeroMorphisms :=
    inferInstanceAs ((SheafOfModules.toSheaf X.ringCatSheaf).PreservesZeroMorphisms)
  let hfinite : PreservesFiniteLimits A :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  let hshape := hfinite.preservesFiniteLimits (Discrete I)
  letI : PreservesLimit (Discrete.functor F) A :=
    hshape.preservesLimit
  letI : PreservesBiproduct F A := preservesBiproduct_of_preservesProduct A
  letI : HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) := biproductCohomologyHasExt X
  let W : TopCat.Sheaf AddCommGrpCat.{u} X := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (yoneda.obj V ⋙ AddCommGrpCat.free)
  let e : CohomologyOn (⨁ F) V n ≃+ (∀ i, CohomologyOn (F i) V n) :=
    Ext.addEquivBiproduct W (isBilimitOfPreserves A (biproduct.isBilimit F)) n
  exact { e with
    map_smul' r x := by
      funext i
      change (CohomologyOn.map (biproduct.π F i) V n) (r • x) =
        r • (CohomologyOn.map (biproduct.π F i) V n) x
      exact (CohomologyOn.map (biproduct.π F i) V n).map_smul r x }

end GlobalTheory.SchemeCohomology
