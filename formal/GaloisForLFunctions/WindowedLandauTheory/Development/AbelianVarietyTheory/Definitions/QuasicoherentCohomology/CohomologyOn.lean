import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.GlobalSectionAction
import Mathlib.Algebra.Module.Hom
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.Abelian

/-! Cohomology of scheme modules on an open set, with its global scalar action. -/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u

variable {X : Scheme.{u}}

private abbrev abelianCohomology (X : Scheme.{u}) (U : X.Opens) (n : ℕ) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙
    (Functor.evaluation (X.Opensᵒᵖ) AddCommGrpCat.{u}).obj (op U)

private instance abelianCohomology_additive (X : Scheme.{u}) (U : X.Opens) (n : ℕ) :
    (abelianCohomology X U n).Additive := by
  change (Abelian.extFunctorObj
    ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free)) n).Additive
  infer_instance

private abbrev cohomologyFunctor (X : Scheme.{u}) (U : X.Opens) (n : ℕ) :
    X.Modules ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf ⋙ abelianCohomology X U n

/-- The `n`th sheaf cohomology of an `𝒪ₓ`-module on `U`. -/
def CohomologyOn (F : X.Modules) (U : X.Opens) (n : ℕ) : Type u :=
  (cohomologyFunctor X U n).obj F

instance (F : X.Modules) (U : X.Opens) (n : ℕ) : AddCommGroup (CohomologyOn F U n) :=
  inferInstanceAs (AddCommGroup ((cohomologyFunctor X U n).obj F))

private def cohomologyAction (F : X.Modules) (U : X.Opens) (n : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End (CohomologyOn F U n) where
  toFun r := ((cohomologyFunctor X U n).map (globalSectionEnd F r)).hom
  map_one' := by
    rw [map_one, Functor.map_id] <;> rfl
  map_mul' r s := by
    rw [map_mul]
    change ((cohomologyFunctor X U n).map (globalSectionEnd F s ≫ globalSectionEnd F r)).hom = _
    rw [Functor.map_comp] <;> rfl
  map_zero' := by
    rw [map_zero, Functor.map_zero] <;> rfl
  map_add' r s := by
    rw [map_add, Functor.map_add] <;> rfl

/-- Scalars act on cohomology by functoriality of their sheaf endomorphisms. -/
instance (F : X.Modules) (U : X.Opens) (n : ℕ) : Module Γ(X, ⊤) (CohomologyOn F U n) :=
  Module.compHom _ (cohomologyAction F U n)

namespace CohomologyOn

def map {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) (n : ℕ) :
    CohomologyOn F U n →ₗ[Γ(X, ⊤)] CohomologyOn G U n :=
  { ((cohomologyFunctor X U n).map φ).hom with
    map_smul' r x := by
      have h := congrArg (cohomologyFunctor X U n).map (globalSectionEnd_natural φ r)
      simp only [Functor.map_comp] at h
      exact ConcreteCategory.congr_hom h x }

/-- Restriction in the cohomology presheaf respects global scalars. -/
def res (F : X.Modules) {U V : X.Opens} (h : V ≤ U) (n : ℕ) :
    CohomologyOn F U n →ₗ[Γ(X, ⊤)] CohomologyOn F V n :=
  let G := SheafOfModules.toSheaf X.ringCatSheaf
  let i : V ⟶ U := homOfLE h
  { (((G.obj F).cohomologyPresheaf n).map i.op).hom with
    map_smul' r x :=
      ConcreteCategory.congr_hom
        ((((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map
          (G.map (globalSectionEnd F r))).naturality i.op).symm) x }

end CohomologyOn

end GlobalTheory.SchemeCohomology
