import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FlatLineBundleCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.AffineBaseChangeSectionRings
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! Restriction of the affine base scalars commutes with Čech cohomology. -/

noncomputable section

open AlgebraicGeometry CategoryTheory HTGeometry TopologicalSpace
open GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

/-- Restricting scalars along an affine base map does not change the
underlying Čech cochains or differential. -/
def cechRestrictScalarsIso {R S : Type} [CommRing R] [CommRing S] (α : R →+* S)
    {X : Scheme.{0}} (g : X ⟶ Spec (.of S)) (F : X.Modules)
    {κ : Type} [LinearOrder κ] (U : κ → X.Opens) :
    cech (g ≫ Spec.map (CommRingCat.ofHom α)) F U ≅
      (((ModuleCat.restrictScalars α).mapHomologicalComplex (ComplexShape.up ℕ)).obj (cech g F U)) := by
  letI : Algebra R S := α.toAlgebra
  let f := g ≫ Spec.map (CommRingCat.ofHom α)
  let h (W : X.Opens) (r : R) :
      letI := sectionAlgebra f W
      letI := sectionAlgebra g W
      algebraMap R Γ(X, W) r = algebraMap S Γ(X, W) (α r) := by
    letI := sectionAlgebra f W
    letI := sectionAlgebra g W
    let j : W ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ W := le_rfl
    have hi : (𝟙 X : X ⟶ X).appLE W W j = 𝟙 Γ(X, W) :=
      (Scheme.Hom.app_eq_appLE (𝟙 X : X ⟶ X)).symm.trans (Scheme.Hom.id_app W)
    have he := congrArg (fun u : Γ(X, W) ⟶ Γ(X, W) => u (algebraMap R Γ(X, W) r)) hi
    exact he.symm.trans (appLE_base_algebraMap (π := 𝟙 X) (Category.id_comp f) j r)
  let C := cech f F U
  let D := cech g F U
  let G := ModuleCat.restrictScalars α
  let e (n : ℕ) : C.X n ≃ₗ[R] G.obj (D.X n) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => Subtype.ext (funext fun s => by
        let W := coverInter ⊤ U s
        letI := sectionAlgebra f W
        letI := sectionAlgebra g W
        let z : Γ(F, W) := x.1 s
        change (algebraMap R Γ(X, W) r) • z = (algebraMap S Γ(X, W) (α r)) • z
        exact congrArg (fun a : Γ(X, W) => a • z) (h W r)) }
  refine HomologicalComplex.Hom.isoOfComponents (fun n => (e n).toModuleIso) ?_
  intro n m hnm
  obtain rfl : m = n + 1 := hnm.symm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (D.d n (n + 1) (show D.X n from x)).1 = (C.d n (n + 1) x).1
  simp only [C, D, cech, FinsetCechDatum.linearComplex, CochainComplex.of_d]
  rfl

/-- The affine-base scalar change acts on Čech cohomology by restriction of scalars. -/
def homologyCechRestrictScalarsEquiv {R S : Type} [CommRing R] [CommRing S] (α : R →+* S)
    {X : Scheme.{0}} (g : X ⟶ Spec (.of S)) (F : X.Modules)
    {κ : Type} [LinearOrder κ] (U : κ → X.Opens) (n : ℕ) :
    (cech (g ≫ Spec.map (CommRingCat.ofHom α)) F U).homology n ≃ₗ[R]
      (ModuleCat.restrictScalars α).obj ((cech g F U).homology n) :=
  ((HomologicalComplex.homologyMapIso (cechRestrictScalarsIso α g F U) n) ≪≫
    ((cech g F U).sc n).mapHomologyIso (ModuleCat.restrictScalars α)).toLinearEquiv

end GlobalTheory.LineBundleSections
