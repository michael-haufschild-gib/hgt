import GaloisForLFunctions.HTGeometry.StokesFirstQuadrantRowwiseQuasiIso
import GaloisForLFunctions.HTGeometry.StokesProjectiveComplexTensorExact

/-!
# K-flatness of componentwise-projective nonnegative complexes

Combining rowwise flatness with first-quadrant totalization proves that total tensor by a
nonnegative complex whose terms are projective module presheaves preserves all quasi-isomorphisms.
This is the unbounded-in-length, bounded-below K-flat theorem needed for derived tensor products.
-/

open CategoryTheory Limits MonoidalCategory

universe u

namespace GaloisForLFunctions.IrregularStokes.ProjectiveComplexTensorKFlat

open ProjectivePresheafTensorFlat
open ProjectiveComplexTensorExact
open FirstQuadrantRowwiseQuasiIso

variable {C : Type u} [SmallCategory C]
variable (A : Cᵒᵖ ⥤ CommRingCat.{u})

abbrev M := PresheafComplexTensor.ModulePresheaf A
abbrev CC := ChainComplex (M A) ℕ

noncomputable abbrev tensorBicomplexFunctor :=
  (MonoidalCategory.curriedTensor (M A)).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)

noncomputable abbrev tensorBicomplex (P X : CC A) :=
  ((tensorBicomplexFunctor A).obj P).obj X

noncomputable def tensorBicomplexMap (P : CC A) {X Y : CC A} (φ : X ⟶ Y) :
    tensorBicomplex A P X ⟶ tensorBicomplex A P Y :=
  ((tensorBicomplexFunctor A).map (𝟙 P)).app X ≫
    ((tensorBicomplexFunctor A).obj P).map φ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem tensorBicomplexMap_row_quasiIso
    (P : CC A) [∀ n, Projective (P.X n)] {X Y : CC A}
    (φ : X ⟶ Y) [QuasiIso φ] (p : ℕ) :
    QuasiIso ((tensorBicomplexMap A P φ).f p) := by
  letI : QuasiIso
      (((MonoidalCategory.tensorLeft (P.X p)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map φ) :=
    projectiveTensorLeft_map_quasiIso A (P.X p) φ
  change QuasiIso
    ((((tensorBicomplexFunctor A).map (𝟙 P)).app X).f p ≫
      (((tensorBicomplexFunctor A).obj P).map φ).f p)
  have hid : ((tensorBicomplexFunctor A).map (𝟙 P)).app X = 𝟙 _ := by
    exact congrArg (fun α => α.app X)
      ((tensorBicomplexFunctor A).map_id P)
  rw [hid, HomologicalComplex.id_f, Category.id_comp]
  exact projectiveTensorLeft_map_quasiIso A (P.X p) φ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A nonnegative componentwise-projective complex of module presheaves is K-flat: total left
tensor by it maps every quasi-isomorphism to a quasi-isomorphism. -/
theorem componentwiseProjectiveTotalTensorLeft_map_quasiIso
    (P : CC A) [∀ n, Projective (P.X n)] {X Y : CC A}
    (φ : X ⟶ Y) [QuasiIso φ] :
    QuasiIso ((@MonoidalCategory.tensorLeft (CC A) _
      (PresheafComplexTensor.chainComplexMonoidalCategory A) P).map φ) := by
  let Φ := tensorBicomplexMap A P φ
  have hΦ : ∀ p : ℕ, QuasiIso (Φ.f p) := fun p =>
    tensorBicomplexMap_row_quasiIso A P φ p
  have htotal := totalMap_quasiIso_of_rowwise A Φ hΦ
  exact htotal

end GaloisForLFunctions.IrregularStokes.ProjectiveComplexTensorKFlat
