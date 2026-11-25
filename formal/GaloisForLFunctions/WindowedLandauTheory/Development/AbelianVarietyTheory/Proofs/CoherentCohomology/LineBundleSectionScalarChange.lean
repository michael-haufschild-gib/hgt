import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.AffineBaseChangeSectionRings
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.AffineLineBundleBaseChange

/-! Line-bundle sections on each affine intersection commute with change of base. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open GlobalTheory.SchemeCohomology ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  {X Y : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of S)}
  {π : Y ⟶ X} (L : LB X)

abbrev sectionBaseModule {A : Type} [CommRing A] {Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of A)) (F : Z.Modules) (U : Z.Opens) : Module A Γ(F, U) :=
  letI := sectionAlgebra p U
  Module.compHom Γ(F, U) (algebraMap A Γ(Z, U))

abbrev scalarPullSection
    (w : π ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
    {U : X.Opens} {V : Y.Opens} (h : V ≤ π ⁻¹ᵁ U) :
    letI := sectionBaseModule f (toMod L) U
    letI := sectionBaseModule g (toMod (L.pull π)) V
    letI : Module R Γ(toMod (L.pull π), V) := Module.compHom _ (algebraMap R S)
    Γ(toMod L, U) →ₗ[R] Γ(toMod (L.pull π), V) :=
  letI := sectionAlgebra f U
  letI := sectionAlgebra g V
  letI := sectionBaseModule f (toMod L) U
  letI := sectionBaseModule g (toMod (L.pull π)) V
  letI : Module R Γ(toMod (L.pull π), V) := Module.compHom _ (algebraMap R S)
  { pullSection (ChartPull.pull L π) h with
    map_smul' r s := by
      change pullSection (ChartPull.pull L π) h (algebraMap R Γ(X, U) r • s) =
        algebraMap S Γ(Y, V) (algebraMap R S r) • pullSection (ChartPull.pull L π) h s
      rw [pullSection_smul, appLE_base_algebraMap w] }

theorem isBaseChange_scalarPullSection (hL : L.IsLB)
    (H : IsPullback π g f (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : V = π ⁻¹ᵁ U) :
    letI := sectionBaseModule f (toMod L) U
    letI := sectionBaseModule g (toMod (L.pull π)) V
    letI : Module R Γ(toMod (L.pull π), V) := Module.compHom _ (algebraMap R S)
    letI : IsScalarTower R S Γ(toMod (L.pull π), V) := .of_algebraMap_smul fun _ _ => rfl
    IsBaseChange S (scalarPullSection L H.w hV.le) := by
  let A := Γ(X, U)
  let B := Γ(Y, V)
  let F := Γ(toMod L, U)
  let G := Γ(toMod (L.pull π), V)
  letI : Algebra R A := sectionAlgebra f U
  letI : Algebra S B := sectionAlgebra g V
  letI : Algebra A B := (π.appLE U V hV.le).hom.toAlgebra
  letI : Algebra R B := ((algebraMap S B).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S B := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R A B := .of_algebraMap_eq fun r =>
    (appLE_base_algebraMap H.w hV.le r).symm
  letI : Algebra.IsPushout R S A B :=
    CommRingCat.isPushout_iff_isPushout.mp (isPushout_sectionAlgebra H hU hV)
  letI : Module R F := sectionBaseModule f (toMod L) U
  letI : Module S G := sectionBaseModule g (toMod (L.pull π)) V
  letI : Module R G := Module.compHom _ (algebraMap R S)
  letI : Module A G := Module.compHom _ (algebraMap A B)
  letI : IsScalarTower R A F := .of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower S B G := .of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower A B G := .of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower R S G := .of_algebraMap_smul fun _ _ => rfl
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hV' : IsAffineOpen V := hV ▸ hU.preimage π
  let e := (isBaseChange_pullSection hL hU hV' hV.le).equiv
  refine IsBaseChange.of_equiv
    ((Algebra.IsPushout.cancelBaseChange R S A B F).symm ≪≫ₗ e.restrictScalars S) fun x => ?_
  simp only [LinearEquiv.trans_apply, Algebra.IsPushout.cancelBaseChange_symm_tmul,
    map_one, LinearEquiv.restrictScalars_apply]
  exact ((isBaseChange_pullSection hL hU hV' hV.le).equiv_tmul (1 : B) x).trans (one_smul B _)

end GlobalTheory.LineBundleSections
