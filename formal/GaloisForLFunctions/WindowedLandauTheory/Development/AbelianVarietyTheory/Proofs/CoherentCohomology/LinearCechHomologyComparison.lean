import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FlatLineBundleCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ModuleCechComparison
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! The scalar-linear Čech complex computes the native Čech cohomology of a scheme module. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HTGeometry
open GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
  (F : X.Modules) {ι : Type} [DecidableEq ι] [LinearOrder ι] (U : ι → X.Opens)

private abbrev forgetModule := forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}

private abbrev C := cech f F U
private abbrev D := sectionDatum F U
private abbrev A := ((forgetModule (R := R)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (C f F U)
private abbrev B := (D F U).cochainComplex

private def degreeIso (n : ℕ) : (A f F U).X n ≅ (B F U).X n where
  hom := AddCommGrpCat.ofHom
    { toFun := fun x => ⟨x.1, x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  inv := AddCommGrpCat.ofHom
    { toFun := fun x => ⟨x.1, x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  hom_inv_id := AddCommGrpCat.ext (fun _ => Subtype.ext rfl)
  inv_hom_id := AddCommGrpCat.ext (fun _ => Subtype.ext rfl)

private def complexIso : A f F U ≅ B F U :=
  HomologicalComplex.Hom.isoOfComponents (degreeIso f F U) (by
    rintro n _ rfl
    apply AddCommGrpCat.ext
    intro x
    change (B F U).d n (n + 1) ((degreeIso f F U n).hom x) =
      (degreeIso f F U (n + 1)).hom ((A f F U).d n (n + 1) x)
    rw [FinsetCechDatum.cochainComplex_d_apply]
    simp only [A, Functor.mapHomologicalComplex_obj_d, C, cech, FinsetCechDatum.linearComplex,
      CochainComplex.of_d]
    rfl)

private def scalarMap (r : R) : B F U ⟶ B F U :=
  letI := sectionAlgebra f ⊤
  let G := SheafOfModules.toSheaf X.ringCatSheaf
  (sheafCechMap (G.map (globalSectionEnd F (algebraMap R Γ(X, ⊤) r))) ⊤ U).cochainMap

private theorem scalar_on_sections (r : R) (s : Finset ι) (x : (D F U).obj s) :
    letI := sectionAlgebra f ⊤
    letI := sectionDatumModule f F U s
    (globalSectionEnd F (algebraMap R Γ(X, ⊤) r)).app (coverInter ⊤ U s) x = r • x := by
  let W := coverInter ⊤ U s
  letI := sectionAlgebra f ⊤
  letI := sectionAlgebra f W
  change (globalSectionEnd F (algebraMap R Γ(X, ⊤) r)).app W (show Γ(F, W) from x) =
    algebraMap R Γ(X, W) r • (show Γ(F, W) from x)
  rw [globalSectionEnd_app]
  exact congrArg (fun a : Γ(X, W) => a • (show Γ(F, W) from x))
    ((sectionRes f (homOfLE (le_top : W ≤ ⊤))).commutes r)

private theorem scalar_commutes (r : R) (n : ℕ) :
    ((C f F U).sc n).mapNatTrans (ModuleCat.smulNatTrans R r) ≫
        ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) n).mapIso
          (complexIso f F U)).hom =
      ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) n).mapIso
        (complexIso f F U)).hom ≫
        (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) n).map (scalarMap f F U r) := by
  apply ShortComplex.hom_ext <;> apply AddCommGrpCat.ext <;> intro x <;>
    apply Subtype.ext <;> funext s <;> exact (scalar_on_sections f F U r s (x.1 s)).symm

/-- Forgetting scalars gives the ordinary Čech complex, and the comparison on homology is linear. -/
def cechCohomologyEquiv (n : ℕ) :
    letI := sectionAlgebra f ⊤
    let H := ModuleCechCohomology ⊤ U F n
    letI := Module.compHom H (algebraMap R Γ(X, ⊤))
    (C f F U).homology n ≃ₗ[R] H := by
  letI := sectionAlgebra f ⊤
  let H := ModuleCechCohomology ⊤ U F n
  letI := Module.compHom H (algebraMap R Γ(X, ⊤))
  let S := (C f F U).sc n
  let G := forgetModule (R := R)
  let e := (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) n).mapIso
    (complexIso f F U)
  let e₀ := S.mapHomologyIso G
  let e₁ := (ShortComplex.homologyFunctor AddCommGrpCat).mapIso e
  let h : G.obj ((C f F U).homology n) ≅ (B F U).homology n := e₀.symm ≪≫ e₁
  let a : (C f F U).homology n →ₗ[R] H :=
    { h.hom.hom with
      map_smul' r x := by
        let τ := ModuleCat.smulNatTrans R r
        let α := S.mapNatTrans τ
        let β := (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) n).map
          (scalarMap f F U r)
        have hn : τ.app (S.homology) ≫ e₀.inv = e₀.inv ≫ ShortComplex.homologyMap α := by
          rw [NatTrans.app_homology τ S]
          change (e₀.inv ≫ ShortComplex.homologyMap α ≫ e₀.hom) ≫ e₀.inv = _
          simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
        have hm : ShortComplex.homologyMap α ≫ e₁.hom =
            e₁.hom ≫ ShortComplex.homologyMap β := by
          exact ((ShortComplex.homologyFunctor AddCommGrpCat).map_comp α e.hom).symm.trans
            ((congrArg (ShortComplex.homologyFunctor AddCommGrpCat).map
              (scalar_commutes f F U r n)).trans
              ((ShortComplex.homologyFunctor AddCommGrpCat).map_comp e.hom β))
        have hs : τ.app (S.homology) ≫ h.hom = h.hom ≫ ShortComplex.homologyMap β := calc
          _ = (τ.app (S.homology) ≫ e₀.inv) ≫ e₁.hom := (Category.assoc _ _ _).symm
          _ = (e₀.inv ≫ ShortComplex.homologyMap α) ≫ e₁.hom := congrArg (· ≫ e₁.hom) hn
          _ = e₀.inv ≫ (ShortComplex.homologyMap α ≫ e₁.hom) := Category.assoc _ _ _
          _ = e₀.inv ≫ (e₁.hom ≫ ShortComplex.homologyMap β) := congrArg (e₀.inv ≫ ·) hm
          _ = _ := (Category.assoc _ _ _).symm
        exact ConcreteCategory.congr_hom hs x }
  exact LinearEquiv.ofBijective a (ConcreteCategory.bijective_of_isIso h.hom)

end GlobalTheory.LineBundleSections
