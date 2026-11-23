import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverRationalForms
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineFormsSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ModuleCechComparison

/-! Restriction of relative forms on affine intersections agrees with inclusion
of their realizations in the exterior algebra of the function field. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HTGeometry
open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
  {s : X ⟶ Spec (CommRingCat.of K)} [Algebra K X.functionField] [Smooth s]
  {ι : Type} {U : ι → X.Opens} {B : Finset ι → Subalgebra K X.functionField}

/-- The realization of an affine form is the map on forms induced by the
generic germ of its section ring. -/
theorem IsAffCover.rationalFormsEquiv_apply_coe (h : IsAffCover s U B)
    {I : Finset ι} (hI : I.Nonempty) (p : ℕ) (ω : FormsOn s (I.inf U) p) :
    (h.rationalFormsEquiv I hI p ω : DR K X.functionField) =
      (ExteriorDifferentials.map ((B I).val.comp (h.sectionEquiv I hI).toAlgHom) p ω :
        DR K X.functionField) := by
  letI := h.isFractionRing I hI
  letI := h.smooth I hI
  change genericForm K X.functionField (B I) p
    (ExteriorDifferentials.map (h.sectionEquiv I hI).toAlgHom p ω) = _
  rw [genericForm_apply, ExteriorDifferentials.map_comp]

/-- Generic realizations commute with restriction to a smaller affine intersection. -/
theorem IsAffCover.rationalFormsEquiv_res (h : IsAffCover s U B)
    {I J : Finset ι} (hI : I.Nonempty) (hIJ : I ⊆ J) (p : ℕ)
    (ω : FormsOn s (I.inf U) p) :
    (h.rationalFormsEquiv J (hI.mono hIJ) p
      (ExteriorDifferentials.map (sectionRes s (homOfLE (Finset.inf_mono hIJ))) p ω) :
      DR K X.functionField) = h.rationalFormsEquiv I hI p ω := by
  let ρ : J.inf U ⟶ I.inf U := homOfLE (Finset.inf_mono hIJ)
  have hg : ((B J).val.comp (h.sectionEquiv J (hI.mono hIJ)).toAlgHom).comp
      (sectionRes s ρ) = (B I).val.comp (h.sectionEquiv I hI).toAlgHom := by
    ext a
    change (h.sectionEquiv J (hI.mono hIJ) (sectionRes s ρ a) : X.functionField) =
      (h.sectionEquiv I hI a : X.functionField)
    rw [h.sectionEquiv_apply_coe, h.sectionEquiv_apply_coe]
    exact X.presheaf.germ_res_apply ρ (genericPoint X) (h.ne J) a
  rw [h.rationalFormsEquiv_apply_coe, h.rationalFormsEquiv_apply_coe,
    ← ExteriorDifferentials.map_comp, hg]

variable [DecidableEq ι] [LinearOrder ι]

abbrev IsAffCover.formCechDatum (_h : IsAffCover s U B) (p : ℕ) :=
  sheafCech ((SheafOfModules.toSheaf X.ringCatSheaf).obj (relativeForms s p)) ⊤ U

private def coverInterIso (I : Finset ι) : I.inf U ≅ coverInter ⊤ U I :=
  eqToIso (top_inf_eq (I.inf U)).symm

/-- Sections of the form sheaf on a nonempty intersection, as rational forms. -/
def IsAffCover.sectionRationalForms (h : IsAffCover s U B)
    {I : Finset ι} (hI : I.Nonempty) (p : ℕ) :
    (h.formCechDatum p).obj I ≃+ omB K X.functionField (B I) p :=
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj (relativeForms s p)
  let e := F.1.mapIso (coverInterIso (U := U) I).op
  e.addCommGroupIsoToAddEquiv.trans
    ((affineFormsSections s p (h.affine I hI)).symm.toAddEquiv.trans
      (h.rationalFormsEquiv I hI p).toAddEquiv)

omit [DecidableEq ι] [LinearOrder ι] in
theorem IsAffCover.sectionRationalForms_res (h : IsAffCover s U B)
    {I J : Finset ι} (hI : I.Nonempty) (hIJ : I ⊆ J) (p : ℕ) (x : (h.formCechDatum p).obj I) :
    (h.sectionRationalForms (hI.mono hIJ) p ((h.formCechDatum p).res hIJ x) :
      DR K X.functionField) = h.sectionRationalForms hI p x := by
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj (relativeForms s p)
  let eI := (F.1.mapIso (coverInterIso (U := U) I).op).addCommGroupIsoToAddEquiv
  let eJ := (F.1.mapIso (coverInterIso (U := U) J).op).addCommGroupIsoToAddEquiv
  let ρ : J.inf U ⟶ I.inf U := homOfLE (Finset.inf_mono hIJ)
  have hcomm : eJ ((h.formCechDatum p).res hIJ x) =
      (relativeForms s p).presheaf.map ρ.op (eI x) := by
    change F.1.map (coverInterIso (U := U) J).hom.op
      (F.1.map (homOfLE (coverInter_anti (V := ⊤) (U := U) hIJ)).op x) =
      F.1.map ρ.op (F.1.map (coverInterIso (U := U) I).hom.op x)
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 2
  let ω := (affineFormsSections s p (h.affine I hI)).symm (eI x)
  have hω : formsOnToSections s p (I.inf U) ω = eI x :=
    (affineFormsSections s p (h.affine I hI)).apply_symm_apply _
  have hω' : (affineFormsSections s p (h.affine J (hI.mono hIJ))).symm
      (eJ ((h.formCechDatum p).res hIJ x)) = ExteriorDifferentials.map (sectionRes s ρ) p ω := by
    apply (affineFormsSections s p (h.affine J (hI.mono hIJ))).injective
    rw [LinearEquiv.apply_symm_apply, affineFormsSections_apply, ← formsOnToSections_res, hω, hcomm]
  change (h.rationalFormsEquiv J (hI.mono hIJ) p
    ((affineFormsSections s p (h.affine J (hI.mono hIJ))).symm
      (eJ ((h.formCechDatum p).res hIJ x))) : DR K X.functionField) =
    h.rationalFormsEquiv I hI p ω
  rw [hω']
  exact h.rationalFormsEquiv_res hI hIJ p ω

omit [DecidableEq ι] [LinearOrder ι] in
theorem IsAffCover.sectionRationalForms_scale (h : IsAffCover s U B)
    {I : Finset ι} (hI : I.Nonempty) (p : ℕ) (r : K) (x : (h.formCechDatum p).obj I) :
    letI := sectionAlgebra s ⊤
    h.sectionRationalForms hI p
      ((globalSectionEnd (relativeForms s p) (algebraMap K Γ(X, ⊤) r)).app
        (coverInter ⊤ U I) x) = r • h.sectionRationalForms hI p x := by
  letI := sectionAlgebra s ⊤
  let W := coverInter ⊤ U I
  let M := relativeForms s p
  let j := (coverInterIso (U := U) I).hom
  letI := sectionAlgebra s W
  letI := sectionAlgebra s (I.inf U)
  let xW : Γ(M, W) := x
  let x' : Γ(M, I.inf U) := M.presheaf.map j.op xW
  have hr : restrictGlobal X W (algebraMap K Γ(X, ⊤) r) =
      algebraMap K Γ(X, W) r := (sectionRes s (homOfLE (le_top : W ≤ ⊤))).commutes r
  rw [globalSectionEnd_app, hr]
  let L := (affineFormsSections s p (h.affine I hI)).symm
  change h.rationalFormsEquiv I hI p (L (M.presheaf.map j.op
    (algebraMap K Γ(X, W) r • xW))) =
    r • h.rationalFormsEquiv I hI p (L x')
  rw [M.map_smul j, show X.presheaf.map j.op (algebraMap K Γ(X, W) r) =
    algebraMap K Γ(X, I.inf U) r from (sectionRes s j).commutes r]
  have hL := L.map_smul (algebraMap K (SectionRing s (I.inf U)) r) x'
  exact (congrArg (h.rationalFormsEquiv I hI p) hL).trans
    ((h.rationalFormsEquiv I hI p).map_smul r (L x'))

end GlobalTheory.PD
