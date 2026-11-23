import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverFormRestrictions

/-! The rational realization of a regular form is given by the generic
germ of the section ring of its open. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HTGeometry
open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
  {s : X ⟶ Spec (CommRingCat.of K)} [Algebra K X.functionField]

private abbrev BaseCompatible := algebraMap K X.functionField =
  @algebraMap K X.functionField _ _ (sectionFunctionFieldAlgebra s)

/-- The generic germ on an open containing the generic point, with a
compatible choice of the base-field algebra. -/
def genericSectionAlg (hs : BaseCompatible (s := s))
    {W : X.Opens} (hW : genericPoint X ∈ W) : SectionRing s W →ₐ[K] X.functionField where
  toRingHom := (X.presheaf.germ W _ hW).hom
  commutes' c := by
    letI : Nonempty W := ⟨⟨genericPoint X, hW⟩⟩
    have hc : (X.presheaf.germ W _ hW).hom (algebraMap K (SectionRing s W) c) =
        @algebraMap K X.functionField _ _ (sectionFunctionFieldAlgebra s) c := by
      letI := sectionFunctionFieldAlgebra s
      exact (sectionToFunctionField s W).commutes c
    exact hc.trans (RingHom.congr_fun hs.symm c)

theorem genericSectionAlg_res (hs : BaseCompatible (s := s))
    {W V : X.Opens} (j : V ⟶ W) (hW : genericPoint X ∈ W) (hV : genericPoint X ∈ V) :
    (genericSectionAlg hs hV).comp (sectionRes s j) = genericSectionAlg hs hW := by
  apply AlgHom.ext
  intro a
  exact X.presheaf.germ_res_apply j (genericPoint X) hV a

variable [Smooth s] {ι : Type} {U : ι → X.Opens} {B : Finset ι → Subalgebra K X.functionField}

theorem IsAffCover.sectionRationalForms_formsOn (h : IsAffCover s U B)
    {I : Finset ι} (hI : I.Nonempty) (p : ℕ)
    (ω : FormsOn s (coverInter ⊤ U I) p) :
    (h.sectionRationalForms hI p (formsOnToSections s p (coverInter ⊤ U I) ω) :
      DR K X.functionField) =
    (ExteriorDifferentials.map
      (genericSectionAlg h.alg (W := coverInter ⊤ U I) ⟨trivial, h.ne I⟩) p ω :
      DR K X.functionField) := by
  let W := coverInter ⊤ U I
  let ρ : I.inf U ⟶ W := eqToHom (top_inf_eq (I.inf U)).symm
  let P := relativeForms s p
  let e := affineFormsSections s p (h.affine I hI)
  have he : e.symm (P.presheaf.map ρ.op (formsOnToSections s p W ω)) =
      ExteriorDifferentials.map (sectionRes s ρ) p ω := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, affineFormsSections_apply, ← formsOnToSections_res]
  let g := (B I).val.comp (h.sectionEquiv I hI).toAlgHom
  have hg : g.comp (sectionRes s ρ) = genericSectionAlg h.alg (show genericPoint X ∈ W from ⟨trivial, h.ne I⟩) := by
    apply AlgHom.ext
    intro a
    change (h.sectionEquiv I hI (sectionRes s ρ a) : X.functionField) =
      (X.presheaf.germ W _ (show genericPoint X ∈ W from ⟨trivial, h.ne I⟩)).hom a
    rw [h.sectionEquiv_apply_coe]
    exact X.presheaf.germ_res_apply ρ (genericPoint X) (h.ne I) a
  change (h.rationalFormsEquiv I hI p
    (e.symm (P.presheaf.map ρ.op (formsOnToSections s p W ω))) : DR K X.functionField) = _
  rw [he, h.rationalFormsEquiv_apply_coe, ← ExteriorDifferentials.map_comp]
  exact congrArg (fun a : SectionRing s W →ₐ[K] X.functionField =>
    (ExteriorDifferentials.map a p ω : DR K X.functionField)) hg


/-- Restricting a section to another affine intersection preserves its
generic form. -/
theorem IsAffCover.sectionRationalForms_restriction (h : IsAffCover s U B)
    {κ : Type} {V : κ → X.Opens} {C : Finset κ → Subalgebra K X.functionField}
    (g : IsAffCover s V C) {I : Finset ι} {J : Finset κ}
    (hI : I.Nonempty) (hJ : J.Nonempty) (p : ℕ)
    (j : coverInter ⊤ V J ⟶ coverInter ⊤ U I) (x : (h.formCechDatum p).obj I) :
    (g.sectionRationalForms hJ p ((relativeForms s p).presheaf.map j.op x) :
      DR K X.functionField) = h.sectionRationalForms hI p x := by
  let W := coverInter ⊤ U I
  have hW : IsAffineOpen W := by simpa only [W, coverInter, top_inf_eq] using h.affine I hI
  obtain ⟨ω, hω⟩ := (affineFormsSections s p hW).surjective x
  change formsOnToSections s p W ω = x at hω
  rw [← hω, formsOnToSections_res, g.sectionRationalForms_formsOn, h.sectionRationalForms_formsOn,
    ← ExteriorDifferentials.map_comp]
  exact congrArg (fun a : SectionRing s W →ₐ[K] X.functionField =>
    (ExteriorDifferentials.map a p ω : DR K X.functionField))
    (genericSectionAlg_res h.alg j ⟨trivial, h.ne I⟩ ⟨trivial, g.ne J⟩)

end GlobalTheory.PD
