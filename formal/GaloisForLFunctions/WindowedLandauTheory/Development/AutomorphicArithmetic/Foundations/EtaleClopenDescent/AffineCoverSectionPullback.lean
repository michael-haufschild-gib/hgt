import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverGenericGerms
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverFormPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RelativeFormsTrace

/-! Pullback of a section on an affine intersection is computed by
pullback in the function fields. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HTGeometry
open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  {s : X ⟶ Spec (CommRingCat.of K)} {t : Y ⟶ Spec (CommRingCat.of K)}
  [Algebra K X.functionField] [Algebra K Y.functionField] [Smooth s] [Smooth t]
  {ι κ : Type} {U : ι → X.Opens} {V : κ → Y.Opens}
  {A : Finset ι → Subalgebra K X.functionField} {B : Finset κ → Subalgebra K Y.functionField}
  {f : Y ⟶ X}

theorem IsAffCover.sectionRationalForms_pullback (hX : IsAffCover s U A) (hY : IsAffCover t V B)
    (hf : f ≫ s = t) (ψ : X.functionField →ₐ[K] Y.functionField)
    (hψ : ∀ (W : X.Opens) (hW : genericPoint X ∈ W)
      (hW' : genericPoint Y ∈ f ⁻¹ᵁ W) (a : Γ(X, W)),
      ψ ((X.presheaf.germ W _ hW).hom a) = (Y.presheaf.germ (f ⁻¹ᵁ W) _ hW').hom ((f.app W).hom a))
    {I : Finset ι} {J : Finset κ} (hi : I.Nonempty) (hj : J.Nonempty)
    (hjv : coverInter ⊤ V J ≤ f ⁻¹ᵁ coverInter ⊤ U I) (p : ℕ)
    (x : (hX.formCechDatum p).obj I) :
    (hY.sectionRationalForms hj p ((relativeForms t p).presheaf.map (homOfLE hjv).op
        ((relativeFormsPullback hf p).app (coverInter ⊤ U I) x)) : DR K Y.functionField) =
      pullbackDR ψ (hX.sectionRationalForms hi p x) := by
  let W := coverInter ⊤ U I
  let Q := coverInter ⊤ V J
  let g : Q ⟶ f ⁻¹ᵁ W := homOfLE hjv
  have hw : IsAffineOpen W := by simpa only [W, coverInter, top_inf_eq] using hX.affine I hi
  obtain ⟨ω, hω⟩ := (affineFormsSections s p hw).surjective x
  change formsOnToSections s p W ω = x at hω
  have hηX : genericPoint X ∈ W := ⟨trivial, hX.ne I⟩
  have hηY : genericPoint Y ∈ Q := ⟨trivial, hY.ne J⟩
  have hη' : genericPoint Y ∈ f ⁻¹ᵁ W := hjv hηY
  have he : ((genericSectionAlg hY.alg hηY).comp (sectionRes t g)).comp (sectionPullback hf W) =
      ψ.comp (genericSectionAlg hX.alg hηX) := by
    apply AlgHom.ext
    intro a
    change (Y.presheaf.germ Q _ hηY).hom (sectionRes t g ((f.app W).hom a)) = _
    exact (Y.presheaf.germ_res_apply g (genericPoint Y) hηY ((f.app W).hom a)).trans
      (hψ W hηX hη' a).symm
  rw [← hω, relativeFormsPullback_app, formsOnToSections_res,
    hY.sectionRationalForms_formsOn, hX.sectionRationalForms_formsOn, pullbackDR_degree,
    ← ExteriorDifferentials.map_comp, ← ExteriorDifferentials.map_comp, ← ExteriorDifferentials.map_comp]
  exact congrArg (fun a : SectionRing s W →ₐ[K] Y.functionField =>
    (ExteriorDifferentials.map a p ω : DR K Y.functionField)) he

end GlobalTheory.PD
