import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverFormRestrictions
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalExteriorPullback

/-! Pullback of forms on affine intersections commutes with their generic realization. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  {s : X ⟶ Spec (CommRingCat.of K)} {t : Y ⟶ Spec (CommRingCat.of K)}
  [Algebra K X.functionField] [Algebra K Y.functionField] [Smooth s] [Smooth t]
  {ι κ : Type} {U : ι → X.Opens} {V : κ → Y.Opens}
  {A : Finset ι → Subalgebra K X.functionField} {B : Finset κ → Subalgebra K Y.functionField}
  {f : Y ⟶ X}

/-- Realization in the exterior algebra commutes with pullback to a refined affine chart. -/
theorem IsAffCover.rationalFormsEquiv_pullback (hX : IsAffCover s U A) (hY : IsAffCover t V B)
    (hf : f ≫ s = t) (ψ : X.functionField →ₐ[K] Y.functionField)
    (hψ : ∀ (W : X.Opens) (hW : genericPoint X ∈ W)
      (hW' : genericPoint Y ∈ f ⁻¹ᵁ W) (a : Γ(X, W)),
      ψ ((X.presheaf.germ W _ hW).hom a) = (Y.presheaf.germ (f ⁻¹ᵁ W) _ hW').hom ((f.app W).hom a))
    {I : Finset ι} {J : Finset κ} (hi : I.Nonempty) (hj : J.Nonempty)
    (hJV : J.inf V ≤ f ⁻¹ᵁ I.inf U) (p : ℕ) (ω : FormsOn s (I.inf U) p) :
    (hY.rationalFormsEquiv J hj p (ExteriorDifferentials.map
      ((sectionRes t (homOfLE hJV)).comp (sectionPullback hf (I.inf U))) p ω) :
      DR K Y.functionField) = pullbackDR ψ (hX.rationalFormsEquiv I hi p ω) := by
  let W := I.inf U
  let ρ : J.inf V ⟶ f ⁻¹ᵁ W := homOfLE hJV
  have hη : genericPoint Y ∈ f ⁻¹ᵁ W := hJV (hY.ne J)
  let x := (A I).val.comp (hX.sectionEquiv I hi).toAlgHom
  let y := (B J).val.comp (hY.sectionEquiv J hj).toAlgHom
  let g := (sectionRes t ρ).comp (sectionPullback hf W)
  have he : y.comp g = ψ.comp x := by
    apply AlgHom.ext
    intro a
    change (hY.sectionEquiv J hj (g a) : Y.functionField) =
      ψ (hX.sectionEquiv I hi a : X.functionField)
    rw [hY.sectionEquiv_apply_coe, hX.sectionEquiv_apply_coe, hψ W (hX.ne I) hη]
    exact Y.presheaf.germ_res_apply ρ (genericPoint Y) (hY.ne J) ((f.app W).hom a)
  rw [hY.rationalFormsEquiv_apply_coe, hX.rationalFormsEquiv_apply_coe, pullbackDR_degree,
    ← ExteriorDifferentials.map_comp, ← ExteriorDifferentials.map_comp]
  exact congrArg (fun a : SectionRing s W →ₐ[K] Y.functionField =>
    (ExteriorDifferentials.map a p ω : DR K Y.functionField)) he

end GlobalTheory.PD
