import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ClopenSectionTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RelativeFormsTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineTraceTower

/-! Trace of relative forms splits over a finite disjoint open cover of the source. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory.SchemeCohomology

variable {K : Type} [CommRing K] {X Y : Scheme.{0}} {J : Type} [Fintype J]
  {s : X ⟶ Spec (CommRingCat.of K)} {t : Y ⟶ Spec (CommRingCat.of K)}
  {f : Y ⟶ X} [IsFinite f] [Etale f]

/-- Restriction to an open part of the source on direct images of forms. -/
def sourcePartForms (t : Y ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ X) (V : Y.Opens) (p : ℕ) :
    (Scheme.Modules.pushforward f).obj (relativeForms t p) ⟶
      (Scheme.Modules.pushforward (V.ι ≫ f)).obj (relativeForms (V.ι ≫ t) p) :=
  (Scheme.Modules.pushforward f).map (relativeFormsPullback (f := V.ι) rfl p) ≫
    (Scheme.Modules.pushforwardComp V.ι f).hom.app (relativeForms (V.ι ≫ t) p)

private theorem sum_app {F G : X.Modules} (S : Finset J) (a : J → (F ⟶ G))
    (U : X.Opens) (x : Γ(F, U)) : (∑ j ∈ S, a j).app U x = ∑ j ∈ S, (a j).app U x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Scheme.Modules.Hom.zero_app]; rfl
  | insert j S hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Scheme.Modules.Hom.add_app, ← ih]
    rfl

private theorem sourcePartForms_app_smul (hf : f ≫ s = t) (V : Y.Opens)
    (hg : (V.ι ≫ f) ≫ s = V.ι ≫ t) (U : X.Opens) (p : ℕ)
    (b : SectionRing t (f ⁻¹ᵁ U)) (ω : FormsOn s U p) :
    (sourcePartForms t f V p).app U
        (formsOnToSections t p (f ⁻¹ᵁ U) (b • ExteriorDifferentials.map (sectionPullback hf U) p ω)) =
      formsOnToSections (V.ι ≫ t) p ((V.ι ≫ f) ⁻¹ᵁ U)
        (sectionPullback (f := V.ι) rfl (f ⁻¹ᵁ U) b •
          ExteriorDifferentials.map (sectionPullback hg U) p ω) := by
  change (relativeFormsPullback (f := V.ι) (s := t) rfl p).app (f ⁻¹ᵁ U)
      (formsOnToSections t p (f ⁻¹ᵁ U) (b • ExteriorDifferentials.map (sectionPullback hf U) p ω)) = _
  rw [relativeFormsPullback_app, LinearMap.map_smulₛₗ, ← ExteriorDifferentials.map_comp]
  have hs : (sectionPullback (f := V.ι) rfl (f ⁻¹ᵁ U)).comp (sectionPullback hf U) =
      sectionPullback hg U := by
    ext a
    exact (ConcreteCategory.congr_hom (Scheme.Hom.comp_app V.ι f U) a).symm
  rw [hs]

/-- Trace of forms on the direct image is the sum of the traces after
restriction to the parts. -/
theorem relativeFormsTrace_eq_sum_clopen (hf : f ≫ s = t) (W : J → Y.Opens)
    (hdis : ∀ i j, i ≠ j → W i ⊓ W j = ⊥) (hcov : iSup W = ⊤)
    [∀ j, IsFinite ((W j).ι ≫ f)] [∀ j, Etale ((W j).ι ≫ f)]
    (p : ℕ) :
    relativeFormsTrace hf p = ∑ j, sourcePartForms t f (W j) p ≫
      relativeFormsTrace (f := (W j).ι ≫ f) (by rw [Category.assoc, hf]) p := by
  let hg (j : J) : ((W j).ι ≫ f) ≫ s = (W j).ι ≫ t := by rw [Category.assoc, hf]
  let a (j : J) := sourcePartForms t f (W j) p ≫ relativeFormsTrace (hg j) p
  apply moduleHom_ext_affine
  intro U hU x
  obtain ⟨ω, rfl⟩ := (affineFormsSections t p (hU.preimage f)).surjective x
  refine affineEtaleForms_induction hf hU p
    (P := fun ω => (relativeFormsTrace hf p).app U (formsOnToSections t p (f ⁻¹ᵁ U) ω) =
      (∑ j, a j).app U (formsOnToSections t p (f ⁻¹ᵁ U) ω)) ?_ ?_ ?_ ω
  · simp only [map_zero]
  · intro u v hu hv
    simp only [map_add, hu, hv]
  · intro b ξ
    rw [relativeFormsTrace_app, affineFormTrace_smul_pullback, sum_app]
    have ht (j : J) :
        (a j).app U
          (formsOnToSections t p (f ⁻¹ᵁ U) (b • ExteriorDifferentials.map (sectionPullback hf U) p ξ)) =
          formsOnToSections s p U
            (affineSectionTrace (f := (W j).ι ≫ f) s ((W j).ι ≫ t) hU
              (((W j).ι.app (f ⁻¹ᵁ U)).hom b) • ξ) := by
      change (relativeFormsTrace (hg j) p).app U ((sourcePartForms t f (W j) p).app U _) = _
      rw [sourcePartForms_app_smul hf _ (hg j), relativeFormsTrace_app,
        affineFormTrace_smul_pullback]
      rfl
    simp only [ht, affineSectionTrace_eq_sum_clopen (f := f) W hdis hcov hU b,
      Finset.sum_smul, map_sum]

end GlobalTheory.SchemeCohomology
