import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RelativeFormsTrace

/-! Relative differential forms pull back functorially along morphisms over the base. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace GlobalTheory.SchemeCohomology

universe u

variable {k : Type u} [CommRing k] {X Y Z : Scheme.{u}}
  {s : X ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}
  {v : Z ⟶ Spec (CommRingCat.of k)} {f : Y ⟶ X} {g : Z ⟶ Y}

private theorem sectionPullback_comp (hf : f ≫ s = t) (hg : g ≫ t = v)
    (hgf : (g ≫ f) ≫ s = v) (U : X.Opens) :
    (sectionPullback hg (f ⁻¹ᵁ U)).comp (sectionPullback hf U) = sectionPullback hgf U := by
  ext r
  exact (ConcreteCategory.congr_hom (Scheme.Hom.comp_app g f U) r).symm

/-- Pullback for a composite agrees with the successive pullbacks under the
canonical identification of the direct images. -/
theorem relativeFormsPullback_comp (hf : f ≫ s = t) (hg : g ≫ t = v)
    (hgf : (g ≫ f) ≫ s = v) (p : ℕ) :
    relativeFormsPullback hf p ≫ (Scheme.Modules.pushforward f).map (relativeFormsPullback hg p) ≫
      (Scheme.Modules.pushforwardComp g f).hom.app (relativeForms v p) =
      relativeFormsPullback hgf p := by
  apply moduleHom_ext_affine
  intro U hU x
  obtain ⟨ω, rfl⟩ := (affineFormsSections s p hU).surjective x
  change (relativeFormsPullback hg p).app (f ⁻¹ᵁ U)
      ((relativeFormsPullback hf p).app U (formsOnToSections s p U ω)) =
    (relativeFormsPullback hgf p).app U (formsOnToSections s p U ω)
  rw [relativeFormsPullback_app hf, relativeFormsPullback_app hg, relativeFormsPullback_app hgf,
    ← ExteriorDifferentials.map_comp, sectionPullback_comp hf hg hgf]
  rfl

end GlobalTheory.SchemeCohomology
