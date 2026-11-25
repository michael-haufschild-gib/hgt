import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeForms
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! The ring of an affine open commutes with pullback of its affine base. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory.SchemeCohomology

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  {X Y : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of S)}
  {π : Y ⟶ X}

theorem appLE_base_algebraMap
    (w : π ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
    {U : X.Opens} {V : Y.Opens} (h : V ≤ π ⁻¹ᵁ U) (r : R) :
    letI := sectionAlgebra f U
    letI := sectionAlgebra g V
    π.appLE U V h (algebraMap R Γ(X, U) r) = algebraMap S Γ(Y, V) (algebraMap R S r) := by
  let b : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec.map b).appLE ⊤ ⊤ (by simp) =
      b ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv := by
    simpa only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.preimage_top] using
      (Scheme.ΓSpecIso_inv_naturality b).symm
  have c : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U (by simp)) ≫
      π.appLE U V h = b ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ g.appLE ⊤ V (by simp) := by
    rw [Category.assoc, Scheme.Hom.appLE_comp_appLE, w,
      ← Scheme.Hom.appLE_comp_appLE g (Spec.map b) ⊤ ⊤ V (by simp) (by simp)]
    rw [← Category.assoc, e, Category.assoc]
  exact congrArg (fun q : CommRingCat.of R ⟶ Γ(Y, V) => q r) c

/-- Affine sections of a scheme pullback form the pushout of the section rings. -/
theorem isPushout_sectionAlgebra
    (H : IsPullback π g f (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : V = π ⁻¹ᵁ U) :
    letI := sectionAlgebra f U
    letI := sectionAlgebra g V
    IsPushout (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (algebraMap R Γ(X, U)))
      (CommRingCat.ofHom (algebraMap S Γ(Y, V))) (π.appLE U V hV.le) := by
  have hv : V = π ⁻¹ᵁ U ⊓ g ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of S)).Opens) := by
    simpa only [Scheme.Hom.preimage_top, inf_top_eq] using hV
  have hp := isIso_pushoutSection_of_isAffineOpen (US := ⊤) (UT := ⊤) H
    (by simp) (by simp) hv (isAffineOpen_top _) (isAffineOpen_top _) hU
  have po := (isIso_pushoutSection_iff H (by simp) (by simp) hv).mp hp
  refine po.flip.of_iso (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · change f.appLE ⊤ U _ ≫ 𝟙 Γ(X, U) = (Scheme.ΓSpecIso _).hom ≫
      (Scheme.ΓSpecIso _).inv ≫ f.appLE ⊤ U _
    simp
  · change g.appLE ⊤ V _ ≫ 𝟙 Γ(Y, V) = (Scheme.ΓSpecIso _).hom ≫
      (Scheme.ΓSpecIso _).inv ≫ g.appLE ⊤ V _
    simp
  · simp

end GlobalTheory.SchemeCohomology
