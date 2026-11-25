import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.AffineBaseChangeSectionRings
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeFormsPullback

/-! Affine rectangles in a fibre product have the tensor product of the two section rings. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace GlobalTheory.SchemeCohomology

variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}
  {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
  {p : Z ⟶ X} {q : Z ⟶ Y}

theorem isAffineOpen_product (H : IsPullback p q f g)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V) := by
  haveI : IsAffine (⊤ : (Spec (CommRingCat.of R)).Opens).toScheme := isAffineOpen_top _
  haveI : IsAffine U.toScheme := hU
  haveI : IsAffine V.toScheme := hV
  exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := V) (UX := U)
    le_top le_top rfl).isoPullback.hom

/-- Algebra map on sections followed by restriction to a smaller open. -/
def sectionPullbackLE (h : p ≫ f = q ≫ g) {V : Y.Opens} {W : Z.Opens} (hW : W ≤ q ⁻¹ᵁ V) :
    SectionRing g V →ₐ[R] SectionRing (p ≫ f) W :=
  (sectionRes (p ≫ f) (homOfLE hW)).comp (sectionPullback h.symm V)

theorem sectionPullbackLE_apply (h : p ≫ f = q ≫ g) {V : Y.Opens} {W : Z.Opens}
    (hW : W ≤ q ⁻¹ᵁ V) (v : SectionRing g V) :
    sectionPullbackLE h hW v = q.appLE V W hW v := by
  rfl

variable (H : IsPullback p q f g) (U : X.Opens) (V : Y.Opens)

private def tensorSections :
    SectionRing f U ⊗[R] SectionRing g V →ₐ[R] SectionRing (p ≫ f) (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V) :=
  Algebra.TensorProduct.productMap
    (sectionPullbackLE (p := p) (f := f) (q := p) (g := f) rfl inf_le_left)
    (sectionPullbackLE H.w inf_le_right)

include H in
/-- The projections on an affine rectangle give a pushout of its section rings. -/
theorem isPushout_productSections (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsPushout (CommRingCat.ofHom (algebraMap R (SectionRing f U)))
      (CommRingCat.ofHom (algebraMap R (SectionRing g V)))
      (p.appLE U (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V) inf_le_left)
      (q.appLE V (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V) inf_le_right) := by
  let W := p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V
  have hp := (isIso_pushoutSection_iff H (US := ⊤) (UT := V) (UX := U) le_top le_top rfl).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) hV hU)
  refine hp.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change _ ≫ 𝟙 Γ(X, U) = (Scheme.ΓSpecIso _).hom ≫
      (Scheme.ΓSpecIso _).inv ≫ f.appLE ⊤ U le_top
    simp
  · change _ ≫ 𝟙 Γ(Y, V) = (Scheme.ΓSpecIso _).hom ≫
      (Scheme.ΓSpecIso _).inv ≫ g.appLE ⊤ V le_top
    simp
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm

private theorem tensorSections_bijective (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Function.Bijective (tensorSections H U V) := by
  let W := p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V
  let A := SectionRing f U
  let B := SectionRing g V
  let l : A →ₐ[R] SectionRing (p ≫ f) W :=
    sectionPullbackLE (p := p) (f := f) (q := p) (g := f) rfl inf_le_left
  let r : B →ₐ[R] SectionRing (p ≫ f) W := sectionPullbackLE H.w inf_le_right
  have h := isPushout_productSections H U V hU hV
  have hT := CommRingCat.isPushout_tensorProduct R A B
  let e := hT.isoIsPushout _ _ h
  have he : e.hom = CommRingCat.ofHom (tensorSections H U V).toRingHom := by
    refine hT.hom_ext ?_ ?_
    · refine (hT.inl_isoIsPushout_hom _ _ h).trans ?_
      ext x
      change l x = (Algebra.TensorProduct.productMap l r) (x ⊗ₜ[R] (1 : B))
      exact (Algebra.TensorProduct.productMap_left_apply l r x).symm
    · refine (hT.inr_isoIsPushout_hom _ _ h).trans ?_
      ext x
      change r x = (Algebra.TensorProduct.productMap l r) ((1 : A) ⊗ₜ[R] x)
      exact (Algebra.TensorProduct.productMap_right_apply l r x).symm
  have hb := ConcreteCategory.bijective_of_isIso e.hom
  rw [he] at hb
  exact hb

/-- Sections on an affine rectangle identify with the tensor product of the factors. -/
def productSectionsEquiv (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    SectionRing f U ⊗[R] SectionRing g V ≃ₐ[R] SectionRing (p ≫ f) (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V) :=
  AlgEquiv.ofBijective (tensorSections H U V) (tensorSections_bijective H U V hU hV)

theorem productSectionsEquiv_tmul (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (a : SectionRing f U) (b : SectionRing g V) :
    productSectionsEquiv H U V hU hV (a ⊗ₜ[R] b) =
      p.appLE U _ inf_le_left a * q.appLE V _ inf_le_right b := rfl

end GlobalTheory.SchemeCohomology
