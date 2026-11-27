import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProjectiveSectionMorphisms

/-! Coordinate surjectivity after identifying the affine base with a spectrum. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open GlobalTheory.SchemeCohomology

namespace GlobalTheory.ProjectiveSections

variable {R : Type} [CommRing R] {X Y : Scheme.{0}}

/-- An affine base isomorphism changes the coefficient ring by a ring isomorphism. -/
theorem sectionAlgebra_comp_iso (q : X ⟶ Y) (e : Y ⟶ Spec (CommRingCat.of R))
    [IsIso e] (W : X.Opens) {σ : Type} (r : σ → Γ(X, W))
    (hr : Function.Surjective (MvPolynomial.eval₂Hom (q.appLE ⊤ W le_top).hom r)) :
    letI := sectionAlgebra (q ≫ e) W
    Function.Surjective (MvPolynomial.eval₂Hom (algebraMap R Γ(X, W)) r) := by
  letI := sectionAlgebra (q ≫ e) W
  let b : CommRingCat.of R ⟶ Γ(Y, ⊤) := (Scheme.ΓSpecIso _).inv ≫ e.appLE ⊤ ⊤ le_top
  haveI : IsIso b := by
    have he : e.appLE ⊤ ⊤ (by simp) = e.appTop := by
      simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.preimage_top]
    haveI : IsIso e.appTop := inferInstanceAs (IsIso (e.app ⊤))
    dsimp only [b]
    rw [he]
    infer_instance
  have hc : b ≫ q.appLE ⊤ W le_top =
      (Scheme.ΓSpecIso _).inv ≫ (q ≫ e).appLE ⊤ W le_top :=
    (Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (Scheme.Hom.appLE_comp_appLE q e ⊤ ⊤ W le_top le_top))
  have hp : MvPolynomial.eval₂Hom (algebraMap R Γ(X, W)) r =
      (MvPolynomial.eval₂Hom (q.appLE ⊤ W le_top).hom r).comp (MvPolynomial.map b.hom) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, MvPolynomial.map_C]
      exact (ConcreteCategory.congr_hom hc x).symm
    · intro j
      simp only [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, MvPolynomial.map_X]
  rw [hp]
  exact hr.comp (MvPolynomial.map_surjective _ (ConcreteCategory.bijective_of_isIso b).2)

end GlobalTheory.ProjectiveSections
