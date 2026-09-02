import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite morphisms from finite section maps on affine restrictions

This file packages the compatibility between a scheme morphism's section map on an affine open
and the global-section map of its restriction to that open.  Mathlib represents the two rings by
definitionally different open-subscheme section objects; the canonical `topIso` isomorphisms
identify them.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

/-- If an affine morphism has a finite section map on an affine target open, its restriction to
that open is a finite morphism. -/
theorem isFinite_restrict_of_finite_app {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (U : Y.Opens) (hU : IsAffineOpen U)
    (hf : RingHom.Finite (f.app U).hom) : IsFinite (f ∣_ U) := by
  letI : IsAffine U := hU
  letI : IsAffine (f ⁻¹ᵁ U) := IsAffineHom.isAffine_preimage U hU
  apply (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).2
  constructor
  · infer_instance
  · let e : Arrow.mk (f ∣_ U).appTop ≅ Arrow.mk (f.app U) :=
      Arrow.isoMk U.topIso (f ⁻¹ᵁ U).topIso (by
        change U.topIso.hom ≫ f.app U =
          (f ∣_ U).appTop ≫ (f ⁻¹ᵁ U).topIso.hom
        rw [morphismRestrict_appTop]
        simp only [Scheme.Opens.topIso_hom]
        change Y.presheaf.map _ ≫ f.app U =
          (f.app (U.ι ''ᵁ ⊤) ≫ _) ≫ _
        rw [f.naturality (eqToHom U.ι_image_top.symm).op]
        rw [Category.assoc]
        congr 1
        calc
          _ = X.presheaf.map
              ((eqToHom (image_morphismRestrict_preimage f U ⊤)).op ≫
                (eqToHom (f ⁻¹ᵁ U).ι_image_top.symm).op) := by
            exact congrArg X.presheaf.map (Subsingleton.elim _ _)
          _ = _ := X.presheaf.map_comp _ _)
    exact (RingHom.finite_respectsIso.arrow_mk_iso_iff e).2 hf

/-- Finiteness can be checked from finite section maps on any affine open cover of the target. -/
theorem isFinite_of_iSup_eq_top_finite_app {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    {ι : Sort*} (U : ι → Y.Opens) (hU : ⨆ i, U i = ⊤)
    (hAffine : ∀ i, IsAffineOpen (U i))
    (hFinite : ∀ i, RingHom.Finite (f.app (U i)).hom) : IsFinite f := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) U hU]
  intro i
  exact isFinite_restrict_of_finite_app f (U i) (hAffine i) (hFinite i)

end

end GaloisForLFunctions.HTGeometry
