import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Algebra.Category.Ring.Constructions

/-! Restriction of an affine morphism to a smaller affine open is ring base change. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace GlobalTheory.SchemeCohomology

universe u

private theorem affineRestriction_isOpenImmersion {X : Scheme.{u}} {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : V ⟶ U) :
    IsOpenImmersion (Spec.map (X.presheaf.map i.op)) := by
  haveI : IsOpenImmersion (Spec.map (X.presheaf.map i.op) ≫ hU.fromSpec) := by
    rw [hU.map_fromSpec hV i.op]
    infer_instance
  exact IsOpenImmersion.of_comp _ hU.fromSpec

private theorem affineRestriction_opensRange {X : Scheme.{u}} {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : V ⟶ U) :
    letI := affineRestriction_isOpenImmersion hU hV i
    (Spec.map (X.presheaf.map i.op)).opensRange = hU.fromSpec ⁻¹ᵁ V := by
  letI := affineRestriction_isOpenImmersion hU hV i
  apply hU.fromSpec.image_injective
  change hU.fromSpec ''ᵁ (Spec.map (X.presheaf.map i.op)).opensRange =
    hU.fromSpec ''ᵁ (hU.fromSpec ⁻¹ᵁ V)
  have e : (Spec.map (X.presheaf.map i.op) ≫ hU.fromSpec).opensRange = V := by
    apply Opens.ext
    change Set.range (Spec.map (X.presheaf.map i.op) ≫ hU.fromSpec) = (V : Set X)
    rw [hU.map_fromSpec hV i.op]
    exact hV.range_fromSpec
  rw [← Scheme.Hom.opensRange_comp, e,
    Scheme.Hom.image_preimage_eq_opensRange_inf, hU.opensRange_fromSpec, inf_eq_right.mpr i.le]

/-- The square of section rings over nested affine opens is a pushout for an affine morphism. -/
theorem isPushout_affineSections {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : V ⟶ U) :
    IsPushout (f.app U) (X.presheaf.map i.op)
      (Y.presheaf.map ((Opens.map f.base).map i).op) (f.app V) := by
  let j := (Opens.map f.base).map i
  let r := X.presheaf.map i.op
  let r' := Y.presheaf.map j.op
  have hU' := hU.preimage f
  have hV' := hV.preimage f
  haveI := affineRestriction_isOpenImmersion hU hV i
  haveI := affineRestriction_isOpenImmersion hU' hV' j
  have H : IsPullback (Spec.map (f.app V)) (Spec.map r') (Spec.map r)
      (Spec.map (f.app U)) := by
    refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
    · have eq : r ≫ f.app V = f.app U ≫ r' := f.naturality i.op
      rw [← Spec.map_comp, ← Spec.map_comp, eq]
    · rw [affineRestriction_opensRange hU hV i, affineRestriction_opensRange hU' hV' j,
        ← Scheme.Hom.comp_preimage]
      have e := hU.SpecMap_appLE_fromSpec f hU' le_rfl
      rw [← Scheme.Hom.app_eq_appLE] at e
      rw [e, Scheme.Hom.comp_preimage]
  have h : IsPullback (f.app V).op r'.op r.op (f.app U).op :=
    H.of_map_of_faithful Scheme.Spec
  exact h.unop

end GlobalTheory.SchemeCohomology
