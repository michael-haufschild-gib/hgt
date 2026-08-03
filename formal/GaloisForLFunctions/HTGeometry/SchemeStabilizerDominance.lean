import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Scheme stabilizers and split dominance

Scheme-theoretic stabilizers are equalizers of an orbit map and the constant map at the point.
They are closed whenever the acted-on scheme is separated, with no affineness hypothesis.  The
file also supplies the scheme-level dominance bridge used by split jet evaluations: a morphism
with a right inverse is surjective and therefore dominant.
-/

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {G X Y : Scheme.{u}}

/-- Scheme-theoretic stabilizer of a point, presented as the equalizer of its orbit map and the
constant map at that point. -/
noncomputable def schemeStabilizer (orbit constant : G ⟶ X) : Scheme.{u} :=
  equalizer orbit constant

/-- Closed inclusion of the scheme-theoretic stabilizer into the acting scheme. -/
noncomputable def schemeStabilizerInclusion (orbit constant : G ⟶ X) :
    schemeStabilizer orbit constant ⟶ G :=
  equalizer.ι orbit constant

theorem schemeStabilizerInclusion_condition (orbit constant : G ⟶ X) :
    schemeStabilizerInclusion orbit constant ≫ orbit =
      schemeStabilizerInclusion orbit constant ≫ constant :=
  equalizer.condition orbit constant

/-- Stabilizers into a separated scheme are closed, without an affineness hypothesis. -/
instance schemeStabilizerInclusion_isClosedImmersion (orbit constant : G ⟶ X)
    [X.IsSeparated] : IsClosedImmersion (schemeStabilizerInclusion orbit constant) := by
  change IsClosedImmersion (equalizer.ι orbit constant)
  infer_instance

/-- A scheme morphism admitting a right inverse is surjective. -/
theorem Scheme.Hom.surjective_of_comp_eq_id (f : X ⟶ Y) (s : Y ⟶ X)
    (h : s ≫ f = 𝟙 Y) : Function.Surjective f := by
  intro y
  refine ⟨s y, ?_⟩
  rw [← Scheme.Hom.comp_apply, h]
  rfl

/-- A split epimorphism of schemes is dominant. -/
theorem Scheme.Hom.isDominant_of_comp_eq_id (f : X ⟶ Y) (s : Y ⟶ X)
    (h : s ≫ f = 𝟙 Y) : IsDominant f := by
  letI : Surjective f := ⟨f.surjective_of_comp_eq_id s h⟩
  infer_instance

end AlgebraicGeometry
