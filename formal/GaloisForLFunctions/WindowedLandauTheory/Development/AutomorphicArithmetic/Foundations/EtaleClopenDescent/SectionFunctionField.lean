import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeForms
import GaloisForLFunctions.HTGeometry.AlgebraicGroupGenericPoint

/-! The generic germ of a regular function preserves the base-field algebra
structure inherited from the structure morphism. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open GaloisForLFunctions.HTGeometry

namespace GlobalTheory.SchemeCohomology

variable {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]

/-- The function-field algebra of the scheme with its given structure morphism. -/
abbrev sectionFunctionFieldAlgebra (s : X ⟶ Spec (CommRingCat.of K)) :
    Algebra K X.functionField :=
  @overFunctionFieldAlgebra K _ (Over.mk s) ‹IsIntegral X›

/-- The generic germ as an algebra map over the base field. -/
def sectionToFunctionField (s : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) [Nonempty U] :
    letI := sectionFunctionFieldAlgebra s
    SectionRing s U →ₐ[K] X.functionField := by
  letI := sectionFunctionFieldAlgebra s
  refine { toRingHom := (X.germToFunctionField U).hom, commutes' := ?_ }
  intro c
  have hc : algebraMap K (SectionRing s U) c =
      X.presheaf.map (homOfLE le_top).op
        (s.appTop ((Scheme.ΓSpecIso (.of K)).inv c)) := rfl
  change X.germToFunctionField U (algebraMap K (SectionRing s U) c) = _
  rw [hc, ← CommRingCat.comp_apply, X.presheaf.germ_res,
    ← Scheme.Hom.functionFieldPullback_germ_appTop]
  change s.functionFieldPullback (StructureSheaf.toStalk K (genericPoint (Spec (.of K))) c) =
    s.functionFieldPullback (Scheme.specFunctionFieldAlgEquiv K c)
  rw [specFunctionFieldAlgEquiv_eq_toStalk]

end GlobalTheory.SchemeCohomology
