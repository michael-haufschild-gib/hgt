import GaloisForLFunctions.HTGeometry.PolarizedExactnessHorizonRelativeConnesPhaseLaw

/-!
# Quotient form of the dual-number residue sequence

Reduction modulo the square-zero socle is an exact local quotient: the doubled horizon modulo its
infinitesimal conormal direction is the residue field.
-/

namespace GaloisForLFunctions.HTGeometry

section Residue

variable {K : Type*} [Field K]

local instance dualNumberResidueModuleQuotient : Module (DualNumber K) K :=
  Module.compHom K (TrivSqZeroExt.fstHom K K K).toRingHom

/-- The socle inclusion and reduction map form an exact local residue sequence. -/
theorem dualNumberSocleResidue_exact :
    Function.Exact (dualNumberSocleInclusion (K := K)) (dualNumberResidue (K := K)) := by
  rw [LinearMap.exact_iff]
  exact (dualNumberSocle_range_eq_residue_ker (K := K)).symm

/-- Reducing modulo the square-zero socle identifies the local quotient with its residue field. -/
noncomputable def dualNumberResidueQuotientEquiv :
    (DualNumber K ⧸ LinearMap.range (dualNumberSocleInclusion (K := K))) ≃ₗ[DualNumber K] K :=
  (dualNumberSocleResidue_exact (K := K)).linearEquivOfSurjective
    (dualNumberResidue_surjective (K := K))

/-- The quotient equivalence is represented by the reduction map. -/
theorem dualNumberResidueQuotientEquiv_mk (x : DualNumber K) :
    dualNumberResidueQuotientEquiv (K := K) (Submodule.Quotient.mk x) =
      dualNumberResidue x :=
  rfl

end Residue

end GaloisForLFunctions.HTGeometry
