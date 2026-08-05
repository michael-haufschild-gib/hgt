import GaloisForLFunctions.HTGeometry.SourceOddQuinticSuccessorModulus

/-!
# Source-projective equivalence of odd quintics is reflexive

The diagonal reparametrization at unit scales is the identity on coefficients, so every odd quintic
is source-projectively equivalent to itself and the invariant cross-product law is not a statement
about an empty relation.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-- The unit reparametrization is the identity. -/
theorem sourceOddQuinticReparam_one (q : SourceOddQuinticCoefficients K) :
    sourceOddQuinticReparam 1 1 1 q = q := by
  cases q
  simp [sourceOddQuinticReparam]

/-- Source-projective equivalence is reflexive. -/
theorem sourceProjectivelyEquivalentOddQuintic_refl (q : SourceOddQuinticCoefficients K) :
    SourceProjectivelyEquivalentOddQuintic q q :=
  ⟨1, 1, 1, one_ne_zero, one_ne_zero, one_ne_zero, (sourceOddQuinticReparam_one q).symm⟩

end GaloisForLFunctions.HTGeometry
