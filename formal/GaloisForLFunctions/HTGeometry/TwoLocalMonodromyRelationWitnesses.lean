import GaloisForLFunctions.HTGeometry.TwoLocalMonodromyRelationRigidity

/-!
# The two-local monodromy relation holds for the zero coefficients

The relation is a linear functional of the coefficient family, so the zero family satisfies it on
every realized permutation.  The rigidity theorem therefore says exactly that the zero relation is
the only invariant one, rather than that none exists.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The zero coefficient family satisfies the common-base two-local relation. -/
theorem commonBaseTwoLocalMonodromyInvariantRelation_zero (m : ℕ) :
    CommonBaseTwoLocalMonodromyInvariantRelation m 0 := by
  intro perm _
  rw [commonBaseTwoLocalSpectralRelation]
  simp

end GaloisForLFunctions.HTGeometry
