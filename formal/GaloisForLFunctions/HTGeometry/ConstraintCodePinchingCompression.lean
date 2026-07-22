import GaloisForLFunctions.HTGeometry.ConstraintCodeReducingSubspace
import GaloisForLFunctions.HTGeometry.TwoOutcomePinchingKadison

/-!
# Pinched observables erase adjoint constraint sandwiches

A nonselective two-outcome measurement deletes both off-diagonal blocks of an observable relative
to its measured projector.  Consequently the pinched observable preserves the measured sector and
commutes with the projector without either fact being assumed.

Combining this measurement identity with the reducing-subspace constraint API gives an exact
hypothesis-free leakage consumer: if a self-adjoint constraint vanishes on a self-adjoint code
projection, then every pinched observable has zero compressed adjoint constraint sandwich.

This is the static algebra of measurement and code compression.  It does not interpret the
projector index or the pinching operation as temporal evolution.
-/

namespace HTGeometry

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **Pinched constraint-sandwich discharge.**  Measurement supplies the no-departure premise
automatically, so a self-adjoint constraint killed on one side of a self-adjoint code projection
has zero adjoint sandwich after pinching every observable. -/
theorem selfAdjointConstraint_twoOutcomePinching_adjointSandwich_compression_eq_zero
    (P C X : E →L[𝕜] E)
    (hP2 : IsIdempotentElem P) (hP : IsSelfAdjoint P)
    (hC : IsSelfAdjoint C) (hPC : P * C = 0) :
    P * ((twoOutcomePinching P X).adjoint * C * twoOutcomePinching P X) * P = 0 := by
  exact selfAdjointConstraint_adjointSandwich_compression_eq_zero_of_noDeparture
    P C (twoOutcomePinching P X) hP hC hPC
      (twoOutcomeLowerTransition_pinching_eq_zero hP2 X)

end

end HTGeometry
