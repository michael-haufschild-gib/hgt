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

variable {R : Type*} [Ring R]

/-- Two-outcome pinching deletes departure from the measured sector. -/
theorem twoOutcomeLowerTransition_pinching_eq_zero
    {P : R} (hP : IsIdempotentElem P) (X : R) :
    twoOutcomeLowerTransition P (twoOutcomePinching P X) = 0 := by
  have hPP : P * P = P := hP
  have hco : (1 - P) * P = 0 := by noncomm_ring [hPP]
  simp only [twoOutcomeLowerTransition, twoOutcomePinching]
  have hfirst : (1 - P) * (P * X * P) * P = 0 := by
    calc
      (1 - P) * (P * X * P) * P = ((1 - P) * P) * X * P * P := by
        noncomm_ring
      _ = 0 := by rw [hco]; simp
  have hsecond : (1 - P) * ((1 - P) * X * (1 - P)) * P = 0 := by
    calc
      (1 - P) * ((1 - P) * X * (1 - P)) * P =
          (1 - P) * (1 - P) * X * ((1 - P) * P) := by noncomm_ring
      _ = 0 := by rw [hco]; simp
  rw [mul_add, add_mul, hfirst, hsecond, add_zero]

/-- Two-outcome pinching also deletes return from the complementary sector. -/
theorem twoOutcomeUpperTransition_pinching_eq_zero
    {P : R} (hP : IsIdempotentElem P) (X : R) :
    twoOutcomeUpperTransition P (twoOutcomePinching P X) = 0 := by
  have hPP : P * P = P := hP
  have hoc : P * (1 - P) = 0 := by noncomm_ring [hPP]
  simp only [twoOutcomeUpperTransition, twoOutcomePinching]
  have hfirst : P * (P * X * P) * (1 - P) = 0 := by
    calc
      P * (P * X * P) * (1 - P) = P * P * X * (P * (1 - P)) := by
        noncomm_ring
      _ = 0 := by rw [hoc]; simp
  have hsecond : P * ((1 - P) * X * (1 - P)) * (1 - P) = 0 := by
    calc
      P * ((1 - P) * X * (1 - P)) * (1 - P) =
          (P * (1 - P)) * X * (1 - P) * (1 - P) := by noncomm_ring
      _ = 0 := by rw [hoc]; simp
  rw [mul_add, add_mul, hfirst, hsecond, add_zero]

/-- Every two-outcome pinched observable commutes with the measured idempotent. -/
theorem twoOutcomePinching_commutes
    {P : R} (hP : IsIdempotentElem P) (X : R) :
    P * twoOutcomePinching P X = twoOutcomePinching P X * P := by
  have hPP : P * P = P := hP
  have hco : (1 - P) * P = 0 := by noncomm_ring [hPP]
  have hoc : P * (1 - P) = 0 := by noncomm_ring [hPP]
  simp only [twoOutcomePinching]
  calc
    P * (P * X * P + (1 - P) * X * (1 - P)) = P * X * P := by
      rw [mul_add]
      have hleft : P * (P * X * P) = P * X * P := by
        calc
          P * (P * X * P) = (P * P) * X * P := by noncomm_ring
          _ = P * X * P := by rw [hPP]
      have hright : P * ((1 - P) * X * (1 - P)) = 0 := by
        calc
          P * ((1 - P) * X * (1 - P)) =
              (P * (1 - P)) * X * (1 - P) := by noncomm_ring
          _ = 0 := by rw [hoc]; simp
      rw [hleft, hright, add_zero]
    _ = (P * X * P + (1 - P) * X * (1 - P)) * P := by
      rw [add_mul]
      have hleft : (P * X * P) * P = P * X * P := by
        calc
          (P * X * P) * P = P * X * (P * P) := by noncomm_ring
          _ = P * X * P := by rw [hPP]
      have hright : ((1 - P) * X * (1 - P)) * P = 0 := by
        calc
          ((1 - P) * X * (1 - P)) * P =
              (1 - P) * X * ((1 - P) * P) := by noncomm_ring
          _ = 0 := by rw [hco]; simp
      rw [hleft, hright, add_zero]

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
