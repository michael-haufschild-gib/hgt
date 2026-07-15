import GaloisForLFunctions.RHTower.SoninLogConstraintCompression
import GaloisForLFunctions.HTGeometry.ConstraintCodePinchingCompression

/-!
# Pinched Sonin observables erase the scattering-constraint sandwich

The invariant logarithmic Sonin scattering sector is selected by an orthogonal projection, and
the scattering constraint `S - 1` is self-adjoint.  The general reducing-subspace theorem therefore
turns one-sided preservation of this sector into vanishing of the compressed adjoint constraint
sandwich.

Two-outcome pinching by the same invariant-sector projection supplies preservation automatically.
Hence every Sonin observable, after its static invariant/anti-invariant measurement, has zero
compressed `A† (S-1) A` insertion with no additional commutation, leakage, or right-annihilation
hypothesis.
-/

open Complex

namespace RHTower

noncomputable section

/-- One-sided preservation of the invariant Sonin sector is sufficient to erase the adjoint
scattering-constraint sandwich.  The opposite leakage block and opposite constraint relation are
derived from self-adjointness. -/
theorem soninLogConstraintAdjointSandwich_compression_eq_zero_of_noDeparture
    (A : SoninL2 →L[ℂ] SoninL2)
    (hpreserve :
      (1 - soninLogFourierInvariantAverage) * A *
        soninLogFourierInvariantAverage = 0) :
    soninLogFourierInvariantAverage *
          (A.adjoint * (soninLogFourierScattering - 1) * A) *
        soninLogFourierInvariantAverage = 0 := by
  have hC : IsSelfAdjoint (soninLogFourierScattering - 1) :=
    soninLogFourierScattering_isSelfAdjoint.sub (by simp)
  exact HTGeometry.selfAdjointConstraint_adjointSandwich_compression_eq_zero_of_noDeparture
    soninLogFourierInvariantAverage (soninLogFourierScattering - 1) A
      soninLogFourierInvariantAverage_isSelfAdjoint hC
      (HTGeometry.finiteCyclicGaugeAverage_mul_constraint_eq_zero
        soninLogFourierScattering 2 soninLogFourierScattering_sq_eq_one)
      hpreserve

/-- **Measured Sonin constraint-sandwich collapse.**  Pinching an arbitrary Sonin observable by
the invariant-sector projection removes both scattering-sector transitions.  Its compressed
adjoint insertion of the logarithmic scattering constraint therefore vanishes with no premise on
the original observable. -/
theorem soninLogConstraintPinchedAdjointSandwich_compression_eq_zero
    (X : SoninL2 →L[ℂ] SoninL2) :
    soninLogFourierInvariantAverage *
          ((HTGeometry.twoOutcomePinching soninLogFourierInvariantAverage X).adjoint *
            (soninLogFourierScattering - 1) *
              HTGeometry.twoOutcomePinching soninLogFourierInvariantAverage X) *
        soninLogFourierInvariantAverage = 0 := by
  have hC : IsSelfAdjoint (soninLogFourierScattering - 1) :=
    soninLogFourierScattering_isSelfAdjoint.sub (by simp)
  exact HTGeometry.selfAdjointConstraint_twoOutcomePinching_adjointSandwich_compression_eq_zero
    soninLogFourierInvariantAverage (soninLogFourierScattering - 1) X
      soninLogFourierInvariantAverage_isIdempotentElem
      soninLogFourierInvariantAverage_isSelfAdjoint hC
      (HTGeometry.finiteCyclicGaugeAverage_mul_constraint_eq_zero
        soninLogFourierScattering 2 soninLogFourierScattering_sq_eq_one)

end

end RHTower
