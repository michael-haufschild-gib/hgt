import GaloisForLFunctions.RHTower.SoninLogCoordinateScattering
import GaloisForLFunctions.HTGeometry.ConstraintCodeCompression

/-!
# Sonin logarithmic-scattering constraint compression

The logarithmic Fourier invariant average compresses away the complete two-sided ideal generated
by the static Sonin scattering constraint.  Thus constraint-equivalent observables define the same
operator and the same matrix elements on the invariant Sonin sector.
-/

open Complex

namespace RHTower

noncomputable section

/-- Two Sonin observables equal modulo the logarithmic-scattering constraint ideal have identical
operators after compression to the invariant sector. -/
theorem soninLogFourierInvariantAverage_compression_congr_mod_constraintIdeal
    (A B L R : SoninL2 →L[ℂ] SoninL2)
    (hmod : B = A +
      ((soninLogFourierScattering - 1) * L +
        R * (soninLogFourierScattering - 1))) :
    soninLogFourierInvariantAverage * B * soninLogFourierInvariantAverage =
      soninLogFourierInvariantAverage * A * soninLogFourierInvariantAverage := by
  simpa only [soninLogFourierInvariantAverage] using
    HTGeometry.finiteCyclicGaugeAverage_compression_congr_mod_constraintTwoSidedIdeal
      soninLogFourierScattering A B L R 2
      soninLogFourierScattering_sq_eq_one hmod

/-- The corresponding physical-sector matrix elements are representative-independent for
arbitrary unprojected input vectors. -/
theorem inner_soninLogFourierInvariantAverage_congr_mod_constraintIdeal
    (A B L R : SoninL2 →L[ℂ] SoninL2)
    (hmod : B = A +
      ((soninLogFourierScattering - 1) * L +
        R * (soninLogFourierScattering - 1)))
    (φ ψ : SoninL2) :
    inner ℂ (soninLogFourierInvariantAverage φ)
        (B (soninLogFourierInvariantAverage ψ)) =
      inner ℂ (soninLogFourierInvariantAverage φ)
        (A (soninLogFourierInvariantAverage ψ)) := by
  simpa only [soninLogFourierInvariantAverage] using
    HTGeometry.finiteClock_matrixElement_congr_mod_constraintTwoSidedIdeal
      soninLogFourierScattering A B L R 2 two_ne_zero
      soninLogFourierScattering_adjoint_mul_self
      soninLogFourierScattering_sq_eq_one hmod φ ψ

end


end RHTower
