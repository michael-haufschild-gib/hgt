import GaloisForLFunctions.RHTower.SoninLogCoordinateScattering
import GaloisForLFunctions.HTGeometry.ConstraintIdealExcursion

/-!
# Sonin logarithmic-scattering constraint compression

The logarithmic Fourier invariant average compresses away every outer term with the static Sonin
scattering constraint at its left or right edge.  Thus observables differing by those terms define
the same operator and the same matrix elements on the invariant Sonin sector.  A genuine ideal
sandwich can survive, and its exact complement-sector factorization is recorded below.
-/

open Complex

namespace RHTower

noncomputable section

/-- Two Sonin observables differing by outer logarithmic-scattering constraint terms have
identical operators after compression to the invariant sector. -/
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

/-- A genuine sandwich in the Sonin scattering-constraint ideal need not disappear.  Its
compressed value is exactly the transition out of the invariant sector, followed by the
constraint, followed by the transition back. -/
theorem soninLogConstraintSandwich_compression_eq_complementExcursion
    (L R : SoninL2 →L[ℂ] SoninL2) :
    soninLogFourierInvariantAverage *
          (L * (soninLogFourierScattering - 1) * R) *
        soninLogFourierInvariantAverage =
      (soninLogFourierInvariantAverage * L *
          (1 - soninLogFourierInvariantAverage)) *
        (soninLogFourierScattering - 1) *
          ((1 - soninLogFourierInvariantAverage) * R *
            soninLogFourierInvariantAverage) := by
  exact HTGeometry.constraintSandwich_compression_eq_transitionExcursion
    soninLogFourierInvariantAverage (soninLogFourierScattering - 1) L R
    (HTGeometry.finiteCyclicGaugeAverage_mul_constraint_eq_zero
      soninLogFourierScattering 2 soninLogFourierScattering_sq_eq_one)
    (HTGeometry.constraint_mul_finiteCyclicGaugeAverage_eq_zero
      soninLogFourierScattering 2 soninLogFourierScattering_sq_eq_one)

end


end RHTower
