import GaloisForLFunctions.HTGeometry.NormalizedMomentQuantumVariance

/-!
# Matrix-mechanics interface for normalized moment states

A nonzero vacuum mass is packaged as part of a moment state. The existing normalized expectation,
centering, variance, and pure-state quantum Fisher laws then become premise-free matrix-mechanics
statements for every polynomial observable.
-/

open Polynomial

namespace HTGeometry

noncomputable section

/-- Moment sequence packaged with the nondegenerate vacuum needed for normalization. -/
structure MomentMechanicsState where
  sequence : ℕ → ℝ
  vacuumMass_ne : sequence 0 ≠ 0

/-- Every packaged moment-mechanics state has unit vacuum expectation. -/
theorem momentMechanics_normalizedExpectation_one (S : MomentMechanicsState) :
    momentNormalizedExpectation S.sequence (1 : Polynomial ℝ) = 1 :=
  momentNormalizedExpectation_one S.sequence S.vacuumMass_ne

/-- Canonical centering gives zero expectation in every packaged moment-mechanics state. -/
theorem momentMechanics_centeredExpectation_zero
    (S : MomentMechanicsState) (p : Polynomial ℝ) :
    momentNormalizedExpectation S.sequence
      (momentVacuumCenteredPolynomial S.sequence p) = 0 :=
  momentNormalizedExpectation_centered S.sequence S.vacuumMass_ne p

/-- The centered observable's second moment is exactly its normalized variance. -/
theorem momentMechanics_centeredSecondMoment_eq_variance
    (S : MomentMechanicsState) (p : Polynomial ℝ) :
    momentNormalizedExpectation S.sequence
      ((momentVacuumCenteredPolynomial S.sequence p) ^ 2) =
        momentNormalizedVariance S.sequence p :=
  momentNormalizedExpectation_centered_sq S.sequence S.vacuumMass_ne p

/-- Pure-state quantum Fisher value is four times moment-mechanics variance. -/
theorem momentMechanics_quantumFisher_eq_four_variance
    (S : MomentMechanicsState) (p : Polynomial ℝ) :
    pureStateQuantumFisherValue (S.sequence 0)
        (momentFunctional S.sequence p) (momentFunctional S.sequence (p ^ 2)) =
      4 * momentNormalizedVariance S.sequence p :=
  pureStateQuantumFisherValue_moment_eq_four_mul_normalizedVariance
    S.sequence S.vacuumMass_ne p

end

end HTGeometry
