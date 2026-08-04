import GaloisForLFunctions.HTGeometry.DifferentialLurothCoefficient

/-!
# Stripping a separant power from a divisibility

An irreducible differential polynomial is prime, and it does not divide its own separant.  So a power
of the separant can be cancelled from any divisibility by it.

Reduction theorems deliver divisibility of a separant-weighted multiple; this is the step that removes
the weight, leaving divisibility of the object one actually cares about.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- **An irreducible divides a separant-weighted multiple only by dividing the multiple.** -/
theorem dvd_of_dvd_separant_pow_mul {A Q : DifferentialPolynomial Unit K}
    (hAvars : A.vars.Nonempty) (hAirreducible : Irreducible A) {e : ℕ}
    (hdvd : A ∣ scalarDifferentialPolynomialSeparant A ^ e * Q) :
    A ∣ Q := by
  classical
  have hprime : Prime A := hAirreducible.prime
  rcases hprime.dvd_mul.1 hdvd with hpow | hQ
  · exact absurd (hprime.dvd_of_dvd_pow hpow)
      (irreducible_not_dvd_scalarDifferentialPolynomialSeparant hAvars hAirreducible)
  · exact hQ

end

end GaloisForLFunctions
