/-
# Closed quarter-power Dirichlet-character second moment

This module specializes the finite quadratic Dirichlet-character second
moment to the fixed exponent `1 / 4`.  It keeps the divisor estimate fully
internal, yielding a source-usable closed theorem without an incoming
positivity premise for an arbitrary epsilon.

No RH, GRH, zero-density hypothesis, or undischarged divisor estimate is
used.
-/

import GaloisForLFunctions.RHTower.DirichletCharacterSecondMomentDivisorBound

open Finset

noncomputable section

namespace RHTower
namespace OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- Closed quarter-power form of the finite interval quadratic
Dirichlet-character second moment.  The positive exponent condition required
by the divisor bound is discharged internally. -/
theorem quadratic_intervalShiftSum_normSq_le_divisorQuarter [DecidableEq I]
    (P : OddPrimeFamily I) (M : ℕ) (b : ℕ → ℂ) :
    ∑ x : ZMod P.modulus, Complex.normSq (quadraticIntervalShiftSum P M b x) ≤
      ((M : ℝ) * (Sieve.divisorBoundConst (1 / 4 : ℝ) * (P.modulus : ℝ) ^ (1 / 4 : ℝ)) +
        (P.modulus : ℝ)) * ∑ k ∈ Finset.Icc 1 M, ‖b k‖ ^ (2 : ℕ) := by
  exact quadratic_intervalShiftSum_normSq_le_divisorRpow P M b (by norm_num)

end OddPrimeFamily
end RHTower
