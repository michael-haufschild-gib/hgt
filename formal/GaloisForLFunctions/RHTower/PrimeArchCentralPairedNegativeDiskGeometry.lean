import GaloisForLFunctions.RHTower.PrimeArchCentralPairedDiagonalAlgebra

/-!
# Exact negative-phase disk for a line-conjugate reciprocal-square pair

The paired imaginary response has a positive denominator and a factor `2 * Im w`.
Its remaining numerator is the squared-distance expression below. Thus an off-line
pair's possible negative-phase set is a disk in the squared spectral coordinate `w`.
This is an atomwise localization, not a positivity theorem for the complete trace.
-/

open Complex

namespace RHTower

noncomputable section

/-- The open scaled disk where one line-conjugate pair's phase numerator is negative. -/
def centralPairedScaledNegativeDisk (w lam : ℂ) : Prop :=
  (Complex.normSq lam * w.re - lam.re) ^ (2 : ℕ) +
      (Complex.normSq lam * w.im) ^ (2 : ℕ) < lam.im ^ (2 : ℕ)

/-- Exact square completion of the Route-Q line-conjugate phase numerator.
For `lam ≠ 0`, the disk center is `Re (1/lam)` and its radius is
`|Im (1/lam)|`; its boundary passes through the two pair poles. -/
theorem centralPaired_barrier_eq_scaled_disk (w lam : ℂ) :
    Complex.normSq lam *
        ((1 - w.re * lam.re) ^ (2 : ℕ) +
          (w.re * lam.im) ^ (2 : ℕ) +
          w.im ^ (2 : ℕ) * Complex.normSq lam) -
      2 * lam.im ^ (2 : ℕ) =
    (Complex.normSq lam * w.re - lam.re) ^ (2 : ℕ) +
      (Complex.normSq lam * w.im) ^ (2 : ℕ) -
      lam.im ^ (2 : ℕ) := by
  simp only [Complex.normSq_apply]
  ring

end
end RHTower
