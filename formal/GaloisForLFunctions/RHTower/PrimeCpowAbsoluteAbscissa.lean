import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Absolute abscissa of the prime complex-power series

The prime series with term `p⁻ˢ` is absolutely summable exactly in the open
half-plane `Re s > 1`.  This exposes the elementary absolute-convergence
boundary shared by Euler-product and local-ratio constructions.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Complex

/-- The prime complex-power series is absolutely summable exactly for `Re s > 1`. -/
theorem summable_norm_primeCpow_neg_iff (s : ℂ) :
    Summable (fun p : Nat.Primes => ‖((p : ℕ) : ℂ) ^ (-s)‖) ↔ 1 < s.re := by
  have hnorm : (fun p : Nat.Primes => ‖((p : ℕ) : ℂ) ^ (-s)‖)
      = fun p : Nat.Primes => (p : ℝ) ^ (-s.re) := by
    funext p
    rw [Complex.norm_natCast_cpow_of_pos p.property.pos]
    simp
  rw [hnorm, Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

/-- On and to the left of `Re s = 1`, prime complex-power terms are not absolutely summable. -/
theorem not_summable_norm_primeCpow_neg_of_re_le_one {s : ℂ} (hs : s.re ≤ 1) :
    ¬ Summable (fun p : Nat.Primes => ‖((p : ℕ) : ℂ) ^ (-s)‖) := by
  intro hsum
  exact (not_lt_of_ge hs) ((summable_norm_primeCpow_neg_iff s).mp hsum)

end GaloisForLFunctions.RHTower

end
