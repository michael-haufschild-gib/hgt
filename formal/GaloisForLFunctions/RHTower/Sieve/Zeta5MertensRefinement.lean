import GaloisForLFunctions.RHTower.Sieve.MertensFirst
import GaloisForLFunctions.HTGeometry.Zeta5ElementaryTransfer

/-!
# The zeta-five factorial estimate in Mertens' first theorem

The factorial step of the existing prime-sum argument accepts the sharper
estimate from `Zeta5.Section6b`. This keeps its linear saving and exposes an
explicit finite-cutoff correction.
-/

namespace RHTower.Sieve

open Finset Nat

private theorem mertensFirst_upper_zeta5_aux {n : ℕ} (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ) ≤
      Real.log n + Real.log 4 - 1 + (Real.log n + 2) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcore := mertensFirst_upper_factorial_core n
  have hcheb := sum_log_primesLE_le n
  have hfac := GaloisForLFunctions.HTGeometry.zeta5_log_factorial_upper n
  have hmain : (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ))
      ≤ (n : ℝ) *
          (Real.log n + Real.log 4 - 1 + (Real.log n + 2) / n) := by
    have hidentity : (n : ℝ) *
        (Real.log n + Real.log 4 - 1 + (Real.log n + 2) / n) =
          (n : ℝ) * Real.log n + (n : ℝ) * Real.log 4 - n + Real.log n + 2 := by
      field_simp [hn0.ne']
      ring
    rw [hidentity]
    linarith
  exact le_of_mul_le_mul_left hmain hn0

/-- A finite-cutoff improvement of `mertensFirst_upper`, with no hypothesis
in its statement. The index is `n + 1` so its logarithms and quotient are
always in their positive domain. -/
theorem mertensFirst_upper_zeta5 (n : ℕ) :
    ∑ p ∈ Nat.primesLE (n + 1), Real.log p / (p : ℝ) ≤
      Real.log (n + 1) + Real.log 4 - 1 +
        (Real.log (n + 1) + 2) / (n + 1) := by
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
    (mertensFirst_upper_zeta5_aux (Nat.succ_le_succ (Nat.zero_le n)))

end RHTower.Sieve
