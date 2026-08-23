import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# A polynomial with constant term one is a non-zero-divisor

If `s` has constant term `1` and `s * R = 0`, then every coefficient of `R` vanishes, by strong
induction on the index: in the `n`-th coefficient of the product only the pair `(0, n)` survives
once all lower coefficients of `R` are known to vanish.
-/

namespace HTGeometry

open Polynomial

variable {A : Type*} [CommRing A]

/-- A polynomial with constant term one is a non-zero-divisor. -/
theorem polynomial_coeffZero_one_mem_nonZeroDivisors {s : Polynomial A} (hs : s.coeff 0 = 1) :
    s ∈ nonZeroDivisors (Polynomial A) := by
  have key : ∀ R : Polynomial A, R * s = 0 → R = 0 := by
    intro R hR
    have hcoeff : ∀ n : ℕ, R.coeff n = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
          have hzero : (R * s).coeff n = 0 := by rw [hR, Polynomial.coeff_zero]
          rw [Polynomial.coeff_mul] at hzero
          have hsum : ∀ q ∈ Finset.antidiagonal n, q ≠ (n, 0) →
              R.coeff q.1 * s.coeff q.2 = 0 := by
            rintro ⟨i, j⟩ hij hne
            rw [Finset.mem_antidiagonal] at hij
            have hij' : i < n := by
              rcases Nat.lt_or_ge i n with h | h
              · exact h
              · exact absurd (Prod.ext (by omega) (by omega)) hne
            rw [ih i hij', zero_mul]
          rw [Finset.sum_eq_single (n, 0) hsum] at hzero
          · rw [hs, mul_one] at hzero
            exact hzero
          · intro hc
            exact absurd (Finset.mem_antidiagonal.2 (by omega)) hc
    exact Polynomial.ext fun n => by rw [hcoeff n, Polynomial.coeff_zero]
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun R hR => key R (by rw [mul_comm]; exact hR), key⟩

end HTGeometry
