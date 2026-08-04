import GaloisForLFunctions.RHTower.Sieve.EulerLogCompare
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# The logarithm of zeta against the prime sum

Mathlib's Euler product writes `ζ(s)` as `exp` of the sum of Euler logarithms, so the modulus of
`ζ` is the exponential of the real part of that sum.  Comparing it termwise with the leading term
gives, for `re s > 1`,

`|log‖ζ(s)‖ − ∑'_p Re(p^{-s})| ≤ ∑'_p ‖p^{-s}‖² < 2`,

with `Re(p^{-s}) = cos(t log p)/p^σ`.  The bound is uniform in the frequency, so a lower bound for
`‖ζ‖` on the one-line transfers directly to the prime sum that the Halász estimate needs.
-/

namespace RHTower.Sieve

open Complex

/-- The modulus of zeta is the exponential of the real part of the Euler logarithm sum. -/
theorem norm_riemannZeta_eq_exp_re {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖
      = Real.exp ((∑' p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))).re) := by
  rw [← riemannZeta_eulerProduct_exp_log hs, Complex.norm_exp]

/-- The logarithm of the modulus of zeta is the real part of the Euler logarithm sum. -/
theorem log_norm_riemannZeta_eq_re {s : ℂ} (hs : 1 < s.re) :
    Real.log ‖riemannZeta s‖
      = (∑' p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))).re := by
  rw [norm_riemannZeta_eq_exp_re hs, Real.log_exp]

/-- **The logarithm of zeta against the prime sum.** -/
theorem abs_log_norm_riemannZeta_sub_tsum_re_le {s : ℂ} (hs : 1 < s.re) :
    |Real.log ‖riemannZeta s‖ - ∑' p : Nat.Primes, (((p : ℕ) : ℂ) ^ (-s)).re|
      ≤ ∑' p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 := by
  have hcpow := summable_prime_cpow hs
  have hre : (∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-s)).re
      = ∑' p : Nat.Primes, (((p : ℕ) : ℂ) ^ (-s)).re := Complex.re_tsum hcpow
  rw [log_norm_riemannZeta_eq_re hs, ← hre, ← Complex.sub_re]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  exact norm_tsum_euler_log_sub_tsum_le hs

end RHTower.Sieve
