import GaloisForLFunctions.RHTower.Sieve.DivisorSwap

/-!
# Chebyshev's `ψ` through the Möbius function

The convolution identity `μ * log = Λ` expresses the von Mangoldt weight as a divisor sum.  Summed
against the divisor swap it turns Chebyshev's `ψ` into a Möbius-weighted sum of the log summatory,
and dually into a log-weighted sum of the Mertens function:

`ψ(N) = ∑_{d ≤ N} μ(d) ∑_{k ≤ N/d} log k`,   `ψ(N) = ∑_{d ≤ N} log d ∑_{k ≤ N/d} μ(k)`.

These are the two elementary bridges between the prime count and the Möbius function: the first
carries a cancellation hypothesis on `μ` into `ψ` (against Stirling for the inner sum), the second
carries prime information back to `μ`.  Both are exact finite identities — no estimate is made here.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- `Λ(n) = ∑_{d ∣ n} μ(d) log(n/d)`. -/
theorem vonMangoldt_eq_sum_moebius_mul_log (n : ℕ) :
    vonMangoldt n = ∑ d ∈ n.divisors, ((moebius d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ) := by
  have h := congrArg (fun F : ArithmeticFunction ℝ => F n)
    moebius_mul_log_eq_vonMangoldt
  simp only [mul_apply, intCoe_apply, log_apply] at h
  rw [← h, Nat.sum_divisorsAntidiagonal
    (f := fun a b => ((moebius a : ℤ) : ℝ) * Real.log (b : ℝ))]

/-- `Λ(n) = ∑_{d ∣ n} log d · μ(n/d)`. -/
theorem vonMangoldt_eq_sum_log_mul_moebius (n : ℕ) :
    vonMangoldt n = ∑ d ∈ n.divisors, Real.log (d : ℝ) * ((moebius (n / d) : ℤ) : ℝ) := by
  have h := congrArg (fun F : ArithmeticFunction ℝ => F n)
    (by rw [mul_comm]; exact moebius_mul_log_eq_vonMangoldt :
      (ArithmeticFunction.log * ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ))
        = vonMangoldt)
  simp only [mul_apply, intCoe_apply, log_apply] at h
  rw [← h, Nat.sum_divisorsAntidiagonal
    (f := fun a b => Real.log (a : ℝ) * ((moebius b : ℤ) : ℝ))]

/-- **Chebyshev's `ψ` as a Möbius-weighted log summatory**:
`ψ(N) = ∑_{d ≤ N} μ(d) ∑_{k ≤ N/d} log k`. -/
theorem sum_vonMangoldt_eq_moebius_logSummatory (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, vonMangoldt n
      = ∑ d ∈ Finset.Icc 1 N,
          ((moebius d : ℤ) : ℝ) * ∑ k ∈ Finset.Icc 1 (N / d), Real.log (k : ℝ) := by
  calc ∑ n ∈ Finset.Icc 1 N, vonMangoldt n
      = ∑ n ∈ Finset.Icc 1 N,
          ∑ d ∈ n.divisors, ((moebius d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ) :=
        Finset.sum_congr rfl fun n _ => vonMangoldt_eq_sum_moebius_mul_log n
    _ = ∑ d ∈ Finset.Icc 1 N,
          ∑ k ∈ Finset.Icc 1 (N / d), ((moebius d : ℤ) : ℝ) * Real.log (k : ℝ) :=
        sum_divisors_swap N fun d k => ((moebius d : ℤ) : ℝ) * Real.log (k : ℝ)
    _ = ∑ d ∈ Finset.Icc 1 N,
          ((moebius d : ℤ) : ℝ) * ∑ k ∈ Finset.Icc 1 (N / d), Real.log (k : ℝ) :=
        Finset.sum_congr rfl fun d _ => (Finset.mul_sum _ _ _).symm

/-- **Chebyshev's `ψ` as a log-weighted Mertens sum**:
`ψ(N) = ∑_{d ≤ N} log d ∑_{k ≤ N/d} μ(k)`. -/
theorem sum_vonMangoldt_eq_log_mertens (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, vonMangoldt n
      = ∑ d ∈ Finset.Icc 1 N,
          Real.log (d : ℝ) * ∑ k ∈ Finset.Icc 1 (N / d), ((moebius k : ℤ) : ℝ) := by
  calc ∑ n ∈ Finset.Icc 1 N, vonMangoldt n
      = ∑ n ∈ Finset.Icc 1 N,
          ∑ d ∈ n.divisors, Real.log (d : ℝ) * ((moebius (n / d) : ℤ) : ℝ) :=
        Finset.sum_congr rfl fun n _ => vonMangoldt_eq_sum_log_mul_moebius n
    _ = ∑ d ∈ Finset.Icc 1 N,
          ∑ k ∈ Finset.Icc 1 (N / d), Real.log (d : ℝ) * ((moebius k : ℤ) : ℝ) :=
        sum_divisors_swap N fun d k => Real.log (d : ℝ) * ((moebius k : ℤ) : ℝ)
    _ = ∑ d ∈ Finset.Icc 1 N,
          Real.log (d : ℝ) * ∑ k ∈ Finset.Icc 1 (N / d), ((moebius k : ℤ) : ℝ) :=
        Finset.sum_congr rfl fun d _ => (Finset.mul_sum _ _ _).symm

end RHTower.Sieve
