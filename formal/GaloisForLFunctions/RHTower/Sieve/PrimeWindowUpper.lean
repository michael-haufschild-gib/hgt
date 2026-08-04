import GaloisForLFunctions.RHTower.Sieve.DivisorSquareSum
import GaloisForLFunctions.RHTower.Sieve.RoughCount

/-!
# The prime count of a window from above

A prime larger than `z` has no prime factor at most `z`, so it is coprime to the primorial `z#`.
The primes of a window therefore inject into its rough integers, and the Selberg upper bound
transfers verbatim:

`#{p ∈ (a, b] : p prime, p > z} ≤ 2(b − a)/log Y + (divisor error)`.

This is the source-side input of the matching step, where the target-side input is the block
lower bound.  Both are now statements about the same window.
-/

namespace RHTower.Sieve

open Finset Nat BoundingSieve

/-- A prime exceeding `z` is coprime to the primorial `z#`. -/
theorem coprime_primorial_of_prime {z p : ℕ} (hp : p.Prime) (hzp : z < p) :
    Nat.Coprime (primorial z) p := by
  rw [Nat.coprime_comm, coprime_primorial_iff]
  intro q hq hqp
  have hqprime : q.Prime := Nat.prime_of_mem_primesLE hq
  have hqz : q ≤ z := (Nat.mem_primesLE.mp hq).1
  have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hp).mp hqp
  omega

/-- The primes of a window above `z` inject into its rough integers. -/
theorem card_primes_Ioc_le_rough (a b z : ℕ) :
    (#{p ∈ Finset.Ioc a b | p.Prime ∧ z < p} : ℕ)
      ≤ (#{n ∈ Finset.Ioc a b | Nat.Coprime (primorial z) n} : ℕ) := by
  classical
  refine Finset.card_le_card ?_
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, coprime_primorial_of_prime hn.2.1 hn.2.2⟩

/-- **The Brun–Titchmarsh upper bound for the primes of a window.** -/
theorem card_primes_Ioc_le_log (a b z Y : ℕ) (hab : a ≤ b) (hY : 1 ≤ Y) (hYz : Y ≤ z)
    (hlog : 0 < Real.log Y) :
    ((#{p ∈ Finset.Ioc a b | p.Prime ∧ z < p} : ℕ) : ℝ)
      ≤ 2 * ((b : ℝ) - a) / Real.log Y
        + ∑ d ∈ (primorial z).divisors,
            |lambdaSquared (selbergTruncWeight (intervalSieve a b z) Y) d| := by
  refine le_trans ?_ (card_coprime_Ioc_le_log a b z Y hab hY hYz hlog)
  exact_mod_cast card_primes_Ioc_le_rough a b z

/-- **The prime count of a window, fully explicit.**  Every quantity is an elementary function of
the parameters. -/
theorem card_primes_Ioc_le_explicit (a b z Y : ℕ) (hab : a ≤ b) (hY : 1 ≤ Y) (hYz : Y ≤ z)
    (hz : 2 ≤ z) (hlog : 0 < Real.log Y) :
    ((#{p ∈ Finset.Ioc a b | p.Prime ∧ z < p} : ℕ) : ℝ)
      ≤ 2 * ((b : ℝ) - a) / Real.log Y
        + ((Y * Y : ℕ) : ℝ)
            * (Real.exp (4 * mertensSecondUpperConst) * (Real.log z) ^ (4 : ℝ)) := by
  refine le_trans ?_ (card_coprime_Ioc_le_explicit a b z Y hab hY hYz hz hlog)
  exact_mod_cast card_primes_Ioc_le_rough a b z

end RHTower.Sieve
