import GaloisForLFunctions.RHTower.Sieve.RamareRemainder

/-!
# The complete multiplicative Ramaré decomposition

Combining the bilinear split with the remainder bound:

`|∑_{m ∈ T} f(pm)/ω_P(pm) - f(p) ∑_{p ∤ m} f(m)/(ω_P(m)+1)| ≤ #{m ∈ T : p ∣ m}`,

and summing over the designated primes,

`|∑_{p ∈ P} ∑_{m ∈ T p} f(pm)/ω_P(pm) - ∑_{p ∈ P} f(p) B_p| ≤ ∑_{p ∈ P} #{m ∈ T p : p ∣ m}`.

So Ramaré's weighted factorisation of a bounded multiplicative function is bilinear up to a term
counted by multiples — the structure Matomäki–Radziwiłł's argument requires, with its error made
explicit.
-/

namespace RHTower.Sieve

open Finset

/-- **The Ramaré inner sum is bilinear up to a counted remainder.** -/
theorem abs_ramare_inner_sub_bilinear_le {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime)
    {f : ℕ → ℝ} (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (hf : ∀ n, |f n| ≤ 1) {p : ℕ} (hp : p.Prime) (hpP : p ∈ P) (T : Finset ℕ) :
    |(∑ m ∈ T, f (p * m) / ((primeFactorsIn P (p * m)).card : ℝ))
        - f p * (∑ m ∈ {m ∈ T | ¬ p ∣ m}, f m / (((primeFactorsIn P m).card : ℝ) + 1))|
      ≤ (({m ∈ T | p ∣ m}).card : ℝ) := by
  classical
  rw [sum_ramare_bilinear_split hPprime hmul hp hpP T, add_sub_cancel_left]
  exact abs_ramare_remainder_le hf hpP T

/-- **The decomposition summed over the designated primes.** -/
theorem abs_sum_ramare_sub_bilinear_le {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime)
    {f : ℕ → ℝ} (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (hf : ∀ n, |f n| ≤ 1) (hprime : ∀ p ∈ P, p.Prime) (T : ℕ → Finset ℕ) :
    |(∑ p ∈ P, ∑ m ∈ T p, f (p * m) / ((primeFactorsIn P (p * m)).card : ℝ))
        - ∑ p ∈ P, f p
            * (∑ m ∈ {m ∈ T p | ¬ p ∣ m}, f m / (((primeFactorsIn P m).card : ℝ) + 1))|
      ≤ ∑ p ∈ P, (({m ∈ T p | p ∣ m}).card : ℝ) := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun p hp => ?_
  exact abs_ramare_inner_sub_bilinear_le hPprime hmul hf (hprime p hp) hp (T p)

end RHTower.Sieve
