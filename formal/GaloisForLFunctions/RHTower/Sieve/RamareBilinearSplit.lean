import GaloisForLFunctions.RHTower.Sieve.RamarePrimeFactor

/-!
# The bilinear Ramaré sum for a multiplicative function

Splitting the inner sum of Ramaré's bilinear decomposition according to whether the designated prime
divides the cofactor,

`∑_{m ∈ T} f(pm)/ω_P(pm) = f(p) ∑_{p ∤ m} f(m)/(ω_P(m)+1) + ∑_{p ∣ m} f(pm)/ω_P(pm)`.

On the first part the multiplicative function factors and the weight depends on the cofactor alone,
so the sum is genuinely bilinear in `p` and `m`.  The second part is the remainder: there `p` occurs
to a higher power, `f` does not factor, and a sieve must bound it separately.

Isolating that remainder explicitly is the point — it is what an argument has to control, and it is
invisible if the decomposition is quoted as if it were bilinear throughout.
-/

namespace RHTower.Sieve

open Finset

/-- **The bilinear split of a Ramaré inner sum.** -/
theorem sum_ramare_bilinear_split {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime)
    {f : ℕ → ℝ} (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    {p : ℕ} (hp : p.Prime) (hpP : p ∈ P) (T : Finset ℕ) :
    ∑ m ∈ T, f (p * m) / ((primeFactorsIn P (p * m)).card : ℝ)
      = f p * (∑ m ∈ {m ∈ T | ¬ p ∣ m}, f m / (((primeFactorsIn P m).card : ℝ) + 1))
        + ∑ m ∈ {m ∈ T | p ∣ m}, f (p * m) / ((primeFactorsIn P (p * m)).card : ℝ) := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not T (fun m => p ∣ m)
    (fun m => f (p * m) / ((primeFactorsIn P (p * m)).card : ℝ))
  have hcop : ∀ m ∈ {m ∈ T | ¬ p ∣ m},
      f (p * m) / ((primeFactorsIn P (p * m)).card : ℝ)
        = f p * (f m / (((primeFactorsIn P m).card : ℝ) + 1)) := by
    intro m hm
    have hpm : ¬ p ∣ m := (Finset.mem_filter.mp hm).2
    rw [map_mul_prime_of_not_dvd hmul hp hpm,
      card_primeFactorsIn_mul_prime hPprime hp hpP hpm]
    push_cast
    ring
  have hcopsum : ∑ m ∈ {m ∈ T | ¬ p ∣ m},
      f (p * m) / ((primeFactorsIn P (p * m)).card : ℝ)
      = f p * ∑ m ∈ {m ∈ T | ¬ p ∣ m}, f m / (((primeFactorsIn P m).card : ℝ) + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hcop
  linarith [hsplit, hcopsum]

end RHTower.Sieve
