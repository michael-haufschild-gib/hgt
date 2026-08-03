import GaloisForLFunctions.RHTower.Sieve.RamareBilinearSplit

/-!
# Bounding the Ramaré remainder

The part of the bilinear decomposition where the designated prime divides the cofactor is bounded
trivially for a function of modulus at most one:

`|∑_{p ∣ m} f(pm)/ω_P(pm)| ≤ #{m ∈ T : p ∣ m}`,

because the designated prime always divides `pm`, so the weight `ω_P(pm)` is at least one and each
term has modulus at most one.

This is the honest bound on the term `RamareBilinearSplit.lean` isolates.  It is crude — no
cancellation is used — but the count on the right is itself small, being the multiples of `p` in the
cofactor range, and that is how a sieve disposes of the remainder.
-/

namespace RHTower.Sieve

open Finset

/-- The designated prime always contributes to its own multiple. -/
theorem one_le_card_primeFactorsIn_mul {P : Finset ℕ} {p : ℕ} (hpP : p ∈ P) (m : ℕ) :
    1 ≤ (primeFactorsIn P (p * m)).card := by
  refine Finset.card_pos.mpr ⟨p, ?_⟩
  rw [mem_primeFactorsIn]
  exact ⟨hpP, Dvd.intro m rfl⟩

/-- **The Ramaré remainder is at most the number of terms.** -/
theorem abs_ramare_remainder_le {P : Finset ℕ} {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1)
    {p : ℕ} (hpP : p ∈ P) (T : Finset ℕ) :
    |∑ m ∈ {m ∈ T | p ∣ m}, f (p * m) / ((primeFactorsIn P (p * m)).card : ℝ)|
      ≤ (({m ∈ T | p ∣ m}).card : ℝ) := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ m ∈ {m ∈ T | p ∣ m},
      |f (p * m) / ((primeFactorsIn P (p * m)).card : ℝ)| ≤ 1 := by
    intro m _
    have hω : (1 : ℝ) ≤ ((primeFactorsIn P (p * m)).card : ℝ) := by
      exact_mod_cast one_le_card_primeFactorsIn_mul hpP m
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((primeFactorsIn P (p * m)).card : ℝ))]
    rw [div_le_one (by linarith)]
    have hnum := hf (p * m)
    linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

end RHTower.Sieve
