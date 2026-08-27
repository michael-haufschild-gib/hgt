import GaloisForLFunctions.RHTower.Sieve.RoughCountTuran
import GaloisForLFunctions.RHTower.Sieve.HarmanMinorant

/-!
# Mean square of a prime-window divisor count

The `c₂,n` term in the Matomäki--Teräväinen minorant is supported on integers having a prime
factor in one short multiplicative block. This file identifies that count with the corpus's
designated prime-factor count and applies its exact second-moment bound.
-/

namespace RHTower.Sieve

open Finset

/-- Primes in the half-open integer interval `[a,b)`. -/
def primesIco (a b : ℕ) : Finset ℕ :=
  (Finset.Ico a b).filter Nat.Prime

theorem mem_primesIco {a b p : ℕ} :
    p ∈ primesIco a b ↔ a ≤ p ∧ p < b ∧ p.Prime := by
  simp [primesIco, and_assoc]

/-- A prime window is the designated prime-factor set for `primesIco`. -/
theorem primeWindow_eq_primeFactorsIn_primesIco (n a b : ℕ) :
    primeWindow n a b = primeFactorsIn (primesIco a b) n := by
  ext p
  simp [mem_primeWindow, mem_primeFactorsIn, mem_primesIco, and_left_comm,
    and_comm, and_assoc]

/-- Exact second-moment upper bound in terms of the reciprocal mass of the prime window. -/
theorem sum_sq_card_primeWindow_le (a b Y : ℕ) :
    ∑ n ∈ Finset.Icc 1 Y, ((primeWindow n a b).card : ℝ) ^ 2 ≤
      (Y : ℝ) * (∑ p ∈ primesIco a b, 1 / (p : ℝ)) +
        (Y : ℝ) * (∑ p ∈ primesIco a b, 1 / (p : ℝ)) ^ 2 := by
  rw [show (∑ n ∈ Finset.Icc 1 Y, ((primeWindow n a b).card : ℝ) ^ 2) =
      ∑ n ∈ Finset.Icc 1 Y, ((primeFactorsIn (primesIco a b) n).card : ℝ) ^ 2 by
    apply Finset.sum_congr rfl
    intro n _
    rw [primeWindow_eq_primeFactorsIn_primesIco]]
  have hprime : ∀ p ∈ primesIco a b, p.Prime := by
    intro p hp
    exact (mem_primesIco.mp hp).2.2
  have hsq := sum_sq_card_primeFactorsIn_Icc_le hprime Y
  have hfirst :
      ∑ p ∈ primesIco a b, ((Y / p : ℕ) : ℝ) ≤
        (Y : ℝ) * (∑ p ∈ primesIco a b, 1 / (p : ℝ)) := by
    rw [← sum_card_primeFactorsIn_Icc (primesIco a b) Y]
    exact sum_card_primeFactorsIn_Icc_le (primesIco a b) Y
  exact hsq.trans (add_le_add hfirst le_rfl)

/-- If the reciprocal mass of a prime window is at most `η`, its count has mean square at most
`Y(η+η²)`. -/
theorem sum_sq_card_primeWindow_le_of_mass
    {a b Y : ℕ} {η : ℝ} (hη : 0 ≤ η)
    (hmass : ∑ p ∈ primesIco a b, 1 / (p : ℝ) ≤ η) :
    ∑ n ∈ Finset.Icc 1 Y, ((primeWindow n a b).card : ℝ) ^ 2 ≤
      (Y : ℝ) * (η + η ^ 2) := by
  have hmass_nonneg : 0 ≤ ∑ p ∈ primesIco a b, 1 / (p : ℝ) := by
    exact Finset.sum_nonneg fun p _ => by positivity
  calc
    ∑ n ∈ Finset.Icc 1 Y, ((primeWindow n a b).card : ℝ) ^ 2 ≤
        (Y : ℝ) * (∑ p ∈ primesIco a b, 1 / (p : ℝ)) +
          (Y : ℝ) * (∑ p ∈ primesIco a b, 1 / (p : ℝ)) ^ 2 :=
      sum_sq_card_primeWindow_le a b Y
    _ ≤ (Y : ℝ) * (η + η ^ 2) := by
      have hsq := (sq_le_sq₀ hmass_nonneg hη).2 hmass
      nlinarith [Nat.cast_nonneg (α := ℝ) Y]

end RHTower.Sieve
