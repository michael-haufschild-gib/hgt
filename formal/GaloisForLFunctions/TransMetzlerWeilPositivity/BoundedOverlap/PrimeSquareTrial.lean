import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.GcdProfilesHaveFiniteRamanujanExpansions
import GaloisForLFunctions.ArithmeticCountingPositivity.PrimeParityRamanujanCoordinates

/-!+# A prime-square truncation of the single-prime sign

The profile is negative exactly on integers of prime valuation one. It has
unit square and its correlation with multiplication by the prime differs
from minus one only on the prime-square fibre.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence

/-- The sign that agrees with prime parity through valuation two. -/
def primeSquareTrial (p n : ℕ) : ℝ :=
  1 - 2 * (if p ∣ n then 1 else 0) + 2 * (if p ^ 2 ∣ n then 1 else 0)

private theorem dvd_of_square_dvd {p n : ℕ} (h : p ^ 2 ∣ n) : p ∣ n :=
  (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)).trans h

/-- The truncated sign has exactly unit square at every integer. -/
theorem primeSquareTrial_sq (p n : ℕ) : primeSquareTrial p n ^ 2 = 1 := by
  unfold primeSquareTrial
  by_cases hp : p ∣ n
  · by_cases hp2 : p ^ 2 ∣ n <;> simp only [hp, hp2, if_true, if_false] <;> norm_num
  · have hp2 : ¬ p ^ 2 ∣ n := fun h => hp (dvd_of_square_dvd h)
    simp only [hp, hp2, if_false]
    norm_num

theorem abs_primeSquareTrial (p n : ℕ) : |primeSquareTrial p n| = 1 := by
  have h := primeSquareTrial_sq p n
  rcases sq_eq_one_iff.mp h with h | h <;> rw [h] <;> norm_num

/-- Multiplication by the prime shifts the exceptional fibre by one valuation. -/
theorem primeSquareTrial_mul {p : ℕ} (hp : 0 < p) (n : ℕ) :
    primeSquareTrial p (p * n) = -1 + 2 * (if p ∣ n then 1 else 0) := by
  have hpow : p ^ 2 ∣ p * n ↔ p ∣ n := by
    rw [pow_two]
    exact Nat.mul_dvd_mul_iff_left hp
  simp only [primeSquareTrial, dvd_mul_right, if_true, hpow]
  ring

/-- The first prime correlation cancels except on the prime-square fibre. -/
theorem primeSquareTrial_mul_correlation {p : ℕ} (hp : 0 < p) (n : ℕ) :
    primeSquareTrial p n * primeSquareTrial p (p * n) =
      -1 + 2 * (if p ^ 2 ∣ n then 1 else 0) := by
  rw [primeSquareTrial_mul hp, primeSquareTrial]
  by_cases hpn : p ∣ n
  · by_cases hp2 : p ^ 2 ∣ n <;> simp only [hpn, hp2, if_true, if_false] <;> norm_num
  · have hp2 : ¬ p ^ 2 ∣ n := fun h => hpn (dvd_of_square_dvd h)
    simp only [hpn, hp2, if_false]
    norm_num

/-- Products of two trial values have absolute value one, including all later prime powers. -/
theorem abs_primeSquareTrial_product (p m n : ℕ) :
    |primeSquareTrial p m * primeSquareTrial p n| = 1 := by
  rw [abs_mul, abs_primeSquareTrial, abs_primeSquareTrial, one_mul]

end GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.primeSquareTrial_mul_correlation
