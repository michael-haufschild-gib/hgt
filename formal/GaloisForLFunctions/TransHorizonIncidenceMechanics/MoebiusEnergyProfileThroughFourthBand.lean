import GaloisForLFunctions.TransHorizonIncidenceMechanics.MoebiusBandAverageStepAndEnergyProfile

/-!
# The Möbius energy profile through the fourth band

In the bands `B = 3, 4` the primes up to `B` are `2, 3`, so the horizons fall into the four smooth-core
classes `1, 2, 3, 6`, each of density `δ_B / r` with `δ_B = (6/π²)(2/3)(3/4) = 3/π²`, and with the class
steps `Δ(1) = B - 2`, `Δ(2) = -B`, `Δ(3) = 2⌊B/2⌋ - B`, `Δ(6) = -B - 2⌊B/5⌋`. The mean steps are

`A(3) = -4/π²`,   `A(4) = -2/π²`,

and the second-difference identity `A(B) = (B+1) P(B-1) - B P(B)` extends the exact profile:

`P(3) = 16/π²`,   `P(4) = 41/(2π²)`,

i.e. `E_N(4N; μ)/N → 16/π²` and `E_N(5N; μ)/N → 41/(2π²)`. With `P(1) = 6/π²`, `P(2) = 11/π²` the
band means `P(B) - P(B-1)` of the squared response are `6, 5, 5, 9/2` (in units of `1/π²`), and every
one of the first four bands dissipates on average.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

private theorem divisors_six : (6 : ℕ).divisors = {1, 2, 3, 6} := by decide

private theorem primeFactors_six : (6 : ℕ).primeFactors = {2, 3} := by
  show (2 * 3 : ℕ).primeFactors = {2, 3}
  rw [Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.prime_two.primeFactors,
    Nat.prime_three.primeFactors]
  rfl

/-- The rough density of the bands `3, 4`: `δ = (6/π²)(2/3)(3/4)`. -/
private theorem bandRoughDensity_of_primorial_six {B : ℕ} (hB : primorial B = 6) :
    bandRoughDensity B = RHTower.Sieve.squarefreeDensity / 2 := by
  rw [bandRoughDensity, hB, primeFactors_six, prod_insert (by decide), prod_singleton]
  norm_num
  ring

/-- The class sum over the divisors of `6`. -/
private theorem bandAverageStep_of_primorial_six {B : ℕ} (hB : primorial B = 6) :
    bandAverageStep B = RHTower.Sieve.squarefreeDensity / 2 *
      (((B : ℝ) - 2) + moebiusBandStep 2 B / 2 + moebiusBandStep 3 B / 3 +
        moebiusBandStep 6 B / 6) := by
  rw [bandAverageStep, hB, divisors_six, bandRoughDensity_of_primorial_six hB]
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp only [bandClassValue, show (2 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 1 by decide,
    show (6 : ℕ) ≠ 1 by decide, if_false]
  push_cast
  ring

/-- `A(3) = -(2/3)(6/π²) = -4/π²`. -/
theorem bandAverageStep_three :
    bandAverageStep 3 = -(2 / 3) * RHTower.Sieve.squarefreeDensity := by
  rw [bandAverageStep_of_primorial_six (by decide), moebiusBandStep_two, moebiusBandStep_three,
    moebiusBandStep_six]
  norm_num
  ring

/-- `A(4) = -(1/3)(6/π²) = -2/π²`. -/
theorem bandAverageStep_four :
    bandAverageStep 4 = -(1 / 3) * RHTower.Sieve.squarefreeDensity := by
  rw [bandAverageStep_of_primorial_six (by decide), moebiusBandStep_two, moebiusBandStep_three,
    moebiusBandStep_six]
  norm_num
  ring

/-- **`P(3) = 16/π²`:** `E_N(4N; μ)/N → (8/3)(6/π²)`. -/
theorem cofinalMobiusQuadraticProfile_three :
    cofinalMobiusQuadraticProfile 3 = 8 / 3 * RHTower.Sieve.squarefreeDensity := by
  have h := bandAverageStep_eq_profile (B := 3) (by norm_num)
  rw [bandAverageStep_three, show (3 : ℕ) - 1 = 2 from rfl, cofinalMobiusQuadraticProfile_two] at h
  push_cast at h
  linarith

/-- **`P(4) = 41/(2π²)`:** `E_N(5N; μ)/N → (41/12)(6/π²)`. -/
theorem cofinalMobiusQuadraticProfile_four :
    cofinalMobiusQuadraticProfile 4 = 41 / 12 * RHTower.Sieve.squarefreeDensity := by
  have h := bandAverageStep_eq_profile (B := 4) (by norm_num)
  rw [bandAverageStep_four, show (4 : ℕ) - 1 = 3 from rfl, cofinalMobiusQuadraticProfile_three] at h
  push_cast at h
  linarith

/-- The first four mean band steps are negative: every one of these bands dissipates on average. -/
theorem bandAverageStep_neg_of_le_four {B : ℕ} (hB1 : 1 ≤ B) (hB4 : B ≤ 4) :
    bandAverageStep B < 0 := by
  have hD : 0 < RHTower.Sieve.squarefreeDensity := by
    rw [RHTower.Sieve.squarefreeDensity_eq]; positivity
  interval_cases B
  · rw [bandAverageStep_one]; linarith
  · rw [bandAverageStep_two]; linarith
  · rw [bandAverageStep_three]; linarith
  · rw [bandAverageStep_four]; linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
