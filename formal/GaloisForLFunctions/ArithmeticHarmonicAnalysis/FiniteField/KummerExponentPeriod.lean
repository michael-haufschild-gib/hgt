import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.KummerExponentGCD

/-!
# Periodicity of reduced geometric branch exponents

Splitting a geometric sum at its midpoint shows that the sum of length
`2n` is divisible by `q^n+1`. Appending this block preserves every
geometric exponent modulo the covering degree.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Finset

/-- Splitting a geometric exponent at any prescribed length separates its initial and translated blocks. -/
theorem kummerExponent_add_length (q a b : ℕ) :
    kummerExponent q (a + b) = kummerExponent q a + q ^ a * kummerExponent q b := by
  unfold kummerExponent
  rw [sum_range_add]
  simp only [pow_add, ← mul_sum]

/-- A doubled geometric sum contains the plus-one covering degree as an explicit factor. -/
theorem kummerExponent_double_length (q n : ℕ) :
    kummerExponent q (2 * n) = (q ^ n + 1) * kummerExponent q n := by
  rw [two_mul, kummerExponent_add_length]
  ring

/-- The reduced branch exponent repeats after twice the exponent of the square-field half-degree. -/
theorem kummerExponent_mod_period (q n r : ℕ) :
    kummerExponent q (r + 2 * n) % (q ^ n + 1) =
      kummerExponent q r % (q ^ n + 1) := by
  rw [kummerExponent_add_length, kummerExponent_double_length,
    show q ^ r * ((q ^ n + 1) * kummerExponent q n) =
      (q ^ n + 1) * (q ^ r * kummerExponent q n) by ring,
    Nat.add_mul_mod_self_left]

/-- Every reduced geometric branch exponent depends only on the length modulo the doubled covering exponent. -/
theorem kummerExponent_mod_reduce (q n r : ℕ) :
    kummerExponent q r % (q ^ n + 1) =
      kummerExponent q (r % (2 * n)) % (q ^ n + 1) := by
  have hblock (a k : ℕ) :
      kummerExponent q (a + (2 * n) * k) % (q ^ n + 1) =
        kummerExponent q a % (q ^ n + 1) := by
    induction k with
    | zero => rw [mul_zero, add_zero]
    | succ k ih => rw [Nat.mul_succ, ← Nat.add_assoc, kummerExponent_mod_period, ih]
  calc
    kummerExponent q r % (q ^ n + 1) =
        kummerExponent q (r % (2 * n) + (2 * n) * (r / (2 * n))) % (q ^ n + 1) :=
      congrArg (fun a => kummerExponent q a % (q ^ n + 1)) (Nat.mod_add_div r (2 * n)).symm
    _ = _ := hblock _ _

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
