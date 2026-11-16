import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Codes.NormalizedKummerEvaluationCodes
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.LinearSingletonBound
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.KummerExponentPeriod

/-!
# Maximum-distance codes at the genus-zero Kummer boundary

A geometric branch length twice the covering exponent gives genus zero.
The actual affine normalization then has `Q²` rational points. Its
one-point evaluation code of pole allowance `m<Q²` has dimension `m+1`
and attained minimum nonzero weight `Q²-m`, meeting Singleton exactly.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n : ℕ)
local notation "K" => SquareConstantField p (kummerSquareIndex d n)
local notation "Q" => p ^ (kummerSquareIndex d n + 1)
local notation "I" => NormalizedKummerAlgebraPoints p d n (2 * n + 1)

local instance : Fintype I := Fintype.ofFinite _

/-- A full doubled branch period has zero actual differential genus. -/
theorem normalizedKummer_double_period_genus_zero :
    Module.finrank K (NormalizedKummerRegularDifferentials p d n (2 * n + 1)) = 0 := by
  have hd : Q + 1 ∣ kummerExponent (p ^ (d + 1)) (2 * n + 1 + 1) := by
    rw [kummerSquareIndex_succ, pow_mul,
      show 2 * n + 1 + 1 = 2 * (n + 1) by omega, kummerExponent_double_length]
    exact ⟨kummerExponent (p ^ (d + 1)) (n + 1), rfl⟩
  have h := normalizedKummer_regularDifferential_finrank_twice p d n (2 * n + 1)
  rw [Nat.gcd_eq_left hd, Nat.sub_self, mul_zero] at h
  omega

/-- The genus-zero boundary has exactly `Q²` actual affine evaluation points. -/
theorem normalizedKummer_double_period_code_length : Fintype.card I = Q ^ 2 := by
  rw [normalizedKummerEvaluationCode_length, normalizedKummer_double_period_genus_zero,
    mul_zero, add_zero]

/-- Every code below the boundary's evaluation length has dimension `m+1`. -/
theorem normalizedKummer_double_period_code_finrank (m : Fin (Q ^ 2)) :
    Module.finrank K (normalizedKummerEvaluationCode p d n (2 * n + 1) m.val) = m.val + 1 := by
  have hrange : m.val < Q ^ 2 + 2 * Q *
      Module.finrank K (NormalizedKummerRegularDifferentials p d n (2 * n + 1)) := by
    rw [normalizedKummer_double_period_genus_zero, mul_zero, add_zero]
    exact m.isLt
  have hgenus : 2 * Module.finrank K
      (NormalizedKummerRegularDifferentials p d n (2 * n + 1)) ≤ m.val + 1 := by
    rw [normalizedKummer_double_period_genus_zero, mul_zero]
    exact Nat.zero_le _
  have h := normalizedKummerEvaluationCode_riemannRoch p d n (2 * n + 1)
    ⟨⟨m.val, hrange⟩, hgenus⟩
  simpa only [normalizedKummer_double_period_genus_zero, add_zero] using h

/-- These actual Kummer evaluation codes attain the Singleton bound. -/
theorem normalizedKummer_double_period_code_minimum_weight (m : Fin (Q ^ 2)) :
    IsLeast {b : ℕ | ∃ w ∈ normalizedKummerEvaluationCode p d n (2 * n + 1) m.val,
      w ≠ 0 ∧ Codes.weight w = b} (Q ^ 2 - m.val) := by
  have hweight : ∀ w ∈ normalizedKummerEvaluationCode p d n (2 * n + 1) m.val,
      w ≠ 0 → Fintype.card I - m.val ≤ Codes.weight w := by
    simpa only [normalizedKummer_double_period_code_length,
      normalizedKummer_double_period_genus_zero, mul_zero, add_zero] using
        normalizedKummerEvaluationCode_weight_bound p d n (2 * n + 1) m.val
  have h := Codes.minimum_weight_eq_singleton _ m.val
    (normalizedKummer_double_period_code_finrank p d n m) hweight
  simpa only [normalizedKummer_double_period_code_length] using h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
