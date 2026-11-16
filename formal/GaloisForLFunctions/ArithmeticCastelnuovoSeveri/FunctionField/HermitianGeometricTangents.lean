import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricPointValuations

/-!
# Normalized tangent orders at every geometric Hermitian point

The first coordinate difference is a uniformizer at each constructed
geometric point valuation. The tangent's additive equation therefore gives
order `Q` at a non-fixed point and `Q+1` at a square-Frobenius-fixed point.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open scoped Classical
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "u" => hermitianExtensionAdditiveCoordinate p s E
local notation "z" => hermitianExtensionRadicalCoordinate p s E

/-- A normalized valuation of the actual function field at the specified geometric point. -/
def hermitianGeometricPointValuation (P : HermitianAffinePoint p s E) :
    Valuation H (WithZero (Multiplicative ℤ)) :=
  (hermitianGeometricPoint_exists_valuation p s P).choose

local notation "V" => hermitianGeometricPointValuation p s

/-- The chosen geometric valuation has the full normalized discrete value group. -/
theorem hermitianGeometricPointValuation_surjective (P : HermitianAffinePoint p s E) :
    Function.Surjective (V P) :=
  (hermitianGeometricPoint_exists_valuation p s P).choose_spec.1

/-- Every nonzero geometric constant has value one. -/
theorem hermitianGeometricPointValuation_constant (P : HermitianAffinePoint p s E)
    (c : E) (hc : c ≠ 0) : V P (algebraMap E H c) = 1 :=
  (hermitianGeometricPoint_exists_valuation p s P).choose_spec.2.1 c hc

/-- The radical coordinate difference is a normalized uniformizer at every geometric point. -/
theorem hermitianGeometricPointValuation_radical_sub (P : HermitianAffinePoint p s E) :
    V P (z - algebraMap E H P.val.1) = WithZero.exp (-1 : ℤ) :=
  (hermitianGeometricPoint_exists_valuation p s P).choose_spec.2.2.1

/-- The additive coordinate has the prescribed geometric residue. -/
theorem hermitianGeometricPointValuation_additive_sub_lt_one (P : HermitianAffinePoint p s E) :
    V P (u - algebraMap E H P.val.2) < 1 :=
  (hermitianGeometricPoint_exists_valuation p s P).choose_spec.2.2.2

private theorem radical_sub_lt_one (P : HermitianAffinePoint p s E) :
    V P (z - algebraMap E H P.val.1) < 1 := by
  rw [hermitianGeometricPointValuation_radical_sub, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

/-- The actual tangent function vanishes in the residue field at its geometric point. -/
theorem hermitianGeometricPointValuation_tangent_lt_one (P : HermitianAffinePoint p s E) :
    V P (hermitianGeometricTangentFunction p s P) < 1 := by
  have hs : V P (algebraMap E H (P.val.1 ^ Q) * (z - algebraMap E H P.val.1)) < 1 := by
    by_cases h : P.val.1 ^ Q = 0
    · rw [h, map_zero, zero_mul, map_zero]
      exact zero_lt_one
    · rw [map_mul, hermitianGeometricPointValuation_constant p s P _ h, one_mul]
      exact radical_sub_lt_one p s P
  rw [hermitianGeometricTangentFunction_eq]
  exact (V P).map_sub_lt (hermitianGeometricPointValuation_additive_sub_lt_one p s P) hs

/-- The normalized tangent order is `Q+1` at a fixed point and `Q` otherwise. -/
theorem hermitianGeometricPointValuation_tangent (P : HermitianAffinePoint p s E) :
    V P (hermitianGeometricTangentFunction p s P) =
      WithZero.exp (-((if P.val.1 ^ (Q * Q) = P.val.1 then Q + 1 else Q : ℕ) : ℤ)) := by
  classical
  have hQ : 1 < Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  have ht := congrArg (V P) (hermitianGeometricTangentFunction_equation p s P)
  rw [valuation_add_power_of_lt_one (V P) Q hQ _
      (hermitianGeometricPointValuation_tangent_lt_one p s P),
    map_mul, map_pow, hermitianGeometricPointValuation_radical_sub] at ht
  by_cases hfix : P.val.1 ^ (Q * Q) = P.val.1
  · rw [if_pos hfix]
    rw [hfix, hermitianGeometricPointValuation_radical_sub,
      ← pow_succ (WithZero.exp (-1 : ℤ)) Q,
      ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one] at ht
    exact ht
  · have hc : P.val.1 - P.val.1 ^ (Q * Q) ≠ 0 := sub_ne_zero.mpr (Ne.symm hfix)
    have hunit : V P (algebraMap E H (P.val.1 - P.val.1 ^ (Q * Q))) = 1 :=
      hermitianGeometricPointValuation_constant p s P _ hc
    have hfactor : V P (z - algebraMap E H (P.val.1 ^ (Q * Q))) = 1 := by
      have hid : z - algebraMap E H (P.val.1 ^ (Q * Q)) =
          (z - algebraMap E H P.val.1) + algebraMap E H (P.val.1 - P.val.1 ^ (Q * Q)) := by
        rw [map_sub]
        ring
      rw [hid]
      exact ((V P).map_add_eq_of_lt_right (hunit.symm ▸ radical_sub_lt_one p s P)).trans hunit
    rw [if_neg hfix]
    rw [hfactor, mul_one, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one] at ht
    exact ht

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
