import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.HermitianSecantLocalEquation
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.HermitianTangentLocalEquation
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.GroupWithZero.WithZero

/-!
# Local Hermitian valuation identities

For elements of positive order, the linear term in `t^Q+t` determines
the valuation. The secant identity then equates coordinate orders at a
point with nonzero first coordinate. The tangent identity determines
contact orders once a normalized local coordinate is supplied.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Below value one, a higher power cannot cancel the linear term. -/
theorem valuation_add_power_of_lt_one {E : Type*} [Field E]
    (V : Valuation E (WithZero (Multiplicative ℤ)))
    (n : ℕ) (hn : 1 < n) (t : E) (ht : V t < 1) : V (t ^ n + t) = V t := by
  by_cases ht0 : t = 0
  · simp only [ht0, zero_pow (by omega : n ≠ 0), zero_add]
  · apply V.map_add_eq_of_lt_right
    rw [map_pow]
    exact pow_lt_self_of_lt_one₀ (pos_iff_ne_zero.mpr (V.ne_zero_iff.mpr ht0)) ht hn

variable (p : ℕ) [Fact p.Prime] (s : ℕ) (E : Type*) [Field E] [CharP E p]
local notation "Q" => p ^ (s + 1)

/-- Near a point with unit first coordinate, the two coordinate differences have equal valuation. -/
theorem hermitianPoint_coordinate_valuation_eq
    (V : Valuation E (WithZero (Multiplicative ℤ))) (P U : HermitianAffinePoint p s E)
    (hP : V P.val.1 = 1) (hx : V (U.val.1 - P.val.1) < 1)
    (hy : V (U.val.2 - P.val.2) < 1) :
    V (U.val.1 - P.val.1) = V (U.val.2 - P.val.2) := by
  have hQ : 1 < Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  have hU : V U.val.1 = 1 := (V.map_eq_of_sub_lt (hP.symm ▸ hx)).trans hP
  have hr : V (U.val.1 ^ Q * (U.val.1 - P.val.1) +
      P.val.1 * (U.val.1 - P.val.1) ^ Q) = V (U.val.1 - P.val.1) := by
    by_cases hz : U.val.1 - P.val.1 = 0
    · simp only [hz, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero),
        mul_zero, add_zero]
    · rw [V.map_add_eq_of_lt_left]
      · rw [map_mul, map_pow, hU, one_pow, one_mul]
      · rw [map_mul, map_mul, map_pow, map_pow, hP, hU, one_pow, one_mul, one_mul]
        exact pow_lt_self_of_lt_one₀ (pos_iff_ne_zero.mpr (V.ne_zero_iff.mpr hz)) hx hQ
  have h := congrArg V (hermitianPoint_secant_equation p s E P U)
  rw [valuation_add_power_of_lt_one V Q hQ _ hy, hr] at h
  exact h.symm

/-- The local tangent valuation is the product of the original and Frobenius contact factors. -/
theorem hermitianTangentDifference_valuation
    (V : Valuation E (WithZero (Multiplicative ℤ))) (P U : HermitianAffinePoint p s E)
    (ht : V (hermitianTangentDifference p s E P U) < 1) :
    V (hermitianTangentDifference p s E P U) =
      V (U.val.1 - P.val.1) ^ Q * V (U.val.1 - P.val.1 ^ (Q * Q)) := by
  have hQ : 1 < Q := Nat.one_lt_pow (Nat.succ_ne_zero s) (Fact.out : p.Prime).one_lt
  have h := congrArg V (hermitianTangentDifference_equation p s E P U)
  rw [valuation_add_power_of_lt_one V Q hQ _ ht, map_mul, map_pow] at h
  exact h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
