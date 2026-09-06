import GaloisForLFunctions.RHTower.MobiusDivisorAbelQuadraticDiagonal

/-!
# Exact integer homothety of literal Möbius–divisor channels

Scaling the cutoff and channel index by the same positive integer scales the
unsigned half-order response by its square root. On disjoint prime supports,
Möbius multiplicativity retains the exact common orientation as well. Empty
channels and the clipped terminal quotient block are included.
-/

noncomputable section
open Finset
namespace RHTower

private theorem mul_pred_quotient {r M d : ℕ} (hr : 1 ≤ r) (hd : 1 ≤ d) :
    (r*M-1)/(r*d) = (M-1)/d := by
  by_cases hM : M = 0
  · simp [hM]
  let Q := (M-1)/d
  have hrd : 0 < r*d := by positivity
  have hlo : Q*d < M := lt_of_le_of_lt (Nat.div_mul_le_self (M-1) d) (by omega)
  have hhi : M ≤ (Q+1)*d := by
    have h := (Nat.div_lt_iff_lt_mul (show 0 < d by omega)).mp
      (show (M-1)/d < Q+1 by dsimp [Q]; omega)
    omega
  have hlo' : Q*(r*d) < r*M := by
    calc
      _ = r*(Q*d) := by ring
      _ < _ := Nat.mul_lt_mul_of_pos_left hlo (by omega)
  have hhi' : r*M ≤ (Q+1)*(r*d) := by
    calc
      _ ≤ r*((Q+1)*d) := Nat.mul_le_mul_left r hhi
      _ = _ := by ring
  have hpos : 0 < r*M := by positivity
  apply Nat.le_antisymm
  · apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hrd).mpr
    exact lt_of_lt_of_le (by omega : r*M-1 < r*M) hhi'
  · apply (Nat.le_div_iff_mul_le hrd).mpr
    change Q*(r*d) ≤ r*M-1
    omega

/-- Exact homothety of the actual signed channel when prime supports are disjoint. -/
theorem mobiusDivisorDilationChannel_mul_coprime {r M d : ℕ}
    (hr : 1 ≤ r) (hd : 1 ≤ d) (hc : r.Coprime d) :
    mobiusDivisorDilationChannel (r*M) (r*d) =
      Real.sqrt r * ((ArithmeticFunction.moebius r : ℤ) : ℝ) *
        mobiusDivisorDilationChannel M d := by
  by_cases hactive : d ≤ M-1
  · have hactive' : r*d ≤ r*M-1 := by
      have hlt : r*d < r*M :=
        Nat.mul_lt_mul_of_pos_left (by omega : d < M) (by omega)
      omega
    have hrd : 1 ≤ r*d := by nlinarith
    rw [mobiusDivisorDilationChannel_eq_full_terminal hrd hactive',
      mobiusDivisorDilationChannel_eq_full_terminal hd hactive,
      mul_pred_quotient hr hd]
    have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc
    rw [hmu, show (M-1)/d*(r*d) = r*(((M-1)/d)*d) by ring]
    push_cast
    simp only [Real.sqrt_mul (Nat.cast_nonneg (α := ℝ) r)]
    ring
  · have hactive' : r*M-1 < r*d := by
      have hle : r*M ≤ r*d := Nat.mul_le_mul_left r (by omega : M ≤ d)
      have hrd : 0 < r*d := by positivity
      omega
    simp [mobiusDivisorDilationChannel,
      Icc_eq_empty_of_lt (show M-1 < d by omega),
      Icc_eq_empty_of_lt hactive']

end RHTower
