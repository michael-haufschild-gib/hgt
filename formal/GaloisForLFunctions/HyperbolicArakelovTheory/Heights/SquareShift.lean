import GaloisForLFunctions.HyperbolicArakelovTheory.TheCoupledLocalProductObstructsOffDiagonalAndTorusInvariance

/-!
# Exact height growth under a shifted square

Adding the integer square `N²` to `q²` creates no denominator cancellation.
For `N ≥ 1`, the numerator dominates the denominator, giving the exact
multiplicative height and the lower bound `h(N²+q²) ≥ h(q)+log N`.
-/

namespace GaloisForLFunctions.HyperbolicArakelovTheory.CoupledProductObstruction

/-- Squaring and then adding an integer square preserves the squared
reduced denominator exactly. -/
theorem squareShift_den (N : ℕ) (q : ℚ) :
    ((N : ℚ) ^ 2 + q ^ 2).den = q.den ^ 2 := by
  have h := Rat.intCast_add_den ((N : ℤ) ^ 2) (q ^ 2)
  push_cast at h
  rw [h, Rat.den_pow]

/-- Exact numerator formula, with no gcd correction. -/
theorem squareShift_num (N : ℕ) (q : ℚ) :
    ((N : ℚ) ^ 2 + q ^ 2).num =
      (N : ℤ) ^ 2 * (q.den : ℤ) ^ 2 + q.num ^ 2 := by
  have h := Rat.mul_den_eq_num ((N : ℚ) ^ 2 + q ^ 2)
  rw [squareShift_den] at h
  have hq := Rat.mul_den_eq_num q
  have hnum : (((N : ℚ) ^ 2 + q ^ 2).num : ℚ) =
      (N : ℚ) ^ 2 * (q.den : ℚ) ^ 2 + (q.num : ℚ) ^ 2 := by
    rw [← h, Nat.cast_pow, ← hq]
    ring
  exact_mod_cast hnum

/-- The exact standard Weil height of a shifted square. -/
theorem weilHeight_squareShift (N : ℕ) (hN : 1 ≤ N) (q : ℚ) :
    weilHeight ((N : ℚ) ^ 2 + q ^ 2) =
      N ^ 2 * q.den ^ 2 + q.num.natAbs ^ 2 := by
  have habs : (((N : ℚ) ^ 2 + q ^ 2).num).natAbs =
      N ^ 2 * q.den ^ 2 + q.num.natAbs ^ 2 := by
    have hnonneg : 0 ≤ (N : ℤ) ^ 2 * (q.den : ℤ) ^ 2 + q.num ^ 2 := by positivity
    apply Int.natCast_injective
    rw [squareShift_num, Int.natAbs_of_nonneg hnonneg]
    push_cast
    rw [← Int.natAbs_pow, Int.natAbs_of_nonneg (sq_nonneg q.num)]
  rw [weilHeight, habs, squareShift_den]
  apply max_eq_left
  have hN2 : 1 ≤ N ^ 2 := one_le_pow₀ hN
  exact (Nat.le_mul_of_pos_left _ (by omega : 0 < N ^ 2)).trans (Nat.le_add_right _ _)

/-- The height dominates the square of the original height. -/
theorem weilHeight_sq_le_squareShift (N : ℕ) (hN : 1 ≤ N) (q : ℚ) :
    weilHeight q ^ 2 ≤ weilHeight ((N : ℚ) ^ 2 + q ^ 2) := by
  rw [weilHeight_squareShift N hN q, weilHeight]
  rcases le_total q.num.natAbs q.den with h | h
  · rw [max_eq_right h]
    have hN2 : 1 ≤ N ^ 2 := one_le_pow₀ hN
    exact (Nat.le_mul_of_pos_left _ (by omega : 0 < N ^ 2)).trans (Nat.le_add_right _ _)
  · rw [max_eq_left h]
    exact Nat.le_add_left _ _

/-- The height also dominates the square of the integer shift. -/
theorem shift_sq_le_weilHeight_squareShift (N : ℕ) (hN : 1 ≤ N) (q : ℚ) :
    N ^ 2 ≤ weilHeight ((N : ℚ) ^ 2 + q ^ 2) := by
  rw [weilHeight_squareShift N hN q]
  have hb : 0 < q.den ^ 2 := pow_pos q.den_pos _
  exact (Nat.le_mul_of_pos_right _ hb).trans (Nat.le_add_right _ _)

/-- Multiplicative form of the shifted-height inequality. -/
theorem mul_weilHeight_le_squareShift (N : ℕ) (hN : 1 ≤ N) (q : ℚ) :
    N * weilHeight q ≤ weilHeight ((N : ℚ) ^ 2 + q ^ 2) := by
  rcases le_total N (weilHeight q) with h | h
  · exact (Nat.mul_le_mul_right _ h).trans (by
      simpa only [sq] using weilHeight_sq_le_squareShift N hN q)
  · exact (Nat.mul_le_mul_left _ h).trans (by
      simpa only [sq] using shift_sq_le_weilHeight_squareShift N hN q)

/-- The logarithmic height grows by at least the logarithm of the shift. -/
theorem log_weilHeight_squareShift_ge (N : ℕ) (hN : 1 ≤ N) (q : ℚ) :
    Real.log (weilHeight q : ℝ) + Real.log (N : ℝ) ≤
      Real.log (weilHeight ((N : ℚ) ^ 2 + q ^ 2) : ℝ) := by
  have hq : 0 < weilHeight q := q.den_pos.trans_le (le_max_right _ _)
  have hN' : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hq' : (0 : ℝ) < weilHeight q := by exact_mod_cast hq
  rw [← Real.log_mul hq'.ne' hN'.ne']
  apply Real.log_le_log (mul_pos hq' hN')
  exact_mod_cast (by simpa only [mul_comm] using mul_weilHeight_le_squareShift N hN q)

end GaloisForLFunctions.HyperbolicArakelovTheory.CoupledProductObstruction
