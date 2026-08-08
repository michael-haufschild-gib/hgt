import Mathlib

/-!
# The sign of the sine on a half-period block

`sgn (sin x)` is the constant `(-1)^k` on each open half period `(kπ, (k+1)π)`
(`sign_sin_of_mem_Ioo`).  Applied to a dilated argument `α T / m` this is the form a Chebyshev
dilation sum meets.

The block value is what turns a von Mangoldt sum weighted by `sgn (sin (αT/m))` into a telescoping
alternating difference of Chebyshev sums.
-/

open Real

namespace GaloisForLFunctions.HTGeometry

theorem sin_nat_mul_pi_add (k : ℕ) (y : ℝ) :
    Real.sin ((k : ℝ) * π + y) = (-1) ^ k * Real.sin y := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : ((k + 1 : ℕ) : ℝ) * π + y = ((k : ℝ) * π + y) + π := by push_cast; ring
      rw [hstep, Real.sin_add_pi, ih, pow_succ]
      ring

/-- **The sign of the sine on an open half period.** -/
theorem sign_sin_of_mem_Ioo {k : ℕ} {x : ℝ} (h1 : (k : ℝ) * π < x) (h2 : x < ((k : ℝ) + 1) * π) :
    Real.sign (Real.sin x) = (-1) ^ k := by
  have hy0 : 0 < x - (k : ℝ) * π := by linarith
  have hyπ : x - (k : ℝ) * π < π := by nlinarith [h2]
  have hsiny : 0 < Real.sin (x - (k : ℝ) * π) := Real.sin_pos_of_pos_of_lt_pi hy0 hyπ
  have hx : Real.sin x = (-1) ^ k * Real.sin (x - (k : ℝ) * π) := by
    have := sin_nat_mul_pi_add k (x - (k : ℝ) * π)
    rw [show (k : ℝ) * π + (x - (k : ℝ) * π) = x by ring] at this
    exact this
  rcases Nat.even_or_odd k with hk | hk
  · rw [hx, hk.neg_one_pow, one_mul, Real.sign_of_pos hsiny]
  · rw [hx, hk.neg_one_pow, Real.sign_of_neg (by linarith)]

theorem abs_sign_sin_le_one (x : ℝ) : |Real.sign (Real.sin x)| ≤ 1 := by
  rcases lt_trichotomy (Real.sin x) 0 with h | h | h
  · rw [Real.sign_of_neg h]
    norm_num
  · rw [h]
    simp [Real.sign]
  · rw [Real.sign_of_pos h]
    norm_num

end GaloisForLFunctions.HTGeometry
