import GaloisForLFunctions.RHTower.Sieve.ChebyshevBracketBound
import GaloisForLFunctions.RHTower.Sieve.ChebyshevSeriesBound
import GaloisForLFunctions.RHTower.Sieve.ChebyshevMassBound

/-!
# The remaining shape data of the width-`1/log` rectangle

Three quantities of the contour bound depend only on the rectangle and the cutoff, not on the
zeta function: the rectangle's width, the von Mangoldt series at the right abscissa, and the mass
of the cutoff.  All three are already available in the corpus; here they are specialised to

```text
c(T) = 1 - (1/40000)/log T,      d(T) = 1 + 1/log T.
```

The series is `8 log²T` — a power of the logarithm, harmless against the truncation height `T`.
The mass is `norm_mellin_smoothWeight_one_le : ‖mellin w 1‖ ≤ N + H`, already in the corpus.
-/

namespace RHTower.Sieve

open ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- The rectangle's width is at most twice the reciprocal logarithm. -/
theorem chebRightTwo_sub_chebLeftTwo_le {T : ℝ} (hT : 8 ≤ Real.log T) :
    chebRightTwo T - chebLeftTwo T ≤ 2 / Real.log T := by
  rw [chebRightTwo_sub_chebLeftTwo]
  have hL : (0 : ℝ) < Real.log T := by linarith
  rw [div_le_div_iff₀ hL hL]
  nlinarith [hL]

/-- The rectangle's width is positive. -/
theorem chebRightTwo_sub_chebLeftTwo_pos {T : ℝ} (hT : 8 ≤ Real.log T) :
    0 < chebRightTwo T - chebLeftTwo T := by
  rw [chebRightTwo_sub_chebLeftTwo]
  have hL : (0 : ℝ) < Real.log T := by linarith
  positivity

/-- **The von Mangoldt series at the right abscissa.**  At `d(T) - 1 = 1/log T` it is `8 log²T`. -/
theorem tsum_vonMangoldt_chebRightTwo_le {T : ℝ} (hT : 8 ≤ Real.log T) :
    ∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(chebRightTwo T)) ≤ 8 * Real.log T ^ 2 := by
  have hL : (0 : ℝ) < Real.log T := by linarith
  have h := tsum_vonMangoldt_rpow_neg_le (d := chebRightTwo T) (one_lt_chebRightTwo hT)
    (le_trans (chebRightTwo_le hT) (by norm_num))
  have hsq : (chebRightTwo T - 1) ^ 2 = 1 / Real.log T ^ 2 := by
    rw [chebRightTwo]
    field_simp
    ring
  rw [hsq] at h
  have heq : (8 : ℝ) / (1 / Real.log T ^ 2) = 8 * Real.log T ^ 2 := by
    field_simp
  linarith [h, heq]

end RHTower.Sieve
