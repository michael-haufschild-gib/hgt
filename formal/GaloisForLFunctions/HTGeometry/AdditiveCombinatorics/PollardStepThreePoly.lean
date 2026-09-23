import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardFullTranslations

/-!
# The polynomial inequalities of Grynkiewicz's STEP 3

Both cases of STEP 3 end in a polynomial inequality in `#B` which the source dismisses with "a
routine calculation shows that the derivative is negative".  Written out, each becomes a positive
combination of powers of the slack variable:

* CASE 3.2 (`t ≥ 3`): substituting `n = 2t + m` turns
  `−n³ + 4(t−1)n² − (6t²−8t+2)n + 2t³ − 4t² + 2t`
  into `−(2t³ + 4t² + 2t) − (2t² + 8t + 2)m − (2t + 4)m² − m³`, visibly negative for `t ≥ 1`,
  `m ≥ 0`.
* CASE 3.1 (`t = 2`): substituting `n = 3 + m` makes
  `−5n⁴ + 26n³ − 50n² + 40n − 15` visibly negative for `m ≥ 0`.
-/

namespace GaloisForLFunctions.HTGeometry.AddComb

/-- **The cubic inequality of Grynkiewicz's CASE 3.2.**  For `t ≥ 1` and `n ≥ 2t`,
`−n³ + 4(t−1)n² − (6t²−8t+2)n + 2t³ − 4t² + 2t < 0`. -/
theorem case32_poly {t n : ℝ} (ht : 1 ≤ t) (hn : 2 * t ≤ n) :
    4 * (t - 1) * n ^ (2 : ℕ) + 2 * t ^ (3 : ℕ) + 2 * t
      < n ^ (3 : ℕ) + (6 * t ^ (2 : ℕ) - 8 * t + 2) * n + 4 * t ^ (2 : ℕ) := by
  have hm : 0 ≤ n - 2 * t := by linarith
  have ht0 : (0 : ℝ) ≤ t := by linarith
  nlinarith [hm, ht0, mul_nonneg hm hm, mul_nonneg (mul_nonneg hm hm) hm,
    mul_nonneg ht0 hm, mul_nonneg (mul_nonneg ht0 hm) hm,
    mul_nonneg (mul_nonneg ht0 ht0) hm, mul_nonneg ht0 (mul_nonneg ht0 ht0)]

/-- **The quartic inequality of Grynkiewicz's CASE 3.1.**  For `n ≥ 3`,
`−5n⁴ + 26n³ − 50n² + 40n − 15 < 0`. -/
theorem case31_poly {n : ℝ} (hn : 3 ≤ n) :
    26 * n ^ (3 : ℕ) + 40 * n < 5 * n ^ (4 : ℕ) + 50 * n ^ (2 : ℕ) + 15 := by
  have hm : 0 ≤ n - 3 := by linarith
  nlinarith [hm, mul_nonneg hm hm, mul_nonneg (mul_nonneg hm hm) hm,
    mul_nonneg (mul_nonneg (mul_nonneg hm hm) hm) hm]

end GaloisForLFunctions.HTGeometry.AddComb
