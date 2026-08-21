import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardQubal
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The arithmetic of Grynkiewicz's CASE 3.2

Lemma 2.1 offers two terms.  `half_le_first_term` shows the first always dominates `#A·#B/2`, and
`case32_first_branch` shows that `#A·#B/2 ≤ t(#A + #B − 2t)` is impossible once
`#A ≥ #B ≥ 2t + 1`, because it says `(#A − 2t)(#B − 2t) ≤ 0`.

For the second term, `case32_denominator` evaluates
`(t−1)#A + #T(#B − t + 1)` at `#T = #A − #B + t − 1` as `#A·#B − (#B − t + 1)²`, and
`case32_key` shows the resulting inequality
`#A·#B(#B − 2t) ≥ (#A + #B − 2t)(#B − t + 1)²` is impossible.
-/

namespace GaloisForLFunctions.HTGeometry.AddComb

/-- **The arithmetic contradiction of Grynkiewicz's CASE 3.2.**  The denominator of the second
term of Lemma 2.1, after substituting `k = t − 1` and `#T ≤ #A − #B + t − 1`, is
`#A·#B − (#B − t + 1)²`, and the resulting inequality is impossible. -/
theorem case32_key {a b t : ℝ} (ht : 1 ≤ t) (hb : 2 * t + 1 ≤ b) (hab : b ≤ a) :
    a * b * (b - 2 * t) < (a + b - 2 * t) * (b - t + 1) ^ 2 := by
  have hu : 0 ≤ a - b := by linarith
  have hm : 0 ≤ b - (2 * t + 1) := by linarith
  have ht0 : (0 : ℝ) ≤ t := by linarith
  nlinarith [hu, hm, ht0, mul_nonneg hm hm, mul_nonneg hu hm, mul_nonneg ht0 hm,
    mul_nonneg ht0 hu, mul_nonneg (mul_nonneg hm hm) hm, mul_nonneg (mul_nonneg ht0 hm) hm,
    mul_nonneg (mul_nonneg ht0 ht0) hm, mul_nonneg (mul_nonneg ht0 ht0) hu,
    mul_nonneg (mul_nonneg hu hm) hm, mul_nonneg (mul_nonneg ht0 hu) hm,
    mul_nonneg ht0 (mul_nonneg ht0 ht0)]

/-- The denominator of the second term of Lemma 2.1 at `k = t − 1`, once `#T` is replaced by its
upper bound, is `#A·#B − (#B − t + 1)²`. -/
theorem case32_denominator (a b t T : ℝ) (hT : T = a - b + t - 1) :
    (t - 1) * a + T * (b - (t - 1)) = a * b - (b - t + 1) ^ 2 := by
  rw [hT]
  ring


/-- The first term of Lemma 2.1 always dominates `#A·#B/2`, because `√(t(t−1)) ≤ t`. -/
theorem half_le_first_term {t : ℝ} (ht : 1 ≤ t) {M : ℝ} (hM : 0 ≤ M) :
    M / 2 ≤ t * M / (t + Real.sqrt (t * (t - 1))) := by
  have hnn : (0 : ℝ) ≤ t * (t - 1) := by nlinarith
  have hs2 : Real.sqrt (t * (t - 1)) ^ 2 = t * (t - 1) := Real.sq_sqrt hnn
  have hs0 : (0 : ℝ) ≤ Real.sqrt (t * (t - 1)) := Real.sqrt_nonneg _
  have hst : Real.sqrt (t * (t - 1)) ≤ t := by nlinarith [hs2, hs0]
  have hpos : (0 : ℝ) < t + Real.sqrt (t * (t - 1)) := by linarith
  rw [div_le_div_iff₀ (by norm_num) hpos]
  nlinarith [hM, hst, hs0]

/-- **The first branch of CASE 3.2.**  `#A·#B/2 ≤ t(#A + #B − 2t)` is impossible when
`#A ≥ #B ≥ 2t + 1`. -/
theorem case32_first_branch {a b t : ℝ} (hb : 2 * t + 1 ≤ b) (hab : b ≤ a)
    (h : a * b / 2 ≤ t * (a + b - 2 * t)) : False := by
  have h1 : (0 : ℝ) < a - 2 * t := by linarith
  have h2 : (0 : ℝ) < b - 2 * t := by linarith
  nlinarith [mul_pos h1 h2]

end GaloisForLFunctions.HTGeometry.AddComb
