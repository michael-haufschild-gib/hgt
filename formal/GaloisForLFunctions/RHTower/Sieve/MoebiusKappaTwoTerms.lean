import GaloisForLFunctions.RHTower.Sieve.MoebiusRatePowers

/-!
# The four edge terms against a common majorant

Each edge of the truncated rectangle contributes a term of the contour bound, and each is bounded
by the trivial size times the edge's exponential factor once the truncation height `≍ K` is known
to dominate.  The three statements here are purely arithmetic — no zeta, no contour — so that the
assembly of the rate never has to elaborate a long chain.

The right line and a horizontal edge reduce to the same inequality: the horizontal edge's factor
`log²K` cancels against the rectangle width `2 log^{-2}K`.
-/

namespace RHTower.Sieve

/-- **The right line's term.**  The truncation height `(K-3)/2` absorbs the growth `K` of the
right-line power, with a factor `2` to spare once `K ≥ 7`. -/
theorem contour_right_term_le {R A Zd Z E K : ℝ} (hR : 0 ≤ R) (hA : 0 ≤ A) (hZ : 0 ≤ Z)
    (hE : 0 ≤ E) (hK : 7 ≤ K) (hZd : Zd ≤ Z * E * K) :
    2 * (R * (A * Zd)) / ((K - 3) / 2) ≤ 8 * (R * A * Z * E) := by
  have hK3 : (0 : ℝ) < (K - 3) / 2 := by linarith
  rw [div_le_iff₀ hK3]
  have hRA : (0 : ℝ) ≤ R * A := mul_nonneg hR hA
  have h1 : 2 * (R * (A * Zd)) ≤ 2 * (R * A) * (Z * E * K) := by
    nlinarith [mul_le_mul_of_nonneg_left hZd hRA]
  have hP : (0 : ℝ) ≤ R * A * Z * E := mul_nonneg (mul_nonneg hRA hZ) hE
  nlinarith [h1, mul_nonneg hP (by linarith : (0 : ℝ) ≤ 2 * K - 12)]

/-- **A horizontal edge's term.**  The factor `log²K` cancels against the rectangle width. -/
theorem contour_horizontal_term_le {M W B Zd Z E K : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hZ : 0 ≤ Z)
    (hE : 0 ≤ E) (hK : 7 ≤ K) (hW : 0 < W) (hZd : Zd ≤ Z * E * K) :
    M * W * (B * Zd) / ((K - 3) / 2) ^ (0 + 1) * (2 / W) ≤ 8 * (M * B * Z * E) := by
  have hK3 : (0 : ℝ) < (K - 3) / 2 := by linarith
  have hpow : ((K - 3) / 2) ^ (0 + 1) = (K - 3) / 2 := by norm_num
  rw [hpow]
  have hsimp : M * W * (B * Zd) / ((K - 3) / 2) * (2 / W)
      = 2 * (M * (B * Zd)) / ((K - 3) / 2) := by
    field_simp
  rw [hsimp]
  exact contour_right_term_le hM hB hZ hE hK hZd

/-- **The left edge's term.**  Dividing by the left abscissa costs at most a factor `2`. -/
theorem contour_left_term_le {M W A Yc Zc Y Z E c : ℝ} (hM : 0 ≤ M) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (hc : 3 / 4 ≤ c) (hY : 0 ≤ Y) (hE : 0 ≤ E)
    (hYc : Yc ≤ Y * E) (hZc : Zc ≤ Z * E) :
    M * W * (2 * (Yc / c) + 2 * (A * Zc)) ≤ M * W * (4 * (Y * E) + 2 * (A * (Z * E))) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hYE : (0 : ℝ) ≤ Y * E := mul_nonneg hY hE
  have hdiv : Yc / c ≤ 2 * (Y * E) := by
    rw [div_le_iff₀ hc0]
    nlinarith [hYc, mul_nonneg hYE (by linarith : (0 : ℝ) ≤ 2 * c - 1)]
  have hAZ : A * Zc ≤ A * (Z * E) := mul_le_mul_of_nonneg_left hZc hA
  exact mul_le_mul_of_nonneg_left (by linarith [hdiv, hAZ]) (mul_nonneg hM hW)

end RHTower.Sieve
