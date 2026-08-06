import GaloisForLFunctions.RHTower.Sieve.ChebyshevKappaOneShape

/-!
# The five terms of the Chebyshev contour bound against a common shape

Each term of `norm_tsum_vonMangoldt_sub_full_main_le_explicit` is reduced here to the trivial size
times the edge's exponential factor.  The statements are purely arithmetic — no zeta, no contour —
so the assembly of the rate never has to elaborate a long chain.

Two facts do all the work: the right-line power satisfies `Zd ≤ Z·E·T`, so the truncation height
cancels it; and the left abscissa is at least `1/2`, so dividing by it costs at most a factor two.
-/

namespace RHTower.Sieve

/-- **The truncation term.**  The height `T` cancels the right line's growth. -/
theorem cheb_trunc_term_le {S W Zd Z E T : ℝ} (hS0 : 0 ≤ S) (hW0 : 0 ≤ W) (hT : 0 < T)
    (hZd : Zd ≤ Z * E * T) :
    2 * (S * (W * Zd)) / T ≤ 2 * (S * (W * (Z * E))) := by
  rw [div_le_iff₀ hT]
  have h : S * (W * Zd) ≤ S * (W * (Z * E * T)) := by gcongr
  nlinarith [h]

/-- **The left edge's bracket.**  Dividing by the left abscissa costs at most a factor two. -/
theorem cheb_left_bracket_le {Yc Zc Y Z E W c : ℝ} (hc : 1 / 2 ≤ c) (hW0 : 0 ≤ W)
    (hY0 : 0 ≤ Y) (hE0 : 0 ≤ E) (hYZ : Y ≤ Z) (hYc : Yc ≤ Y * E) (hZc : Zc ≤ Z * E) :
    2 * (Yc / c) + 2 * (W * Zc) ≤ 4 * (Z * E) + 2 * (W * (Z * E)) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hZ0 : (0 : ℝ) ≤ Z := le_trans hY0 hYZ
  have hZE0 : (0 : ℝ) ≤ Z * E := mul_nonneg hZ0 hE0
  have h1 : Yc ≤ Z * E := le_trans hYc (mul_le_mul_of_nonneg_right hYZ hE0)
  have hdiv : Yc / c ≤ 2 * (Z * E) := by
    rw [div_le_iff₀ hc0]
    nlinarith [h1, mul_nonneg hZE0 (by linarith : (0 : ℝ) ≤ 2 * c - 1)]
  have hWZ : W * Zc ≤ W * (Z * E) := mul_le_mul_of_nonneg_left hZc hW0
  linarith

/-- **The horizontal edges' pole term.**  A height past one only helps. -/
theorem cheb_horiz_pole_le {w Cd Mm T : ℝ} (hw0 : 0 ≤ w) (hCd0 : 0 ≤ Cd) (hT1 : 1 ≤ T) :
    2 * (w * ((Cd / T ^ (1 + 1) + Mm) / T)) ≤ 2 * (w * ((Cd + Mm) / T)) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hpow : (1 : ℝ) ≤ T ^ (1 + 1) := one_le_pow₀ hT1
  have hle : Cd / T ^ (1 + 1) ≤ Cd := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hCd0, hpow]
  have hstep : (Cd / T ^ (1 + 1) + Mm) / T ≤ (Cd + Mm) / T :=
    div_le_div_of_nonneg_right (by linarith) hT0.le
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep hw0) (by norm_num)

/-- **The horizontal edges' regular term.** -/
theorem cheb_horiz_reg_le {w R W Zd Z E T : ℝ} (hw0 : 0 ≤ w) (hR0 : 0 ≤ R) (hW0 : 0 ≤ W)
    (hT1 : 1 ≤ T) (hZd : Zd ≤ Z * E * T) (hZE0 : 0 ≤ Z * E) :
    2 * (w * (R * (W * Zd / T ^ (1 + 1)))) ≤ 2 * (w * (R * (W * (Z * E)))) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hpow0 : (0 : ℝ) < T ^ (1 + 1) := by positivity
  have hkey : W * Zd / T ^ (1 + 1) ≤ W * (Z * E) := by
    have hTT : T ^ (1 + 1) = T * T := by ring
    rw [hTT, div_le_iff₀ (mul_pos hT0 hT0)]
    have h1 : W * Zd ≤ W * (Z * E * T) := mul_le_mul_of_nonneg_left hZd hW0
    have h2 : (0 : ℝ) ≤ W * (Z * E) := mul_nonneg hW0 hZE0
    nlinarith [h1, mul_nonneg (mul_nonneg h2 hT0.le) (by linarith : (0 : ℝ) ≤ T - 1)]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkey hR0) hw0) (by norm_num)

end RHTower.Sieve
