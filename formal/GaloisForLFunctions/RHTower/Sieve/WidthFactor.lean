import GaloisForLFunctions.RHTower.Sieve.MoebiusContourBoundGeneral

/-!
# The cost of narrow smoothing

The smoothing width enters the contour bound only through `H^{-(j+1)}(N+H+1)^{j+1}`, which is
`((N+H+1)/H)^{j+1}`.  Writing the ratio `N/H` as `L`, this is at most `(L+2)^{j+1}` as soon as
`H ≥ 1`: the `+1` inside contributes at most `1/H ≤ 1`, and the `+H` contributes exactly `1`.

So narrowing the smoothing by a factor `L` costs `L^{j+1}` and nothing else.
-/

namespace RHTower.Sieve

/-- The width factor is at most `L + 2`. -/
theorem width_ratio_le {N H L : ℝ} (hH1 : 1 ≤ H) (hN : 0 ≤ N) (hL : N / H ≤ L) :
    (N + H + 1) / H ≤ L + 2 := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hsplit : (N + H + 1) / H = N / H + 1 + 1 / H := by
    field_simp
  have hinv : 1 / H ≤ 1 := by
    rw [div_le_one hH0]
    exact hH1
  rw [hsplit]
  linarith

/-- The order-two width factor. -/
theorem sq_width_factor_le {N H L C : ℝ} (hH1 : 1 ≤ H) (hN : 0 ≤ N) (hL : N / H ≤ L)
    (hC : 0 ≤ C) :
    C / H ^ 2 * (N + H + 1) ^ 2 ≤ C * (L + 2) ^ 2 := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hratio := width_ratio_le hH1 hN hL
  have hratio0 : (0 : ℝ) ≤ (N + H + 1) / H := by positivity
  have hpow : ((N + H + 1) / H) ^ 2 ≤ (L + 2) ^ 2 := by
    exact pow_le_pow_left₀ hratio0 hratio 2
  have hrw : C / H ^ 2 * (N + H + 1) ^ 2 = C * ((N + H + 1) / H) ^ 2 := by
    rw [div_pow]
    field_simp
  rw [hrw]
  exact mul_le_mul_of_nonneg_left hpow hC

/-- The order-one width factor. -/
theorem width_factor_le {N H L C : ℝ} (hH1 : 1 ≤ H) (hN : 0 ≤ N) (hL : N / H ≤ L)
    (hC : 0 ≤ C) :
    C / H ^ 1 * (N + H + 1) ^ 1 ≤ C * (L + 2) := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hratio := width_ratio_le hH1 hN hL
  have hrw : C / H ^ 1 * (N + H + 1) ^ 1 = C * ((N + H + 1) / H) := by
    rw [pow_one, pow_one]
    field_simp
  rw [hrw]
  exact mul_le_mul_of_nonneg_left hratio hC

end RHTower.Sieve
