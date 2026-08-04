import GaloisForLFunctions.RHTower.Sieve.ZeroFreeAssembly

/-!
# The comparison that the reciprocal bound needs

`norm_inv_riemannZeta_left_le_segment` is left with one hypothesis: the derivative bound times the
distance moved left must not exceed half the lower bound at the abscissa `σ`.  That is the same
balance the zero-free region strikes, with two differences — a factor `2`, and the fact that here
the distance `σ - β` is a free parameter rather than being forced by a hypothetical zero.

The balance is settled by rescaling.  Writing `σ - β = κ·(σ - 1)`, the comparison is exactly the
zero-free comparison applied to `(σ - 1)·κ⁴` in place of `σ - 1`, because the lower bound scales
like the `3/4` power and the two sides then differ by precisely `κ·(σ-1)^{1/4}`.  So a single
scaled form of `quarter_comparison` settles it, and no new numerical constant is needed.
-/

namespace RHTower.Sieve

open Complex

/-- **The quarter comparison, rescaled.**  Applying `quarter_comparison` at `δ·κ⁴` divides the
right-hand side by `κ`, which is what a distance `κ` times the offset requires. -/
theorem quarter_comparison_scaled {L δ κ : ℝ} (hL : 3 ≤ L) (hδ0 : 0 < δ) (hκ : 0 < κ)
    (hδ : δ * κ ^ 4
      < (Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * (2 : ℝ) ^ (-(1 : ℝ) / 4) / 64) ^ (4 : ℕ)
          / L ^ 9) :
    κ * δ ^ ((1 : ℝ) / 4)
      < Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * (5 / 2 + L) ^ (-(1 : ℝ) / 4)
          / (64 * L ^ 2) := by
  have hbase := quarter_comparison hL (by positivity : (0 : ℝ) < δ * κ ^ 4) hδ
  have hsplit : (δ * κ ^ 4) ^ ((1 : ℝ) / 4) = δ ^ ((1 : ℝ) / 4) * κ := by
    rw [Real.mul_rpow hδ0.le (by positivity)]
    congr 1
    rw [← Real.rpow_natCast κ 4, ← Real.rpow_mul hκ.le]
    norm_num
  rw [hsplit, mul_comm] at hbase
  exact hbase

/-- **The comparison, discharged.**  With the offset `δ = σ - 1` and the distance `D = σ - β`
constrained by `D⁴·L⁹ < c·δ³`, the derivative bound `32L²` times the distance is at most half the
lower bound at `σ`.  This is the last hypothesis of the reciprocal estimate. -/
theorem half_comparison {L δ D : ℝ} (hL : 3 ≤ L) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hD0 : 0 < D)
    (hscale : D ^ 4 * L ^ 9
      < (Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * (2 : ℝ) ^ (-(1 : ℝ) / 4) / 64) ^ (4 : ℕ)
          * δ ^ 3) :
    4 * 8 * L ^ 2 * D
      ≤ Real.exp ((-22 - 3 * Real.log (1 + 1 / δ) - Real.log (5 / 2 + L)) / 4) / 2 := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hB0 : (0 : ℝ) < 5 / 2 + L := by linarith
  set κ : ℝ := D / δ with hκdef
  have hκ : 0 < κ := div_pos hD0 hδ0
  have hhyp : δ * κ ^ 4
      < (Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * (2 : ℝ) ^ (-(1 : ℝ) / 4) / 64) ^ (4 : ℕ)
          / L ^ 9 := by
    have heq : δ * κ ^ 4 = D ^ 4 / δ ^ 3 := by
      rw [hκdef, div_pow]
      field_simp
    rw [heq, div_lt_div_iff₀ (by positivity) (by positivity)]
    exact hscale
  have hqc := quarter_comparison_scaled hL hδ0 hκ hhyp
  have hδ34 : (0 : ℝ) < δ ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hδ0 _
  have hmul := mul_lt_mul_of_pos_right hqc hδ34
  have hD : κ * δ ^ ((1 : ℝ) / 4) * δ ^ ((3 : ℝ) / 4) = D := by
    rw [mul_assoc, ← Real.rpow_add hδ0, show (1 : ℝ) / 4 + 3 / 4 = 1 by norm_num,
      Real.rpow_one, hκdef]
    field_simp
  rw [hD] at hmul
  have hpow : (δ / 2) ^ ((3 : ℝ) / 4) = δ ^ ((3 : ℝ) / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) := by
    rw [Real.div_rpow hδ0.le (by norm_num), show (-(3 : ℝ) / 4) = -((3 : ℝ) / 4) by ring,
      Real.rpow_neg (by norm_num), div_eq_mul_inv]
  have hrhs : Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * (5 / 2 + L) ^ (-(1 : ℝ) / 4)
      / (64 * L ^ 2) * δ ^ ((3 : ℝ) / 4)
      = Real.exp (-22 / 4) * (δ / 2) ^ ((3 : ℝ) / 4) * (5 / 2 + L) ^ (-(1 : ℝ) / 4)
        / (64 * L ^ 2) := by
    rw [hpow]
    field_simp
  rw [hrhs] at hmul
  have hmul2 : D * (64 * L ^ 2)
      < Real.exp (-22 / 4) * (δ / 2) ^ ((3 : ℝ) / 4) * (5 / 2 + L) ^ (-(1 : ℝ) / 4) := by
    rwa [lt_div_iff₀ (by positivity : (0 : ℝ) < 64 * L ^ 2)] at hmul
  have hbase := exp_three_four_one_ge hδ0 hδ1 hB0
  have hkey : 4 * 8 * L ^ 2 * D
      ≤ Real.exp (-22 / 4) * (δ / 2) ^ ((3 : ℝ) / 4) * (5 / 2 + L) ^ (-(1 : ℝ) / 4) / 2 := by
    linarith [hmul2]
  refine le_trans hkey ?_
  linarith [hbase]

end RHTower.Sieve
