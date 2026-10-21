import GaloisForLFunctions.ArithmeticCriticalityTheory.FoldBoundaryQuarticGaugeWeilPositivity
import GaloisForLFunctions.ArithmeticIncidencePositivity.CurvedFoldOddWindowPositivity

/-!
# Weil positivity on `[−29/100, 29/100]`: past the plastic fold boundary

The even fold is free only up to the plastic threshold `log ρ ≈ 0.28120`: beyond it the folded
conductance `κ(s) + κ(s + 2x)`, `κ = ω − 2cosh(t/2)`, is negative near the binding pair
`(x, s) → (0, R)`. The negative part is not an obstruction. Midpoint convexity of the minorant
`f(t) = 1/(2t) − 7/4 − t/48 − 9t²/32 − t⁴/192 − t⁵/1600` gives `κ(s) + κ(s + 2x) ≥ 2f(x + s)`, and
convexity of `f` at `281/1000` gives `2f(m) ≥ −13.03 (m − 281/1000)⁺` for `m < 291/1000`
(`weilJumpDensity_fold_ge_neg_pastFoldCost`). A lower bound of the folded conductance by a function of
the outer point is paid by potentials (`integral_kappa_mul_gaugeJumpProfile_ge_foldCost`): a constant
`2 ∫_{y>0} G M ≤ 0.00057` and the edge potential `2R G(|x|)`, which the edge logarithm of the gauge
absorbs.

The gauge is the quartic window `q P`, `q(y) = 1 − 12.98 y² + 38.5 y⁴`, radius `291/1000`, collar
`1/1000`. Its potential is `≈ 0.0032–0.0048` on `[0, 0.23]`; fourteen pieces with anchors
`(3/4)^k (15/16)^j` bound it below by the cost plus `1/1000`. The odd sector is the curved odd fold on
`[−17/50, 17/50]`.

**Theorem** (`fullZeroForm_ge_of_support_le_pastFold`). Every real `F ∈ C²_c` vanishing outside
`[−29/100, 29/100]` satisfies `Ẑ(F) ≥ (1/1000) ∫ F²`; hence `μ(A) ≥ 1/1000` for every aperture
`A ≤ 29/100` (`one_div_1000_le_ccmRestrictedWeilGroundEnergy_pastFold`). The plastic threshold
`log ρ`, the boundary of the free even fold, is not a boundary of Weil positivity.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar GaloisForLFunctions.ArithmeticIncidencePositivity
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The constants and the anchors -/

/-- `−log(291/500) − 291/2000 − (γ + log π) ≥ −1.32646`. -/
theorem pastFoldGauge_constant_ge :
    -1.32646 ≤ -Real.log (2 * (291 / 1000)) - 291 / 1000 / 2 - 2 * archConstantReal := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(-(41 / 250) : ℝ)| < 1 by norm_num) 7
  rw [show (1 : ℝ) - -(41 / 250) = 291 / 250 by norm_num, abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have hsplit : Real.log (2 * (291 / 1000)) = Real.log (291 / 250) - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have h2 := Real.log_two_gt_d9
  have hC := two_mul_archConstantReal_lt_sharp
  linarith [h.1, h.2]

theorem log_sixteen_fifteenths_gt : 0.06453 < Real.log (16 / 15) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(1 / 16 : ℝ)| < 1 by norm_num) 5
  rw [show (1 : ℝ) - 1 / 16 = 15 / 16 by norm_num, abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have e : Real.log (16 / 15) = -Real.log (15 / 16) := by
    rw [← Real.log_inv]; norm_num
  linarith [h.1, h.2]

/-- The anchors `c = (3/4)^k (15/16)^j`:
`−½ log(1 − s) ≥ 0.1438 k + 0.032265 j + (s − (1 − c))/(2c)`. -/
theorem neg_half_log_one_sub_ge_anchor_grid {s : ℝ} (hs : s < 1) (k j : ℕ) :
    0.1438 * k + 0.032265 * j +
        (s - (1 - (3 / 4 : ℝ) ^ k * (15 / 16) ^ j)) / (2 * ((3 / 4) ^ k * (15 / 16) ^ j)) ≤
      -(1 / 2) * Real.log (1 - s) := by
  have hL : 0.2876 * k + 0.06453 * j ≤ -Real.log ((3 / 4 : ℝ) ^ k * (15 / 16) ^ j) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv,
      show (15 / 16 : ℝ) = (16 / 15)⁻¹ by norm_num, Real.log_inv]
    have := log_four_thirds_gt
    have := log_sixteen_fifteenths_gt
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have h := neg_half_log_one_sub_ge_anchor hs (by positivity) hL
  linarith

/-- The hints of an anchored piece `lo ≤ y ≤ hi` of a window inequality in `z = y²`: the interval
bounds, the concavity product, the cubic tangent at the midpoint and the quartic cap. -/
theorem window_piece_hints {y lo hi : ℝ} (hl : lo ≤ y) (hh : y ≤ hi) (h0 : 0 ≤ lo) :
    lo ^ 2 ≤ y ^ 2 ∧ y ^ 2 ≤ hi ^ 2 ∧ 0 ≤ (y ^ 2 - lo ^ 2) * (hi ^ 2 - y ^ 2) ∧
      0 ≤ (y ^ 2 - (lo ^ 2 + hi ^ 2) / 2) ^ 2 * (y ^ 2 + (lo ^ 2 + hi ^ 2)) ∧
      y ^ 4 * y ^ 4 ≤ hi ^ 4 * y ^ 4 := by
  have hyp : 0 ≤ y := h0.trans hl
  have h1 : lo ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ h0 hl 2
  have h2 : y ^ 2 ≤ hi ^ 2 := pow_le_pow_left₀ hyp hh 2
  have h4 : y ^ 4 ≤ hi ^ 4 := pow_le_pow_left₀ hyp hh 4
  exact ⟨h1, h2, mul_nonneg (by linarith) (by linarith),
    mul_nonneg (sq_nonneg _) (by nlinarith), mul_le_mul_of_nonneg_right h4 (by positivity)⟩

/-- **The window inequality past the fold**, inner part `[0, 0.189]`. -/
theorem pastFoldGauge_window_inequality_inner_low {y D : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 0.189)
    (hD : -1.32646 ≤ D) :
    0.00157 ≤ (1 - 12.98 * y ^ 2 + 38.5 * y ^ 4) *
        (D + -(1 / 2) * Real.log (1 - 1000000 / 84681 * y ^ 2)) +
      (1.32933 - 22.9261 * y ^ 2 + 85.50528 * y ^ 4 + 1.38535 * y ^ 6 - 0.40105 * y ^ 8) := by
  have hz0 : 0 ≤ y ^ 2 := sq_nonneg y
  have hy2 : y ^ 2 ≤ 0.189 ^ 2 := pow_le_pow_left₀ hy0 hy 2
  have hq : 0 ≤ (1 - 12.98 * y ^ 2 + 38.5 * y ^ 4) := by nlinarith
  have hs : 1000000 / 84681 * y ^ 2 < 1 := by nlinarith
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have anc := fun k j : ℕ => mul_le_mul_of_nonneg_left
    (neg_half_log_one_sub_ge_anchor_grid (s := 1000000 / 84681 * y ^ 2) hs k j) hq
  set ℓ := -(1 / 2) * Real.log (1 - 1000000 / 84681 * y ^ 2) with hℓ
  rcases le_or_gt y 0.077 with h0 | h0
  · obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints hy0 h0 (by norm_num : (0 : ℝ) ≤ 0)
    have h := anc 0 0; norm_num at h; linarith
  rcases le_or_gt y 0.129 with h1 | h1
  · obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0.le h1 (by norm_num)
    have h := anc 0 2; norm_num at h; linarith
  rcases le_or_gt y 0.157 with h2 | h2
  · obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h1.le h2 (by norm_num)
    have h := anc 1 0; norm_num at h; linarith
  rcases le_or_gt y 0.177 with h3 | h3
  · obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h2.le h3 (by norm_num)
    have h := anc 1 2; norm_num at h; linarith
  · obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h3.le hy (by norm_num)
    have h := anc 1 3; norm_num at h; linarith

/-- **The window inequality past the fold**, inner part `[0.189, 0.237]`. -/
theorem pastFoldGauge_window_inequality_inner_high {y D : ℝ} (hy0 : 0.189 ≤ y) (hy : y ≤ 0.237)
    (hD : -1.32646 ≤ D) :
    0.00157 ≤ (1 - 12.98 * y ^ 2 + 38.5 * y ^ 4) *
        (D + -(1 / 2) * Real.log (1 - 1000000 / 84681 * y ^ 2)) +
      (1.32933 - 22.9261 * y ^ 2 + 85.50528 * y ^ 4 + 1.38535 * y ^ 6 - 0.40105 * y ^ 8) := by
  have hyp : 0 ≤ y := le_trans (by norm_num) hy0
  have hz0 : 0 ≤ y ^ 2 := sq_nonneg y
  have hy2 : y ^ 2 ≤ 0.237 ^ 2 := pow_le_pow_left₀ hyp hy 2
  have hq : 0 ≤ (1 - 12.98 * y ^ 2 + 38.5 * y ^ 4) := by nlinarith
  have hs : 1000000 / 84681 * y ^ 2 < 1 := by nlinarith
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have anc := fun k j : ℕ => mul_le_mul_of_nonneg_left
    (neg_half_log_one_sub_ge_anchor_grid (s := 1000000 / 84681 * y ^ 2) hs k j) hq
  set ℓ := -(1 / 2) * Real.log (1 - 1000000 / 84681 * y ^ 2) with hℓ
  rcases le_or_gt y 0.201 with h0 | h0
  · obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints hy0 h0 (by norm_num)
    have h := anc 2 0; norm_num at h; linarith
  rcases le_or_gt y 0.212 with h1 | h1
  · obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0.le h1 (by norm_num)
    have h := anc 2 2; norm_num at h; linarith
  rcases le_or_gt y 0.22 with h2 | h2
  · obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h1.le h2 (by norm_num)
    have h := anc 2 3; norm_num at h; linarith
  rcases le_or_gt y 0.23 with h3 | h3
  · obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h2.le h3 (by norm_num)
    have h := anc 3 0; norm_num at h; linarith
  · obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h3.le hy (by norm_num)
    have h := anc 3 2; norm_num at h; linarith

/-- **The window inequality past the fold**, outer part `[0.237, 281/1000]`, where the second-moment
coefficient is nonpositive and its correction is at most `3·10⁻⁶`. -/
theorem pastFoldGauge_window_inequality_outer {y D : ℝ} (hy0 : 0.237 ≤ y) (hy : y ≤ 281 / 1000)
    (hD : -1.32646 ≤ D) :
    0.00157 ≤ (1 - 12.98 * y ^ 2 + 38.5 * y ^ 4) *
        (D + -(1 / 2) * Real.log (1 - 1000000 / 84681 * y ^ 2)) +
      (1.32967 - 22.89214 * y ^ 2 + 85.02981 * y ^ 4 - 2.81596 * y ^ 6 - 0.40105 * y ^ 8 -
        0.000003) := by
  have hyp : 0 ≤ y := le_trans (by norm_num) hy0
  have hz0 : 0 ≤ y ^ 2 := sq_nonneg y
  have hy2 : y ^ 2 ≤ (281 / 1000) ^ 2 := pow_le_pow_left₀ hyp hy 2
  have hq : 0 ≤ (1 - 12.98 * y ^ 2 + 38.5 * y ^ 4) := by nlinarith
  have hs : 1000000 / 84681 * y ^ 2 < 1 := by nlinarith
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have anc := fun k j : ℕ => mul_le_mul_of_nonneg_left
    (neg_half_log_one_sub_ge_anchor_grid (s := 1000000 / 84681 * y ^ 2) hs k j) hq
  set ℓ := -(1 / 2) * Real.log (1 - 1000000 / 84681 * y ^ 2) with hℓ
  rcases le_or_gt y 0.251 with h0 | h0
  · obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints hy0 h0 (by norm_num)
    have h := anc 4 0; norm_num at h; linarith
  rcases le_or_gt y 0.27 with h1 | h1
  · obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0.le h1 (by norm_num)
    have h := anc 5 0; norm_num at h; linarith
  · obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h1.le hy (by norm_num)
    have h := anc 6 3; norm_num at h; linarith

/-- **The window inequality past the fold**, edge part `[281/1000, 29/100]`, carrying the fold cost
`13.4938 (y² − (281/1000)²)`. -/
theorem pastFoldGauge_window_inequality_edge {y D : ℝ} (hy0 : 281 / 1000 ≤ y) (hy : y ≤ 29 / 100)
    (hD : -1.32646 ≤ D) :
    0.00157 + 13.4938 * (y ^ 2 - (281 / 1000) ^ 2) ≤ (1 - 12.98 * y ^ 2 + 38.5 * y ^ 4) *
        (D + -(1 / 2) * Real.log (1 - 1000000 / 84681 * y ^ 2)) +
      (1.32967 - 22.89214 * y ^ 2 + 85.02981 * y ^ 4 - 2.81596 * y ^ 6 - 0.40105 * y ^ 8 -
        0.000003) := by
  have hyp : 0 ≤ y := le_trans (by norm_num) hy0
  have hz0 : 0 ≤ y ^ 2 := sq_nonneg y
  have hy2 : y ^ 2 ≤ (29 / 100) ^ 2 := pow_le_pow_left₀ hyp hy 2
  have hq : 0 ≤ (1 - 12.98 * y ^ 2 + 38.5 * y ^ 4) := by nlinarith
  have hs : 1000000 / 84681 * y ^ 2 < 1 := by nlinarith
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have h := mul_le_mul_of_nonneg_left
    (neg_half_log_one_sub_ge_anchor_grid (s := 1000000 / 84681 * y ^ 2) hs 9 3) hq
  set ℓ := -(1 / 2) * Real.log (1 - 1000000 / 84681 * y ^ 2) with hℓ
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints hy0 hy (by norm_num)
  norm_num at h
  linarith


/-! ### The fold past the plastic boundary -/

/-- **The folded conductance as a function of the outer point.** For `x + s < 291/1000`,
`κ(s) + κ(s + 2x) ≥ 2f(s + x)`: the reciprocal part gains `x²/(m(m² − x²)) ≥ x²/0.291³`, the
polynomial part loses `x²(9/16 + …)`. -/
theorem weilJumpDensity_fold_ge_two_mul_poly {s x : ℝ} (hs : 0 < s) (hx : 0 < x)
    (hxs : x + s < 291 / 1000) :
    1 / (s + x) + 2 * (-(7 / 4) - (s + x) / 48 - 9 * (s + x) ^ 2 / 32 - (s + x) ^ 4 / 192 -
      (s + x) ^ 5 / 1600) ≤ weilJumpDensity s + weilJumpDensity (s + 2 * x) := by
  have h1 := weilJumpDensity_ge_poly hs (by linarith)
  have h2 := weilJumpDensity_ge_poly (t := s + 2 * x) (by linarith) (by linarith)
  set m := s + x with hmdef
  have hm : 0 < m := by rw [hmdef]; linarith
  have hmR : m < 291 / 1000 := by rw [hmdef]; linarith
  have hxm : x < m := by rw [hmdef]; linarith
  -- the reciprocal part: `1/(2s) + 1/(2t) = 1/m + x²/(m(m² − x²))`
  have hst : 0 < m ^ 2 - x ^ 2 := by nlinarith
  have hrec : 1 / (2 * s) + 1 / (2 * (s + 2 * x)) = 1 / m + x ^ 2 / (m * (m ^ 2 - x ^ 2)) := by
    have hs' : s = m - x := by rw [hmdef]; ring
    have ht' : s + 2 * x = m + x := by rw [hmdef]; ring
    rw [ht', hs']
    have h1' : m - x ≠ 0 := by linarith
    have h2' : m + x ≠ 0 := by linarith
    field_simp
    ring
  have hden : m * (m ^ 2 - x ^ 2) ≤ (291 / 1000) ^ 3 := by
    have : m * (m ^ 2 - x ^ 2) ≤ m ^ 3 := by nlinarith [sq_nonneg x]
    have h3 : m ^ 3 ≤ (291 / 1000) ^ 3 := pow_le_pow_left₀ hm.le hmR.le 3
    linarith
  have hgain : x ^ 2 / (291 / 1000) ^ 3 ≤ x ^ 2 / (m * (m ^ 2 - x ^ 2)) :=
    div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) hden
  -- the polynomial part at `m ± x`
  have hpoly : (-(7 / 4) - s / 48 - 9 * s ^ 2 / 32 - s ^ 4 / 192 - s ^ 5 / 1600) +
      (-(7 / 4) - (s + 2 * x) / 48 - 9 * (s + 2 * x) ^ 2 / 32 - (s + 2 * x) ^ 4 / 192 -
        (s + 2 * x) ^ 5 / 1600) =
      2 * (-(7 / 4) - m / 48 - 9 * m ^ 2 / 32 - m ^ 4 / 192 - m ^ 5 / 1600) -
        x ^ 2 * (9 / 16 + m ^ 2 / 16 + x ^ 2 / 96 + m ^ 3 / 80 + m * x ^ 2 / 160) := by
    rw [hmdef]; ring
  have hbr : x ^ 2 * (9 / 16 + m ^ 2 / 16 + x ^ 2 / 96 + m ^ 3 / 80 + m * x ^ 2 / 160) ≤
      x ^ 2 / (291 / 1000) ^ 3 := by
    have hm2 : m ^ 2 ≤ (291 / 1000) ^ 2 := pow_le_pow_left₀ hm.le hmR.le 2
    have hx2 : x ^ 2 ≤ (291 / 1000) ^ 2 := pow_le_pow_left₀ hx.le (by linarith) 2
    have hm3 : m ^ 3 ≤ (291 / 1000) ^ 3 := pow_le_pow_left₀ hm.le hmR.le 3
    have hmx : m * x ^ 2 ≤ (291 / 1000) ^ 3 := by
      have := mul_le_mul hmR.le hx2 (sq_nonneg x) (by norm_num)
      linarith [show (291 / 1000 : ℝ) * (291 / 1000) ^ 2 = (291 / 1000) ^ 3 by ring]
    have hB : 9 / 16 + m ^ 2 / 16 + x ^ 2 / 96 + m ^ 3 / 80 + m * x ^ 2 / 160 ≤
        1 / (291 / 1000) ^ 3 := by
      norm_num; nlinarith
    have := mul_le_mul_of_nonneg_left hB (sq_nonneg x)
    rw [mul_one_div] at this
    exact this
  linarith [h1, h2, hpoly, hbr, hrec, hgain]

/-- The fold cost `G(y) = 13.03 (min(y, 291/1000) − 281/1000)⁺`. -/
def pastFoldCost (y : ℝ) : ℝ := 1303 / 100 * max (min y (291 / 1000) - 281 / 1000) 0

theorem continuous_pastFoldCost : Continuous pastFoldCost := by
  unfold pastFoldCost; fun_prop

theorem pastFoldCost_nonneg (y : ℝ) : 0 ≤ pastFoldCost y :=
  mul_nonneg (by norm_num) (le_max_right _ _)

theorem pastFoldCost_le (y : ℝ) : pastFoldCost y ≤ 1303 / 10000 := by
  unfold pastFoldCost
  have : max (min y (291 / 1000) - 281 / 1000) 0 ≤ 1 / 100 :=
    max_le (by linarith [min_le_right y (291 / 1000)]) (by norm_num)
  linarith

theorem pastFoldCost_eq_zero {y : ℝ} (hy : y ≤ 281 / 1000) : pastFoldCost y = 0 := by
  unfold pastFoldCost
  rw [max_eq_right (by linarith [min_le_left y (291 / 1000)]), mul_zero]

/-- On the edge the cost potential is at most `13.4938 (y² − (281/1000)²)`. -/
theorem pastFoldCost_le_sq {y : ℝ} (hy : 281 / 1000 ≤ y) :
    2 * (291 / 1000) * pastFoldCost y ≤ 13.4938 * (y ^ 2 - (281 / 1000) ^ 2) := by
  unfold pastFoldCost
  have h1 : max (min y (291 / 1000) - 281 / 1000) 0 ≤ y - 281 / 1000 :=
    max_le (by linarith [min_le_left y (291 / 1000)]) (by linarith)
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y - 281 / 1000)
    (by linarith : (0 : ℝ) ≤ y + 281 / 1000 - 562 / 1000)]

/-- **The fold cost past the plastic boundary.** For `x + s < 291/1000`,
`κ(s) + κ(s + 2x) ≥ −13.03 (x + s − 281/1000)⁺`: `f` is positive up to `281/1000` and its tangent
there has slope `> −6.515`. -/
theorem weilJumpDensity_fold_ge_neg_pastFoldCost {s x : ℝ} (hs : 0 < s) (hx : 0 < x)
    (hxs : x + s < 291 / 1000) :
    -pastFoldCost (x + s) ≤ weilJumpDensity s + weilJumpDensity (s + 2 * x) := by
  have h := weilJumpDensity_fold_ge_two_mul_poly hs hx hxs
  rw [show x + s = s + x by ring]
  rw [show x + s = s + x by ring] at hxs
  set m := s + x with hmdef
  have hm0 : 0 < m := by rw [hmdef]; linarith
  have hm2 : m ^ 2 ≤ (291 / 1000) ^ 2 := pow_le_pow_left₀ hm0.le hxs.le 2
  have hm4 : m ^ 4 ≤ (291 / 1000) ^ 4 := pow_le_pow_left₀ hm0.le hxs.le 4
  have hm5 : m ^ 5 ≤ (291 / 1000) ^ 5 := pow_le_pow_left₀ hm0.le hxs.le 5
  rcases le_or_gt m (281 / 1000) with hm | hm
  · rw [pastFoldCost_eq_zero hm]
    have hinv : 1000 / 281 ≤ 1 / m := by rw [le_div_iff₀ hm0]; nlinarith
    have hm2' : m ^ 2 ≤ (281 / 1000) ^ 2 := pow_le_pow_left₀ hm0.le hm 2
    have hm4' : m ^ 4 ≤ (281 / 1000) ^ 4 := pow_le_pow_left₀ hm0.le hm 4
    have hm5' : m ^ 5 ≤ (281 / 1000) ^ 5 := pow_le_pow_left₀ hm0.le hm 5
    linarith
  · have hG : pastFoldCost m = 1303 / 100 * (m - 281 / 1000) := by
      unfold pastFoldCost
      rw [min_eq_left hxs.le, max_eq_left (by linarith)]
    rw [hG]
    -- the tangent of `1/m` at `281/1000`
    have hinv : 2 * (1000 / 281) - m * (1000 / 281) ^ 2 ≤ 1 / m := by
      rw [le_div_iff₀ hm0]; nlinarith [sq_nonneg (m * (1000 / 281) - 1)]
    -- the chord of `m²` on `[281/1000, 291/1000]`
    have hch : m ^ 2 ≤ (281 / 1000 + 291 / 1000) * m - 281 / 1000 * (291 / 1000) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ m - 281 / 1000)
        (by linarith : (0 : ℝ) ≤ 291 / 1000 - m)]
    linarith

/-! ### The cost constant -/

/-- On the edge `[281/1000, 291/1000]` the gauge is at most `q(281/1000) < 0.2152`. -/
theorem pastFoldGauge_le_edge {y : ℝ} (hy1 : 281 / 1000 ≤ |y|) (hy2 : |y| ≤ 291 / 1000) :
    quarticWindowGauge (649 / 50) (77 / 2) (291 / 1000) (1 / 1000) y ≤ 0.2152 := by
  have hz1 : (281 / 1000) ^ 2 ≤ y ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) hy1 2; rwa [sq_abs] at this
  have hz2 : y ^ 2 ≤ (291 / 1000) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg y) hy2 2; rwa [sq_abs] at this
  have hq0 : 0 ≤ quarticProfile (649 / 50) (77 / 2) y := by
    have := quarticProfile_ge_of_le (c := 649 / 50) (d := 77 / 2) (R := 291 / 1000) (by norm_num)
      (by norm_num) hy2
    linarith
  have hq : quarticProfile (649 / 50) (77 / 2) y ≤ 0.2152 := by
    unfold quarticProfile
    have h4 : y ^ 4 = (y ^ 2) ^ 2 := by ring
    rw [h4]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y ^ 2 - (281 / 1000) ^ 2)
      (by nlinarith : (0 : ℝ) ≤ 649 / 50 - 77 / 2 * (y ^ 2 + (281 / 1000) ^ 2))]
  unfold quarticWindowGauge
  have := mul_le_mul_of_nonneg_left (plateauGauge_le_one (291 / 1000) (1 / 1000) y) hq0
  linarith

/-- **The constant cost**: `∫_{y>0} G(y) M(y) dy ≤ 0.000285`, `G` supported in
`[281/1000, 291/1000]` where `G ≤ 0.1303`, `M ≤ 0.2152`. -/
theorem integral_pastFoldCost_mul_gauge_le :
    ∫ y in Ioi (0 : ℝ), pastFoldCost y *
      quarticWindowGauge (649 / 50) (77 / 2) (291 / 1000) (1 / 1000) y ≤ 0.000285 := by
  have hδ : (0 : ℝ) < 1 / 1000 := by norm_num
  have hint : Integrable fun y => pastFoldCost y *
      quarticWindowGauge (649 / 50) (77 / 2) (291 / 1000) (1 / 1000) y :=
    (continuous_pastFoldCost.mul (contDiff_quarticWindowGauge _ _ _ _).continuous
      ).integrable_of_hasCompactSupport (hasCompactSupport_quarticWindowGauge _ _ _ hδ).mul_left
  have hind : IntegrableOn (fun y => (Ioc (281 / 1000 : ℝ) (291 / 1000)).indicator
      (fun _ => (0.02805 : ℝ)) y) (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))).integrableOn
  have hpt : ∀ y ∈ Ioi (0 : ℝ), pastFoldCost y *
      quarticWindowGauge (649 / 50) (77 / 2) (291 / 1000) (1 / 1000) y ≤
      (Ioc (281 / 1000 : ℝ) (291 / 1000)).indicator (fun _ => (0.02805 : ℝ)) y := by
    intro y hy
    have hy0 : 0 < y := hy
    have hI0 : 0 ≤ (Ioc (281 / 1000 : ℝ) (291 / 1000)).indicator (fun _ => (0.02805 : ℝ)) y :=
      Set.indicator_nonneg (fun _ _ => by norm_num) y
    by_cases h1 : y ≤ 281 / 1000
    · rw [pastFoldCost_eq_zero h1, zero_mul]; exact hI0
    by_cases h2 : 291 / 1000 ≤ y
    · rw [quarticWindowGauge_eq_zero _ _ hδ (by rw [abs_of_pos hy0]; exact h2), mul_zero]
      exact hI0
    rw [Set.indicator_of_mem (show y ∈ Ioc (281 / 1000 : ℝ) (291 / 1000) from
      ⟨not_le.mp h1, (not_le.mp h2).le⟩)]
    have hM := pastFoldGauge_le_edge (y := y) (by rw [abs_of_pos hy0]; linarith)
      (by rw [abs_of_pos hy0]; linarith)
    have hM0 := quarticWindowGauge_nonneg (c := 649 / 50) (d := 77 / 2) (R := 291 / 1000)
      (by norm_num) (by norm_num) (by norm_num) hδ y
    have hG := pastFoldCost_le y
    have hG0 := pastFoldCost_nonneg y
    calc pastFoldCost y * quarticWindowGauge (649 / 50) (77 / 2) (291 / 1000) (1 / 1000) y ≤
        1303 / 10000 * 0.2152 := mul_le_mul hG hM hM0 (by norm_num)
      _ ≤ 0.02805 := by norm_num
  have hval : (∫ y in Ioi (0 : ℝ), (Ioc (281 / 1000 : ℝ) (291 / 1000)).indicator
      (fun _ => (0.02805 : ℝ)) y) = 0.02805 * (1 / 100) := by
    rw [setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.mpr (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))]
    simp only [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc]
    norm_num
  have := setIntegral_mono_on hint.integrableOn hind measurableSet_Ioi hpt
  rw [hval] at this
  linarith

/-! ### The potential of the gauge past the fold -/

/-- The potential on the inner region `|x| ≤ 0.237`, where `12.98 − 231 x² ≥ 0`, as the window
polynomial. -/
theorem pastFoldGauge_potential_ge_inner_poly {x : ℝ} (hx : |x| ≤ 0.237) :
    (1 - 12.98 * |x| ^ 2 + 38.5 * |x| ^ 4) *
        ((-Real.log (2 * (291 / 1000)) - 291 / 1000 / 2 - 2 * archConstantReal) +
          -(1 / 2) * Real.log (1 - 1000000 / 84681 * |x| ^ 2)) +
      (1.32933 - 22.9261 * |x| ^ 2 + 85.50528 * |x| ^ 4 + 1.38535 * |x| ^ 6 -
        0.40105 * |x| ^ 8) ≤
    -poleFreeWeilOperator (quarticWindowGauge (649 / 50) (77 / 2) (291 / 1000) (1 / 1000)) x +
      2 * ∫ y, quarticWindowGauge (649 / 50) (77 / 2) (291 / 1000) (1 / 1000) y *
        Real.cosh ((x - y) / 2) := by
  set y := |x| with hydef
  have hy0 : 0 ≤ y := abs_nonneg x
  have hd : (0 : ℝ) ≤ 77 / 2 := by norm_num
  have hdc2 : 2 * (77 / 2) * (291 / 1000 : ℝ) ^ 2 ≤ 649 / 50 := by norm_num
  have hqR : (0 : ℝ) ≤ 1 - 649 / 50 * (291 / 1000) ^ 2 + 77 / 2 * (291 / 1000) ^ 4 := by norm_num
  have hδ : (0 : ℝ) < 1 / 1000 := by norm_num
  have hyR : |y| ≤ 291 / 1000 := by rw [abs_of_nonneg hy0]; linarith
  have hWy : poleFreeWeilOperator (quarticWindowGauge (649 / 50) (77 / 2) (291 / 1000) (1 / 1000)) x =
      poleFreeWeilOperator (quarticWindowGauge (649 / 50) (77 / 2) (291 / 1000) (1 / 1000)) y := by
    rcases le_or_gt 0 x with h | h
    · rw [hydef, abs_of_nonneg h]
    · rw [hydef, abs_of_neg h, poleFreeWeilOperator_neg (quarticWindowGauge_neg _ _ _ _)]
  rw [hWy]
  have hα : 0 ≤ 649 / 50 - 6 * (77 / 2) * y ^ 2 := by
    have : y ^ 2 ≤ 0.237 ^ 2 := pow_le_pow_left₀ hy0 hx 2
    linarith
  have hW := neg_poleFreeWeilOperator_quarticWindowGauge_ge_max (c := 649 / 50) (d := 77 / 2)
    (R := 291 / 1000) (δ := 1 / 1000) (x := y) hd hdc2 hqR hδ (by norm_num) hy0 (by linarith)
  rw [max_eq_left hα] at hW
  have hbr := cubicGauge_bracket_ge (R := 291 / 1000) (x := y) (by norm_num) (by norm_num)
    (by rw [abs_of_nonneg hy0]; linarith)
  have hk : y ^ 2 / (291 / 1000) ^ 2 = 1000000 / 84681 * y ^ 2 := by ring
  rw [hk] at hbr
  have hq0 : 0 ≤ quarticProfile (649 / 50) (77 / 2) y := by
    have := quarticProfile_ge_of_le hd hdc2 hyR; linarith
  have hqbr := mul_le_mul_of_nonneg_left hbr hq0
  have hG := integral_quarticWindowGauge_cosh_ge (c := 649 / 50) (d := 77 / 2) (R := 291 / 1000)
    (δ := 1 / 1000) (x := x) hd hdc2 hqR hδ (by norm_num) (by norm_num) (by linarith)
  rw [← sq_abs x, ← hydef] at hG
  have p2 := pow_nonneg hy0 2
  have p4 := pow_nonneg hy0 4
  have p6 := pow_nonneg hy0 6
  have p8 := pow_nonneg hy0 8
  simp only [levyMomentPoly, levyMomentErr, Nat.cast_ofNat] at hW
  unfold quarticProfile at hW hqbr
  linarith [hW, hqbr, hG, p2, p4, p6, p8]

/-- The potential on the outer region `0.237 ≤ |x| ≤ 29/100`, where the second-moment correction is at
most `3·10⁻⁶`, as the window polynomial. -/
theorem pastFoldGauge_potential_ge_outer_poly {x : ℝ} (hx1 : 0.237 ≤ |x|) (hx : |x| ≤ 29 / 100) :
    (1 - 12.98 * |x| ^ 2 + 38.5 * |x| ^ 4) *
        ((-Real.log (2 * (291 / 1000)) - 291 / 1000 / 2 - 2 * archConstantReal) +
          -(1 / 2) * Real.log (1 - 1000000 / 84681 * |x| ^ 2)) +
      (1.32967 - 22.89214 * |x| ^ 2 + 85.02981 * |x| ^ 4 - 2.81596 * |x| ^ 6 -
        0.40105 * |x| ^ 8 - 0.000003) ≤
    -poleFreeWeilOperator (quarticWindowGauge (649 / 50) (77 / 2) (291 / 1000) (1 / 1000)) x +
      2 * ∫ y, quarticWindowGauge (649 / 50) (77 / 2) (291 / 1000) (1 / 1000) y *
        Real.cosh ((x - y) / 2) := by
  set y := |x| with hydef
  have hy0 : 0 ≤ y := abs_nonneg x
  have hd : (0 : ℝ) ≤ 77 / 2 := by norm_num
  have hdc2 : 2 * (77 / 2) * (291 / 1000 : ℝ) ^ 2 ≤ 649 / 50 := by norm_num
  have hqR : (0 : ℝ) ≤ 1 - 649 / 50 * (291 / 1000) ^ 2 + 77 / 2 * (291 / 1000) ^ 4 := by norm_num
  have hδ : (0 : ℝ) < 1 / 1000 := by norm_num
  have hyR : |y| ≤ 291 / 1000 := by rw [abs_of_nonneg hy0]; linarith
  have hWy : poleFreeWeilOperator (quarticWindowGauge (649 / 50) (77 / 2) (291 / 1000) (1 / 1000)) x =
      poleFreeWeilOperator (quarticWindowGauge (649 / 50) (77 / 2) (291 / 1000) (1 / 1000)) y := by
    rcases le_or_gt 0 x with h | h
    · rw [hydef, abs_of_nonneg h]
    · rw [hydef, abs_of_neg h, poleFreeWeilOperator_neg (quarticWindowGauge_neg _ _ _ _)]
  rw [hWy]
  have hmax : max (649 / 50 - 6 * (77 / 2) * y ^ 2) 0 ≤ 0.0051 := by
    have : 0.237 ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by norm_num) hx1 2
    exact max_le (by linarith) (by norm_num)
  have hE0 : 0 ≤ levyMomentErr 2 (291 / 1000 - y) + levyMomentErr 2 (291 / 1000 + y) := by
    unfold levyMomentErr
    have : 0 ≤ 291 / 1000 - y := by linarith
    positivity
  have hE1 : levyMomentErr 2 (291 / 1000 - y) + levyMomentErr 2 (291 / 1000 + y) ≤ 0.00042 := by
    unfold levyMomentErr
    have ha : (291 / 1000 - y) ^ (2 + 3) ≤ (54 / 1000 : ℝ) ^ 5 :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have hb : (291 / 1000 + y) ^ (2 + 3) ≤ (581 / 1000 : ℝ) ^ 5 :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    push_cast at ha hb ⊢
    norm_num at ha hb ⊢
    linarith
  have hcorr : max (649 / 50 - 6 * (77 / 2) * y ^ 2) 0 *
      (levyMomentErr 2 (291 / 1000 - y) + levyMomentErr 2 (291 / 1000 + y)) ≤ 0.000003 :=
    (mul_le_mul hmax hE1 hE0 (by norm_num)).trans (by norm_num)
  have hW := neg_poleFreeWeilOperator_quarticWindowGauge_ge_max (c := 649 / 50) (d := 77 / 2)
    (R := 291 / 1000) (δ := 1 / 1000) (x := y) hd hdc2 hqR hδ (by norm_num) hy0 (by linarith)
  have hbr := cubicGauge_bracket_ge (R := 291 / 1000) (x := y) (by norm_num) (by norm_num)
    (by rw [abs_of_nonneg hy0]; linarith)
  have hk : y ^ 2 / (291 / 1000) ^ 2 = 1000000 / 84681 * y ^ 2 := by ring
  rw [hk] at hbr
  have hq0 : 0 ≤ quarticProfile (649 / 50) (77 / 2) y := by
    have := quarticProfile_ge_of_le hd hdc2 hyR; linarith
  have hqbr := mul_le_mul_of_nonneg_left hbr hq0
  have hG := integral_quarticWindowGauge_cosh_ge (c := 649 / 50) (d := 77 / 2) (R := 291 / 1000)
    (δ := 1 / 1000) (x := x) hd hdc2 hqR hδ (by norm_num) (by norm_num) (by linarith)
  rw [← sq_abs x, ← hydef] at hG
  have p2 := pow_nonneg hy0 2
  have p4 := pow_nonneg hy0 4
  have p6 := pow_nonneg hy0 6
  have p8 := pow_nonneg hy0 8
  simp only [levyMomentPoly, levyMomentErr, Nat.cast_ofNat] at hW hcorr
  unfold quarticProfile at hW hqbr
  linarith [hW, hqbr, hG, hcorr, p2, p4, p6, p8]

/-- **The potential past the fold pays the fold cost**:
`−𝒲M(x) + 2 ∫ M(y) cosh((x − y)/2) dy ≥ 1/1000 + 0.00057 + 2R G(|x|)` on `[−29/100, 29/100]`. -/
theorem pastFoldGauge_potential_ge {x : ℝ} (hx : |x| ≤ 29 / 100) :
    1 / 1000 + 2 * 0.000285 + 2 * (291 / 1000) * pastFoldCost |x| ≤
    -poleFreeWeilOperator (quarticWindowGauge (649 / 50) (77 / 2) (291 / 1000) (1 / 1000)) x +
      2 * ∫ y, quarticWindowGauge (649 / 50) (77 / 2) (291 / 1000) (1 / 1000) y *
        Real.cosh ((x - y) / 2) := by
  have hD := pastFoldGauge_constant_ge
  have hy0 : 0 ≤ |x| := abs_nonneg x
  rcases le_or_gt |x| 0.237 with h1 | h1
  · have hP := pastFoldGauge_potential_ge_inner_poly h1
    have hc : pastFoldCost |x| = 0 := pastFoldCost_eq_zero (by linarith)
    rcases le_or_gt |x| 0.189 with h2 | h2
    · have hw := pastFoldGauge_window_inequality_inner_low hy0 h2 hD
      rw [hc]; linarith
    · have hw := pastFoldGauge_window_inequality_inner_high h2.le h1 hD
      rw [hc]; linarith
  · have hP := pastFoldGauge_potential_ge_outer_poly h1.le hx
    rcases le_or_gt |x| (281 / 1000) with h2 | h2
    · have hw := pastFoldGauge_window_inequality_outer h1.le h2 hD
      rw [pastFoldCost_eq_zero h2]; linarith
    · have hw := pastFoldGauge_window_inequality_edge h2.le hx hD
      have hc := pastFoldCost_le_sq h2.le
      linarith

/-! ### Even-sector positivity on `[−29/100, 29/100]` -/

/-- **Weil positivity of every even test supported in `[−29/100, 29/100]`.** Every even `F ∈ C²_c`
vanishing outside `[−29/100, 29/100]` satisfies `Ẑ(F) ≥ (1/1000) ∫ F²`: the fold cost is a constant
potential `0.00057` and the edge potential `2R G(|x|)`, both below the gauge potential. -/
theorem fullZeroForm_ge_of_even_support_le_pastFold {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (heven : ∀ x, F (-x) = F x)
    (hsupp : ∀ x, 29 / 100 < |x| → F x = 0) :
    1 / 1000 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  set M := quarticWindowGauge (649 / 50) (77 / 2) (291 / 1000) (1 / 1000) with hMdef
  set u : ℝ → ℝ := fun x => F x * (quarticProfile (649 / 50) (77 / 2) x)⁻¹ with hudef
  have hd : (0 : ℝ) ≤ 77 / 2 := by norm_num
  have hdc2 : 2 * (77 / 2) * (291 / 1000 : ℝ) ^ 2 ≤ 649 / 50 := by norm_num
  have hqR : (0 : ℝ) ≤ 1 - 649 / 50 * (291 / 1000) ^ 2 + 77 / 2 * (291 / 1000) ^ 4 := by norm_num
  have hδ : (0 : ℝ) < 1 / 1000 := by norm_num
  have hMd : ContDiff ℝ 2 M := contDiff_quarticWindowGauge _ _ _ _
  have hMcs : HasCompactSupport M := hasCompactSupport_quarticWindowGauge _ _ _ hδ
  have hnn : ∀ y, 0 ≤ M y := quarticWindowGauge_nonneg hd hdc2 hqR hδ
  have hle : ∀ y, M y ≤ 1 := quarticWindowGauge_le_one hd hdc2 hqR hδ
  have hzero : ∀ y, 291 / 1000 ≤ |y| → M y = 0 := fun y hy =>
    quarticWindowGauge_eq_zero _ _ hδ hy
  have hMB : ∀ x, M x ≠ 0 → |x| ≤ 291 / 1000 := fun x hx => by
    by_contra h
    exact hx (hzero x (not_le.mp h).le)
  have hMe : ∀ y, M (-y) = M y := quarticWindowGauge_neg _ _ _ _
  have hlog2 : 2 * (291 / 1000 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num; linarith
  have hqpos : ∀ y, |y| ≤ 291 / 1000 → 0 < quarticProfile (649 / 50) (77 / 2) y := fun y hy => by
    have := quarticProfile_ge_of_le hd hdc2 hy
    norm_num at this
    linarith
  -- the profile
  have hu : ContDiff ℝ 2 u := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : |y| < 291 / 1000
    · exact hF.contDiffAt.mul ((contDiff_quarticProfile _ _).contDiffAt.inv
        (hqpos y hy.le).ne' |>.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl))
    · have hopen : IsOpen {z : ℝ | 29 / 100 < |z|} := isOpen_lt continuous_const continuous_abs
      have hev : u =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hopen.mem_nhds (show 29 / 100 < |y| by linarith [not_lt.mp hy])] with z hz
        simp [hudef, hsupp z hz]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have huc : HasCompactSupport u := hFc.mul_right
  have hue : ∀ x, u (-x) = u x := fun x => by
    simp only [hudef]
    rw [heven, quarticProfile_neg]
  have hFu : (fun x => M x * u x) = F := funext fun x => by
    by_cases hx : |x| ≤ 29 / 100
    · have hq := (hqpos x (by linarith)).ne'
      simp only [hudef, hMdef]
      rw [quarticWindowGauge_eq _ _ hδ (by linarith : |x| ≤ 291 / 1000 - 1 / 1000)]
      field_simp
    · simp only [hudef, hsupp x (not_le.mp hx), zero_mul, mul_zero]
  -- the representation
  have hrep := fullZeroForm_mul_eq_gauge_window hu huc hMd hMcs hle hnn hzero hlog2
  rw [hFu] at hrep
  -- the jump part: the fold with its cost
  obtain ⟨Ku, -, hKu⟩ := exists_lipschitz_bound_of_compactSupport (hu.of_le (by norm_num)) huc
  have huL : ∀ a b, |u a - u b| ≤ Ku * |a - b| := fun a b => hKu b a
  have hωI := integrableOn_archLevy_mul_gaugeJumpProfile hle hnn hzero (by norm_num) (by norm_num)
    hu.continuous hMd.continuous hMcs huL
  have hcI : Integrable fun t => Real.cosh (t / 2) * gaugeJumpProfile M u t :=
    (integrable_gaugeJump_kernel hu.continuous hMd.continuous hMB).integral_prod_left.congr
      (Eventually.of_forall fun t => by
        simp only [gaugeJumpProfile]
        rw [integral_const_mul])
  have hcost := integral_kappa_mul_gaugeJumpProfile_ge_foldCost hMd.continuous hu.continuous hMe
    hue hnn hle hzero huL (by norm_num) measurable_weilJumpDensity (C := 4) (by norm_num)
    (fun t ht0 ht1 => abs_weilJumpDensity_le ht0 (by linarith))
    continuous_pastFoldCost.measurable pastFoldCost_nonneg pastFoldCost_le
    (fun s x hs hx hxs => weilJumpDensity_fold_ge_neg_pastFoldCost hs hx hxs)
  have eκ : (∫ t in Ioi (0 : ℝ), weilJumpDensity t * gaugeJumpProfile M u t) =
      (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile M u t) -
        2 * ∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile M u t := by
    rw [← integral_const_mul, ← integral_sub hωI (hcI.integrableOn.const_mul 2)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    unfold weilJumpDensity
    ring
  -- the half-line integrals of even integrands
  have habs : ∀ x, u |x| = u x ∧ M |x| = M x := fun x => by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]; exact ⟨rfl, rfl⟩
    · rw [abs_of_neg h]; exact ⟨hue x, hMe x⟩
  have hA : (∫ x, u x ^ 2 * M x) = 2 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * M x := by
    rw [← integral_comp_abs (f := fun x => u x ^ 2 * M x)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [(habs x).1, (habs x).2]
  have hB : (∫ x, pastFoldCost |x| * M x * u x ^ 2) =
      2 * ∫ y in Ioi (0 : ℝ), pastFoldCost y * M y * u y ^ 2 := by
    rw [← integral_comp_abs (f := fun y => pastFoldCost y * M y * u y ^ 2)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [(habs x).1, (habs x).2]
  have hΓ : (∫ y in Ioi (0 : ℝ), pastFoldCost y * M y) ≤ 0.000285 :=
    integral_pastFoldCost_mul_gauge_le
  have hA0 : 0 ≤ ∫ x in Ioi (0 : ℝ), u x ^ 2 * M x :=
    setIntegral_nonneg measurableSet_Ioi fun x _ => mul_nonneg (sq_nonneg _) (hnn x)
  have hΓA := mul_le_mul_of_nonneg_right hΓ hA0
  -- the potential integrands
  obtain ⟨KM, -, hKM⟩ := exists_lipschitz_bound_of_compactSupport (hMd.of_le (by norm_num)) hMcs
  have hML : ∀ a b, |M a - M b| ≤ KM * |a - b| := fun a b => hKM b a
  have hdec8 : ∀ y, |M y| ≤ Real.exp (8 * (291 / 1000)) * Real.exp (-(8 * |y|)) := by
    intro y
    by_cases hy : |y| < 291 / 1000
    · rw [abs_of_nonneg (hnn y), ← Real.exp_add]
      exact (hle y).trans (Real.one_le_exp (by nlinarith))
    · rw [hzero y (not_lt.mp hy), abs_zero]
      positivity
  have hW : Continuous fun x => -poleFreeWeilOperator M x :=
    (continuous_poleFreeWeilOperator hMd.continuous hML hdec8).neg
  have hG : Continuous fun x => ∫ y, M y * Real.cosh ((x - y) / 2) := by
    have e := funext (integral_gauge_cosh_eq hMd.continuous hMcs)
    rw [e]
    fun_prop
  have hu2M : Continuous fun x => u x ^ 2 * M x := (hu.continuous.pow 2).mul hMd.continuous
  have hu2Mc : HasCompactSupport fun x => u x ^ 2 * M x := (hasCompactSupport_sq huc).mul_right
  have i1 : Integrable fun x => u x ^ 2 * M x * -poleFreeWeilOperator M x :=
    (hu2M.mul hW).integrable_of_hasCompactSupport hu2Mc.mul_right
  have i2 : Integrable fun x => u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2) :=
    (hu2M.mul hG).integrable_of_hasCompactSupport hu2Mc.mul_right
  have i3 : Integrable fun x => u x ^ 2 * M x := hu2M.integrable_of_hasCompactSupport hu2Mc
  have i4 : Integrable fun x => pastFoldCost |x| * M x * u x ^ 2 :=
    (((continuous_pastFoldCost.comp continuous_abs).mul hMd.continuous).mul
      (hu.continuous.pow 2)).integrable_of_hasCompactSupport (hMcs.mul_left.mul_right)
  -- the pointwise potential, net of the fold cost
  have hpt : ∀ x, 1 / 1000 * F x ^ 2 ≤ u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * (∫ y, M y * Real.cosh ((x - y) / 2)) - 2 * 0.000285 -
        2 * (291 / 1000) * pastFoldCost |x|) := by
    intro x
    by_cases hx : |x| ≤ 29 / 100
    · have hpot := pastFoldGauge_potential_ge hx
      rw [← hMdef] at hpot
      have hFx : F x = M x * u x := (congrFun hFu x).symm
      rw [hFx]
      have hu2 : 0 ≤ u x ^ 2 * M x := mul_nonneg (sq_nonneg _) (hnn x)
      have hM1 := hle x
      have hP : 1 / 1000 ≤ -poleFreeWeilOperator M x + 2 * (∫ y, M y * Real.cosh ((x - y) / 2)) -
          2 * 0.000285 - 2 * (291 / 1000) * pastFoldCost |x| := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hP hu2, mul_nonneg hu2 (by linarith : 0 ≤ 1 - M x)]
    · have hF0 : F x = 0 := hsupp x (not_le.mp hx)
      have hu0 : u x = 0 := by simp [hudef, hF0]
      rw [hF0, hu0]
      simp
  -- assemble
  have hF2 : Integrable fun x => 1 / 1000 * F x ^ 2 :=
    ((hF.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)).const_mul _
  have e : ∀ x, u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * (∫ y, M y * Real.cosh ((x - y) / 2)) - 2 * 0.000285 -
        2 * (291 / 1000) * pastFoldCost |x|) =
      (u x ^ 2 * M x * -poleFreeWeilOperator M x +
        2 * (u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2))) -
        (2 * 0.000285 * (u x ^ 2 * M x) +
          2 * (291 / 1000) * (pastFoldCost |x| * M x * u x ^ 2)) := fun x => by ring
  have i12 : Integrable fun x => u x ^ 2 * M x * -poleFreeWeilOperator M x +
      2 * (u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2)) := i1.add (i2.const_mul 2)
  have i34 : Integrable fun x => 2 * 0.000285 * (u x ^ 2 * M x) +
      2 * (291 / 1000) * (pastFoldCost |x| * M x * u x ^ 2) :=
    (i3.const_mul _).add (i4.const_mul _)
  have hsum : Integrable fun x => u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * (∫ y, M y * Real.cosh ((x - y) / 2)) - 2 * 0.000285 -
        2 * (291 / 1000) * pastFoldCost |x|) :=
    (i12.sub i34).congr (Eventually.of_forall fun x => (e x).symm)
  have hint := integral_mono hF2 hsum hpt
  have hsplit : (∫ x, u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * (∫ y, M y * Real.cosh ((x - y) / 2)) - 2 * 0.000285 -
        2 * (291 / 1000) * pastFoldCost |x|)) =
      ((∫ x, u x ^ 2 * M x * -poleFreeWeilOperator M x) +
        2 * ∫ x, u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2)) -
        (2 * 0.000285 * (∫ x, u x ^ 2 * M x) +
          2 * (291 / 1000) * ∫ x, pastFoldCost |x| * M x * u x ^ 2) := by
    rw [integral_congr_ae (Eventually.of_forall e), integral_sub i12 i34,
      integral_add (f := fun x => u x ^ 2 * M x * -poleFreeWeilOperator M x)
        (g := fun x => 2 * (u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2))) i1
        (i2.const_mul 2),
      integral_add (f := fun x => 2 * 0.000285 * (u x ^ 2 * M x))
        (g := fun x => 2 * (291 / 1000) * (pastFoldCost |x| * M x * u x ^ 2))
        (i3.const_mul _) (i4.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul]
  rw [integral_const_mul] at hint
  rw [hrep]
  linarith [hcost, eκ, hA, hB, hΓA, hint, hsplit]

/-! ### All profiles on `[−29/100, 29/100]` -/

/-- **Weil positivity on `[−29/100, 29/100]`, past the plastic fold boundary.** Every real
`F ∈ C²_c` vanishing outside `[−29/100, 29/100]` satisfies `Ẑ(F) ≥ (1/1000) ∫ F²`. -/
theorem fullZeroForm_ge_of_support_le_pastFold {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hsupp : ∀ x, 29 / 100 < |x| → F x = 0) :
    1 / 1000 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  have hse : ∀ x, 29 / 100 < |x| → evenPartReal F x = 0 := fun x hx => by
    unfold evenPartReal
    rw [hsupp x hx, hsupp (-x) (by rwa [abs_neg])]
    norm_num
  have hso : ∀ x, 17 / 50 < |x| → oddPartReal F x = 0 := fun x hx => by
    unfold oddPartReal
    rw [hsupp x (by linarith), hsupp (-x) (by rw [abs_neg]; linarith)]
    norm_num
  have he := fullZeroForm_ge_of_even_support_le_pastFold (contDiff_evenPartReal hF)
    (hasCompactSupport_evenPartReal hFc) (evenPartReal_neg F) hse
  have ho := fullZeroForm_ge_of_odd_support_le_curved (contDiff_oddPartReal hF)
    (hasCompactSupport_oddPartReal hFc) (oddPartReal_neg F) hso
  have hnn : 0 ≤ ∫ x, oddPartReal F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [fullZeroForm_eq_even_add_odd hF hFc, integral_sq_eq_even_add_odd hF.continuous hFc]
  linarith

/-! ### Complex tests and the restricted Weil ground energy -/

/-- **Coercive zeta positivity for complex tests on `[−29/100, 29/100]`.** -/
theorem zetaZeroConfig_re_W_ge_of_support_le_pastFold {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Icc (-(29 / 100)) (29 / 100)) :
    1 / 1000 * ∫ x, ‖g x‖ ^ 2 ≤ (zetaZeroConfig.W g g).re := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hzero : ∀ x, 29 / 100 < |x| → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hgs h
      rw [mem_Icc] at this
      exact absurd (abs_le.mpr this) (not_le.mpr hx)
  have hre : ContDiff ℝ 2 fun u => (g u).re := Complex.reCLM.contDiff.comp hg
  have him : ContDiff ℝ 2 fun u => (g u).im := Complex.imCLM.contDiff.comp hg
  have hrec : HasCompactSupport fun u => (g u).re := hgc.comp_left Complex.zero_re
  have himc : HasCompactSupport fun u => (g u).im := hgc.comp_left Complex.zero_im
  have h1 := fullZeroForm_ge_of_support_le_pastFold hre hrec fun x hx => by simp [hzero x hx]
  have h2 := fullZeroForm_ge_of_support_le_pastFold him himc fun x hx => by simp [hzero x hx]
  have hsplit := GaloisForLFunctions.ArithmeticPositivityTheory.zeta_W_re_eq_fullZeroForm_re_add_im
    hg hgc
  have i1 : Integrable fun x => (g x).re ^ 2 :=
    (hre.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hrec)
  have i2 : Integrable fun x => (g x).im ^ 2 :=
    (him.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq himc)
  have hnorm : (∫ x, ‖g x‖ ^ 2) = (∫ x, (g x).re ^ 2) + ∫ x, (g x).im ^ 2 := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [hsplit, hnorm]
  linarith

/-- **The floor past the fold**: `μ(A) ≥ 1/1000` for every aperture `A ≤ 29/100`. -/
theorem one_div_1000_le_ccmRestrictedWeilGroundEnergy_pastFold {A : SuzukiPositiveAperture}
    (hA : A.1 ≤ 29 / 100) : 1 / 1000 ≤ ccmRestrictedWeilGroundEnergy A := by
  rw [← suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy]
  refine (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy A).2 ?_
  rintro r ⟨u, hu, rfl⟩
  have hnorm : ‖suzukiWeilIntervalFormEmbedding A u.toCCMFormVector‖ =
      ‖ccmArchimedeanFormToAperture A u.toCCMFormVector‖ := by
    change ‖suzukiPhysicalToApertureCLM A (ccmArchimedeanFormToAperture A u.toCCMFormVector)‖ = _
    exact (suzukiApertureL2Equiv A).symm.norm_map _
  have hmass : suzukiWeilIntervalFormMass A u.toCCMFormVector = ∫ x, ‖u x‖ ^ 2 := by
    unfold suzukiWeilIntervalFormMass
    rw [hnorm, norm_sq_ccmArchimedeanFormToAperture_toCCMFormVector]
  have hpos : 0 < suzukiWeilIntervalFormMass A u.toCCMFormVector :=
    pow_pos (norm_pos_iff.mpr hu) 2
  unfold suzukiWeilIntervalFormRayleigh
  rw [le_div_iff₀ hpos, ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil, hmass]
  have hsupp : tsupport (u : ℝ → ℂ) ⊆ Icc (-(29 / 100)) (29 / 100) :=
    u.tsupport_subset.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact zetaZeroConfig_re_W_ge_of_support_le_pastFold
    (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) hsupp

/-- **Contact apertures exceed `29/100`.** -/
theorem lt_of_ccmRestrictedWeilGroundEnergy_nonpos_pastFold {A : SuzukiPositiveAperture}
    (h : ccmRestrictedWeilGroundEnergy A ≤ 0) : 29 / 100 < A.1 := by
  by_contra hA
  have := one_div_1000_le_ccmRestrictedWeilGroundEnergy_pastFold (not_lt.mp hA)
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory
