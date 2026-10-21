import GaloisForLFunctions.ArithmeticCriticalityTheory.QuarticGaugeParityFoldedWeilPositivity

/-!
# Weil positivity on `[−7/25, 7/25]`: the even fold at the plastic boundary

The even fold makes the negative pole density free as long as the folded conductance
`κ(s) + κ(s + 2x)`, `κ = ω − 2cosh(t/2)`, is nonnegative on the pairs `x + s < R`; its binding pair is
`(x, s) → (0, R)`, where it equals `2κ(R)`, so the fold reaches up to the plastic threshold `log ρ`.
At `R = 281/1000 < log ρ ≈ 0.28120` the crude case analysis of `weilJumpDensity_fold_nonneg` no longer
suffices: the sharp minorant `κ(t) ≥ f(t) = 1/(2t) − 7/4 − t/48 − 9t²/32 − t⁴/192 − t⁵/1600` is midpoint
convex, `f(s) + f(t) ≥ 2f(m) + x²/R³ − x²(9/16 + …)`, `m = s + x`, and `f(m) ≥ f(R) ≈ 0.0013 > 0`
(`weilJumpDensity_fold_nonneg_boundary`).

The quartic even gauge `q P`, `q(y) = 1 − 13.2 y² + 37.5 y⁴`, radius `281/1000`, collar `1/1000`, has a
large quartic term: the second-moment coefficient `13.2 − 225 y²` changes sign at `y ≈ 0.2422`, which
the potential bound absorbs by `max(·, 0)` (`neg_poleFreeWeilOperator_quarticWindowGauge_ge_max`). Its
potential is nearly flat, `≈ 0.0062–0.0080` across `[0, 0.23]`, and fifteen anchored pieces (anchors
`(3/4)^k` and `(7/8)(3/4)^k`) bound it below by `1/500` (`boundaryGauge_window_inequality_inner`,
`boundaryGauge_window_inequality_outer`). The odd sector is the folded odd plateau on `[−7/25, 7/25]`.

**Theorem** (`fullZeroForm_ge_of_support_le_foldBoundary`). Every real `F ∈ C²_c` vanishing outside
`[−7/25, 7/25]` satisfies `Ẑ(F) ≥ (1/500) ∫ F²`; hence `μ(A) ≥ 1/500` for every aperture `A ≤ 7/25`
(`one_div_500_le_ccmRestrictedWeilGroundEnergy`). The reach is `2.67` times the Markov window `21/200`
and `0.996` of the plastic threshold, the boundary of the even fold.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar GaloisForLFunctions.ArithmeticIncidencePositivity
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The constants -/

/-- `−log(281/500) − 281/2000 − (γ + log π) ≥ −1.28637`. -/
theorem boundaryGauge_constant_ge :
    -1.28637 ≤ -Real.log (2 * (281 / 1000)) - 281 / 1000 / 2 - 2 * archConstantReal := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(-(31 / 250) : ℝ)| < 1 by norm_num) 6
  rw [show (1 : ℝ) - -(31 / 250) = 281 / 250 by norm_num, abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have hsplit : Real.log (2 * (281 / 1000)) = Real.log (281 / 250) - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have h2 := Real.log_two_gt_d9
  have hC := two_mul_archConstantReal_lt_sharp
  linarith [h.1, h.2]

/-- `log(8/7) > 0.13352`. -/
theorem log_eight_sevenths_gt : 0.13352 < Real.log (8 / 7) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(1 / 8 : ℝ)| < 1 by norm_num) 6
  rw [show (1 : ℝ) - 1 / 8 = 7 / 8 by norm_num, abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have e : Real.log (8 / 7) = -Real.log (7 / 8) := by
    rw [← Real.log_inv]; norm_num
  linarith [h.1, h.2]

/-! ### The fold at the plastic boundary -/

/-- `ω(t) − 2cosh(t/2) ≥ 1/(2t) − 7/4 − t/48 − 9t²/32 − t⁴/192 − t⁵/1600` on `(0, 1]`. -/
theorem weilJumpDensity_ge_poly {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    1 / (2 * t) - 7 / 4 - t / 48 - 9 * t ^ 2 / 32 - t ^ 4 / 192 - t ^ 5 / 1600 ≤
      weilJumpDensity t := by
  have hω := mul_archLevyDensity_ge_sharp ht0 ht1
  have hp := exp_le_taylor_five (x := t / 2) (by rw [abs_of_pos (by linarith)]; linarith)
  have hm := exp_le_taylor_five (x := -(t / 2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  rw [abs_of_pos (by linarith : (0 : ℝ) < t / 2)] at hp
  rw [abs_neg, abs_of_pos (by linarith : (0 : ℝ) < t / 2)] at hm
  have hc : 2 * Real.cosh (t / 2) ≤ 2 + t ^ 2 / 4 + t ^ 4 / 192 + t ^ 5 / 1600 := by
    rw [Real.cosh_eq]
    nlinarith
  have hω' : 1 / (2 * t) + 1 / 4 - t / 48 - t ^ 2 / 32 ≤ archLevyDensity t := by
    rw [show 1 / (2 * t) + 1 / 4 - t / 48 - t ^ 2 / 32 =
      (1 / 2 + t / 4 - t ^ 2 / 48 - t ^ 3 / 32) / t by field_simp, div_le_iff₀ ht0]
    linarith
  unfold weilJumpDensity
  linarith

/-- **The folded Weil conductance at the plastic boundary.** For `x + s < 281/1000`,
`κ(s) + κ(s + 2x) ≥ 0`: the polynomial minorant `f` of `κ` is midpoint convex,
`f(s) + f(t) − 2f(m) ≥ x²/R³ − x²(9/16 + …) ≥ 0`, `m = s + x`, and `f(m) ≥ f(281/1000) > 0`. -/
theorem weilJumpDensity_fold_nonneg_boundary {s x : ℝ} (hs : 0 < s) (hx : 0 < x)
    (hxs : x + s < 281 / 1000) : 0 ≤ weilJumpDensity s + weilJumpDensity (s + 2 * x) := by
  have h1 := weilJumpDensity_ge_poly hs (by linarith)
  have h2 := weilJumpDensity_ge_poly (t := s + 2 * x) (by linarith) (by linarith)
  set m := s + x with hmdef
  have hm : 0 < m := by rw [hmdef]; linarith
  have hmR : m < 281 / 1000 := by rw [hmdef]; linarith
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
  have hden : m * (m ^ 2 - x ^ 2) ≤ (281 / 1000) ^ 3 := by
    have : m * (m ^ 2 - x ^ 2) ≤ m ^ 3 := by nlinarith [sq_nonneg x]
    have h3 : m ^ 3 ≤ (281 / 1000) ^ 3 := pow_le_pow_left₀ hm.le hmR.le 3
    linarith
  have hgain : x ^ 2 / (281 / 1000) ^ 3 ≤ x ^ 2 / (m * (m ^ 2 - x ^ 2)) :=
    div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) hden
  have hinv : 1000 / 281 ≤ 1 / m := by
    rw [le_div_iff₀ hm]; nlinarith
  -- the polynomial part at `m ± x`
  have hpoly : (-(7 / 4) - s / 48 - 9 * s ^ 2 / 32 - s ^ 4 / 192 - s ^ 5 / 1600) +
      (-(7 / 4) - (s + 2 * x) / 48 - 9 * (s + 2 * x) ^ 2 / 32 - (s + 2 * x) ^ 4 / 192 -
        (s + 2 * x) ^ 5 / 1600) =
      2 * (-(7 / 4) - m / 48 - 9 * m ^ 2 / 32 - m ^ 4 / 192 - m ^ 5 / 1600) -
        x ^ 2 * (9 / 16 + m ^ 2 / 16 + x ^ 2 / 96 + m ^ 3 / 80 + m * x ^ 2 / 160) := by
    rw [hmdef]; ring
  have hGm : 2 * (-(7 / 4) - (281 / 1000) / 48 - 9 * (281 / 1000) ^ 2 / 32 - (281 / 1000) ^ 4 / 192 -
      (281 / 1000) ^ 5 / 1600) ≤
      2 * (-(7 / 4) - m / 48 - 9 * m ^ 2 / 32 - m ^ 4 / 192 - m ^ 5 / 1600) := by
    have hm2 : m ^ 2 ≤ (281 / 1000) ^ 2 := pow_le_pow_left₀ hm.le hmR.le 2
    have hm4 : m ^ 4 ≤ (281 / 1000) ^ 4 := pow_le_pow_left₀ hm.le hmR.le 4
    have hm5 : m ^ 5 ≤ (281 / 1000) ^ 5 := pow_le_pow_left₀ hm.le hmR.le 5
    linarith
  have hbr : x ^ 2 * (9 / 16 + m ^ 2 / 16 + x ^ 2 / 96 + m ^ 3 / 80 + m * x ^ 2 / 160) ≤
      x ^ 2 / (281 / 1000) ^ 3 := by
    have hm2 : m ^ 2 ≤ (281 / 1000) ^ 2 := pow_le_pow_left₀ hm.le hmR.le 2
    have hx2 : x ^ 2 ≤ (281 / 1000) ^ 2 := pow_le_pow_left₀ hx.le (by linarith) 2
    have hm3 : m ^ 3 ≤ (281 / 1000) ^ 3 := pow_le_pow_left₀ hm.le hmR.le 3
    have hmx : m * x ^ 2 ≤ (281 / 1000) ^ 3 := by
      have := mul_le_mul hmR.le hx2 (sq_nonneg x) (by norm_num)
      linarith [show (281 / 1000 : ℝ) * (281 / 1000) ^ 2 = (281 / 1000) ^ 3 by ring]
    have hB : 9 / 16 + m ^ 2 / 16 + x ^ 2 / 96 + m ^ 3 / 80 + m * x ^ 2 / 160 ≤ 1 / (281 / 1000) ^ 3 := by
      norm_num; nlinarith
    have := mul_le_mul_of_nonneg_left hB (sq_nonneg x)
    rw [mul_one_div] at this
    exact this
  have hrec' : 1 / (2 * s) + 1 / (2 * (s + 2 * x)) ≥ 1000 / 281 + x ^ 2 / (281 / 1000) ^ 3 := by
    rw [hrec]; linarith
  nlinarith [h1, h2, hpoly, hGm, hbr, hrec']

/-! ### The window inequalities -/

/-- The anchors `c = (7/8)(3/4)^k`, halfway between the anchors `(3/4)^k`. -/
theorem neg_half_log_one_sub_ge_anchor_seven_eighths {s : ℝ} (hs : s < 1) (k : ℕ) :
    0.1438 * k + 0.06676 + (s - (1 - 7 / 8 * (3 / 4 : ℝ) ^ k)) / (2 * (7 / 8 * (3 / 4) ^ k)) ≤
      -(1 / 2) * Real.log (1 - s) := by
  have hL : 0.2876 * k + 0.13352 ≤ -Real.log (7 / 8 * (3 / 4 : ℝ) ^ k) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv,
      show (7 / 8 : ℝ) = (8 / 7)⁻¹ by norm_num, Real.log_inv]
    have := log_four_thirds_gt
    have := log_eight_sevenths_gt
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have h := neg_half_log_one_sub_ge_anchor hs (by positivity) hL
  linarith

/-- **The inner window inequality** on `[0, 0.242]`, where `13.2 − 225 y² ≥ 0`; fifteen anchored pieces
in all, here ten. -/
theorem boundaryGauge_window_inequality_inner {y D : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 0.242)
    (hD : -1.28637 ≤ D) :
    1 / 500 ≤ (1 - 13.2 * y ^ 2 + 37.5 * y ^ 4) * (D + -(1 / 2) * Real.log (1 - 1000000 / 78961 * y ^ 2)) + (1.2925 - 23.06832 * y ^ 2 + 83.099 * y ^ 4 + 1.3217 * y ^ 6 - 0.390625 * y ^ 8) := by
  have hyp : 0 ≤ y := le_trans (by norm_num) hy0
  have hy2 : y ^ 2 ≤ (7 / 25) ^ 2 := pow_le_pow_left₀ hyp (by linarith) 2
  have hz0 : 0 ≤ y ^ 2 := sq_nonneg y
  have hq : 0 ≤ (1 - 13.2 * y ^ 2 + 37.5 * y ^ 4) := by nlinarith
  have hs : 1000000 / 78961 * y ^ 2 < 1 := by nlinarith
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have anc := fun k : ℕ => mul_le_mul_of_nonneg_left
    (neg_half_log_one_sub_ge_anchor_pow (s := 1000000 / 78961 * y ^ 2) hs k) hq
  have anc' := fun k : ℕ => mul_le_mul_of_nonneg_left
    (neg_half_log_one_sub_ge_anchor_seven_eighths (s := 1000000 / 78961 * y ^ 2) hs k) hq
  set ℓ := -(1 / 2) * Real.log (1 - 1000000 / 78961 * y ^ 2) with hℓ
  have piece : ∀ (lo hi : ℝ), lo ≤ y → y ≤ hi → 0 ≤ lo →
      (lo ^ 2 ≤ y ^ 2 ∧ y ^ 2 ≤ hi ^ 2 ∧ 0 ≤ (y ^ 2 - lo ^ 2) * (hi ^ 2 - y ^ 2) ∧
        0 ≤ (y ^ 2 - (lo ^ 2 + hi ^ 2) / 2) ^ 2 * (y ^ 2 + (lo ^ 2 + hi ^ 2)) ∧
        y ^ 4 * y ^ 4 ≤ hi ^ 4 * y ^ 4) := by
    intro lo hi hl hh h0
    have h1 : lo ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ h0 hl 2
    have h2 : y ^ 2 ≤ hi ^ 2 := pow_le_pow_left₀ (h0.trans hl) hh 2
    have h4 : y ^ 4 ≤ hi ^ 4 := pow_le_pow_left₀ hyp hh 4
    exact ⟨h1, h2, mul_nonneg (by linarith) (by linarith),
      mul_nonneg (sq_nonneg _) (by nlinarith), mul_le_mul_of_nonneg_right h4 (by positivity)⟩
  rcases le_or_gt y 0.07 with h0 | h0
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0 0.07 hy0 h0 (by norm_num)
    have h := anc 0; norm_num at h; linarith
  rcases le_or_gt y 0.12 with h1 | h1
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.07 0.12 h0.le h1 (by norm_num)
    have h := anc' 0; norm_num at h; linarith
  rcases le_or_gt y 0.155 with h2 | h2
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.12 0.155 h1.le h2 (by norm_num)
    have h := anc 1; norm_num at h; linarith
  rcases le_or_gt y 0.175 with h3 | h3
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.155 0.175 h2.le h3 (by norm_num)
    have h := anc' 1; norm_num at h; linarith
  rcases le_or_gt y 0.193 with h4 | h4
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.175 0.193 h3.le h4 (by norm_num)
    have h := anc 2; norm_num at h; linarith
  rcases le_or_gt y 0.207 with h5 | h5
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.193 0.207 h4.le h5 (by norm_num)
    have h := anc' 2; norm_num at h; linarith
  rcases le_or_gt y 0.218 with h6 | h6
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.207 0.218 h5.le h6 (by norm_num)
    have h := anc 3; norm_num at h; linarith
  rcases le_or_gt y 0.228 with h7 | h7
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.218 0.228 h6.le h7 (by norm_num)
    have h := anc' 3; norm_num at h; linarith
  rcases le_or_gt y 0.236 with h8 | h8
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.228 0.236 h7.le h8 (by norm_num)
    have h := anc 4; norm_num at h; linarith
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.236 0.242 h8.le hy (by norm_num)
    have h := anc' 4; norm_num at h; linarith

/-- **The outer window inequality** on `[0.242, 7/25]`, where the second-moment coefficient is
nonpositive and its correction is at most `10⁻⁵`. -/
theorem boundaryGauge_window_inequality_outer {y D : ℝ} (hy0 : 0.242 ≤ y) (hy : y ≤ 7 / 25)
    (hD : -1.28637 ≤ D) :
    1 / 500 ≤ (1 - 13.2 * y ^ 2 + 37.5 * y ^ 4) * (D + -(1 / 2) * Real.log (1 - 1000000 / 78961 * y ^ 2)) + (1.2928 - 23.03663 * y ^ 2 + 82.7068 * y ^ 4 - 2.62986 * y ^ 6 - 0.390625 * y ^ 8 - 0.00001) := by
  have hyp : 0 ≤ y := le_trans (by norm_num) hy0
  have hy2 : y ^ 2 ≤ (7 / 25) ^ 2 := pow_le_pow_left₀ hyp (by linarith) 2
  have hz0 : 0 ≤ y ^ 2 := sq_nonneg y
  have hq : 0 ≤ (1 - 13.2 * y ^ 2 + 37.5 * y ^ 4) := by nlinarith
  have hs : 1000000 / 78961 * y ^ 2 < 1 := by nlinarith
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have anc := fun k : ℕ => mul_le_mul_of_nonneg_left
    (neg_half_log_one_sub_ge_anchor_pow (s := 1000000 / 78961 * y ^ 2) hs k) hq
  have anc' := fun k : ℕ => mul_le_mul_of_nonneg_left
    (neg_half_log_one_sub_ge_anchor_seven_eighths (s := 1000000 / 78961 * y ^ 2) hs k) hq
  set ℓ := -(1 / 2) * Real.log (1 - 1000000 / 78961 * y ^ 2) with hℓ
  have piece : ∀ (lo hi : ℝ), lo ≤ y → y ≤ hi → 0 ≤ lo →
      (lo ^ 2 ≤ y ^ 2 ∧ y ^ 2 ≤ hi ^ 2 ∧ 0 ≤ (y ^ 2 - lo ^ 2) * (hi ^ 2 - y ^ 2) ∧
        0 ≤ (y ^ 2 - (lo ^ 2 + hi ^ 2) / 2) ^ 2 * (y ^ 2 + (lo ^ 2 + hi ^ 2)) ∧
        y ^ 4 * y ^ 4 ≤ hi ^ 4 * y ^ 4) := by
    intro lo hi hl hh h0
    have h1 : lo ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ h0 hl 2
    have h2 : y ^ 2 ≤ hi ^ 2 := pow_le_pow_left₀ (h0.trans hl) hh 2
    have h4 : y ^ 4 ≤ hi ^ 4 := pow_le_pow_left₀ hyp hh 4
    exact ⟨h1, h2, mul_nonneg (by linarith) (by linarith),
      mul_nonneg (sq_nonneg _) (by nlinarith), mul_le_mul_of_nonneg_right h4 (by positivity)⟩
  rcases le_or_gt y 0.25 with h0 | h0
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.242 0.25 hy0 h0 (by norm_num)
    have h := anc 5; norm_num at h; linarith
  rcases le_or_gt y 0.258 with h1 | h1
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.25 0.258 h0.le h1 (by norm_num)
    have h := anc 6; norm_num at h; linarith
  rcases le_or_gt y 0.266 with h2 | h2
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.258 0.266 h1.le h2 (by norm_num)
    have h := anc 7; norm_num at h; linarith
  rcases le_or_gt y 0.272 with h3 | h3
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.266 0.272 h2.le h3 (by norm_num)
    have h := anc 8; norm_num at h; linarith
  · obtain ⟨p1, p2, p3, p4, p5⟩ := piece 0.272 (7 / 25) h3.le hy (by norm_num)
    have h := anc 9; norm_num at h; linarith

/-! ### The potential of the boundary gauge -/

/-- The potential bound on the inner region `|x| ≤ 0.242`, where `13.2 − 225 x² ≥ 0`. -/
theorem boundaryGauge_potential_inner {x : ℝ} (hx : |x| ≤ 0.242) :
    1 / 500 ≤ -poleFreeWeilOperator (quarticWindowGauge (66 / 5) (75 / 2) (281 / 1000) (1 / 1000)) x +
      2 * ∫ y, quarticWindowGauge (66 / 5) (75 / 2) (281 / 1000) (1 / 1000) y * Real.cosh ((x - y) / 2) := by
  set y := |x| with hydef
  have hy0 : 0 ≤ y := abs_nonneg x
  have hd : (0 : ℝ) ≤ 75 / 2 := by norm_num
  have hdc2 : 2 * (75 / 2) * (281 / 1000 : ℝ) ^ 2 ≤ 66 / 5 := by norm_num
  have hqR : (0 : ℝ) ≤ 1 - 66 / 5 * (281 / 1000) ^ 2 + 75 / 2 * (281 / 1000) ^ 4 := by norm_num
  have hδ : (0 : ℝ) < 1 / 1000 := by norm_num
  have hyR : |y| ≤ 281 / 1000 := by rw [abs_of_nonneg hy0]; linarith
  have hWy : poleFreeWeilOperator (quarticWindowGauge (66 / 5) (75 / 2) (281 / 1000) (1 / 1000)) x =
      poleFreeWeilOperator (quarticWindowGauge (66 / 5) (75 / 2) (281 / 1000) (1 / 1000)) y := by
    rcases le_or_gt 0 x with h | h
    · rw [hydef, abs_of_nonneg h]
    · rw [hydef, abs_of_neg h, poleFreeWeilOperator_neg (quarticWindowGauge_neg _ _ _ _)]
  rw [hWy]
  have hα : 0 ≤ 66 / 5 - 6 * (75 / 2) * y ^ 2 := by
    have : y ^ 2 ≤ 0.242 ^ 2 := pow_le_pow_left₀ hy0 hx 2
    linarith
  have hW := neg_poleFreeWeilOperator_quarticWindowGauge_ge_max (c := 66 / 5) (d := 75 / 2)
    (R := 281 / 1000) (δ := 1 / 1000) (x := y) hd hdc2 hqR hδ (by norm_num) hy0 (by linarith)
  rw [max_eq_left hα] at hW
  have hbr := cubicGauge_bracket_ge (R := 281 / 1000) (x := y) (by norm_num) (by norm_num)
    (by rw [abs_of_nonneg hy0]; linarith)
  have hk : y ^ 2 / (281 / 1000) ^ 2 = 1000000 / 78961 * y ^ 2 := by ring
  rw [hk] at hbr
  have hq0 : 0 ≤ quarticProfile (66 / 5) (75 / 2) y := by
    have := quarticProfile_ge_of_le hd hdc2 hyR; linarith
  have hqbr := mul_le_mul_of_nonneg_left hbr hq0
  have hG := integral_quarticWindowGauge_cosh_ge (c := 66 / 5) (d := 75 / 2) (R := 281 / 1000)
    (δ := 1 / 1000) (x := x) hd hdc2 hqR hδ (by norm_num) (by norm_num) (by linarith)
  rw [← sq_abs x, ← hydef] at hG
  have p2 := pow_nonneg hy0 2
  have p4 := pow_nonneg hy0 4
  have p6 := pow_nonneg hy0 6
  have p8 := pow_nonneg hy0 8
  have h1D := boundaryGauge_window_inequality_inner hy0 hx boundaryGauge_constant_ge
  simp only [levyMomentPoly, levyMomentErr, Nat.cast_ofNat] at hW
  unfold quarticProfile at hW hqbr
  linarith [hW, hqbr, hG, h1D, p2, p4, p6, p8]

/-- The potential bound on the outer region `0.242 ≤ |x| ≤ 7/25`, where the second-moment correction
is at most `10⁻⁵`. -/
theorem boundaryGauge_potential_outer {x : ℝ} (hx1 : 0.242 ≤ |x|) (hx : |x| ≤ 7 / 25) :
    1 / 500 ≤ -poleFreeWeilOperator (quarticWindowGauge (66 / 5) (75 / 2) (281 / 1000) (1 / 1000)) x +
      2 * ∫ y, quarticWindowGauge (66 / 5) (75 / 2) (281 / 1000) (1 / 1000) y * Real.cosh ((x - y) / 2) := by
  set y := |x| with hydef
  have hy0 : 0 ≤ y := abs_nonneg x
  have hd : (0 : ℝ) ≤ 75 / 2 := by norm_num
  have hdc2 : 2 * (75 / 2) * (281 / 1000 : ℝ) ^ 2 ≤ 66 / 5 := by norm_num
  have hqR : (0 : ℝ) ≤ 1 - 66 / 5 * (281 / 1000) ^ 2 + 75 / 2 * (281 / 1000) ^ 4 := by norm_num
  have hδ : (0 : ℝ) < 1 / 1000 := by norm_num
  have hyR : |y| ≤ 281 / 1000 := by rw [abs_of_nonneg hy0]; linarith
  have hWy : poleFreeWeilOperator (quarticWindowGauge (66 / 5) (75 / 2) (281 / 1000) (1 / 1000)) x =
      poleFreeWeilOperator (quarticWindowGauge (66 / 5) (75 / 2) (281 / 1000) (1 / 1000)) y := by
    rcases le_or_gt 0 x with h | h
    · rw [hydef, abs_of_nonneg h]
    · rw [hydef, abs_of_neg h, poleFreeWeilOperator_neg (quarticWindowGauge_neg _ _ _ _)]
  rw [hWy]
  have hmax : max (66 / 5 - 6 * (75 / 2) * y ^ 2) 0 ≤ 0.0231 := by
    have : 0.242 ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by norm_num) hx1 2
    exact max_le (by linarith) (by norm_num)
  have hE0 : 0 ≤ levyMomentErr 2 (281 / 1000 - y) + levyMomentErr 2 (281 / 1000 + y) := by
    unfold levyMomentErr
    have : 0 ≤ 281 / 1000 - y := by linarith
    positivity
  have hE1 : levyMomentErr 2 (281 / 1000 - y) + levyMomentErr 2 (281 / 1000 + y) ≤ 0.0004 := by
    unfold levyMomentErr
    have ha : (281 / 1000 - y) ^ (2 + 3) ≤ (281 / 1000 : ℝ) ^ 5 :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have hb : (281 / 1000 + y) ^ (2 + 3) ≤ (562 / 1000 : ℝ) ^ 5 :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    push_cast at ha hb ⊢
    norm_num at ha hb ⊢
    linarith
  have hcorr : max (66 / 5 - 6 * (75 / 2) * y ^ 2) 0 *
      (levyMomentErr 2 (281 / 1000 - y) + levyMomentErr 2 (281 / 1000 + y)) ≤ 0.00001 :=
    (mul_le_mul hmax hE1 hE0 (by norm_num)).trans (by norm_num)
  have hW := neg_poleFreeWeilOperator_quarticWindowGauge_ge_max (c := 66 / 5) (d := 75 / 2)
    (R := 281 / 1000) (δ := 1 / 1000) (x := y) hd hdc2 hqR hδ (by norm_num) hy0 (by linarith)
  have hbr := cubicGauge_bracket_ge (R := 281 / 1000) (x := y) (by norm_num) (by norm_num)
    (by rw [abs_of_nonneg hy0]; linarith)
  have hk : y ^ 2 / (281 / 1000) ^ 2 = 1000000 / 78961 * y ^ 2 := by ring
  rw [hk] at hbr
  have hq0 : 0 ≤ quarticProfile (66 / 5) (75 / 2) y := by
    have := quarticProfile_ge_of_le hd hdc2 hyR; linarith
  have hqbr := mul_le_mul_of_nonneg_left hbr hq0
  have hG := integral_quarticWindowGauge_cosh_ge (c := 66 / 5) (d := 75 / 2) (R := 281 / 1000)
    (δ := 1 / 1000) (x := x) hd hdc2 hqR hδ (by norm_num) (by norm_num) (by linarith)
  rw [← sq_abs x, ← hydef] at hG
  have p2 := pow_nonneg hy0 2
  have p4 := pow_nonneg hy0 4
  have p6 := pow_nonneg hy0 6
  have p8 := pow_nonneg hy0 8
  have h1D := boundaryGauge_window_inequality_outer hx1 hx boundaryGauge_constant_ge
  simp only [levyMomentPoly, levyMomentErr, Nat.cast_ofNat] at hW hcorr
  unfold quarticProfile at hW hqbr
  linarith [hW, hqbr, hG, h1D, hcorr, p2, p4, p6, p8]

/-- **The potential bound of the boundary gauge** `M`: `−𝒲M(x) + 2 ∫ M(y) cosh((x − y)/2) dy ≥ 1/500`
on `[−7/25, 7/25]`. -/
theorem boundaryGauge_potential_ge {x : ℝ} (hx : |x| ≤ 7 / 25) :
    1 / 500 ≤ -poleFreeWeilOperator (quarticWindowGauge (66 / 5) (75 / 2) (281 / 1000) (1 / 1000)) x +
      2 * ∫ y, quarticWindowGauge (66 / 5) (75 / 2) (281 / 1000) (1 / 1000) y * Real.cosh ((x - y) / 2) := by
  rcases le_or_gt |x| 0.242 with h | h
  · exact boundaryGauge_potential_inner h
  · exact boundaryGauge_potential_outer h.le hx

/-! ### Even-sector positivity on `[−7/25, 7/25]` -/

/-- **Weil positivity of every even test supported in `[−7/25, 7/25]`.** Every even `F ∈ C²_c`
vanishing outside `[−7/25, 7/25]` satisfies `Ẑ(F) ≥ (1/500) ∫ F²`. -/
theorem fullZeroForm_ge_of_even_support_le_foldBoundary {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (heven : ∀ x, F (-x) = F x)
    (hsupp : ∀ x, 7 / 25 < |x| → F x = 0) :
    1 / 500 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  set M := quarticWindowGauge (66 / 5) (75 / 2) (281 / 1000) (1 / 1000) with hMdef
  set u : ℝ → ℝ := fun x => F x * (quarticProfile (66 / 5) (75 / 2) x)⁻¹ with hudef
  have hd : (0 : ℝ) ≤ 75 / 2 := by norm_num
  have hdc2 : 2 * (75 / 2) * (281 / 1000 : ℝ) ^ 2 ≤ 66 / 5 := by norm_num
  have hqR : (0 : ℝ) ≤ 1 - 66 / 5 * (281 / 1000) ^ 2 + 75 / 2 * (281 / 1000) ^ 4 := by norm_num
  have hδ : (0 : ℝ) < 1 / 1000 := by norm_num
  have hMd : ContDiff ℝ 2 M := contDiff_quarticWindowGauge _ _ _ _
  have hMcs : HasCompactSupport M := hasCompactSupport_quarticWindowGauge _ _ _ hδ
  have hnn : ∀ y, 0 ≤ M y := quarticWindowGauge_nonneg hd hdc2 hqR hδ
  have hle : ∀ y, M y ≤ 1 := quarticWindowGauge_le_one hd hdc2 hqR hδ
  have hzero : ∀ y, 281 / 1000 ≤ |y| → M y = 0 := fun y hy =>
    quarticWindowGauge_eq_zero _ _ hδ hy
  have hMB : ∀ x, M x ≠ 0 → |x| ≤ 281 / 1000 := fun x hx => by
    by_contra h
    exact hx (hzero x (not_le.mp h).le)
  have hMe : ∀ y, M (-y) = M y := quarticWindowGauge_neg _ _ _ _
  have hlog2 : 2 * (281 / 1000 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num; linarith
  have hqpos : ∀ y, |y| ≤ 281 / 1000 → 0 < quarticProfile (66 / 5) (75 / 2) y := fun y hy => by
    have := quarticProfile_ge_of_le hd hdc2 hy
    norm_num at this
    linarith
  -- the profile
  have hu : ContDiff ℝ 2 u := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : |y| < 281 / 1000
    · exact hF.contDiffAt.mul ((contDiff_quarticProfile _ _).contDiffAt.inv
        (hqpos y hy.le).ne' |>.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl))
    · have hopen : IsOpen {z : ℝ | 7 / 25 < |z|} := isOpen_lt continuous_const continuous_abs
      have hev : u =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hopen.mem_nhds (show 7 / 25 < |y| by linarith [not_lt.mp hy])] with z hz
        simp [hudef, hsupp z hz]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have huc : HasCompactSupport u := hFc.mul_right
  have hue : ∀ x, u (-x) = u x := fun x => by
    simp only [hudef]
    rw [heven, quarticProfile_neg]
  have hFu : (fun x => M x * u x) = F := funext fun x => by
    by_cases hx : |x| ≤ 7 / 25
    · have hq := (hqpos x (by linarith)).ne'
      simp only [hudef, hMdef]
      rw [quarticWindowGauge_eq _ _ hδ (by linarith : |x| ≤ 281 / 1000 - 1 / 1000)]
      field_simp
    · simp only [hudef, hsupp x (not_le.mp hx), zero_mul, mul_zero]
  -- the representation
  have hrep := fullZeroForm_mul_eq_gauge_window hu huc hMd hMcs hle hnn hzero hlog2
  rw [hFu] at hrep
  -- the jump part is a folded nonnegative energy
  obtain ⟨Ku, -, hKu⟩ := exists_lipschitz_bound_of_compactSupport (hu.of_le (by norm_num)) huc
  have huL : ∀ a b, |u a - u b| ≤ Ku * |a - b| := fun a b => hKu b a
  have hωI := integrableOn_archLevy_mul_gaugeJumpProfile hle hnn hzero (by norm_num) (by norm_num)
    hu.continuous hMd.continuous hMcs huL
  have hcI : Integrable fun t => Real.cosh (t / 2) * gaugeJumpProfile M u t :=
    (integrable_gaugeJump_kernel hu.continuous hMd.continuous hMB).integral_prod_left.congr
      (Eventually.of_forall fun t => by
        simp only [gaugeJumpProfile]
        rw [integral_const_mul])
  have hfoldI : 0 ≤ ∫ t in Ioi (0 : ℝ), weilJumpDensity t * gaugeJumpProfile M u t :=
    integral_kappa_mul_gaugeJumpProfile_nonneg_of_fold hMd.continuous hu.continuous hMe hue hnn
      hle hzero huL (by norm_num) measurable_weilJumpDensity (C := 4) (by norm_num)
      (fun t ht0 ht1 => abs_weilJumpDensity_le ht0 (by linarith))
      (fun s x hs hx hxs => weilJumpDensity_fold_nonneg_boundary hs hx hxs)
  have hjump : 0 ≤ (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile M u t) -
      2 * ∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile M u t := by
    have e : (∫ t in Ioi (0 : ℝ), weilJumpDensity t * gaugeJumpProfile M u t) =
        (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile M u t) -
          2 * ∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile M u t := by
      rw [← integral_const_mul, ← integral_sub hωI (hcI.integrableOn.const_mul 2)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      unfold weilJumpDensity
      ring
    rw [← e]
    exact hfoldI
  -- the potential integrands
  obtain ⟨KM, -, hKM⟩ := exists_lipschitz_bound_of_compactSupport (hMd.of_le (by norm_num)) hMcs
  have hML : ∀ a b, |M a - M b| ≤ KM * |a - b| := fun a b => hKM b a
  have hdec8 : ∀ y, |M y| ≤ Real.exp (8 * (281 / 1000)) * Real.exp (-(8 * |y|)) := by
    intro y
    by_cases hy : |y| < 281 / 1000
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
  -- the pointwise potential
  have hpt : ∀ x, 1 / 500 * F x ^ 2 ≤ u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * ∫ y, M y * Real.cosh ((x - y) / 2)) := by
    intro x
    by_cases hx : |x| ≤ 7 / 25
    · have hpot := boundaryGauge_potential_ge hx
      rw [← hMdef] at hpot
      have hFx : F x = M x * u x := (congrFun hFu x).symm
      rw [hFx]
      have hu2 : 0 ≤ u x ^ 2 * M x := mul_nonneg (sq_nonneg _) (hnn x)
      have hM1 := hle x
      nlinarith [mul_le_mul_of_nonneg_left hpot hu2, mul_nonneg hu2 (by linarith : 0 ≤ 1 - M x)]
    · have hF0 : F x = 0 := hsupp x (not_le.mp hx)
      have hu0 : u x = 0 := by simp [hudef, hF0]
      rw [hF0, hu0]
      simp
  -- assemble
  have hF2 : Integrable fun x => 1 / 500 * F x ^ 2 :=
    ((hF.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)).const_mul _
  have e : ∀ x, u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * ∫ y, M y * Real.cosh ((x - y) / 2)) =
      u x ^ 2 * M x * -poleFreeWeilOperator M x +
        2 * (u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2)) := fun x => by ring
  have hsum : Integrable fun x => u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * ∫ y, M y * Real.cosh ((x - y) / 2)) :=
    (i1.add (i2.const_mul 2)).congr (Eventually.of_forall fun x => (e x).symm)
  have hint := integral_mono hF2 hsum hpt
  have hsplit : (∫ x, u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * ∫ y, M y * Real.cosh ((x - y) / 2))) =
      (∫ x, u x ^ 2 * M x * -poleFreeWeilOperator M x) +
        2 * ∫ x, u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2) := by
    rw [integral_congr_ae (Eventually.of_forall e),
      integral_add (f := fun x => u x ^ 2 * M x * -poleFreeWeilOperator M x)
        (g := fun x => 2 * (u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2))) i1
        (i2.const_mul 2), integral_const_mul]
  rw [integral_const_mul] at hint
  rw [hrep]
  linarith [hjump, hint, hsplit]

/-! ### All profiles on `[−7/25, 7/25]` -/

/-- **Weil positivity on `[−7/25, 7/25]` at the fold boundary.** Every real `F ∈ C²_c`
vanishing outside `[−7/25, 7/25]` satisfies `Ẑ(F) ≥ (1/500) ∫ F²`. -/
theorem fullZeroForm_ge_of_support_le_foldBoundary {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hsupp : ∀ x, 7 / 25 < |x| → F x = 0) :
    1 / 500 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  have hse : ∀ x, 7 / 25 < |x| → evenPartReal F x = 0 := fun x hx => by
    unfold evenPartReal
    rw [hsupp x hx, hsupp (-x) (by rwa [abs_neg])]
    norm_num
  have hso : ∀ x, 7 / 25 < |x| → oddPartReal F x = 0 := fun x hx => by
    unfold oddPartReal
    rw [hsupp x hx, hsupp (-x) (by rwa [abs_neg])]
    norm_num
  have he := fullZeroForm_ge_of_even_support_le_foldBoundary (contDiff_evenPartReal hF)
    (hasCompactSupport_evenPartReal hFc) (evenPartReal_neg F) hse
  have ho := fullZeroForm_ge_of_odd_support_le (contDiff_oddPartReal hF)
    (hasCompactSupport_oddPartReal hFc) (oddPartReal_neg F) hso
  have hnn : 0 ≤ ∫ x, oddPartReal F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [fullZeroForm_eq_even_add_odd hF hFc, integral_sq_eq_even_add_odd hF.continuous hFc]
  linarith

/-! ### Complex tests and the restricted Weil ground energy -/

/-- **Coercive zeta positivity for complex tests on `[−7/25, 7/25]`.** -/
theorem zetaZeroConfig_re_W_ge_of_support_le_foldBoundary {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Icc (-(7 / 25)) (7 / 25)) :
    1 / 500 * ∫ x, ‖g x‖ ^ 2 ≤ (zetaZeroConfig.W g g).re := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hzero : ∀ x, 7 / 25 < |x| → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hgs h
      rw [mem_Icc] at this
      exact absurd (abs_le.mpr this) (not_le.mpr hx)
  have hre : ContDiff ℝ 2 fun u => (g u).re := Complex.reCLM.contDiff.comp hg
  have him : ContDiff ℝ 2 fun u => (g u).im := Complex.imCLM.contDiff.comp hg
  have hrec : HasCompactSupport fun u => (g u).re := hgc.comp_left Complex.zero_re
  have himc : HasCompactSupport fun u => (g u).im := hgc.comp_left Complex.zero_im
  have h1 := fullZeroForm_ge_of_support_le_foldBoundary hre hrec fun x hx => by simp [hzero x hx]
  have h2 := fullZeroForm_ge_of_support_le_foldBoundary him himc fun x hx => by simp [hzero x hx]
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

/-- **The fold-boundary floor**: `μ(A) ≥ 1/500` for every aperture `A ≤ 7/25`. -/
theorem one_div_500_le_ccmRestrictedWeilGroundEnergy {A : SuzukiPositiveAperture}
    (hA : A.1 ≤ 7 / 25) : 1 / 500 ≤ ccmRestrictedWeilGroundEnergy A := by
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
  have hsupp : tsupport (u : ℝ → ℂ) ⊆ Icc (-(7 / 25)) (7 / 25) :=
    u.tsupport_subset.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact zetaZeroConfig_re_W_ge_of_support_le_foldBoundary
    (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) hsupp

/-- **Contact apertures exceed `7/25`.** -/
theorem lt_of_ccmRestrictedWeilGroundEnergy_nonpos_foldBoundary {A : SuzukiPositiveAperture}
    (h : ccmRestrictedWeilGroundEnergy A ≤ 0) : 7 / 25 < A.1 := by
  by_contra hA
  have := one_div_500_le_ccmRestrictedWeilGroundEnergy (not_lt.mp hA)
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory
