import GaloisForLFunctions.ArithmeticCriticalityTheory.FoldedJumpHubSchur
import GaloisForLFunctions.ArithmeticCriticalityTheory.SharpLevyMomentQuarticPotential
import GaloisForLFunctions.ArithmeticCriticalityTheory.PastPlasticFoldWeilPositivity

/-!
# Weil positivity on `[−3/10, 3/10]`: sharp moments and a two-point fold cost

Two losses limited the quartic even gauges near `0.29`.

* **The moments.** The upper bound `u ω ≤ ½ + u/4 − u²/48` dropped the exact cubic term `−u³/32`, and
  with it `E_k` on every moment of negative coefficient in the gauge potential, about `3·10⁻³` at
  `x ≈ 0.2`. The sharp potential (`neg_poleFreeWeilOperator_quarticWindowGauge_ge_sharp`) keeps it.
* **The fold cost.** Past the plastic threshold the folded conductance satisfies
  `κ(s) + κ(s + 2x) ≥ 2f(x + s) + 36x²` (`weilJumpDensity_fold_ge_poly_gain`), so it is negative only on
  pairs with inner point `x < 0.0851`, and `−G(x, y)`, `G(x, y) = (13.03 (y − 281/1000) − 36x²)⁺`, bounds
  it below. The fold with a two-point cost (`integral_kappa_mul_gaugeJumpProfile_ge_hub`, hub weight
  `0`) pays it on `u(x)²` with the inner cost `C₁(x) = ∫ G(x, x + s) M(x + s) ds`, supported in
  `|x| < 0.0851` and at most `5.8·10⁻⁴` (`integral_threeTenthsFoldCost_mul_gauge_le`), and on `u(y)²`
  with the outer cost `2X₀ G_y(|y|)`, `X₀ = 0.0851`, which the edge logarithm absorbs.

The gauge is `q P`, `q(y) = 1 − 12.88 y² + 38.5 y⁴`, radius `301/1000`, collar `1/1000`; thirty pieces
with anchors `(3/4)^k (15/16)^j` bound its potential below by `1/5000 + 2C₁(x) + 2X₀ G_y(|x|)`
(`threeTenthsGauge_potential_ge`). The odd sector is the curved odd fold on `[−17/50, 17/50]`.

**Theorem** (`fullZeroForm_ge_of_support_le_threeTenths`). Every real `F ∈ C²_c` vanishing outside
`[−3/10, 3/10]` satisfies `Ẑ(F) ≥ (1/5000) ∫ F²`; hence `μ(A) ≥ 1/5000` for every aperture
`A ≤ 3/10` (`one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeTenths`).
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar GaloisForLFunctions.ArithmeticIncidencePositivity
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The constant -/

/-- `−log(301/500) − 301/2000 − (γ + log π) ≥ −1.36513`. -/
theorem threeTenthsGauge_constant_ge :
    -1.36513 ≤ -Real.log (2 * (301 / 1000)) - 301 / 1000 / 2 - 2 * archConstantReal := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(-(51 / 250) : ℝ)| < 1 by norm_num) 8
  rw [show (1 : ℝ) - -(51 / 250) = 301 / 250 by norm_num, abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have hsplit : Real.log (2 * (301 / 1000)) = Real.log (301 / 250) - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have h2 := Real.log_two_gt_d9
  have hC := two_mul_archConstantReal_lt_sharp
  linarith [h.1, h.2]

/-! ### The fold beyond the plastic boundary, with the gain of the inner point -/

/-- **The folded conductance with its quadratic gain.** For `x + s < 301/1000`,
`κ(s) + κ(s + 2x) ≥ 2f(m) + 36x²`, `m = s + x`: the reciprocal part gains `x²/m³ ≥ 36.6 x²`, the
polynomial part loses at most `0.57 x²`. -/
theorem weilJumpDensity_fold_ge_poly_gain {s x : ℝ} (hs : 0 < s) (hx : 0 < x)
    (hxs : x + s < 301 / 1000) :
    1 / (s + x) + 2 * (-(7 / 4) - (s + x) / 48 - 9 * (s + x) ^ 2 / 32 - (s + x) ^ 4 / 192 -
      (s + x) ^ 5 / 1600) + 36 * x ^ 2 ≤ weilJumpDensity s + weilJumpDensity (s + 2 * x) := by
  have h1 := weilJumpDensity_ge_poly hs (by linarith)
  have h2 := weilJumpDensity_ge_poly (t := s + 2 * x) (by linarith) (by linarith)
  set m := s + x with hmdef
  have hm : 0 < m := by rw [hmdef]; linarith
  have hmR : m < 301 / 1000 := by rw [hmdef]; linarith
  have hxm : x < m := by rw [hmdef]; linarith
  have hst : 0 < m ^ 2 - x ^ 2 := by nlinarith
  have hrec : 1 / (2 * s) + 1 / (2 * (s + 2 * x)) = 1 / m + x ^ 2 / (m * (m ^ 2 - x ^ 2)) := by
    have hs' : s = m - x := by rw [hmdef]; ring
    have ht' : s + 2 * x = m + x := by rw [hmdef]; ring
    rw [ht', hs']
    have h1' : m - x ≠ 0 := by linarith
    have h2' : m + x ≠ 0 := by linarith
    field_simp
    ring
  have hden : m * (m ^ 2 - x ^ 2) ≤ (301 / 1000) ^ 3 := by
    have : m * (m ^ 2 - x ^ 2) ≤ m ^ 3 := by nlinarith [sq_nonneg x]
    have h3 : m ^ 3 ≤ (301 / 1000) ^ 3 := pow_le_pow_left₀ hm.le hmR.le 3
    linarith
  have hgain : x ^ 2 / (301 / 1000) ^ 3 ≤ x ^ 2 / (m * (m ^ 2 - x ^ 2)) :=
    div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) hden
  have hpoly : (-(7 / 4) - s / 48 - 9 * s ^ 2 / 32 - s ^ 4 / 192 - s ^ 5 / 1600) +
      (-(7 / 4) - (s + 2 * x) / 48 - 9 * (s + 2 * x) ^ 2 / 32 - (s + 2 * x) ^ 4 / 192 -
        (s + 2 * x) ^ 5 / 1600) =
      2 * (-(7 / 4) - m / 48 - 9 * m ^ 2 / 32 - m ^ 4 / 192 - m ^ 5 / 1600) -
        x ^ 2 * (9 / 16 + m ^ 2 / 16 + x ^ 2 / 96 + m ^ 3 / 80 + m * x ^ 2 / 160) := by
    rw [hmdef]; ring
  have hbr : x ^ 2 * (9 / 16 + m ^ 2 / 16 + x ^ 2 / 96 + m ^ 3 / 80 + m * x ^ 2 / 160) ≤
      57 / 100 * x ^ 2 := by
    have hm2 : m ^ 2 ≤ (301 / 1000) ^ 2 := pow_le_pow_left₀ hm.le hmR.le 2
    have hx2 : x ^ 2 ≤ (301 / 1000) ^ 2 := pow_le_pow_left₀ hx.le (by linarith) 2
    have hm3 : m ^ 3 ≤ (301 / 1000) ^ 3 := pow_le_pow_left₀ hm.le hmR.le 3
    have hmx : m * x ^ 2 ≤ (301 / 1000) ^ 3 := by
      have := mul_le_mul hmR.le hx2 (sq_nonneg x) (by norm_num)
      linarith [show (301 / 1000 : ℝ) * (301 / 1000) ^ 2 = (301 / 1000) ^ 3 by ring]
    have hB : 9 / 16 + m ^ 2 / 16 + x ^ 2 / 96 + m ^ 3 / 80 + m * x ^ 2 / 160 ≤ 57 / 100 := by
      norm_num at hm2 hx2 hm3 hmx ⊢; nlinarith
    exact (mul_le_mul_of_nonneg_left hB (sq_nonneg x)).trans_eq (by ring)
  have hg36 : 36 * x ^ 2 + 57 / 100 * x ^ 2 ≤ x ^ 2 / (301 / 1000) ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg x]
  linarith [h1, h2, hpoly, hbr, hrec, hgain, hg36]

/-- `2f(m) ≥ −13.03 (m − 281/1000)⁺` for `0 < m < 301/1000`: `f` is positive up to `281/1000`, and
beyond it lies above the tangent of `1/m` and the chord of `m²`. -/
theorem threeTenths_poly_ge_neg_cost {m : ℝ} (hm0 : 0 < m) (hmR : m < 301 / 1000) :
    -(1303 / 100 * max (m - 281 / 1000) 0) ≤
      1 / m + 2 * (-(7 / 4) - m / 48 - 9 * m ^ 2 / 32 - m ^ 4 / 192 - m ^ 5 / 1600) := by
  have hm4 : m ^ 4 ≤ (301 / 1000) ^ 4 := pow_le_pow_left₀ hm0.le hmR.le 4
  have hm5 : m ^ 5 ≤ (301 / 1000) ^ 5 := pow_le_pow_left₀ hm0.le hmR.le 5
  rcases le_or_gt m (281 / 1000) with hm | hm
  · rw [max_eq_right (by linarith), mul_zero, neg_zero]
    have hinv : 1000 / 281 ≤ 1 / m := by rw [le_div_iff₀ hm0]; nlinarith
    have hm2' : m ^ 2 ≤ (281 / 1000) ^ 2 := pow_le_pow_left₀ hm0.le hm 2
    have hm4' : m ^ 4 ≤ (281 / 1000) ^ 4 := pow_le_pow_left₀ hm0.le hm 4
    have hm5' : m ^ 5 ≤ (281 / 1000) ^ 5 := pow_le_pow_left₀ hm0.le hm 5
    linarith
  · rw [max_eq_left (by linarith)]
    have hinv : 2 * (1000 / 281) - m * (1000 / 281) ^ 2 ≤ 1 / m := by
      rw [le_div_iff₀ hm0]; nlinarith [sq_nonneg (m * (1000 / 281) - 1)]
    have hch : m ^ 2 ≤ (281 / 1000 + 301 / 1000) * m - 281 / 1000 * (301 / 1000) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ m - 281 / 1000)
        (by linarith : (0 : ℝ) ≤ 301 / 1000 - m)]
    linarith

/-- The two-point fold cost `G(x, y) = (13.03 (min(y, 301/1000) − 281/1000) − 36 x²)⁺`. -/
def threeTenthsFoldCost (x y : ℝ) : ℝ :=
  max (1303 / 100 * (min y (301 / 1000) - 281 / 1000) - 36 * x ^ 2) 0

/-- The outer majorant `G_y(y) = 13.03 (min(y, 301/1000) − 281/1000)⁺`. -/
def threeTenthsOuterCost (y : ℝ) : ℝ := 1303 / 100 * max (min y (301 / 1000) - 281 / 1000) 0

theorem threeTenthsFoldCost_nonneg (x y : ℝ) : 0 ≤ threeTenthsFoldCost x y := le_max_right _ _

theorem threeTenthsFoldCost_le_outer (x y : ℝ) : threeTenthsFoldCost x y ≤ threeTenthsOuterCost y := by
  unfold threeTenthsFoldCost threeTenthsOuterCost
  refine max_le ?_ (by positivity)
  have := le_max_left (min y (301 / 1000) - 281 / 1000) 0
  nlinarith [sq_nonneg x]

theorem threeTenthsOuterCost_le (y : ℝ) : threeTenthsOuterCost y ≤ 1303 / 5000 := by
  unfold threeTenthsOuterCost
  have : max (min y (301 / 1000) - 281 / 1000) 0 ≤ 1 / 50 :=
    max_le (by linarith [min_le_right y (301 / 1000)]) (by norm_num)
  linarith

theorem threeTenthsOuterCost_eq_zero {y : ℝ} (hy : y ≤ 281 / 1000) : threeTenthsOuterCost y = 0 := by
  unfold threeTenthsOuterCost
  rw [max_eq_right (by linarith [min_le_left y (301 / 1000)]), mul_zero]

theorem threeTenthsOuterCost_le_sq {y : ℝ} (hy : 281 / 1000 ≤ y) :
    2 * (851 / 10000) * threeTenthsOuterCost y ≤ 3.9462 * (y ^ 2 - 0.078961) := by
  unfold threeTenthsOuterCost
  have h1 : max (min y (301 / 1000) - 281 / 1000) 0 ≤ y - 281 / 1000 :=
    max_le (by linarith [min_le_left y (301 / 1000)]) (by linarith)
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y - 281 / 1000)
    (by linarith : (0 : ℝ) ≤ y + 281 / 1000 - 562 / 1000), le_max_right (min y (301 / 1000) - 281 / 1000) 0]

theorem threeTenthsFoldCost_eq_zero {x y : ℝ} (hx : 851 / 10000 ≤ x) : threeTenthsFoldCost x y = 0 := by
  unfold threeTenthsFoldCost
  refine max_eq_right ?_
  have h1 : 1303 / 100 * (min y (301 / 1000) - 281 / 1000) ≤ 1303 / 5000 := by
    linarith [min_le_right y (301 / 1000)]
  have h2 : (851 / 10000) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) hx 2
  nlinarith

/-- **The fold cost past the plastic boundary.** For `x + s < 301/1000`,
`κ(s) + κ(s + 2x) ≥ −G(x, x + s)`. -/
theorem weilJumpDensity_fold_ge_neg_threeTenthsFoldCost {s x : ℝ} (hs : 0 < s) (hx : 0 < x)
    (hxs : x + s < 301 / 1000) :
    -threeTenthsFoldCost x (x + s) ≤ weilJumpDensity s + weilJumpDensity (s + 2 * x) := by
  have h := weilJumpDensity_fold_ge_poly_gain hs hx hxs
  have hp := threeTenths_poly_ge_neg_cost (m := s + x) (by linarith) (by linarith)
  unfold threeTenthsFoldCost
  rw [min_eq_left hxs.le, show x + s = s + x by ring]
  have hmax := le_max_left (1303 / 100 * (s + x - 281 / 1000) - 36 * x ^ 2) 0
  rcases le_or_gt (s + x) (281 / 1000) with hm | hm
  · rw [max_eq_right (by linarith : s + x - 281 / 1000 ≤ 0)] at hp
    have := le_max_right (1303 / 100 * (s + x - 281 / 1000) - 36 * x ^ 2) 0
    nlinarith [sq_nonneg x]
  · rw [max_eq_left (by linarith : 0 ≤ s + x - 281 / 1000)] at hp
    linarith

/-! ### The gauge and the inner cost -/

/-- The gauge of the aperture `3/10`: `q(y) = 1 − 12.88 y² + 38.5 y⁴` on the window of radius
`301/1000` with collar `1/1000`. -/
abbrev threeTenthsGauge : ℝ → ℝ := quarticWindowGauge (322 / 25) (77 / 2) (301 / 1000) (1 / 1000)

/-- On the fold strip `[281/1000, 301/1000]` the gauge is at most `q(281/1000) < 0.2231`. -/
theorem threeTenthsGauge_le_edge {y : ℝ} (hy1 : 281 / 1000 ≤ |y|) (hy2 : |y| ≤ 301 / 1000) :
    threeTenthsGauge y ≤ 0.2231 := by
  have hz1 : (281 / 1000) ^ 2 ≤ y ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) hy1 2; rwa [sq_abs] at this
  have hz2 : y ^ 2 ≤ (301 / 1000) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg y) hy2 2; rwa [sq_abs] at this
  have hq0 : 0 ≤ quarticProfile (322 / 25) (77 / 2) y := by
    have := quarticProfile_ge_of_le (c := 322 / 25) (d := 77 / 2) (R := 301 / 1000) (by norm_num)
      (by norm_num) hy2
    linarith
  have hq : quarticProfile (322 / 25) (77 / 2) y ≤ 0.2231 := by
    unfold quarticProfile
    have h4 : y ^ 4 = (y ^ 2) ^ 2 := by ring
    rw [h4]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y ^ 2 - (281 / 1000) ^ 2)
      (by nlinarith : (0 : ℝ) ≤ 322 / 25 - 77 / 2 * (y ^ 2 + (281 / 1000) ^ 2))]
  show quarticWindowGauge (322 / 25) (77 / 2) (301 / 1000) (1 / 1000) y ≤ 0.2231
  unfold quarticWindowGauge
  have := mul_le_mul_of_nonneg_left (plateauGauge_le_one (301 / 1000) (1 / 1000) y) hq0
  linarith

/-- The inner cost `C₁(x) = 0.2231 · (13.03/2) · ((301/1000 − 281/1000) − (3600/1303) x²)₊²`, the
integral over the outer point of the two-point cost against the gauge. -/
def threeTenthsInnerCost (x : ℝ) : ℝ :=
  2231 / 10000 * (1303 / 200) * max ((301 / 1000 - 281 / 1000) - 3600 / 1303 * x ^ 2) 0 ^ 2

theorem threeTenthsInnerCost_nonneg (x : ℝ) : 0 ≤ threeTenthsInnerCost x := by
  unfold threeTenthsInnerCost; positivity

theorem threeTenthsInnerCost_le (x : ℝ) : threeTenthsInnerCost x ≤ 1303 / 5000 := by
  unfold threeTenthsInnerCost
  have h1 : max ((301 / 1000 - 281 / 1000) - 3600 / 1303 * x ^ 2) 0 ≤ 1 / 50 :=
    max_le (by nlinarith [sq_nonneg x]) (by norm_num)
  have h0 := le_max_right ((301 / 1000 - 281 / 1000) - 3600 / 1303 * x ^ 2) 0
  have := pow_le_pow_left₀ h0 h1 2
  nlinarith

theorem threeTenthsInnerCost_le_sq (x : ℝ) :
    threeTenthsInnerCost x ≤ 2231 / 10000 * (1303 / 200) *
      ((301 / 1000 - 281 / 1000) - 3600 / 1303 * x ^ 2) ^ 2 := by
  unfold threeTenthsInnerCost
  have : max ((301 / 1000 - 281 / 1000) - 3600 / 1303 * x ^ 2) 0 ^ 2 ≤
      ((301 / 1000 - 281 / 1000) - 3600 / 1303 * x ^ 2) ^ 2 := by
    rcases le_total 0 ((301 / 1000 - 281 / 1000) - 3600 / 1303 * x ^ 2) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h]; nlinarith [sq_nonneg ((301 / 1000 - 281 / 1000) - 3600 / 1303 * x ^ 2)]
  nlinarith

theorem threeTenthsInnerCost_eq_zero {x : ℝ} (hx : 851 / 10000 ≤ x) : threeTenthsInnerCost x = 0 := by
  unfold threeTenthsInnerCost
  have h2 : (851 / 10000) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) hx 2
  rw [max_eq_right (by nlinarith)]
  norm_num

/-- **The inner cost.** `∫_{s>0} G(x, x + s) M(x + s) ds ≤ C₁(x)`: the integrand is supported where
`y₀ = 281/1000 + (3600/1303) x² < x + s < 301/1000`, equals `13.03 (x + s − y₀)` times a gauge value
at most `0.2231` there, and integrates to `13.03 · 0.2231 · (301/1000 − y₀)²/2`. -/
theorem integral_threeTenthsFoldCost_mul_gauge_le {x : ℝ} (hx : 0 < x) :
    (∫ s in Ioi (0 : ℝ), threeTenthsFoldCost x (x + s) * threeTenthsGauge (x + s)) ≤
      threeTenthsInnerCost x := by
  have hδ : (0 : ℝ) < 1 / 1000 := by norm_num
  set y₀ := 281 / 1000 + 3600 / 1303 * x ^ 2 with hy₀
  set κ' : ℝ := 2231 / 10000 * (1303 / 100) with hκ'
  set φ : ℝ → ℝ := (Ioo (y₀ - x) (301 / 1000 - x)).indicator fun s => κ' * (x + s - y₀) with hφ
  have hG : ∀ s, threeTenthsFoldCost x (x + s) = 1303 / 100 *
      max (min (x + s) (301 / 1000) - y₀) 0 := fun s => by
    unfold threeTenthsFoldCost
    have e : 1303 / 100 * (min (x + s) (301 / 1000) - 281 / 1000) - 36 * x ^ 2 =
        1303 / 100 * (min (x + s) (301 / 1000) - y₀) := by rw [hy₀]; ring
    rw [e, mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1303 / 100), mul_zero]
  have hM0 : ∀ y, 0 ≤ threeTenthsGauge y :=
    quarticWindowGauge_nonneg (by norm_num) (by norm_num) (by norm_num) hδ
  have hM1 : ∀ y, threeTenthsGauge y ≤ 1 :=
    quarticWindowGauge_le_one (by norm_num) (by norm_num) (by norm_num) hδ
  have hφ0 : ∀ s, 0 ≤ φ s := fun s => by
    rw [hφ]
    by_cases h : s ∈ Ioo (y₀ - x) (301 / 1000 - x)
    · rw [Set.indicator_of_mem h]; exact mul_nonneg (by norm_num) (by linarith [h.1])
    · rw [Set.indicator_of_notMem h]
  have hpt : ∀ s, threeTenthsFoldCost x (x + s) * threeTenthsGauge (x + s) ≤ φ s := fun s => by
    have hg0 := threeTenthsFoldCost_nonneg x (x + s)
    by_cases hR : 301 / 1000 ≤ x + s
    · rw [show threeTenthsGauge (x + s) = 0 from
        quarticWindowGauge_eq_zero _ _ hδ (by rw [abs_of_pos (by linarith)]; exact hR), mul_zero]
      exact hφ0 s
    · have hR' : x + s < 301 / 1000 := not_le.mp hR
      by_cases hy : x + s ≤ y₀
      · rw [hG s, min_eq_left hR'.le, max_eq_right (by linarith), mul_zero, zero_mul]
        exact hφ0 s
      · have hy' : y₀ < x + s := not_le.mp hy
        have hmem : s ∈ Ioo (y₀ - x) (301 / 1000 - x) := ⟨by linarith, by linarith⟩
        rw [hφ, Set.indicator_of_mem hmem, hG s, min_eq_left hR'.le, max_eq_left (by linarith)]
        have hya : 281 / 1000 ≤ y₀ := by rw [hy₀]; nlinarith [sq_nonneg x]
        have hM := threeTenthsGauge_le_edge (y := x + s)
          (by rw [abs_of_pos (by linarith)]; linarith) (by rw [abs_of_pos (by linarith)]; linarith)
        have hMs := hM0 (x + s)
        rw [hκ']
        nlinarith [mul_le_mul_of_nonneg_left hM (by linarith : (0 : ℝ) ≤ x + s - y₀)]
  have hφi : Integrable φ := by
    rw [hφ]
    exact (integrable_indicator_iff measurableSet_Ioo).mpr
      ((continuous_const.mul ((continuous_const.add continuous_id).sub continuous_const)
        ).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
  have hLi : IntegrableOn (fun s => threeTenthsFoldCost x (x + s) * threeTenthsGauge (x + s))
      (Ioi 0) := by
    have hc : Continuous fun s => threeTenthsFoldCost x (x + s) * threeTenthsGauge (x + s) := by
      have h1 : Continuous fun s => threeTenthsFoldCost x (x + s) := by
        unfold threeTenthsFoldCost; fun_prop
      exact h1.mul ((contDiff_quarticWindowGauge _ _ _ _).continuous.comp
        (continuous_const.add continuous_id))
    refine integrableOn_Ioi_of_bound hc.measurable (A := 1303 / 5000) (T := 301 / 1000)
      (fun s _ => ?_) (fun s hs => ?_)
    · rw [abs_of_nonneg (mul_nonneg (threeTenthsFoldCost_nonneg _ _) (hM0 _))]
      calc threeTenthsFoldCost x (x + s) * threeTenthsGauge (x + s) ≤ 1303 / 5000 * 1 :=
            mul_le_mul ((threeTenthsFoldCost_le_outer _ _).trans (threeTenthsOuterCost_le _))
              (hM1 _) (hM0 _) (by norm_num)
        _ = 1303 / 5000 := by ring
    · rw [show threeTenthsGauge (x + s) = 0 from quarticWindowGauge_eq_zero _ _ hδ
        (by rw [abs_of_pos (by linarith)]; linarith), mul_zero]
  have h1 := setIntegral_mono_on hLi hφi.integrableOn measurableSet_Ioi fun s _ => hpt s
  have h2 : (∫ s in Ioi (0 : ℝ), φ s) ≤ ∫ s, φ s :=
    setIntegral_le_integral hφi (Eventually.of_forall hφ0)
  have h3 : (∫ s, φ s) ≤ threeTenthsInnerCost x := by
    rw [hφ, integral_indicator measurableSet_Ioo]
    unfold threeTenthsInnerCost
    rcases le_or_gt (301 / 1000 - x) (y₀ - x) with hw | hw
    · rw [Ioo_eq_empty (not_lt.mpr hw), Measure.restrict_empty, integral_zero_measure]
      positivity
    · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hw.le]
      have e : (∫ s in (y₀ - x)..(301 / 1000 - x), κ' * (x + s - y₀)) =
          κ' * ((301 / 1000 - y₀) ^ 2 / 2) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        have h := intervalIntegral.integral_comp_sub_right (fun t : ℝ => t) (y₀ - x)
          (a := y₀ - x) (b := 301 / 1000 - x)
        rw [show (fun s : ℝ => x + s - y₀) = fun s => s - (y₀ - x) by funext s; ring, h,
          integral_id]
        ring
      rw [e, max_eq_left (by linarith), hκ', hy₀]
      ring_nf
      exact le_rfl
  linarith

/-! ### The window inequalities -/

/-- The sharp window polynomial of the gauge on the inner region (`12.88 − 231 y² ≥ 0`), as a
function of `y = |x|`, the killing constant `D` and the edge logarithm `ℓ`. -/
def threeTenthsWindowInner (y D ℓ : ℝ) : ℝ :=
  (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) * (D + ℓ + (((301 / 1000) - y) ^ 2 + ((301 / 1000) + y) ^ 2) / 96 - (((301 / 1000) - y) ^ 4 + ((301 / 1000) + y) ^ 4) / 192) + (((322 / 25) - 6 * (77 / 2) * y ^ 2) * ((((301 / 1000) - y) ^ 2 / (2 * 2) + ((301 / 1000) - y) ^ (2 + 1) / (4 * (2 + 1)) - ((301 / 1000) - y) ^ (2 + 2) / (48 * (2 + 2))) + (((301 / 1000) + y) ^ 2 / (2 * 2) + ((301 / 1000) + y) ^ (2 + 1) / (4 * (2 + 1)) - ((301 / 1000) + y) ^ (2 + 2) / (48 * (2 + 2)))) - ((322 / 25) - 6 * (77 / 2) * y ^ 2) * ((((301 / 1000) - y) ^ (2 + 3) / (32 * (2 + 3))) + (((301 / 1000) + y) ^ (2 + 3) / (32 * (2 + 3)))) - (77 / 2) * ((((301 / 1000) - y) ^ 4 / (2 * 4) + ((301 / 1000) - y) ^ (4 + 1) / (4 * (4 + 1)) - ((301 / 1000) - y) ^ (4 + 2) / (48 * (4 + 2))) + (((301 / 1000) + y) ^ 4 / (2 * 4) + ((301 / 1000) + y) ^ (4 + 1) / (4 * (4 + 1)) - ((301 / 1000) + y) ^ (4 + 2) / (48 * (4 + 2))) - ((((301 / 1000) - y) ^ (4 + 3) / (32 * (4 + 3))) + (((301 / 1000) + y) ^ (4 + 3) / (32 * (4 + 3)))) + ((((301 / 1000) - y) ^ (4 + 4) / (1152 * (4 + 4)) + ((301 / 1000) - y) ^ (4 + 5) / (256 * (4 + 5))) + (((301 / 1000) + y) ^ (4 + 4) / (1152 * (4 + 4)) + ((301 / 1000) + y) ^ (4 + 5) / (256 * (4 + 5))))) - 2 * y * ((322 / 25) - 2 * (77 / 2) * y ^ 2) * ((((301 / 1000) + y) ^ 1 / (2 * 1) + ((301 / 1000) + y) ^ (1 + 1) / (4 * (1 + 1)) - ((301 / 1000) + y) ^ (1 + 2) / (48 * (1 + 2))) - (((301 / 1000) - y) ^ 1 / (2 * 1) + ((301 / 1000) - y) ^ (1 + 1) / (4 * (1 + 1)) - ((301 / 1000) - y) ^ (1 + 2) / (48 * (1 + 2))) - ((((301 / 1000) + y) ^ (1 + 3) / (32 * (1 + 3))) - (((301 / 1000) - y) ^ (1 + 3) / (32 * (1 + 3)))) + ((((301 / 1000) + y) ^ (1 + 4) / (1152 * (1 + 4)) + ((301 / 1000) + y) ^ (1 + 5) / (256 * (1 + 5))) - (((301 / 1000) - y) ^ (1 + 4) / (1152 * (1 + 4)) + ((301 / 1000) - y) ^ (1 + 5) / (256 * (1 + 5))))) + 4 * (77 / 2) * y * ((((301 / 1000) + y) ^ 3 / (2 * 3) + ((301 / 1000) + y) ^ (3 + 1) / (4 * (3 + 1)) - ((301 / 1000) + y) ^ (3 + 2) / (48 * (3 + 2))) - (((301 / 1000) - y) ^ 3 / (2 * 3) + ((301 / 1000) - y) ^ (3 + 1) / (4 * (3 + 1)) - ((301 / 1000) - y) ^ (3 + 2) / (48 * (3 + 2))) - ((((301 / 1000) + y) ^ (3 + 3) / (32 * (3 + 3))) - (((301 / 1000) - y) ^ (3 + 3) / (32 * (3 + 3)))))) + 2 * (2 * ((3 / 10) - (322 / 25) * (3 / 10) ^ 3 / 3 + (77 / 2) * (3 / 10) ^ 5 / 5) * (1 + y ^ 2 / 8) + 2 * ((3 / 10) ^ 3 / 3 - (322 / 25) * (3 / 10) ^ 5 / 5 + (77 / 2) * (3 / 10) ^ 7 / 7) / 8)

/-- The sharp window polynomial of the gauge on the outer region (`12.88 − 231 y² ≤ 10⁻⁴`). -/
def threeTenthsWindowOuter (y D ℓ : ℝ) : ℝ :=
  (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) * (D + ℓ + (((301 / 1000) - y) ^ 2 + ((301 / 1000) + y) ^ 2) / 96 - (((301 / 1000) - y) ^ 4 + ((301 / 1000) + y) ^ 4) / 192) + (((322 / 25) - 6 * (77 / 2) * y ^ 2) * ((((301 / 1000) - y) ^ 2 / (2 * 2) + ((301 / 1000) - y) ^ (2 + 1) / (4 * (2 + 1)) - ((301 / 1000) - y) ^ (2 + 2) / (48 * (2 + 2))) + (((301 / 1000) + y) ^ 2 / (2 * 2) + ((301 / 1000) + y) ^ (2 + 1) / (4 * (2 + 1)) - ((301 / 1000) + y) ^ (2 + 2) / (48 * (2 + 2)))) - ((322 / 25) - 6 * (77 / 2) * y ^ 2) * ((((301 / 1000) - y) ^ (2 + 3) / (32 * (2 + 3))) + (((301 / 1000) + y) ^ (2 + 3) / (32 * (2 + 3)))) + (((322 / 25) - 6 * (77 / 2) * y ^ 2) - 1 / 10000) * ((((301 / 1000) - y) ^ (2 + 4) / (1152 * (2 + 4)) + ((301 / 1000) - y) ^ (2 + 5) / (256 * (2 + 5))) + (((301 / 1000) + y) ^ (2 + 4) / (1152 * (2 + 4)) + ((301 / 1000) + y) ^ (2 + 5) / (256 * (2 + 5)))) - (77 / 2) * ((((301 / 1000) - y) ^ 4 / (2 * 4) + ((301 / 1000) - y) ^ (4 + 1) / (4 * (4 + 1)) - ((301 / 1000) - y) ^ (4 + 2) / (48 * (4 + 2))) + (((301 / 1000) + y) ^ 4 / (2 * 4) + ((301 / 1000) + y) ^ (4 + 1) / (4 * (4 + 1)) - ((301 / 1000) + y) ^ (4 + 2) / (48 * (4 + 2))) - ((((301 / 1000) - y) ^ (4 + 3) / (32 * (4 + 3))) + (((301 / 1000) + y) ^ (4 + 3) / (32 * (4 + 3)))) + ((((301 / 1000) - y) ^ (4 + 4) / (1152 * (4 + 4)) + ((301 / 1000) - y) ^ (4 + 5) / (256 * (4 + 5))) + (((301 / 1000) + y) ^ (4 + 4) / (1152 * (4 + 4)) + ((301 / 1000) + y) ^ (4 + 5) / (256 * (4 + 5))))) - 2 * y * ((322 / 25) - 2 * (77 / 2) * y ^ 2) * ((((301 / 1000) + y) ^ 1 / (2 * 1) + ((301 / 1000) + y) ^ (1 + 1) / (4 * (1 + 1)) - ((301 / 1000) + y) ^ (1 + 2) / (48 * (1 + 2))) - (((301 / 1000) - y) ^ 1 / (2 * 1) + ((301 / 1000) - y) ^ (1 + 1) / (4 * (1 + 1)) - ((301 / 1000) - y) ^ (1 + 2) / (48 * (1 + 2))) - ((((301 / 1000) + y) ^ (1 + 3) / (32 * (1 + 3))) - (((301 / 1000) - y) ^ (1 + 3) / (32 * (1 + 3)))) + ((((301 / 1000) + y) ^ (1 + 4) / (1152 * (1 + 4)) + ((301 / 1000) + y) ^ (1 + 5) / (256 * (1 + 5))) - (((301 / 1000) - y) ^ (1 + 4) / (1152 * (1 + 4)) + ((301 / 1000) - y) ^ (1 + 5) / (256 * (1 + 5))))) + 4 * (77 / 2) * y * ((((301 / 1000) + y) ^ 3 / (2 * 3) + ((301 / 1000) + y) ^ (3 + 1) / (4 * (3 + 1)) - ((301 / 1000) + y) ^ (3 + 2) / (48 * (3 + 2))) - (((301 / 1000) - y) ^ 3 / (2 * 3) + ((301 / 1000) - y) ^ (3 + 1) / (4 * (3 + 1)) - ((301 / 1000) - y) ^ (3 + 2) / (48 * (3 + 2))) - ((((301 / 1000) + y) ^ (3 + 3) / (32 * (3 + 3))) - (((301 / 1000) - y) ^ (3 + 3) / (32 * (3 + 3)))))) + 2 * (2 * ((3 / 10) - (322 / 25) * (3 / 10) ^ 3 / 3 + (77 / 2) * (3 / 10) ^ 5 / 5) * (1 + y ^ 2 / 8) + 2 * ((3 / 10) ^ 3 / 3 - (322 / 25) * (3 / 10) ^ 5 / 5 + (77 / 2) * (3 / 10) ^ 7 / 7) / 8)

theorem threeTenthsWindow_piece_0 {y D ℓ : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 0.02) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((0 : ℕ)) : ℝ) + 0.032265 * (((0 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (0 : ℕ) * (15 / 16) ^ (0 : ℕ))) /
        (2 * ((3 / 4) ^ (0 : ℕ) * (15 / 16) ^ (0 : ℕ))) ≤ ℓ) :
    1 / 5000 + 2 * ((2231 / 10000 * (1303 / 200)) * ((301 / 1000 - 281 / 1000) - (3600 / 1303) * y ^ 2) ^ 2) ≤ threeTenthsWindowInner y D ℓ := by
  unfold threeTenthsWindowInner
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_1 {y D ℓ : ℝ} (h0 : 0.02 ≤ y) (h1 : y ≤ 0.04) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((0 : ℕ)) : ℝ) + 0.032265 * (((0 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (0 : ℕ) * (15 / 16) ^ (0 : ℕ))) /
        (2 * ((3 / 4) ^ (0 : ℕ) * (15 / 16) ^ (0 : ℕ))) ≤ ℓ) :
    1 / 5000 + 2 * ((2231 / 10000 * (1303 / 200)) * ((301 / 1000 - 281 / 1000) - (3600 / 1303) * y ^ 2) ^ 2) ≤ threeTenthsWindowInner y D ℓ := by
  unfold threeTenthsWindowInner
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_2 {y D ℓ : ℝ} (h0 : 0.04 ≤ y) (h1 : y ≤ 0.06) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((0 : ℕ)) : ℝ) + 0.032265 * (((0 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (0 : ℕ) * (15 / 16) ^ (0 : ℕ))) /
        (2 * ((3 / 4) ^ (0 : ℕ) * (15 / 16) ^ (0 : ℕ))) ≤ ℓ) :
    1 / 5000 + 2 * ((2231 / 10000 * (1303 / 200)) * ((301 / 1000 - 281 / 1000) - (3600 / 1303) * y ^ 2) ^ 2) ≤ threeTenthsWindowInner y D ℓ := by
  unfold threeTenthsWindowInner
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_3 {y D ℓ : ℝ} (h0 : 0.06 ≤ y) (h1 : y ≤ 0.0851) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((0 : ℕ)) : ℝ) + 0.032265 * (((1 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (0 : ℕ) * (15 / 16) ^ (1 : ℕ))) /
        (2 * ((3 / 4) ^ (0 : ℕ) * (15 / 16) ^ (1 : ℕ))) ≤ ℓ) :
    1 / 5000 + 2 * ((2231 / 10000 * (1303 / 200)) * ((301 / 1000 - 281 / 1000) - (3600 / 1303) * y ^ 2) ^ 2) ≤ threeTenthsWindowInner y D ℓ := by
  unfold threeTenthsWindowInner
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_4 {y D ℓ : ℝ} (h0 : 0.0851 ≤ y) (h1 : y ≤ 0.1) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((0 : ℕ)) : ℝ) + 0.032265 * (((2 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (0 : ℕ) * (15 / 16) ^ (2 : ℕ))) /
        (2 * ((3 / 4) ^ (0 : ℕ) * (15 / 16) ^ (2 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowInner y D ℓ := by
  unfold threeTenthsWindowInner
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_5 {y D ℓ : ℝ} (h0 : 0.1 ≤ y) (h1 : y ≤ 0.115) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((0 : ℕ)) : ℝ) + 0.032265 * (((2 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (0 : ℕ) * (15 / 16) ^ (2 : ℕ))) /
        (2 * ((3 / 4) ^ (0 : ℕ) * (15 / 16) ^ (2 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowInner y D ℓ := by
  unfold threeTenthsWindowInner
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_6 {y D ℓ : ℝ} (h0 : 0.115 ≤ y) (h1 : y ≤ 0.13) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((0 : ℕ)) : ℝ) + 0.032265 * (((3 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (0 : ℕ) * (15 / 16) ^ (3 : ℕ))) /
        (2 * ((3 / 4) ^ (0 : ℕ) * (15 / 16) ^ (3 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowInner y D ℓ := by
  unfold threeTenthsWindowInner
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_7 {y D ℓ : ℝ} (h0 : 0.13 ≤ y) (h1 : y ≤ 0.145) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((0 : ℕ)) : ℝ) + 0.032265 * (((3 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (0 : ℕ) * (15 / 16) ^ (3 : ℕ))) /
        (2 * ((3 / 4) ^ (0 : ℕ) * (15 / 16) ^ (3 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowInner y D ℓ := by
  unfold threeTenthsWindowInner
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_8 {y D ℓ : ℝ} (h0 : 0.145 ≤ y) (h1 : y ≤ 0.16) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((1 : ℕ)) : ℝ) + 0.032265 * (((0 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (1 : ℕ) * (15 / 16) ^ (0 : ℕ))) /
        (2 * ((3 / 4) ^ (1 : ℕ) * (15 / 16) ^ (0 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowInner y D ℓ := by
  unfold threeTenthsWindowInner
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_9 {y D ℓ : ℝ} (h0 : 0.16 ≤ y) (h1 : y ≤ 0.172) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((1 : ℕ)) : ℝ) + 0.032265 * (((1 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (1 : ℕ) * (15 / 16) ^ (1 : ℕ))) /
        (2 * ((3 / 4) ^ (1 : ℕ) * (15 / 16) ^ (1 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowInner y D ℓ := by
  unfold threeTenthsWindowInner
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_10 {y D ℓ : ℝ} (h0 : 0.172 ≤ y) (h1 : y ≤ 0.184) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((1 : ℕ)) : ℝ) + 0.032265 * (((2 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (1 : ℕ) * (15 / 16) ^ (2 : ℕ))) /
        (2 * ((3 / 4) ^ (1 : ℕ) * (15 / 16) ^ (2 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowInner y D ℓ := by
  unfold threeTenthsWindowInner
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_11 {y D ℓ : ℝ} (h0 : 0.184 ≤ y) (h1 : y ≤ 0.195) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((1 : ℕ)) : ℝ) + 0.032265 * (((3 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (1 : ℕ) * (15 / 16) ^ (3 : ℕ))) /
        (2 * ((3 / 4) ^ (1 : ℕ) * (15 / 16) ^ (3 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowInner y D ℓ := by
  unfold threeTenthsWindowInner
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_12 {y D ℓ : ℝ} (h0 : 0.195 ≤ y) (h1 : y ≤ 0.205) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((2 : ℕ)) : ℝ) + 0.032265 * (((0 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (2 : ℕ) * (15 / 16) ^ (0 : ℕ))) /
        (2 * ((3 / 4) ^ (2 : ℕ) * (15 / 16) ^ (0 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowInner y D ℓ := by
  unfold threeTenthsWindowInner
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_13 {y D ℓ : ℝ} (h0 : 0.205 ≤ y) (h1 : y ≤ 0.214) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((2 : ℕ)) : ℝ) + 0.032265 * (((1 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (2 : ℕ) * (15 / 16) ^ (1 : ℕ))) /
        (2 * ((3 / 4) ^ (2 : ℕ) * (15 / 16) ^ (1 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowInner y D ℓ := by
  unfold threeTenthsWindowInner
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_14 {y D ℓ : ℝ} (h0 : 0.214 ≤ y) (h1 : y ≤ 0.222) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((2 : ℕ)) : ℝ) + 0.032265 * (((3 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (2 : ℕ) * (15 / 16) ^ (3 : ℕ))) /
        (2 * ((3 / 4) ^ (2 : ℕ) * (15 / 16) ^ (3 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowInner y D ℓ := by
  unfold threeTenthsWindowInner
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_15 {y D ℓ : ℝ} (h0 : 0.222 ≤ y) (h1 : y ≤ 0.229) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((3 : ℕ)) : ℝ) + 0.032265 * (((0 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (3 : ℕ) * (15 / 16) ^ (0 : ℕ))) /
        (2 * ((3 / 4) ^ (3 : ℕ) * (15 / 16) ^ (0 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowInner y D ℓ := by
  unfold threeTenthsWindowInner
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_16 {y D ℓ : ℝ} (h0 : 0.229 ≤ y) (h1 : y ≤ 0.23613) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((3 : ℕ)) : ℝ) + 0.032265 * (((1 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (3 : ℕ) * (15 / 16) ^ (1 : ℕ))) /
        (2 * ((3 / 4) ^ (3 : ℕ) * (15 / 16) ^ (1 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowInner y D ℓ := by
  unfold threeTenthsWindowInner
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_17 {y D ℓ : ℝ} (h0 : 0.23613 ≤ y) (h1 : y ≤ 0.243) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((3 : ℕ)) : ℝ) + 0.032265 * (((2 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (3 : ℕ) * (15 / 16) ^ (2 : ℕ))) /
        (2 * ((3 / 4) ^ (3 : ℕ) * (15 / 16) ^ (2 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowOuter y D ℓ := by
  unfold threeTenthsWindowOuter
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_18 {y D ℓ : ℝ} (h0 : 0.243 ≤ y) (h1 : y ≤ 0.25) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((4 : ℕ)) : ℝ) + 0.032265 * (((0 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (4 : ℕ) * (15 / 16) ^ (0 : ℕ))) /
        (2 * ((3 / 4) ^ (4 : ℕ) * (15 / 16) ^ (0 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowOuter y D ℓ := by
  unfold threeTenthsWindowOuter
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_19 {y D ℓ : ℝ} (h0 : 0.25 ≤ y) (h1 : y ≤ 0.258) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((4 : ℕ)) : ℝ) + 0.032265 * (((1 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (4 : ℕ) * (15 / 16) ^ (1 : ℕ))) /
        (2 * ((3 / 4) ^ (4 : ℕ) * (15 / 16) ^ (1 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowOuter y D ℓ := by
  unfold threeTenthsWindowOuter
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_20 {y D ℓ : ℝ} (h0 : 0.258 ≤ y) (h1 : y ≤ 0.266) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((5 : ℕ)) : ℝ) + 0.032265 * (((0 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (5 : ℕ) * (15 / 16) ^ (0 : ℕ))) /
        (2 * ((3 / 4) ^ (5 : ℕ) * (15 / 16) ^ (0 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowOuter y D ℓ := by
  unfold threeTenthsWindowOuter
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_21 {y D ℓ : ℝ} (h0 : 0.266 ≤ y) (h1 : y ≤ 0.274) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((5 : ℕ)) : ℝ) + 0.032265 * (((3 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (5 : ℕ) * (15 / 16) ^ (3 : ℕ))) /
        (2 * ((3 / 4) ^ (5 : ℕ) * (15 / 16) ^ (3 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowOuter y D ℓ := by
  unfold threeTenthsWindowOuter
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_22 {y D ℓ : ℝ} (h0 : 0.274 ≤ y) (h1 : y ≤ 0.281) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((6 : ℕ)) : ℝ) + 0.032265 * (((3 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (6 : ℕ) * (15 / 16) ^ (3 : ℕ))) /
        (2 * ((3 / 4) ^ (6 : ℕ) * (15 / 16) ^ (3 : ℕ))) ≤ ℓ) :
    1 / 5000 ≤ threeTenthsWindowOuter y D ℓ := by
  unfold threeTenthsWindowOuter
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_23 {y D ℓ : ℝ} (h0 : 0.281 ≤ y) (h1 : y ≤ 0.285) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((7 : ℕ)) : ℝ) + 0.032265 * (((2 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (7 : ℕ) * (15 / 16) ^ (2 : ℕ))) /
        (2 * ((3 / 4) ^ (7 : ℕ) * (15 / 16) ^ (2 : ℕ))) ≤ ℓ) :
    1 / 5000 + 3.9462 * (y ^ 2 - 0.078961) ≤ threeTenthsWindowOuter y D ℓ := by
  unfold threeTenthsWindowOuter
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_24 {y D ℓ : ℝ} (h0 : 0.285 ≤ y) (h1 : y ≤ 0.289) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((8 : ℕ)) : ℝ) + 0.032265 * (((2 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (8 : ℕ) * (15 / 16) ^ (2 : ℕ))) /
        (2 * ((3 / 4) ^ (8 : ℕ) * (15 / 16) ^ (2 : ℕ))) ≤ ℓ) :
    1 / 5000 + 3.9462 * (y ^ 2 - 0.078961) ≤ threeTenthsWindowOuter y D ℓ := by
  unfold threeTenthsWindowOuter
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_25 {y D ℓ : ℝ} (h0 : 0.289 ≤ y) (h1 : y ≤ 0.292) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((9 : ℕ)) : ℝ) + 0.032265 * (((1 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (9 : ℕ) * (15 / 16) ^ (1 : ℕ))) /
        (2 * ((3 / 4) ^ (9 : ℕ) * (15 / 16) ^ (1 : ℕ))) ≤ ℓ) :
    1 / 5000 + 3.9462 * (y ^ 2 - 0.078961) ≤ threeTenthsWindowOuter y D ℓ := by
  unfold threeTenthsWindowOuter
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_26 {y D ℓ : ℝ} (h0 : 0.292 ≤ y) (h1 : y ≤ 0.295) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((10 : ℕ)) : ℝ) + 0.032265 * (((2 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (10 : ℕ) * (15 / 16) ^ (2 : ℕ))) /
        (2 * ((3 / 4) ^ (10 : ℕ) * (15 / 16) ^ (2 : ℕ))) ≤ ℓ) :
    1 / 5000 + 3.9462 * (y ^ 2 - 0.078961) ≤ threeTenthsWindowOuter y D ℓ := by
  unfold threeTenthsWindowOuter
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_27 {y D ℓ : ℝ} (h0 : 0.295 ≤ y) (h1 : y ≤ 0.297) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((12 : ℕ)) : ℝ) + 0.032265 * (((0 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (12 : ℕ) * (15 / 16) ^ (0 : ℕ))) /
        (2 * ((3 / 4) ^ (12 : ℕ) * (15 / 16) ^ (0 : ℕ))) ≤ ℓ) :
    1 / 5000 + 3.9462 * (y ^ 2 - 0.078961) ≤ threeTenthsWindowOuter y D ℓ := by
  unfold threeTenthsWindowOuter
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_28 {y D ℓ : ℝ} (h0 : 0.297 ≤ y) (h1 : y ≤ 0.2985) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((13 : ℕ)) : ℝ) + 0.032265 * (((2 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (13 : ℕ) * (15 / 16) ^ (2 : ℕ))) /
        (2 * ((3 / 4) ^ (13 : ℕ) * (15 / 16) ^ (2 : ℕ))) ≤ ℓ) :
    1 / 5000 + 3.9462 * (y ^ 2 - 0.078961) ≤ threeTenthsWindowOuter y D ℓ := by
  unfold threeTenthsWindowOuter
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

theorem threeTenthsWindow_piece_29 {y D ℓ : ℝ} (h0 : 0.2985 ≤ y) (h1 : y ≤ 0.3) (hD : -1.36513 ≤ D)
    (hℓ : 0.1438 * (((15 : ℕ)) : ℝ) + 0.032265 * (((2 : ℕ)) : ℝ) +
      (1000000 / 90601 * y ^ 2 - (1 - (3 / 4 : ℝ) ^ (15 : ℕ) * (15 / 16) ^ (2 : ℕ))) /
        (2 * ((3 / 4) ^ (15 : ℕ) * (15 / 16) ^ (2 : ℕ))) ≤ ℓ) :
    1 / 5000 + 3.9462 * (y ^ 2 - 0.078961) ≤ threeTenthsWindowOuter y D ℓ := by
  unfold threeTenthsWindowOuter
  have hyp : 0 ≤ y := le_trans (by norm_num) h0
  have hq : 0 ≤ (1 - (322 / 25) * y ^ 2 + (77 / 2) * y ^ 4) := by nlinarith [sq_nonneg y, pow_le_pow_left₀ hyp h1 2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := window_piece_hints h0 h1 (by norm_num)
  have hDq := mul_le_mul_of_nonneg_left hD hq
  have hℓq := mul_le_mul_of_nonneg_left hℓ hq
  norm_num at hℓq
  linarith [hDq, hℓq, p1, p2, p3, p4, p5]

/-! ### The potential of the gauge -/

/-- The potential on the inner region `|x| ≤ 0.23613`, where `12.88 − 231 x² ≥ 0`. -/
theorem threeTenthsGauge_potential_ge_inner {x : ℝ} (hx : |x| ≤ 0.23613) :
    threeTenthsWindowInner |x| (-Real.log (2 * (301 / 1000)) - 301 / 1000 / 2 - 2 * archConstantReal) (-(1 / 2) * Real.log (1 - 1000000 / 90601 * |x| ^ 2)) ≤
      -poleFreeWeilOperator threeTenthsGauge x + 2 * ∫ y, threeTenthsGauge y * Real.cosh ((x - y) / 2) := by
  set y := |x| with hydef
  have hy0 : 0 ≤ y := abs_nonneg x
  have hd : (0 : ℝ) ≤ 77 / 2 := by norm_num
  have hdc2 : 2 * (77 / 2) * (301 / 1000 : ℝ) ^ 2 ≤ 322 / 25 := by norm_num
  have hqR : (0 : ℝ) ≤ 1 - 322 / 25 * (301 / 1000) ^ 2 + 77 / 2 * (301 / 1000) ^ 4 := by norm_num
  have hδ : (0 : ℝ) < 1 / 1000 := by norm_num
  have hyR : |y| ≤ 301 / 1000 := by rw [abs_of_nonneg hy0]; linarith
  have hWy : poleFreeWeilOperator threeTenthsGauge x = poleFreeWeilOperator threeTenthsGauge y := by
    rcases le_or_gt 0 x with h | h
    · rw [hydef, abs_of_nonneg h]
    · rw [hydef, abs_of_neg h, poleFreeWeilOperator_neg (quarticWindowGauge_neg _ _ _ _)]
  rw [hWy]
  have hW := neg_poleFreeWeilOperator_quarticWindowGauge_ge_sharp (c := 322 / 25) (d := 77 / 2)
    (R := 301 / 1000) (δ := 1 / 1000) (x := y) hd hdc2 hqR hδ (by norm_num) hy0 (by linarith)
  have hα : 0 ≤ 322 / 25 - 6 * (77 / 2) * y ^ 2 := by
    have : y ^ 2 ≤ 0.23613 ^ 2 := pow_le_pow_left₀ hy0 hx 2
    linarith
  rw [min_eq_right hα, zero_mul, add_zero] at hW
  have hbr := cubicGauge_bracket_ge (R := 301 / 1000) (x := y) (by norm_num) (by norm_num)
    (by rw [abs_of_nonneg hy0]; linarith)
  have hk : y ^ 2 / (301 / 1000) ^ 2 = 1000000 / 90601 * y ^ 2 := by ring
  rw [hk] at hbr
  have hq0 : 0 ≤ quarticProfile (322 / 25) (77 / 2) y := by
    have := quarticProfile_ge_of_le hd hdc2 hyR; linarith
  have hqbr := mul_le_mul_of_nonneg_left hbr hq0
  have hG := integral_quarticWindowGauge_cosh_ge (c := 322 / 25) (d := 77 / 2) (R := 301 / 1000)
    (δ := 1 / 1000) (x := x) hd hdc2 hqR hδ (by norm_num) (by norm_num) (by linarith)
  rw [← sq_abs x, ← hydef] at hG
  simp only [levyMomentPoly, levyMomentErr, levyMomentErrUp, Nat.cast_ofNat] at hW
  unfold quarticProfile at hW hqbr
  unfold threeTenthsWindowInner
  linarith [hW, hqbr, hG]

/-- The potential on the outer region `0.23613 ≤ |x| ≤ 3/10`, where `12.88 − 231 x² ≤ 10⁻⁴`. -/
theorem threeTenthsGauge_potential_ge_outer {x : ℝ} (hx1 : 0.23613 ≤ |x|) (hx : |x| ≤ 3 / 10) :
    threeTenthsWindowOuter |x| (-Real.log (2 * (301 / 1000)) - 301 / 1000 / 2 - 2 * archConstantReal) (-(1 / 2) * Real.log (1 - 1000000 / 90601 * |x| ^ 2)) ≤
      -poleFreeWeilOperator threeTenthsGauge x + 2 * ∫ y, threeTenthsGauge y * Real.cosh ((x - y) / 2) := by
  set y := |x| with hydef
  have hy0 : 0 ≤ y := abs_nonneg x
  have hd : (0 : ℝ) ≤ 77 / 2 := by norm_num
  have hdc2 : 2 * (77 / 2) * (301 / 1000 : ℝ) ^ 2 ≤ 322 / 25 := by norm_num
  have hqR : (0 : ℝ) ≤ 1 - 322 / 25 * (301 / 1000) ^ 2 + 77 / 2 * (301 / 1000) ^ 4 := by norm_num
  have hδ : (0 : ℝ) < 1 / 1000 := by norm_num
  have hyR : |y| ≤ 301 / 1000 := by rw [abs_of_nonneg hy0]; linarith
  have hWy : poleFreeWeilOperator threeTenthsGauge x = poleFreeWeilOperator threeTenthsGauge y := by
    rcases le_or_gt 0 x with h | h
    · rw [hydef, abs_of_nonneg h]
    · rw [hydef, abs_of_neg h, poleFreeWeilOperator_neg (quarticWindowGauge_neg _ _ _ _)]
  rw [hWy]
  have hW := neg_poleFreeWeilOperator_quarticWindowGauge_ge_sharp (c := 322 / 25) (d := 77 / 2)
    (R := 301 / 1000) (δ := 1 / 1000) (x := y) hd hdc2 hqR hδ (by norm_num) hy0 (by linarith)
  have hU0 : 0 ≤ levyMomentErrUp 2 (301 / 1000 - y) + levyMomentErrUp 2 (301 / 1000 + y) := by
    unfold levyMomentErrUp
    have : 0 ≤ 301 / 1000 - y := by linarith
    positivity
  have hmin : 322 / 25 - 6 * (77 / 2) * y ^ 2 - 1 / 10000 ≤ min (322 / 25 - 6 * (77 / 2) * y ^ 2) 0 := by
    have : 0.23613 ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by norm_num) hx1 2
    exact le_min (by linarith) (by linarith)
  have hminU := mul_le_mul_of_nonneg_right hmin hU0
  have hbr := cubicGauge_bracket_ge (R := 301 / 1000) (x := y) (by norm_num) (by norm_num)
    (by rw [abs_of_nonneg hy0]; linarith)
  have hk : y ^ 2 / (301 / 1000) ^ 2 = 1000000 / 90601 * y ^ 2 := by ring
  rw [hk] at hbr
  have hq0 : 0 ≤ quarticProfile (322 / 25) (77 / 2) y := by
    have := quarticProfile_ge_of_le hd hdc2 hyR; linarith
  have hqbr := mul_le_mul_of_nonneg_left hbr hq0
  have hG := integral_quarticWindowGauge_cosh_ge (c := 322 / 25) (d := 77 / 2) (R := 301 / 1000)
    (δ := 1 / 1000) (x := x) hd hdc2 hqR hδ (by norm_num) (by norm_num) (by linarith)
  rw [← sq_abs x, ← hydef] at hG
  simp only [levyMomentPoly, levyMomentErr, levyMomentErrUp, Nat.cast_ofNat] at hW
  unfold quarticProfile at hW hqbr
  simp only [levyMomentErrUp, Nat.cast_ofNat] at hminU
  unfold threeTenthsWindowOuter
  linarith [hW, hqbr, hG, hminU]

/-- The potential bound on `0 ≤ |x| ≤ 0.1`. -/
theorem threeTenthsGauge_potential_ge_group_0 {x : ℝ} (hlo : 0 ≤ |x|) (hhi : |x| ≤ 0.1) :
    1 / 5000 + 2 * threeTenthsInnerCost x + 2 * (851 / 10000) * threeTenthsOuterCost |x| ≤
      -poleFreeWeilOperator threeTenthsGauge x + 2 * ∫ y, threeTenthsGauge y * Real.cosh ((x - y) / 2) := by
  have hD := threeTenthsGauge_constant_ge
  have hy0 : 0 ≤ |x| := abs_nonneg x
  have hs : 1000000 / 90601 * |x| ^ 2 < 1 := by
    have : |x| ^ 2 ≤ (3 / 10) ^ 2 := pow_le_pow_left₀ hy0 (by linarith) 2
    nlinarith
  have hC : threeTenthsInnerCost x = threeTenthsInnerCost |x| := by
    unfold threeTenthsInnerCost; rw [sq_abs]
  rw [hC]
  have anc := fun k j : ℕ => neg_half_log_one_sub_ge_anchor_grid hs k j

  rcases le_or_gt |x| 0.02 with h0 | h0
  ·
    have hw := threeTenthsWindow_piece_0 (y := |x|) (by linarith) (by linarith) hD (anc 0 0)
    have hP := threeTenthsGauge_potential_ge_inner (x := x) (by linarith)
    have hc1 := threeTenthsInnerCost_le_sq |x|
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc2]
    linarith
  rcases le_or_gt |x| 0.04 with h1 | h1
  ·
    have hw := threeTenthsWindow_piece_1 (y := |x|) (by linarith) (by linarith) hD (anc 0 0)
    have hP := threeTenthsGauge_potential_ge_inner (x := x) (by linarith)
    have hc1 := threeTenthsInnerCost_le_sq |x|
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc2]
    linarith
  rcases le_or_gt |x| 0.06 with h2 | h2
  ·
    have hw := threeTenthsWindow_piece_2 (y := |x|) (by linarith) (by linarith) hD (anc 0 0)
    have hP := threeTenthsGauge_potential_ge_inner (x := x) (by linarith)
    have hc1 := threeTenthsInnerCost_le_sq |x|
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc2]
    linarith
  rcases le_or_gt |x| 0.0851 with h3 | h3
  ·
    have hw := threeTenthsWindow_piece_3 (y := |x|) (by linarith) (by linarith) hD (anc 0 1)
    have hP := threeTenthsGauge_potential_ge_inner (x := x) (by linarith)
    have hc1 := threeTenthsInnerCost_le_sq |x|
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc2]
    linarith
  ·
    have hw := threeTenthsWindow_piece_4 (y := |x|) (by linarith) (by linarith) hD (anc 0 2)
    have hP := threeTenthsGauge_potential_ge_inner (x := x) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith

/-- The potential bound on `0.1 ≤ |x| ≤ 0.172`. -/
theorem threeTenthsGauge_potential_ge_group_1 {x : ℝ} (hlo : 0.1 ≤ |x|) (hhi : |x| ≤ 0.172) :
    1 / 5000 + 2 * threeTenthsInnerCost x + 2 * (851 / 10000) * threeTenthsOuterCost |x| ≤
      -poleFreeWeilOperator threeTenthsGauge x + 2 * ∫ y, threeTenthsGauge y * Real.cosh ((x - y) / 2) := by
  have hD := threeTenthsGauge_constant_ge
  have hy0 : 0 ≤ |x| := abs_nonneg x
  have hs : 1000000 / 90601 * |x| ^ 2 < 1 := by
    have : |x| ^ 2 ≤ (3 / 10) ^ 2 := pow_le_pow_left₀ hy0 (by linarith) 2
    nlinarith
  have hC : threeTenthsInnerCost x = threeTenthsInnerCost |x| := by
    unfold threeTenthsInnerCost; rw [sq_abs]
  rw [hC]
  have anc := fun k j : ℕ => neg_half_log_one_sub_ge_anchor_grid hs k j

  rcases le_or_gt |x| 0.115 with h0 | h0
  ·
    have hw := threeTenthsWindow_piece_5 (y := |x|) (by linarith) (by linarith) hD (anc 0 2)
    have hP := threeTenthsGauge_potential_ge_inner (x := x) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith
  rcases le_or_gt |x| 0.13 with h1 | h1
  ·
    have hw := threeTenthsWindow_piece_6 (y := |x|) (by linarith) (by linarith) hD (anc 0 3)
    have hP := threeTenthsGauge_potential_ge_inner (x := x) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith
  rcases le_or_gt |x| 0.145 with h2 | h2
  ·
    have hw := threeTenthsWindow_piece_7 (y := |x|) (by linarith) (by linarith) hD (anc 0 3)
    have hP := threeTenthsGauge_potential_ge_inner (x := x) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith
  rcases le_or_gt |x| 0.16 with h3 | h3
  ·
    have hw := threeTenthsWindow_piece_8 (y := |x|) (by linarith) (by linarith) hD (anc 1 0)
    have hP := threeTenthsGauge_potential_ge_inner (x := x) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith
  ·
    have hw := threeTenthsWindow_piece_9 (y := |x|) (by linarith) (by linarith) hD (anc 1 1)
    have hP := threeTenthsGauge_potential_ge_inner (x := x) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith

/-- The potential bound on `0.172 ≤ |x| ≤ 0.222`. -/
theorem threeTenthsGauge_potential_ge_group_2 {x : ℝ} (hlo : 0.172 ≤ |x|) (hhi : |x| ≤ 0.222) :
    1 / 5000 + 2 * threeTenthsInnerCost x + 2 * (851 / 10000) * threeTenthsOuterCost |x| ≤
      -poleFreeWeilOperator threeTenthsGauge x + 2 * ∫ y, threeTenthsGauge y * Real.cosh ((x - y) / 2) := by
  have hD := threeTenthsGauge_constant_ge
  have hy0 : 0 ≤ |x| := abs_nonneg x
  have hs : 1000000 / 90601 * |x| ^ 2 < 1 := by
    have : |x| ^ 2 ≤ (3 / 10) ^ 2 := pow_le_pow_left₀ hy0 (by linarith) 2
    nlinarith
  have hC : threeTenthsInnerCost x = threeTenthsInnerCost |x| := by
    unfold threeTenthsInnerCost; rw [sq_abs]
  rw [hC]
  have anc := fun k j : ℕ => neg_half_log_one_sub_ge_anchor_grid hs k j

  rcases le_or_gt |x| 0.184 with h0 | h0
  ·
    have hw := threeTenthsWindow_piece_10 (y := |x|) (by linarith) (by linarith) hD (anc 1 2)
    have hP := threeTenthsGauge_potential_ge_inner (x := x) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith
  rcases le_or_gt |x| 0.195 with h1 | h1
  ·
    have hw := threeTenthsWindow_piece_11 (y := |x|) (by linarith) (by linarith) hD (anc 1 3)
    have hP := threeTenthsGauge_potential_ge_inner (x := x) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith
  rcases le_or_gt |x| 0.205 with h2 | h2
  ·
    have hw := threeTenthsWindow_piece_12 (y := |x|) (by linarith) (by linarith) hD (anc 2 0)
    have hP := threeTenthsGauge_potential_ge_inner (x := x) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith
  rcases le_or_gt |x| 0.214 with h3 | h3
  ·
    have hw := threeTenthsWindow_piece_13 (y := |x|) (by linarith) (by linarith) hD (anc 2 1)
    have hP := threeTenthsGauge_potential_ge_inner (x := x) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith
  ·
    have hw := threeTenthsWindow_piece_14 (y := |x|) (by linarith) (by linarith) hD (anc 2 3)
    have hP := threeTenthsGauge_potential_ge_inner (x := x) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith

/-- The potential bound on `0.222 ≤ |x| ≤ 0.258`. -/
theorem threeTenthsGauge_potential_ge_group_3 {x : ℝ} (hlo : 0.222 ≤ |x|) (hhi : |x| ≤ 0.258) :
    1 / 5000 + 2 * threeTenthsInnerCost x + 2 * (851 / 10000) * threeTenthsOuterCost |x| ≤
      -poleFreeWeilOperator threeTenthsGauge x + 2 * ∫ y, threeTenthsGauge y * Real.cosh ((x - y) / 2) := by
  have hD := threeTenthsGauge_constant_ge
  have hy0 : 0 ≤ |x| := abs_nonneg x
  have hs : 1000000 / 90601 * |x| ^ 2 < 1 := by
    have : |x| ^ 2 ≤ (3 / 10) ^ 2 := pow_le_pow_left₀ hy0 (by linarith) 2
    nlinarith
  have hC : threeTenthsInnerCost x = threeTenthsInnerCost |x| := by
    unfold threeTenthsInnerCost; rw [sq_abs]
  rw [hC]
  have anc := fun k j : ℕ => neg_half_log_one_sub_ge_anchor_grid hs k j

  rcases le_or_gt |x| 0.229 with h0 | h0
  ·
    have hw := threeTenthsWindow_piece_15 (y := |x|) (by linarith) (by linarith) hD (anc 3 0)
    have hP := threeTenthsGauge_potential_ge_inner (x := x) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith
  rcases le_or_gt |x| 0.23613 with h1 | h1
  ·
    have hw := threeTenthsWindow_piece_16 (y := |x|) (by linarith) (by linarith) hD (anc 3 1)
    have hP := threeTenthsGauge_potential_ge_inner (x := x) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith
  rcases le_or_gt |x| 0.243 with h2 | h2
  ·
    have hw := threeTenthsWindow_piece_17 (y := |x|) (by linarith) (by linarith) hD (anc 3 2)
    have hP := threeTenthsGauge_potential_ge_outer (x := x) (by linarith) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith
  rcases le_or_gt |x| 0.25 with h3 | h3
  ·
    have hw := threeTenthsWindow_piece_18 (y := |x|) (by linarith) (by linarith) hD (anc 4 0)
    have hP := threeTenthsGauge_potential_ge_outer (x := x) (by linarith) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith
  ·
    have hw := threeTenthsWindow_piece_19 (y := |x|) (by linarith) (by linarith) hD (anc 4 1)
    have hP := threeTenthsGauge_potential_ge_outer (x := x) (by linarith) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith

/-- The potential bound on `0.258 ≤ |x| ≤ 0.289`. -/
theorem threeTenthsGauge_potential_ge_group_4 {x : ℝ} (hlo : 0.258 ≤ |x|) (hhi : |x| ≤ 0.289) :
    1 / 5000 + 2 * threeTenthsInnerCost x + 2 * (851 / 10000) * threeTenthsOuterCost |x| ≤
      -poleFreeWeilOperator threeTenthsGauge x + 2 * ∫ y, threeTenthsGauge y * Real.cosh ((x - y) / 2) := by
  have hD := threeTenthsGauge_constant_ge
  have hy0 : 0 ≤ |x| := abs_nonneg x
  have hs : 1000000 / 90601 * |x| ^ 2 < 1 := by
    have : |x| ^ 2 ≤ (3 / 10) ^ 2 := pow_le_pow_left₀ hy0 (by linarith) 2
    nlinarith
  have hC : threeTenthsInnerCost x = threeTenthsInnerCost |x| := by
    unfold threeTenthsInnerCost; rw [sq_abs]
  rw [hC]
  have anc := fun k j : ℕ => neg_half_log_one_sub_ge_anchor_grid hs k j

  rcases le_or_gt |x| 0.266 with h0 | h0
  ·
    have hw := threeTenthsWindow_piece_20 (y := |x|) (by linarith) (by linarith) hD (anc 5 0)
    have hP := threeTenthsGauge_potential_ge_outer (x := x) (by linarith) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith
  rcases le_or_gt |x| 0.274 with h1 | h1
  ·
    have hw := threeTenthsWindow_piece_21 (y := |x|) (by linarith) (by linarith) hD (anc 5 3)
    have hP := threeTenthsGauge_potential_ge_outer (x := x) (by linarith) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith
  rcases le_or_gt |x| 0.281 with h2 | h2
  ·
    have hw := threeTenthsWindow_piece_22 (y := |x|) (by linarith) (by linarith) hD (anc 6 3)
    have hP := threeTenthsGauge_potential_ge_outer (x := x) (by linarith) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 : threeTenthsOuterCost |x| = 0 := threeTenthsOuterCost_eq_zero (by linarith)
    rw [hc1, hc2]
    linarith
  rcases le_or_gt |x| 0.285 with h3 | h3
  ·
    have hw := threeTenthsWindow_piece_23 (y := |x|) (by linarith) (by linarith) hD (anc 7 2)
    have hP := threeTenthsGauge_potential_ge_outer (x := x) (by linarith) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 := threeTenthsOuterCost_le_sq (y := |x|) (by linarith)
    rw [hc1]
    linarith
  ·
    have hw := threeTenthsWindow_piece_24 (y := |x|) (by linarith) (by linarith) hD (anc 8 2)
    have hP := threeTenthsGauge_potential_ge_outer (x := x) (by linarith) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 := threeTenthsOuterCost_le_sq (y := |x|) (by linarith)
    rw [hc1]
    linarith

/-- The potential bound on `0.289 ≤ |x| ≤ 0.3`. -/
theorem threeTenthsGauge_potential_ge_group_5 {x : ℝ} (hlo : 0.289 ≤ |x|) (hhi : |x| ≤ 0.3) :
    1 / 5000 + 2 * threeTenthsInnerCost x + 2 * (851 / 10000) * threeTenthsOuterCost |x| ≤
      -poleFreeWeilOperator threeTenthsGauge x + 2 * ∫ y, threeTenthsGauge y * Real.cosh ((x - y) / 2) := by
  have hD := threeTenthsGauge_constant_ge
  have hy0 : 0 ≤ |x| := abs_nonneg x
  have hs : 1000000 / 90601 * |x| ^ 2 < 1 := by
    have : |x| ^ 2 ≤ (3 / 10) ^ 2 := pow_le_pow_left₀ hy0 (by linarith) 2
    nlinarith
  have hC : threeTenthsInnerCost x = threeTenthsInnerCost |x| := by
    unfold threeTenthsInnerCost; rw [sq_abs]
  rw [hC]
  have anc := fun k j : ℕ => neg_half_log_one_sub_ge_anchor_grid hs k j

  rcases le_or_gt |x| 0.292 with h0 | h0
  ·
    have hw := threeTenthsWindow_piece_25 (y := |x|) (by linarith) (by linarith) hD (anc 9 1)
    have hP := threeTenthsGauge_potential_ge_outer (x := x) (by linarith) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 := threeTenthsOuterCost_le_sq (y := |x|) (by linarith)
    rw [hc1]
    linarith
  rcases le_or_gt |x| 0.295 with h1 | h1
  ·
    have hw := threeTenthsWindow_piece_26 (y := |x|) (by linarith) (by linarith) hD (anc 10 2)
    have hP := threeTenthsGauge_potential_ge_outer (x := x) (by linarith) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 := threeTenthsOuterCost_le_sq (y := |x|) (by linarith)
    rw [hc1]
    linarith
  rcases le_or_gt |x| 0.297 with h2 | h2
  ·
    have hw := threeTenthsWindow_piece_27 (y := |x|) (by linarith) (by linarith) hD (anc 12 0)
    have hP := threeTenthsGauge_potential_ge_outer (x := x) (by linarith) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 := threeTenthsOuterCost_le_sq (y := |x|) (by linarith)
    rw [hc1]
    linarith
  rcases le_or_gt |x| 0.2985 with h3 | h3
  ·
    have hw := threeTenthsWindow_piece_28 (y := |x|) (by linarith) (by linarith) hD (anc 13 2)
    have hP := threeTenthsGauge_potential_ge_outer (x := x) (by linarith) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 := threeTenthsOuterCost_le_sq (y := |x|) (by linarith)
    rw [hc1]
    linarith
  ·
    have hw := threeTenthsWindow_piece_29 (y := |x|) (by linarith) (by linarith) hD (anc 15 2)
    have hP := threeTenthsGauge_potential_ge_outer (x := x) (by linarith) (by linarith)
    have hc1 : threeTenthsInnerCost |x| = 0 := threeTenthsInnerCost_eq_zero (by linarith)
    have hc2 := threeTenthsOuterCost_le_sq (y := |x|) (by linarith)
    rw [hc1]
    linarith

/-- **The potential of the gauge pays the fold costs**:
`−𝒲M(x) + 2 ∫ M(y) cosh((x − y)/2) dy ≥ 1/5000 + 2 C₁(x) + 2X₀ G_y(|x|)` on `[−3/10, 3/10]`,
`X₀ = 851/10000`, by thirty anchored pieces. -/
theorem threeTenthsGauge_potential_ge {x : ℝ} (hx : |x| ≤ 3 / 10) :
    1 / 5000 + 2 * threeTenthsInnerCost x + 2 * (851 / 10000) * threeTenthsOuterCost |x| ≤
      -poleFreeWeilOperator threeTenthsGauge x + 2 * ∫ y, threeTenthsGauge y * Real.cosh ((x - y) / 2) := by
  have hy0 : 0 ≤ |x| := abs_nonneg x
  rcases le_or_gt |x| 0.1 with g0 | g0
  · exact threeTenthsGauge_potential_ge_group_0 (by linarith) g0
  rcases le_or_gt |x| 0.172 with g1 | g1
  · exact threeTenthsGauge_potential_ge_group_1 (by linarith) g1
  rcases le_or_gt |x| 0.222 with g2 | g2
  · exact threeTenthsGauge_potential_ge_group_2 (by linarith) g2
  rcases le_or_gt |x| 0.258 with g3 | g3
  · exact threeTenthsGauge_potential_ge_group_3 (by linarith) g3
  rcases le_or_gt |x| 0.289 with g4 | g4
  · exact threeTenthsGauge_potential_ge_group_4 (by linarith) g4
  · exact threeTenthsGauge_potential_ge_group_5 (by linarith) (by linarith)

/-! ### Even-sector positivity on `[−3/10, 3/10]` -/

/-- **Weil positivity of every even test supported in `[−3/10, 3/10]`.** Every even `F ∈ C²_c`
vanishing outside `[−3/10, 3/10]` satisfies `Ẑ(F) ≥ (1/5000) ∫ F²`: the fold cost is paid on the
inner point by `2C₁(x)`, on the outer point by `2X₀ G_y(|x|)`, both below the sharp gauge potential. -/
theorem fullZeroForm_ge_of_even_support_le_threeTenths {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (heven : ∀ x, F (-x) = F x)
    (hsupp : ∀ x, 3 / 10 < |x| → F x = 0) :
    1 / 5000 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  set M := quarticWindowGauge (322 / 25) (77 / 2) (301 / 1000) (1 / 1000) with hMdef
  set u : ℝ → ℝ := fun x => F x * (quarticProfile (322 / 25) (77 / 2) x)⁻¹ with hudef
  have hd : (0 : ℝ) ≤ 77 / 2 := by norm_num
  have hdc2 : 2 * (77 / 2) * (301 / 1000 : ℝ) ^ 2 ≤ 322 / 25 := by norm_num
  have hqR : (0 : ℝ) ≤ 1 - 322 / 25 * (301 / 1000) ^ 2 + 77 / 2 * (301 / 1000) ^ 4 := by norm_num
  have hδ : (0 : ℝ) < 1 / 1000 := by norm_num
  have hMd : ContDiff ℝ 2 M := contDiff_quarticWindowGauge _ _ _ _
  have hMcs : HasCompactSupport M := hasCompactSupport_quarticWindowGauge _ _ _ hδ
  have hnn : ∀ y, 0 ≤ M y := quarticWindowGauge_nonneg hd hdc2 hqR hδ
  have hle : ∀ y, M y ≤ 1 := quarticWindowGauge_le_one hd hdc2 hqR hδ
  have hzero : ∀ y, 301 / 1000 ≤ |y| → M y = 0 := fun y hy =>
    quarticWindowGauge_eq_zero _ _ hδ hy
  have hMB : ∀ x, M x ≠ 0 → |x| ≤ 301 / 1000 := fun x hx => by
    by_contra h
    exact hx (hzero x (not_le.mp h).le)
  have hMe : ∀ y, M (-y) = M y := quarticWindowGauge_neg _ _ _ _
  have hlog2 : 2 * (301 / 1000 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num; linarith
  have hqpos : ∀ y, |y| ≤ 301 / 1000 → 0 < quarticProfile (322 / 25) (77 / 2) y := fun y hy => by
    have := quarticProfile_ge_of_le hd hdc2 hy
    norm_num at this
    linarith
  -- the profile
  have hu : ContDiff ℝ 2 u := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : |y| < 301 / 1000
    · exact hF.contDiffAt.mul ((contDiff_quarticProfile _ _).contDiffAt.inv
        (hqpos y hy.le).ne' |>.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl))
    · have hopen : IsOpen {z : ℝ | 3 / 10 < |z|} := isOpen_lt continuous_const continuous_abs
      have hev : u =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hopen.mem_nhds (show 3 / 10 < |y| by linarith [not_lt.mp hy])] with z hz
        simp [hudef, hsupp z hz]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have huc : HasCompactSupport u := hFc.mul_right
  have hue : ∀ x, u (-x) = u x := fun x => by
    simp only [hudef]
    rw [heven, quarticProfile_neg]
  have hFu : (fun x => M x * u x) = F := funext fun x => by
    by_cases hx : |x| ≤ 3 / 10
    · have hq := (hqpos x (by linarith)).ne'
      simp only [hudef, hMdef]
      rw [quarticWindowGauge_eq _ _ hδ (by linarith : |x| ≤ 301 / 1000 - 1 / 1000)]
      field_simp
    · simp only [hudef, hsupp x (not_le.mp hx), zero_mul, mul_zero]
  -- the representation
  have hrep := fullZeroForm_mul_eq_gauge_window hu huc hMd hMcs hle hnn hzero hlog2
  rw [hFu] at hrep
  -- the jump part: the fold with its two-point cost
  obtain ⟨Ku, -, hKu⟩ := exists_lipschitz_bound_of_compactSupport (hu.of_le (by norm_num)) huc
  have huL : ∀ a b, |u a - u b| ≤ Ku * |a - b| := fun a b => hKu b a
  have hωI := integrableOn_archLevy_mul_gaugeJumpProfile hle hnn hzero (by norm_num) (by norm_num)
    hu.continuous hMd.continuous hMcs huL
  have hcI : Integrable fun t => Real.cosh (t / 2) * gaugeJumpProfile M u t :=
    (integrable_gaugeJump_kernel hu.continuous hMd.continuous hMB).integral_prod_left.congr
      (Eventually.of_forall fun t => by
        simp only [gaugeJumpProfile]
        rw [integral_const_mul])
  have hGm : ∀ x, Measurable (threeTenthsFoldCost x) := fun x => by
    have : Continuous (threeTenthsFoldCost x) := by unfold threeTenthsFoldCost; fun_prop
    exact this.measurable
  have hGym : Measurable threeTenthsOuterCost := by
    have : Continuous threeTenthsOuterCost := by unfold threeTenthsOuterCost; fun_prop
    exact this.measurable
  have hC₁m : Measurable threeTenthsInnerCost := by
    have : Continuous threeTenthsInnerCost := by unfold threeTenthsInnerCost; fun_prop
    exact this.measurable
  have hcost := integral_kappa_mul_gaugeJumpProfile_ge_hub hMd.continuous hu.continuous hMe hue hnn
    hle hzero huL (by norm_num) measurable_weilJumpDensity (C := 4) (by norm_num)
    (fun t ht0 ht1 => abs_weilJumpDensity_le ht0 (by linarith)) MeasurableSet.empty
    (empty_subset _) 0 hGm hGym threeTenthsFoldCost_nonneg threeTenthsFoldCost_le_outer
    threeTenthsOuterCost_le hC₁m threeTenthsInnerCost_nonneg threeTenthsInnerCost_le
    (fun x hx _ => integral_threeTenthsFoldCost_mul_gauge_le hx) (X₀ := 851 / 10000) (by norm_num)
    (fun x y hx => threeTenthsFoldCost_eq_zero hx)
    (fun s x hs hx hxs => by
      have := weilJumpDensity_fold_ge_neg_threeTenthsFoldCost hs hx hxs
      simpa using this)
  rw [mul_zero, zero_mul, zero_sub] at hcost
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
  have hC1abs : ∀ x, threeTenthsInnerCost |x| = threeTenthsInnerCost x := fun x => by
    unfold threeTenthsInnerCost; rw [sq_abs]
  have hA : (∫ x, threeTenthsInnerCost x * (u x ^ 2 * M x)) =
      2 * ∫ x in Ioi (0 : ℝ), threeTenthsInnerCost x * (u x ^ 2 * M x) := by
    rw [← integral_comp_abs (f := fun x => threeTenthsInnerCost x * (u x ^ 2 * M x))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [(habs x).1, (habs x).2, hC1abs]
  have hB : (∫ x, threeTenthsOuterCost |x| * M x * u x ^ 2) =
      2 * ∫ y in Ioi (0 : ℝ), threeTenthsOuterCost y * M y * u y ^ 2 := by
    rw [← integral_comp_abs (f := fun y => threeTenthsOuterCost y * M y * u y ^ 2)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [(habs x).1, (habs x).2]
  -- the potential integrands
  obtain ⟨KM, -, hKM⟩ := exists_lipschitz_bound_of_compactSupport (hMd.of_le (by norm_num)) hMcs
  have hML : ∀ a b, |M a - M b| ≤ KM * |a - b| := fun a b => hKM b a
  have hdec8 : ∀ y, |M y| ≤ Real.exp (8 * (301 / 1000)) * Real.exp (-(8 * |y|)) := by
    intro y
    by_cases hy : |y| < 301 / 1000
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
  have i3 : Integrable fun x => threeTenthsInnerCost x * (u x ^ 2 * M x) := by
    have hc : Continuous threeTenthsInnerCost := by unfold threeTenthsInnerCost; fun_prop
    exact (hc.mul hu2M).integrable_of_hasCompactSupport hu2Mc.mul_left
  have hOc : Continuous threeTenthsOuterCost := by unfold threeTenthsOuterCost; fun_prop
  have i4 : Integrable fun x => threeTenthsOuterCost |x| * M x * u x ^ 2 :=
    (((hOc.comp continuous_abs).mul hMd.continuous).mul
      (hu.continuous.pow 2)).integrable_of_hasCompactSupport (hMcs.mul_left.mul_right)
  -- the pointwise potential, net of the fold costs
  have hpt : ∀ x, 1 / 5000 * F x ^ 2 ≤ u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * (∫ y, M y * Real.cosh ((x - y) / 2)) - 2 * threeTenthsInnerCost x -
        2 * (851 / 10000) * threeTenthsOuterCost |x|) := by
    intro x
    by_cases hx : |x| ≤ 3 / 10
    · have hpot : 1 / 5000 + 2 * threeTenthsInnerCost x +
          2 * (851 / 10000) * threeTenthsOuterCost |x| ≤
          -poleFreeWeilOperator M x + 2 * ∫ y, M y * Real.cosh ((x - y) / 2) :=
        threeTenthsGauge_potential_ge hx
      have hFx : F x = M x * u x := (congrFun hFu x).symm
      rw [hFx]
      have hu2 : 0 ≤ u x ^ 2 * M x := mul_nonneg (sq_nonneg _) (hnn x)
      have hM1 := hle x
      have hP : 1 / 5000 ≤ -poleFreeWeilOperator M x + 2 * (∫ y, M y * Real.cosh ((x - y) / 2)) -
          2 * threeTenthsInnerCost x - 2 * (851 / 10000) * threeTenthsOuterCost |x| := by
        linarith
      nlinarith [mul_le_mul_of_nonneg_left hP hu2, mul_nonneg hu2 (by linarith : 0 ≤ 1 - M x)]
    · have hF0 : F x = 0 := hsupp x (not_le.mp hx)
      have hu0 : u x = 0 := by simp [hudef, hF0]
      rw [hF0, hu0]
      simp
  -- assemble
  have hF2 : Integrable fun x => 1 / 5000 * F x ^ 2 :=
    ((hF.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)).const_mul _
  have e : ∀ x, u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * (∫ y, M y * Real.cosh ((x - y) / 2)) - 2 * threeTenthsInnerCost x -
        2 * (851 / 10000) * threeTenthsOuterCost |x|) =
      (u x ^ 2 * M x * -poleFreeWeilOperator M x +
        2 * (u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2))) -
        (2 * (threeTenthsInnerCost x * (u x ^ 2 * M x)) +
          2 * (851 / 10000) * (threeTenthsOuterCost |x| * M x * u x ^ 2)) := fun x => by ring
  have i12 : Integrable fun x => u x ^ 2 * M x * -poleFreeWeilOperator M x +
      2 * (u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2)) := i1.add (i2.const_mul 2)
  have i34 : Integrable fun x => 2 * (threeTenthsInnerCost x * (u x ^ 2 * M x)) +
      2 * (851 / 10000) * (threeTenthsOuterCost |x| * M x * u x ^ 2) :=
    (i3.const_mul _).add (i4.const_mul _)
  have hsum : Integrable fun x => u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * (∫ y, M y * Real.cosh ((x - y) / 2)) - 2 * threeTenthsInnerCost x -
        2 * (851 / 10000) * threeTenthsOuterCost |x|) :=
    (i12.sub i34).congr (Eventually.of_forall fun x => (e x).symm)
  have hint := integral_mono hF2 hsum hpt
  have hsplit : (∫ x, u x ^ 2 * M x * (-poleFreeWeilOperator M x +
      2 * (∫ y, M y * Real.cosh ((x - y) / 2)) - 2 * threeTenthsInnerCost x -
        2 * (851 / 10000) * threeTenthsOuterCost |x|)) =
      ((∫ x, u x ^ 2 * M x * -poleFreeWeilOperator M x) +
        2 * ∫ x, u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2)) -
        (2 * (∫ x, threeTenthsInnerCost x * (u x ^ 2 * M x)) +
          2 * (851 / 10000) * ∫ x, threeTenthsOuterCost |x| * M x * u x ^ 2) := by
    rw [integral_congr_ae (Eventually.of_forall e), integral_sub i12 i34,
      integral_add (f := fun x => u x ^ 2 * M x * -poleFreeWeilOperator M x)
        (g := fun x => 2 * (u x ^ 2 * M x * ∫ y, M y * Real.cosh ((x - y) / 2))) i1
        (i2.const_mul 2),
      integral_add (f := fun x => 2 * (threeTenthsInnerCost x * (u x ^ 2 * M x)))
        (g := fun x => 2 * (851 / 10000) * (threeTenthsOuterCost |x| * M x * u x ^ 2))
        (i3.const_mul _) (i4.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul]
  rw [integral_const_mul] at hint
  rw [hrep]
  linarith [hcost, eκ, hA, hB, hint, hsplit]

/-! ### All profiles on `[−29/100, 29/100]` -/

/-- **Weil positivity on `[−29/100, 29/100]`, past the plastic fold boundary.** Every real
`F ∈ C²_c` vanishing outside `[−29/100, 29/100]` satisfies `Ẑ(F) ≥ (1/5000) ∫ F²`. -/
theorem fullZeroForm_ge_of_support_le_threeTenths {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hsupp : ∀ x, 3 / 10 < |x| → F x = 0) :
    1 / 5000 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  have hse : ∀ x, 3 / 10 < |x| → evenPartReal F x = 0 := fun x hx => by
    unfold evenPartReal
    rw [hsupp x hx, hsupp (-x) (by rwa [abs_neg])]
    norm_num
  have hso : ∀ x, 17 / 50 < |x| → oddPartReal F x = 0 := fun x hx => by
    unfold oddPartReal
    rw [hsupp x (by linarith), hsupp (-x) (by rw [abs_neg]; linarith)]
    norm_num
  have he := fullZeroForm_ge_of_even_support_le_threeTenths (contDiff_evenPartReal hF)
    (hasCompactSupport_evenPartReal hFc) (evenPartReal_neg F) hse
  have ho := fullZeroForm_ge_of_odd_support_le_curved (contDiff_oddPartReal hF)
    (hasCompactSupport_oddPartReal hFc) (oddPartReal_neg F) hso
  have hnn : 0 ≤ ∫ x, oddPartReal F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [fullZeroForm_eq_even_add_odd hF hFc, integral_sq_eq_even_add_odd hF.continuous hFc]
  linarith

/-! ### Complex tests and the restricted Weil ground energy -/

/-- **Coercive zeta positivity for complex tests on `[−29/100, 29/100]`.** -/
theorem zetaZeroConfig_re_W_ge_of_support_le_threeTenths {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Icc (-(3 / 10)) (3 / 10)) :
    1 / 5000 * ∫ x, ‖g x‖ ^ 2 ≤ (zetaZeroConfig.W g g).re := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hzero : ∀ x, 3 / 10 < |x| → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hgs h
      rw [mem_Icc] at this
      exact absurd (abs_le.mpr this) (not_le.mpr hx)
  have hre : ContDiff ℝ 2 fun u => (g u).re := Complex.reCLM.contDiff.comp hg
  have him : ContDiff ℝ 2 fun u => (g u).im := Complex.imCLM.contDiff.comp hg
  have hrec : HasCompactSupport fun u => (g u).re := hgc.comp_left Complex.zero_re
  have himc : HasCompactSupport fun u => (g u).im := hgc.comp_left Complex.zero_im
  have h1 := fullZeroForm_ge_of_support_le_threeTenths hre hrec fun x hx => by simp [hzero x hx]
  have h2 := fullZeroForm_ge_of_support_le_threeTenths him himc fun x hx => by simp [hzero x hx]
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

/-- **The floor past the fold**: `μ(A) ≥ 1/5000` for every aperture `A ≤ 29/100`. -/
theorem one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeTenths {A : SuzukiPositiveAperture}
    (hA : A.1 ≤ 3 / 10) : 1 / 5000 ≤ ccmRestrictedWeilGroundEnergy A := by
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
  have hsupp : tsupport (u : ℝ → ℂ) ⊆ Icc (-(3 / 10)) (3 / 10) :=
    u.tsupport_subset.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact zetaZeroConfig_re_W_ge_of_support_le_threeTenths
    (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) hsupp

/-- **Contact apertures exceed `29/100`.** -/
theorem lt_of_ccmRestrictedWeilGroundEnergy_nonpos_threeTenths {A : SuzukiPositiveAperture}
    (h : ccmRestrictedWeilGroundEnergy A ≤ 0) : 3 / 10 < A.1 := by
  by_contra hA
  have := one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeTenths (not_lt.mp hA)
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory
