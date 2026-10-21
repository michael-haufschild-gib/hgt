import GaloisForLFunctions.ArithmeticIncidencePositivity.SharpFoldOddWindowPastSevenTwentieths

/-!
# The potential numerator of the window `356/1000`

For the gauge `h(y) = 1/500 + (3/5)y − y² − (11/50)y³ − (49/20)y⁴` and the plateau of radius
`R = 7121/20000` around the window `r = 356/1000`, the ground-state potential, the killing, the
plateau potential and the second-order expansions combine, after multiplication by `h(x)`, into the
numerator `N(κ, x)` (`schurFoldNumerator`, `κ = log 2 + γ + log π`). This module certifies its size
on `(0, 356/1000]`:

* `N ≥ 0` on `(0, 337/1000]` (`schurFoldNumerator_nonneg_inner`);
* `N ≥ 2/1000` on the inner edge `[337/1000, 343/1000]` of the prime strip
  (`schurFoldNumerator_innerEdge`);
* `N ≥ 33/10000` on `[343/1000, 35/100]` (`schurFoldNumerator_strip`);
* `N ≥ 85/10000` on the hub `[35/100, 356/1000]` (`schurFoldNumerator_hub`).

Every interval bound linearises the logarithms by a tangent at a `7`-smooth anchor, or uses
monotonicity of the logarithmic terms, and closes the remaining polynomial inequality.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The gauge and the numerator -/

theorem schurFoldGauge_ge {x : ℝ} (hx0 : 0 ≤ x) (hxr : x ≤ 356 / 1000) :
    1 / 500 ≤ quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x := by
  unfold quarticGauge
  have h : 0 ≤ 3 / 5 - x - 11 / 50 * x ^ 2 - 49 / 20 * x ^ 3 := by
    nlinarith [pow_le_pow_left₀ hx0 hxr 3]
  nlinarith [mul_nonneg hx0 h]

theorem schurFoldGauge_divDiff_le {u v : ℝ} (hu0 : 0 ≤ u) (hur : u ≤ 356 / 1000) (hv0 : 0 ≤ v)
    (hvr : v ≤ 356 / 1000) :
    |3 / 5 + -1 * (u + v) + -11 / 50 * (u ^ 2 + u * v + v ^ 2) +
      -49 / 20 * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3)| ≤ 16 / 25 := by
  have h1 := mul_nonneg hu0 hv0
  have h2 : u ^ 3 ≤ (356 / 1000) ^ 3 := pow_le_pow_left₀ hu0 hur 3
  have h3 : v ^ 3 ≤ (356 / 1000) ^ 3 := pow_le_pow_left₀ hv0 hvr 3
  have h4 : u ^ 2 * v ≤ (356 / 1000) ^ 3 := by
    nlinarith [mul_le_mul (pow_le_pow_left₀ hu0 hur 2) hvr hv0 (by positivity)]
  have h5 : u * v ^ 2 ≤ (356 / 1000) ^ 3 := by
    nlinarith [mul_le_mul hur (pow_le_pow_left₀ hv0 hvr 2) (by positivity) (by norm_num)]
  have h6 : 0 ≤ u ^ 2 * v := by positivity
  have h7 : 0 ≤ u * v ^ 2 := by positivity
  have h8 : 0 ≤ u ^ 3 := by positivity
  have h9 : 0 ≤ v ^ 3 := by positivity
  rw [abs_le]; constructor <;> nlinarith

/-- The polynomial part of the principal surplus of the gauge on `[0, 356/1000]`. -/
def schurFoldPoly (x : ℝ) : ℝ :=
  3 / 5 * x + -1 * (3 / 2 * x ^ 2 - 356 / 1000 * x) +
    -11 / 50 * (11 / 6 * x ^ 3 - (356 / 1000) ^ 2 * x / 2) +
    -49 / 20 * (25 / 12 * x ^ 4 - 356 / 1000 * x ^ 3 - (356 / 1000) ^ 3 * x / 3)

/-- The numerator of the potential on `[−356/1000, 356/1000]` (`κ` stands for `log 2 + γ + log π`). -/
def schurFoldNumerator (κ x : ℝ) : ℝ :=
  (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Real.log (x + 356 / 1000) - Real.log x) +
    quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x *
      (-(1 / 2) * Real.log (7121 / 20000 - x) - 1 / 2 * Real.log (7121 / 20000 + x) - κ - 1 / 40000 -
        (x + 356 / 1000) ^ 2 / 48 - 5 * (x + 356 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7121 / 20000) ^ 2) / 48 - 331 / 20000) +
    schurFoldPoly x + firstOrderSurplus (3 / 5) (-1) (-11 / 50) (-49 / 20) (356 / 1000) x - 16 / 25 * (4 / 125 * (356 / 1000) ^ 5)

/-- **Tangent form of the numerator** on `[p, q] ⊆ [7/100, 356/1000]`. -/
theorem schurFoldNumerator_ge_tangent {κ x p q v a b Lv La Lb : ℝ} (hp : 7 / 100 ≤ p)
    (hpx : p ≤ x) (hxq : x ≤ q) (hq : q ≤ 356 / 1000) (hv : 0 < v) (ha : 0 < a) (hb : 0 < b)
    (hLv : Real.log v ≤ Lv) (hLa : Real.log a ≤ La) (hLb : Real.log b ≤ Lb)
    (hκ : κ ≤ 241517 / 100000) :
    (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Lv + 1 / v - 1) +
        356 / 1000 / v * (1 / (500 * q) - x - 49 / 20 * x ^ 3) +
        quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x *
          (-(1 / 2) * (La + (7121 / 20000 - x) / a - 1) - 1 / 2 * (Lb + (7121 / 20000 + x) / b - 1) -
            241517 / 100000 - 1 / 40000 - (q + 356 / 1000) ^ 2 / 48 -
            5 * (q + 356 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7121 / 20000) ^ 2) / 48 - 331 / 20000) +
        schurFoldPoly x + firstOrderSurplus (3 / 5) (-1) (-11 / 50) (-49 / 20) (356 / 1000) x - 16 / 25 * (4 / 125 * (356 / 1000) ^ 5) ≤
      schurFoldNumerator κ x := by
  have hx0 : 0 < x := by linarith
  have hxr : x ≤ 356 / 1000 := le_trans hxq hq
  have hℓ : Real.log (x + 356 / 1000) - Real.log x ≤ Lv + (1 + 356 / 1000 / x) / v - 1 := by
    rw [← Real.log_div (by linarith) hx0.ne']
    have e : (x + 356 / 1000) / x = 1 + 356 / 1000 / x := by field_simp
    rw [e]
    have := log_le_tangent (show 0 < 1 + 356 / 1000 / x by positivity) hv
    linarith
  have hc : 1 / 500 - x ^ 2 - 49 / 20 * x ^ 4 ≤ 0 := by nlinarith [pow_nonneg hx0.le 4]
  have h1 : (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Lv + (1 + 356 / 1000 / x) / v - 1) ≤
      (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Real.log (x + 356 / 1000) - Real.log x) :=
    mul_le_mul_of_nonpos_left hℓ hc
  have h1' : (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Lv + 1 / v - 1) +
      356 / 1000 / v * (1 / (500 * q) - x - 49 / 20 * x ^ 3) ≤
      (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Lv + (1 + 356 / 1000 / x) / v - 1) := by
    have e : (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Lv + (1 + 356 / 1000 / x) / v - 1) =
        (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Lv + 1 / v - 1) +
          356 / 1000 / v * (1 / (500 * x) - x - 49 / 20 * x ^ 3) := by
      field_simp; ring
    rw [e]
    have hqx : 1 / (500 * q) ≤ 1 / (500 * x) := one_div_le_one_div_of_le (by positivity) (by linarith)
    have hv' : 0 ≤ 356 / 1000 / v := by positivity
    nlinarith
  have hla : -(1 / 2) * (La + (7121 / 20000 - x) / a - 1) ≤ -(1 / 2) * Real.log (7121 / 20000 - x) := by
    have := log_le_tangent (show (0 : ℝ) < 7121 / 20000 - x by linarith) ha
    linarith
  have hlb : -(1 / 2) * (Lb + (7121 / 20000 + x) / b - 1) ≤ -(1 / 2) * Real.log (7121 / 20000 + x) := by
    have := log_le_tangent (show (0 : ℝ) < 7121 / 20000 + x by linarith) hb
    linarith
  have hp2 : (x + 356 / 1000) ^ 2 ≤ (q + 356 / 1000) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 356 / 1000) ^ 3 ≤ (q + 356 / 1000) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := schurFoldGauge_ge hx0.le hxr
  have h2 : quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x *
        (-(1 / 2) * (La + (7121 / 20000 - x) / a - 1) - 1 / 2 * (Lb + (7121 / 20000 + x) / b - 1) -
          241517 / 100000 - 1 / 40000 - (q + 356 / 1000) ^ 2 / 48 -
          5 * (q + 356 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7121 / 20000) ^ 2) / 48 - 331 / 20000) ≤
      quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x *
        (-(1 / 2) * Real.log (7121 / 20000 - x) - 1 / 2 * Real.log (7121 / 20000 + x) - κ - 1 / 40000 -
          (x + 356 / 1000) ^ 2 / 48 - 5 * (x + 356 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7121 / 20000) ^ 2) / 48 - 331 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold schurFoldNumerator
  linarith

/-- **Monotone form of the numerator** on `[p, q] ⊆ [7/100, 356/1000]`. -/
theorem schurFoldNumerator_ge_monotone {κ x p q Lℓ Llam : ℝ} (hp : 7 / 100 ≤ p) (hpx : p ≤ x)
    (hxq : x ≤ q) (hq : q ≤ 356 / 1000)
    (hLℓ : Real.log (p + 356 / 1000) - Real.log p ≤ Lℓ)
    (hLlam : Llam ≤ -(1 / 2) * Real.log ((7121 / 20000) ^ 2 - p ^ 2)) (hκ : κ ≤ 241517 / 100000) :
    (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * Lℓ +
        quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x *
          (Llam - 241517 / 100000 - 1 / 40000 - (q + 356 / 1000) ^ 2 / 48 -
            5 * (q + 356 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7121 / 20000) ^ 2) / 48 - 331 / 20000) +
        schurFoldPoly x + firstOrderSurplus (3 / 5) (-1) (-11 / 50) (-49 / 20) (356 / 1000) x - 16 / 25 * (4 / 125 * (356 / 1000) ^ 5) ≤
      schurFoldNumerator κ x := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 < x := by linarith
  have hxr : x ≤ 356 / 1000 := le_trans hxq hq
  have hℓ : Real.log (x + 356 / 1000) - Real.log x ≤ Lℓ := by
    rw [← Real.log_div (by linarith) hx0.ne']
    rw [← Real.log_div (by linarith) hp0.ne'] at hLℓ
    refine le_trans (Real.log_le_log (by positivity) ?_) hLℓ
    rw [div_le_div_iff₀ hx0 hp0]; nlinarith
  have hc : 1 / 500 - x ^ 2 - 49 / 20 * x ^ 4 ≤ 0 := by nlinarith [pow_nonneg hx0.le 4]
  have h1 := mul_le_mul_of_nonpos_left hℓ hc
  have hlam : Llam ≤ -(1 / 2) * Real.log (7121 / 20000 - x) - 1 / 2 * Real.log (7121 / 20000 + x) := by
    have e : -(1 / 2) * Real.log (7121 / 20000 - x) - 1 / 2 * Real.log (7121 / 20000 + x) =
        -(1 / 2) * Real.log ((7121 / 20000) ^ 2 - x ^ 2) := by
      rw [show (7121 / 20000 : ℝ) ^ 2 - x ^ 2 = (7121 / 20000 - x) * (7121 / 20000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hmono : Real.log ((7121 / 20000) ^ 2 - x ^ 2) ≤ Real.log ((7121 / 20000) ^ 2 - p ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    linarith
  have hp2 : (x + 356 / 1000) ^ 2 ≤ (q + 356 / 1000) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 356 / 1000) ^ 3 ≤ (q + 356 / 1000) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := schurFoldGauge_ge hx0.le hxr
  have h2 : quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x *
        (Llam - 241517 / 100000 - 1 / 40000 - (q + 356 / 1000) ^ 2 / 48 -
          5 * (q + 356 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7121 / 20000) ^ 2) / 48 - 331 / 20000) ≤
      quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x *
        (-(1 / 2) * Real.log (7121 / 20000 - x) - 1 / 2 * Real.log (7121 / 20000 + x) - κ - 1 / 40000 -
          (x + 356 / 1000) ^ 2 / 48 - 5 * (x + 356 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7121 / 20000) ^ 2) / 48 - 331 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold schurFoldNumerator
  nlinarith

theorem schurFoldNumerator_nonneg_one {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 7/100 ≤ x)
    (h2 : x ≤ 1/10) : 0 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ea := log_smooth_div 0 3 0 0 2 0 2 0
  have eb := log_smooth_div 0 0 0 1 4 0 0 0
  norm_num at ea eb
  have hv : Real.log (5) ≤ 1.609438 := by linarith [l5.2]
  have ha : Real.log (27/100) ≤ -1.309333 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (7/16) ≤ -0.826678 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (schurFoldNumerator_ge_tangent (p := 7/100) (q := 1/10) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 17/200)),
    sq_nonneg (x - 17/200), mul_nonneg (sq_nonneg (x - 17/200)) (sq_nonneg (x - 17/200)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem schurFoldNumerator_nonneg_two {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 1/10 ≤ x)
    (h2 : x ≤ 13/100) : 0 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 2 0 0 0 0 0 0 0
  have ea := log_smooth_div 1 1 0 0 0 0 2 0
  have eb := log_smooth_div 0 0 2 0 1 3 0 0
  norm_num at ev ea eb
  have hv : Real.log (4) ≤ 1.386295 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (6/25) ≤ -1.427116 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (25/54) ≤ -0.770107 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (schurFoldNumerator_ge_tangent (p := 1/10) (q := 13/100) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 23/200)),
    sq_nonneg (x - 23/200), mul_nonneg (sq_nonneg (x - 23/200)) (sq_nonneg (x - 23/200)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem schurFoldNumerator_nonneg_three {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 13/100 ≤ x)
    (h2 : x ≤ 4/25) : 0 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 3 0 0 3 0 0 0
  have ea := log_smooth_div 0 1 0 1 2 0 2 0
  have eb := log_smooth_div 0 0 0 2 2 0 2 0
  norm_num at ev ea eb
  have hv : Real.log (27/8) ≤ 1.216396 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (21/100) ≤ -1.560647 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (49/100) ≤ -0.713349 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (schurFoldNumerator_ge_tangent (p := 13/100) (q := 4/25) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 29/200)),
    sq_nonneg (x - 29/200), mul_nonneg (sq_nonneg (x - 29/200)) (sq_nonneg (x - 29/200)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem schurFoldNumerator_nonneg_four {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 4/25 ≤ x)
    (h2 : x ≤ 9/50) : 0 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ea := log_smooth_div 1 0 0 1 0 1 2 0
  have eb := log_smooth_div 1 0 0 1 0 3 0 0
  norm_num at ea eb
  have hv : Real.log (3) ≤ 1.098613 := by linarith [l3.2]
  have ha : Real.log (14/75) ≤ -1.678430 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (14/27) ≤ -0.656779 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (schurFoldNumerator_ge_tangent (p := 4/25) (q := 9/50) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 17/100)),
    sq_nonneg (x - 17/100), mul_nonneg (sq_nonneg (x - 17/100)) (sq_nonneg (x - 17/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem schurFoldNumerator_nonneg_five {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 9/50 ≤ x)
    (h2 : x ≤ 1/5) : 0 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 1 0 0 1 0 0 1 0
  have ea := log_smooth_div 0 0 0 0 1 1 0 0
  have eb := log_smooth_div 0 3 0 0 1 0 2 0
  norm_num at ev ea eb
  have hv : Real.log (14/5) ≤ 1.029620 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (1/6) ≤ -1.791759 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (27/50) ≤ -0.616186 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (schurFoldNumerator_ge_tangent (p := 9/50) (q := 1/5) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 19/100)),
    sq_nonneg (x - 19/100), mul_nonneg (sq_nonneg (x - 19/100)) (sq_nonneg (x - 19/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem schurFoldNumerator_nonneg_six {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 1/5 ≤ x)
    (h2 : x ≤ 11/50) : 0 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 3 0 0 0 0 1 0 0
  have ea := log_smooth_div 0 0 0 1 4 1 0 0
  have eb := log_smooth_div 0 0 1 0 0 2 0 0
  norm_num at ev ea eb
  have hv : Real.log (8/3) ≤ 0.980830 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (7/48) ≤ -1.925290 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (5/9) ≤ -0.587786 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (schurFoldNumerator_ge_tangent (p := 1/5) (q := 11/50) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 21/100)),
    sq_nonneg (x - 21/100), mul_nonneg (sq_nonneg (x - 21/100)) (sq_nonneg (x - 21/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem schurFoldNumerator_nonneg_seven {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 11/50 ≤ x)
    (h2 : x ≤ 6/25) : 0 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 1 0 1 0 0 0
  have ea := log_smooth_div 0 2 0 1 2 0 3 0
  have eb := log_smooth_div 3 2 0 0 0 0 3 0
  norm_num at ev ea eb
  have hv : Real.log (5/2) ≤ 0.916291 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (63/500) ≤ -2.071473 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (72/125) ≤ -0.551647 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (schurFoldNumerator_ge_tangent (p := 11/50) (q := 6/25) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 23/100)),
    sq_nonneg (x - 23/100), mul_nonneg (sq_nonneg (x - 23/100)) (sq_nonneg (x - 23/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem schurFoldNumerator_nonneg_eight {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 6/25 ≤ x)
    (h2 : x ≤ 13/50) : 0 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 2 1 0 0 0 0 1 0
  have ea := log_smooth_div 3 0 0 0 0 1 2 0
  have eb := log_smooth_div 0 1 0 0 0 0 1 0
  norm_num at ev ea eb
  have hv : Real.log (12/5) ≤ 0.875469 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (8/75) ≤ -2.238046 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (3/5) ≤ -0.510825 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (schurFoldNumerator_ge_tangent (p := 6/25) (q := 13/50) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 1/4)),
    sq_nonneg (x - 1/4), mul_nonneg (sq_nonneg (x - 1/4)) (sq_nonneg (x - 1/4)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem schurFoldNumerator_nonneg_nine {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 13/50 ≤ x)
    (h2 : x ≤ 7/25) : 0 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 4 0 0 0 0 0 0 1
  have ea := log_smooth_div 0 1 0 0 0 0 1 1
  have eb := log_smooth_div 0 0 1 0 3 0 0 0
  norm_num at ev ea eb
  have hv : Real.log (16/7) ≤ 0.826679 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (3/35) ≤ -2.456735 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (5/8) ≤ -0.470003 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (schurFoldNumerator_ge_tangent (p := 13/50) (q := 7/25) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 27/100)),
    sq_nonneg (x - 27/100), mul_nonneg (sq_nonneg (x - 27/100)) (sq_nonneg (x - 27/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem schurFoldNumerator_nonneg_ten {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 7/25 ≤ x)
    (h2 : x ≤ 3/10) : 0 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 1 1 4 0 0 0
  have ea := log_smooth_div 0 0 0 0 0 1 1 0
  have eb := log_smooth_div 4 0 0 0 0 0 2 0
  norm_num at ev ea eb
  have hv : Real.log (35/16) ≤ 0.782760 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (1/15) ≤ -2.708050 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (16/25) ≤ -0.446287 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (schurFoldNumerator_ge_tangent (p := 7/25) (q := 3/10) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 29/100)),
    sq_nonneg (x - 29/100), mul_nonneg (sq_nonneg (x - 29/100)) (sq_nonneg (x - 29/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem schurFoldNumerator_nonneg_eleven {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 3/10 ≤ x)
    (h2 : x ≤ 63/200) : 0 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 5 0 0 0 0 1 1 0
  have ea := log_smooth_div 0 0 0 2 3 0 3 0
  have eb := log_smooth_div 0 1 0 1 5 0 0 0
  norm_num at ev ea eb
  have hv : Real.log (32/15) ≤ 0.757686 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (49/1000) ≤ -3.015934 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (21/32) ≤ -0.421213 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (schurFoldNumerator_ge_tangent (p := 3/10) (q := 63/200) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 123/400)),
    sq_nonneg (x - 123/400), mul_nonneg (sq_nonneg (x - 123/400)) (sq_nonneg (x - 123/400)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem schurFoldNumerator_nonneg_twelve {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 63/200 ≤ x)
    (h2 : x ≤ 13/40) : 0 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 2 0 2 1 0 0
  have ea := log_smooth_div 0 2 0 0 1 0 3 0
  have eb := log_smooth_div 1 0 0 0 0 1 0 0
  norm_num at ev ea eb
  have hv : Real.log (25/12) ≤ 0.733970 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (9/250) ≤ -3.324236 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (2/3) ≤ -0.405465 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (schurFoldNumerator_ge_tangent (p := 63/200) (q := 13/40) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 8/25)),
    sq_nonneg (x - 8/25), mul_nonneg (sq_nonneg (x - 8/25)) (sq_nonneg (x - 8/25)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem schurFoldNumerator_nonneg_thirteen {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 13/40 ≤ x)
    (h2 : x ≤ 333/1000) : 0 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 3 2 0 0 0 0 1 1
  have ea := log_smooth_div 0 3 0 0 3 0 3 0
  have eb := log_smooth_div 0 3 0 0 3 0 1 0
  norm_num at ev ea eb
  have hv : Real.log (72/35) ≤ 0.721319 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (27/1000) ≤ -3.611918 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (27/40) ≤ -0.393042 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (schurFoldNumerator_ge_tangent (p := 13/40) (q := 333/1000) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 329/1000)),
    sq_nonneg (x - 329/1000), mul_nonneg (sq_nonneg (x - 329/1000)) (sq_nonneg (x - 329/1000)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem schurFoldNumerator_nonneg_fourteen {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 333/1000 ≤ x)
    (h2 : x ≤ 337/1000) : 0 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 4 0 0 3 0 1 0
  have ea := log_smooth_div 0 1 0 1 3 0 3 0
  have eb := log_smooth_div 3 1 0 0 0 0 1 1
  norm_num at ev ea eb
  have hv : Real.log (81/40) ≤ 0.705570 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (21/1000) ≤ -3.863232 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (24/35) ≤ -0.377294 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (schurFoldNumerator_ge_tangent (p := 333/1000) (q := 337/1000) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 335/1000)),
    sq_nonneg (x - 335/1000), mul_nonneg (sq_nonneg (x - 335/1000)) (sq_nonneg (x - 335/1000)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem schurFoldNumerator_innerA {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 337/1000 ≤ x)
    (h2 : x ≤ 34/100) : 2 / 1000 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ea := log_smooth_div 0 0 0 1 4 0 2 0
  have eb := log_smooth_div 0 0 2 0 2 2 0 0
  norm_num at ea eb
  have hv : Real.log (2) ≤ 0.693148 := by linarith [l2b]
  have ha : Real.log (7/400) ≤ -4.045554 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (25/36) ≤ -0.364642 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (schurFoldNumerator_ge_tangent (p := 337/1000) (q := 34/100) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 3385/10000)),
    sq_nonneg (x - 3385/10000), mul_nonneg (sq_nonneg (x - 3385/10000)) (sq_nonneg (x - 3385/10000)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem schurFoldNumerator_innerB {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 34/100 ≤ x)
    (h2 : x ≤ 343/1000) : 2 / 1000 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ea := log_smooth_div 0 0 0 1 5 1 1 0
  have eb := log_smooth_div 0 0 0 1 1 0 1 0
  norm_num at ea eb
  have hv : Real.log (2) ≤ 0.693148 := by linarith [l2b]
  have ha : Real.log (7/480) ≤ -4.227875 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (7/10) ≤ -0.356674 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (schurFoldNumerator_ge_tangent (p := 34/100) (q := 343/1000) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 3415/10000)),
    sq_nonneg (x - 3415/10000), mul_nonneg (sq_nonneg (x - 3415/10000)) (sq_nonneg (x - 3415/10000)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem schurFoldNumerator_stripA {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 343/1000 ≤ x)
    (h2 : x ≤ 3465/10000) : 33 / 10000 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ea := log_smooth_div 0 2 0 0 5 0 2 0
  have eb := log_smooth_div 0 0 0 1 1 0 1 0
  norm_num at ea eb
  have hv : Real.log (2) ≤ 0.693148 := by linarith [l2b]
  have ha : Real.log (9/800) ≤ -4.487387 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (7/10) ≤ -0.356674 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (schurFoldNumerator_ge_tangent (p := 343/1000) (q := 3465/10000) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 34475/100000)),
    sq_nonneg (x - 34475/100000), mul_nonneg (sq_nonneg (x - 34475/100000)) (sq_nonneg (x - 34475/100000)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem schurFoldNumerator_stripB {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 3465/10000 ≤ x)
    (h2 : x ≤ 35/100) : 33 / 10000 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ea := log_smooth_div 0 0 0 0 7 0 0 0
  have eb := log_smooth_div 0 0 0 1 1 0 1 0
  norm_num at ea eb
  have hv : Real.log (2) ≤ 0.693148 := by linarith [l2b]
  have ha : Real.log (1/128) ≤ -4.852030 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (7/10) ≤ -0.356674 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (schurFoldNumerator_ge_tangent (p := 3465/10000) (q := 35/100) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 34825/100000)),
    sq_nonneg (x - 34825/100000), mul_nonneg (sq_nonneg (x - 34825/100000)) (sq_nonneg (x - 34825/100000)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem schurFoldNumerator_hubA {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 35/100 ≤ x)
    (h2 : x ≤ 352/1000) : 85 / 10000 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (35/100 + 356 / 1000) - Real.log (35/100) ≤ 701719 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (35/100 + 356 / 1000) / (35/100) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2727851 / 1000000 ≤ -(1 / 2) * Real.log ((7121 / 20000) ^ 2 - (35/100) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (7121 / 20000) ^ 2 - (35/100) ^ 2 by norm_num)
      (show (0 : ℝ) < 27/6250 by norm_num)
    have e := log_smooth_div 0 3 0 0 1 0 5 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := schurFoldNumerator_ge_monotone (p := 35/100) (q := 352/1000) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 351/1000)),
    sq_nonneg (x - 351/1000)]

theorem schurFoldNumerator_hubB {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 352/1000 ≤ x)
    (h2 : x ≤ 354/1000) : 85 / 10000 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (352/1000 + 356 / 1000) - Real.log (352/1000) ≤ 698830 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (352/1000 + 356 / 1000) / (352/1000) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2927134 / 1000000 ≤ -(1 / 2) * Real.log ((7121 / 20000) ^ 2 - (352/1000) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (7121 / 20000) ^ 2 - (352/1000) ^ 2 by norm_num)
      (show (0 : ℝ) < 9/3125 by norm_num)
    have e := log_smooth_div 0 2 0 0 0 0 5 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := schurFoldNumerator_ge_monotone (p := 352/1000) (q := 354/1000) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 353/1000)),
    sq_nonneg (x - 353/1000)]

theorem schurFoldNumerator_hubC {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 354/1000 ≤ x)
    (h2 : x ≤ 356/1000) : 85 / 10000 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (354/1000 + 356 / 1000) - Real.log (354/1000) ≤ 695973 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (354/1000 + 356 / 1000) / (354/1000) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 3266138 / 1000000 ≤ -(1 / 2) * Real.log ((7121 / 20000) ^ 2 - (354/1000) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (7121 / 20000) ^ 2 - (354/1000) ^ 2 by norm_num)
      (show (0 : ℝ) < 9/6250 by norm_num)
    have e := log_smooth_div 0 2 0 0 1 0 5 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := schurFoldNumerator_ge_monotone (p := 354/1000) (q := 356/1000) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 355/1000)),
    sq_nonneg (x - 355/1000)]
/-- The numerator near the origin, `0 < x ≤ 11/250`. -/
theorem schurFoldNumerator_nonneg_origin {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 0 < x)
    (h2 : x ≤ 11 / 250) : 0 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hxr : x ≤ 356 / 1000 := by linarith
  have hℓ : 207 / 100 ≤ Real.log (x + 356 / 1000) - Real.log x := by
    rw [← Real.log_div (by linarith) h1.ne']
    have h8 : Real.log 8 ≤ Real.log ((x + 356 / 1000) / x) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ h1]; linarith)
    have e8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith
  have hlam : 1032530 / 1000000 ≤
      -(1 / 2) * Real.log (7121 / 20000 - x) - 1 / 2 * Real.log (7121 / 20000 + x) := by
    have e : -(1 / 2) * Real.log (7121 / 20000 - x) - 1 / 2 * Real.log (7121 / 20000 + x) =
        -(1 / 2) * Real.log ((7121 / 20000) ^ 2 - x ^ 2) := by
      rw [show (7121 / 20000 : ℝ) ^ 2 - x ^ 2 = (7121 / 20000 - x) * (7121 / 20000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hm : Real.log ((7121 / 20000) ^ 2 - x ^ 2) ≤ Real.log ((7121 / 20000) ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have hR : Real.log ((7121 / 20000 : ℝ) ^ 2) = 2 * Real.log (7121 / 20000) := by
      rw [Real.log_pow]; norm_num
    have ht := log_le_tangent (show (0 : ℝ) < 7121 / 20000 by norm_num) (show (0 : ℝ) < 7 / 20 by norm_num)
    have e7 := log_smooth_div 0 0 0 1 2 0 1 0
    norm_num at e7 ht
    rw [e7] at ht
    linarith
  have hc : 0 ≤ 1 / 500 - x ^ 2 - 49 / 20 * x ^ 4 := by nlinarith [pow_le_pow_left₀ h1.le h2 4]
  have hp2 : (x + 356 / 1000) ^ 2 ≤ (11 / 250 + 356 / 1000) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 356 / 1000) ^ 3 ≤ (11 / 250 + 356 / 1000) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := schurFoldGauge_ge h1.le hxr
  have hA : (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (207 / 100) ≤
      (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Real.log (x + 356 / 1000) - Real.log x) :=
    mul_le_mul_of_nonneg_left hℓ hc
  have hB : quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x *
        (1032530 / 1000000 - 241517 / 100000 - 1 / 40000 - (11 / 250 + 356 / 1000) ^ 2 / 48 -
          5 * (11 / 250 + 356 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7121 / 20000) ^ 2) / 48 - 331 / 20000) ≤
      quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x *
        (-(1 / 2) * Real.log (7121 / 20000 - x) - 1 / 2 * Real.log (7121 / 20000 + x) - κ - 1 / 40000 -
          (x + 356 / 1000) ^ 2 / 48 - 5 * (x + 356 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7121 / 20000) ^ 2) / 48 - 331 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hpoly : 0 ≤ (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (207 / 100) + quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x *
        (1032530 / 1000000 - 241517 / 100000 - 1 / 40000 - (11 / 250 + 356 / 1000) ^ 2 / 48 -
          5 * (11 / 250 + 356 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7121 / 20000) ^ 2) / 48 - 331 / 20000) +
      schurFoldPoly x + firstOrderSurplus (3 / 5) (-1) (-11 / 50) (-49 / 20) (356 / 1000) x - 16 / 25 * (4 / 125 * (356 / 1000) ^ 5) := by
    unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
    nlinarith [mul_nonneg h1.le (sub_nonneg.2 h2), sq_nonneg x,
      mul_nonneg (mul_nonneg h1.le h1.le) (sub_nonneg.2 h2), pow_nonneg h1.le 3, pow_nonneg h1.le 4,
      pow_nonneg h1.le 5, pow_nonneg h1.le 6, pow_nonneg h1.le 7]
  unfold schurFoldNumerator
  linarith

/-- The numerator on a collar `[p, q] ⊆ [11/250, 7/100]`: `ℓ` between its endpoint values. -/
theorem schurFoldNumerator_ge_collar {κ x p q Llo Lhi Llam : ℝ} (hp : 11 / 250 ≤ p) (hpx : p ≤ x)
    (hxq : x ≤ q) (hq : q ≤ 7 / 100)
    (hlo : Llo ≤ Real.log (x + 356 / 1000) - Real.log x)
    (hhi : Real.log (x + 356 / 1000) - Real.log x ≤ Lhi)
    (hlam : Llam ≤ -(1 / 2) * Real.log (7121 / 20000 - x) - 1 / 2 * Real.log (7121 / 20000 + x))
    (hκ : κ ≤ 241517 / 100000) :
    1 / 500 * Llo - (x ^ 2 + 49 / 20 * x ^ 4) * Lhi +
        quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x * (Llam - 241517 / 100000 - 1 / 40000 - (q + 356 / 1000) ^ 2 / 48 -
          5 * (q + 356 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7121 / 20000) ^ 2) / 48 - 331 / 20000) +
        schurFoldPoly x + firstOrderSurplus (3 / 5) (-1) (-11 / 50) (-49 / 20) (356 / 1000) x - 16 / 25 * (4 / 125 * (356 / 1000) ^ 5) ≤
      schurFoldNumerator κ x := by
  have hx0 : 0 < x := by linarith
  have hxr : x ≤ 356 / 1000 := by linarith
  have hp2 : (x + 356 / 1000) ^ 2 ≤ (q + 356 / 1000) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 356 / 1000) ^ 3 ≤ (q + 356 / 1000) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := schurFoldGauge_ge hx0.le hxr
  have hw : 0 ≤ x ^ 2 + 49 / 20 * x ^ 4 := by positivity
  have hA : 1 / 500 * Llo - (x ^ 2 + 49 / 20 * x ^ 4) * Lhi ≤
      (1 / 500 - x ^ 2 - 49 / 20 * x ^ 4) * (Real.log (x + 356 / 1000) - Real.log x) := by
    nlinarith [mul_le_mul_of_nonneg_left hhi hw]
  have hB : quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x * (Llam - 241517 / 100000 - 1 / 40000 - (q + 356 / 1000) ^ 2 / 48 -
          5 * (q + 356 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7121 / 20000) ^ 2) / 48 - 331 / 20000) ≤
      quarticGauge (1 / 500) (3 / 5) (-1) (-11 / 50) (-49 / 20) x *
        (-(1 / 2) * Real.log (7121 / 20000 - x) - 1 / 2 * Real.log (7121 / 20000 + x) - κ - 1 / 40000 -
          (x + 356 / 1000) ^ 2 / 48 - 5 * (x + 356 / 1000) ^ 3 / 192 + (2 * x ^ 2 + (7121 / 20000) ^ 2) / 48 - 331 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold schurFoldNumerator
  linarith

/-- The window ratio `log((x + 356/1000)/x)` on a collar, from both endpoints. -/
theorem schurFoldWindowRatio_bounds {x p q : ℝ} (hp : 0 < p) (hpx : p ≤ x) (hxq : x ≤ q) :
    Real.log (q + 356 / 1000) - Real.log q ≤ Real.log (x + 356 / 1000) - Real.log x ∧
      Real.log (x + 356 / 1000) - Real.log x ≤ Real.log (p + 356 / 1000) - Real.log p := by
  have hx0 : 0 < x := by linarith
  have hq0 : 0 < q := by linarith
  rw [← Real.log_div (by linarith) hx0.ne', ← Real.log_div (by linarith) hq0.ne',
    ← Real.log_div (by linarith) hp.ne']
  constructor
  · exact Real.log_le_log (by positivity) (by rw [div_le_div_iff₀ hq0 hx0]; nlinarith)
  · exact Real.log_le_log (by positivity) (by rw [div_le_div_iff₀ hx0 hp]; nlinarith)

theorem schurFoldNumerator_nonneg_collarA {κ x : ℝ} (hκ : κ ≤ 241517 / 100000)
    (h1 : 11 / 250 ≤ x) (h2 : x ≤ 57 / 1000) : 0 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  obtain ⟨hr1, hr2⟩ := schurFoldWindowRatio_bounds (by norm_num) h1 h2
  have hlo : 1979807 / 1000000 ≤ Real.log (x + 356 / 1000) - Real.log x := by
    refine le_trans ?_ hr1
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_ge_tangent (show (0 : ℝ) < (57 / 1000 + 356 / 1000) / (57 / 1000) by norm_num)
      (show (0 : ℝ) < 7 by norm_num)
    norm_num at ht ⊢
    linarith
  have hhi : Real.log (x + 356 / 1000) - Real.log x ≤ 2207326 / 1000000 := by
    refine le_trans hr2 ?_
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (11 / 250 + 356 / 1000) / (11 / 250) by norm_num)
      (show (0 : ℝ) < 9 by norm_num)
    have e9 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
    norm_num at ht ⊢
    linarith
  have hlam : 1039983 / 1000000 ≤
      -(1 / 2) * Real.log (7121 / 20000 - x) - 1 / 2 * Real.log (7121 / 20000 + x) := by
    have e : -(1 / 2) * Real.log (7121 / 20000 - x) - 1 / 2 * Real.log (7121 / 20000 + x) =
        -(1 / 2) * Real.log ((7121 / 20000) ^ 2 - x ^ 2) := by
      rw [show (7121 / 20000 : ℝ) ^ 2 - x ^ 2 = (7121 / 20000 - x) * (7121 / 20000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hm : Real.log ((7121 / 20000) ^ 2 - x ^ 2) ≤ Real.log ((7121 / 20000) ^ 2 - (11 / 250) ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have ht := log_le_tangent (show (0 : ℝ) < (7121 / 20000) ^ 2 - (11 / 250) ^ 2 by norm_num)
      (show (0 : ℝ) < 3 / 25 by norm_num)
    have e := log_smooth_div 0 1 0 0 0 0 2 0
    norm_num at e ht
    rw [e] at ht
    linarith
  refine le_trans ?_ (schurFoldNumerator_ge_collar (p := 11 / 250) (q := 57 / 1000) le_rfl h1 h2
    (by norm_num) hlo hhi hlam hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 5 / 100)),
    sq_nonneg (x - 5 / 100)]

theorem schurFoldNumerator_nonneg_collarB {κ x : ℝ} (hκ : κ ≤ 241517 / 100000)
    (h1 : 57 / 1000 ≤ x) (h2 : x ≤ 7 / 100) : 0 ≤ schurFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  obtain ⟨hr1, hr2⟩ := schurFoldWindowRatio_bounds (by norm_num) h1 h2
  have hlo : 1805843 / 1000000 ≤ Real.log (x + 356 / 1000) - Real.log x := by
    refine le_trans ?_ hr1
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_ge_tangent (show (0 : ℝ) < (7 / 100 + 356 / 1000) / (7 / 100) by norm_num)
      (show (0 : ℝ) < 6 by norm_num)
    have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    norm_num at ht ⊢
    linarith
  have hhi : Real.log (x + 356 / 1000) - Real.log x ≤ 1980998 / 1000000 := by
    refine le_trans hr2 ?_
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (57 / 1000 + 356 / 1000) / (57 / 1000) by norm_num)
      (show (0 : ℝ) < 7 by norm_num)
    norm_num at ht ⊢
    linarith
  have hlam : 1045454 / 1000000 ≤
      -(1 / 2) * Real.log (7121 / 20000 - x) - 1 / 2 * Real.log (7121 / 20000 + x) := by
    have e : -(1 / 2) * Real.log (7121 / 20000 - x) - 1 / 2 * Real.log (7121 / 20000 + x) =
        -(1 / 2) * Real.log ((7121 / 20000) ^ 2 - x ^ 2) := by
      rw [show (7121 / 20000 : ℝ) ^ 2 - x ^ 2 = (7121 / 20000 - x) * (7121 / 20000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hm : Real.log ((7121 / 20000) ^ 2 - x ^ 2) ≤ Real.log ((7121 / 20000) ^ 2 - (57 / 1000) ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have ht := log_le_tangent (show (0 : ℝ) < (7121 / 20000) ^ 2 - (57 / 1000) ^ 2 by norm_num)
      (show (0 : ℝ) < 3 / 25 by norm_num)
    have e := log_smooth_div 0 1 0 0 0 0 2 0
    norm_num at e ht
    rw [e] at ht
    linarith
  refine le_trans ?_ (schurFoldNumerator_ge_collar (p := 57 / 1000) (q := 7 / 100) (by norm_num) h1
    h2 le_rfl hlo hhi hlam hκ)
  unfold quarticGauge schurFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 635 / 10000)),
    sq_nonneg (x - 635 / 10000)]

/-- **The numerator is nonnegative on `(0, 337/1000]`.** -/
theorem schurFoldNumerator_nonneg_inner {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (hx0 : 0 < x)
    (hxr : x ≤ 337 / 1000) : 0 ≤ schurFoldNumerator κ x := by
  rcases le_or_gt x (11 / 250) with h | h
  · exact schurFoldNumerator_nonneg_origin hκ hx0 h
  rcases le_or_gt x (57 / 1000) with h' | h'
  · exact schurFoldNumerator_nonneg_collarA hκ h.le h'
  rcases le_or_gt x (7 / 100) with h0 | h0
  · exact schurFoldNumerator_nonneg_collarB hκ h'.le h0
  rcases le_or_gt x (1 / 10) with h1 | h1
  · exact schurFoldNumerator_nonneg_one hκ h0.le h1
  rcases le_or_gt x (13 / 100) with h2 | h2
  · exact schurFoldNumerator_nonneg_two hκ h1.le h2
  rcases le_or_gt x (4 / 25) with h3 | h3
  · exact schurFoldNumerator_nonneg_three hκ h2.le h3
  rcases le_or_gt x (9 / 50) with h4 | h4
  · exact schurFoldNumerator_nonneg_four hκ h3.le h4
  rcases le_or_gt x (1 / 5) with h5 | h5
  · exact schurFoldNumerator_nonneg_five hκ h4.le h5
  rcases le_or_gt x (11 / 50) with h6 | h6
  · exact schurFoldNumerator_nonneg_six hκ h5.le h6
  rcases le_or_gt x (6 / 25) with h7 | h7
  · exact schurFoldNumerator_nonneg_seven hκ h6.le h7
  rcases le_or_gt x (13 / 50) with h8 | h8
  · exact schurFoldNumerator_nonneg_eight hκ h7.le h8
  rcases le_or_gt x (7 / 25) with h9 | h9
  · exact schurFoldNumerator_nonneg_nine hκ h8.le h9
  rcases le_or_gt x (3 / 10) with h10 | h10
  · exact schurFoldNumerator_nonneg_ten hκ h9.le h10
  rcases le_or_gt x (63 / 200) with h11 | h11
  · exact schurFoldNumerator_nonneg_eleven hκ h10.le h11
  rcases le_or_gt x (13 / 40) with h12 | h12
  · exact schurFoldNumerator_nonneg_twelve hκ h11.le h12
  rcases le_or_gt x (333 / 1000) with h13 | h13
  · exact schurFoldNumerator_nonneg_thirteen hκ h12.le h13
  · exact schurFoldNumerator_nonneg_fourteen hκ h13.le hxr

/-- **The numerator on the inner edge `[337/1000, 343/1000]`** exceeds `2/1000`. -/
theorem schurFoldNumerator_innerEdge {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 337 / 1000 ≤ x)
    (h2 : x ≤ 343 / 1000) : 2 / 1000 ≤ schurFoldNumerator κ x := by
  rcases le_or_gt x (34 / 100) with ha | ha
  · exact schurFoldNumerator_innerA hκ h1 ha
  · exact schurFoldNumerator_innerB hκ ha.le h2

/-- **The numerator on `[343/1000, 35/100]`** exceeds the strip loss `33/10000`. -/
theorem schurFoldNumerator_strip {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 343 / 1000 ≤ x)
    (h2 : x ≤ 35 / 100) : 33 / 10000 ≤ schurFoldNumerator κ x := by
  rcases le_or_gt x (3465 / 10000) with ha | ha
  · exact schurFoldNumerator_stripA hκ h1 ha
  · exact schurFoldNumerator_stripB hκ ha.le h2

/-- **The numerator on the hub `[35/100, 356/1000]`** exceeds the strip loss plus the Schur cost,
`85/10000`. -/
theorem schurFoldNumerator_hub {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 35 / 100 ≤ x)
    (h2 : x ≤ 356 / 1000) : 85 / 10000 ≤ schurFoldNumerator κ x := by
  rcases le_or_gt x (352 / 1000) with ha | ha
  · exact schurFoldNumerator_hubA hκ h1 ha
  rcases le_or_gt x (354 / 1000) with hb | hb
  · exact schurFoldNumerator_hubB hκ ha.le hb
  · exact schurFoldNumerator_hubC hκ hb.le h2

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
