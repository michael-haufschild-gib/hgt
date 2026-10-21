import GaloisForLFunctions.ArithmeticIncidencePositivity.SharpFoldOddWindowPastSevenTwentieths

/-!
# The potential numerator of the window `181/500`

For the gauge `h(y) = 1/500 + (59/100)y − (29/30)y² − (21/100)y³ − (16/7)y⁴` (the gauge of the window
`9/25` dilated by `181/180`, rounded) and the plateau of radius `R = 7241/20000` around `r = 181/500`,
the ground-state potential, the killing, the plateau potential and the second-order expansions
combine, after multiplication by `h(x)`, into the numerator `N(κ, x)` (`lendFoldNumerator`). This
module certifies:

* `N ≥ 0` on `(0, 11/250)`, on `[7/100, 7/50]` and on `[27/100, 181/500]`;
* `N ≥ 22/10000` on the origin hub `[11/250, 7/100]`, which lends potential (`lendFoldNumerator_hubA`);
* `N ≥ −38/100000` on the middle `[7/50, 27/100]`, which borrows (`lendFoldNumerator_middle`).

Every interval bound linearises the logarithms by a tangent at a `7`-smooth anchor, or uses
monotonicity of the logarithmic terms, and closes the remaining polynomial inequality.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The gauge and the numerator -/

theorem lendFoldGauge_ge {x : ℝ} (hx0 : 0 ≤ x) (hxr : x ≤ 181 / 500) :
    1 / 500 ≤ quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x := by
  unfold quarticGauge
  have h : 0 ≤ 59 / 100 - 29 / 30 * x - 21 / 100 * x ^ 2 - 16 / 7 * x ^ 3 := by
    nlinarith [pow_le_pow_left₀ hx0 hxr 3]
  nlinarith [mul_nonneg hx0 h]

theorem lendFoldGauge_divDiff_le {u v : ℝ} (hu0 : 0 ≤ u) (hur : u ≤ 181 / 500) (hv0 : 0 ≤ v)
    (hvr : v ≤ 181 / 500) :
    |59 / 100 + -29 / 30 * (u + v) + -21 / 100 * (u ^ 2 + u * v + v ^ 2) +
      -16 / 7 * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3)| ≤ 16 / 25 := by
  have h1 := mul_nonneg hu0 hv0
  have h2 : u ^ 3 ≤ (181 / 500) ^ 3 := pow_le_pow_left₀ hu0 hur 3
  have h3 : v ^ 3 ≤ (181 / 500) ^ 3 := pow_le_pow_left₀ hv0 hvr 3
  have h4 : u ^ 2 * v ≤ (181 / 500) ^ 3 := by
    nlinarith [mul_le_mul (pow_le_pow_left₀ hu0 hur 2) hvr hv0 (by positivity)]
  have h5 : u * v ^ 2 ≤ (181 / 500) ^ 3 := by
    nlinarith [mul_le_mul hur (pow_le_pow_left₀ hv0 hvr 2) (by positivity) (by norm_num)]
  have h6 : 0 ≤ u ^ 2 * v := by positivity
  have h7 : 0 ≤ u * v ^ 2 := by positivity
  have h8 : 0 ≤ u ^ 3 := by positivity
  have h9 : 0 ≤ v ^ 3 := by positivity
  rw [abs_le]; constructor <;> nlinarith

/-- The polynomial part of the principal surplus of the gauge on `[0, 181/500]`. -/
def lendFoldPoly (x : ℝ) : ℝ :=
  59 / 100 * x + -29 / 30 * (3 / 2 * x ^ 2 - 181 / 500 * x) +
    -21 / 100 * (11 / 6 * x ^ 3 - (181 / 500) ^ 2 * x / 2) +
    -16 / 7 * (25 / 12 * x ^ 4 - 181 / 500 * x ^ 3 - (181 / 500) ^ 3 * x / 3)

/-- The numerator of the potential on `[−181/500, 181/500]` (`κ` stands for `log 2 + γ + log π`). -/
def lendFoldNumerator (κ x : ℝ) : ℝ :=
  (1 / 500 - 29 / 30 * x ^ 2 - 16 / 7 * x ^ 4) * (Real.log (x + 181 / 500) - Real.log x) +
    quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x *
      (-(1 / 2) * Real.log (7241 / 20000 - x) - 1 / 2 * Real.log (7241 / 20000 + x) - κ - 1 / 40000 -
        (x + 181 / 500) ^ 2 / 48 - 5 * (x + 181 / 500) ^ 3 / 192 + (2 * x ^ 2 + (7241 / 20000) ^ 2) / 48 - 347 / 20000) +
    lendFoldPoly x + firstOrderSurplus (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) (181 / 500) x - 16 / 25 * (4 / 125 * (181 / 500) ^ 5)

/-- **Tangent form of the numerator** on `[p, q] ⊆ [7/100, 181/500]`. -/
theorem lendFoldNumerator_ge_tangent {κ x p q v a b Lv La Lb : ℝ} (hp : 7 / 100 ≤ p)
    (hpx : p ≤ x) (hxq : x ≤ q) (hq : q ≤ 181 / 500) (hv : 0 < v) (ha : 0 < a) (hb : 0 < b)
    (hLv : Real.log v ≤ Lv) (hLa : Real.log a ≤ La) (hLb : Real.log b ≤ Lb)
    (hκ : κ ≤ 241517 / 100000) :
    (1 / 500 - 29 / 30 * x ^ 2 - 16 / 7 * x ^ 4) * (Lv + 1 / v - 1) +
        181 / 500 / v * (1 / (500 * q) - 29 / 30 * x - 16 / 7 * x ^ 3) +
        quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x *
          (-(1 / 2) * (La + (7241 / 20000 - x) / a - 1) - 1 / 2 * (Lb + (7241 / 20000 + x) / b - 1) -
            241517 / 100000 - 1 / 40000 - (q + 181 / 500) ^ 2 / 48 -
            5 * (q + 181 / 500) ^ 3 / 192 + (2 * x ^ 2 + (7241 / 20000) ^ 2) / 48 - 347 / 20000) +
        lendFoldPoly x + firstOrderSurplus (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) (181 / 500) x - 16 / 25 * (4 / 125 * (181 / 500) ^ 5) ≤
      lendFoldNumerator κ x := by
  have hx0 : 0 < x := by linarith
  have hxr : x ≤ 181 / 500 := le_trans hxq hq
  have hℓ : Real.log (x + 181 / 500) - Real.log x ≤ Lv + (1 + 181 / 500 / x) / v - 1 := by
    rw [← Real.log_div (by linarith) hx0.ne']
    have e : (x + 181 / 500) / x = 1 + 181 / 500 / x := by field_simp
    rw [e]
    have := log_le_tangent (show 0 < 1 + 181 / 500 / x by positivity) hv
    linarith
  have hc : 1 / 500 - 29 / 30 * x ^ 2 - 16 / 7 * x ^ 4 ≤ 0 := by nlinarith [pow_nonneg hx0.le 4]
  have h1 : (1 / 500 - 29 / 30 * x ^ 2 - 16 / 7 * x ^ 4) * (Lv + (1 + 181 / 500 / x) / v - 1) ≤
      (1 / 500 - 29 / 30 * x ^ 2 - 16 / 7 * x ^ 4) * (Real.log (x + 181 / 500) - Real.log x) :=
    mul_le_mul_of_nonpos_left hℓ hc
  have h1' : (1 / 500 - 29 / 30 * x ^ 2 - 16 / 7 * x ^ 4) * (Lv + 1 / v - 1) +
      181 / 500 / v * (1 / (500 * q) - 29 / 30 * x - 16 / 7 * x ^ 3) ≤
      (1 / 500 - 29 / 30 * x ^ 2 - 16 / 7 * x ^ 4) * (Lv + (1 + 181 / 500 / x) / v - 1) := by
    have e : (1 / 500 - 29 / 30 * x ^ 2 - 16 / 7 * x ^ 4) * (Lv + (1 + 181 / 500 / x) / v - 1) =
        (1 / 500 - 29 / 30 * x ^ 2 - 16 / 7 * x ^ 4) * (Lv + 1 / v - 1) +
          181 / 500 / v * (1 / (500 * x) - 29 / 30 * x - 16 / 7 * x ^ 3) := by
      field_simp; ring
    rw [e]
    have hqx : 1 / (500 * q) ≤ 1 / (500 * x) := one_div_le_one_div_of_le (by positivity) (by linarith)
    have hv' : 0 ≤ 181 / 500 / v := by positivity
    nlinarith
  have hla : -(1 / 2) * (La + (7241 / 20000 - x) / a - 1) ≤ -(1 / 2) * Real.log (7241 / 20000 - x) := by
    have := log_le_tangent (show (0 : ℝ) < 7241 / 20000 - x by linarith) ha
    linarith
  have hlb : -(1 / 2) * (Lb + (7241 / 20000 + x) / b - 1) ≤ -(1 / 2) * Real.log (7241 / 20000 + x) := by
    have := log_le_tangent (show (0 : ℝ) < 7241 / 20000 + x by linarith) hb
    linarith
  have hp2 : (x + 181 / 500) ^ 2 ≤ (q + 181 / 500) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 181 / 500) ^ 3 ≤ (q + 181 / 500) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := lendFoldGauge_ge hx0.le hxr
  have h2 : quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x *
        (-(1 / 2) * (La + (7241 / 20000 - x) / a - 1) - 1 / 2 * (Lb + (7241 / 20000 + x) / b - 1) -
          241517 / 100000 - 1 / 40000 - (q + 181 / 500) ^ 2 / 48 -
          5 * (q + 181 / 500) ^ 3 / 192 + (2 * x ^ 2 + (7241 / 20000) ^ 2) / 48 - 347 / 20000) ≤
      quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x *
        (-(1 / 2) * Real.log (7241 / 20000 - x) - 1 / 2 * Real.log (7241 / 20000 + x) - κ - 1 / 40000 -
          (x + 181 / 500) ^ 2 / 48 - 5 * (x + 181 / 500) ^ 3 / 192 + (2 * x ^ 2 + (7241 / 20000) ^ 2) / 48 - 347 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold lendFoldNumerator
  linarith

/-- **Monotone form of the numerator** on `[p, q] ⊆ [7/100, 181/500]`. -/
theorem lendFoldNumerator_ge_monotone {κ x p q Lℓ Llam : ℝ} (hp : 7 / 100 ≤ p) (hpx : p ≤ x)
    (hxq : x ≤ q) (hq : q ≤ 181 / 500)
    (hLℓ : Real.log (p + 181 / 500) - Real.log p ≤ Lℓ)
    (hLlam : Llam ≤ -(1 / 2) * Real.log ((7241 / 20000) ^ 2 - p ^ 2)) (hκ : κ ≤ 241517 / 100000) :
    (1 / 500 - 29 / 30 * x ^ 2 - 16 / 7 * x ^ 4) * Lℓ +
        quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x *
          (Llam - 241517 / 100000 - 1 / 40000 - (q + 181 / 500) ^ 2 / 48 -
            5 * (q + 181 / 500) ^ 3 / 192 + (2 * x ^ 2 + (7241 / 20000) ^ 2) / 48 - 347 / 20000) +
        lendFoldPoly x + firstOrderSurplus (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) (181 / 500) x - 16 / 25 * (4 / 125 * (181 / 500) ^ 5) ≤
      lendFoldNumerator κ x := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 < x := by linarith
  have hxr : x ≤ 181 / 500 := le_trans hxq hq
  have hℓ : Real.log (x + 181 / 500) - Real.log x ≤ Lℓ := by
    rw [← Real.log_div (by linarith) hx0.ne']
    rw [← Real.log_div (by linarith) hp0.ne'] at hLℓ
    refine le_trans (Real.log_le_log (by positivity) ?_) hLℓ
    rw [div_le_div_iff₀ hx0 hp0]; nlinarith
  have hc : 1 / 500 - 29 / 30 * x ^ 2 - 16 / 7 * x ^ 4 ≤ 0 := by nlinarith [pow_nonneg hx0.le 4]
  have h1 := mul_le_mul_of_nonpos_left hℓ hc
  have hlam : Llam ≤ -(1 / 2) * Real.log (7241 / 20000 - x) - 1 / 2 * Real.log (7241 / 20000 + x) := by
    have e : -(1 / 2) * Real.log (7241 / 20000 - x) - 1 / 2 * Real.log (7241 / 20000 + x) =
        -(1 / 2) * Real.log ((7241 / 20000) ^ 2 - x ^ 2) := by
      rw [show (7241 / 20000 : ℝ) ^ 2 - x ^ 2 = (7241 / 20000 - x) * (7241 / 20000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hmono : Real.log ((7241 / 20000) ^ 2 - x ^ 2) ≤ Real.log ((7241 / 20000) ^ 2 - p ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    linarith
  have hp2 : (x + 181 / 500) ^ 2 ≤ (q + 181 / 500) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 181 / 500) ^ 3 ≤ (q + 181 / 500) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := lendFoldGauge_ge hx0.le hxr
  have h2 : quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x *
        (Llam - 241517 / 100000 - 1 / 40000 - (q + 181 / 500) ^ 2 / 48 -
          5 * (q + 181 / 500) ^ 3 / 192 + (2 * x ^ 2 + (7241 / 20000) ^ 2) / 48 - 347 / 20000) ≤
      quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x *
        (-(1 / 2) * Real.log (7241 / 20000 - x) - 1 / 2 * Real.log (7241 / 20000 + x) - κ - 1 / 40000 -
          (x + 181 / 500) ^ 2 / 48 - 5 * (x + 181 / 500) ^ 3 / 192 + (2 * x ^ 2 + (7241 / 20000) ^ 2) / 48 - 347 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold lendFoldNumerator
  nlinarith

theorem lendFoldNumerator_nonneg_one {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 7/100 ≤ x)
    (h2 : x ≤ 1/10) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 1 0 1 2 0 0 0
  have ea := log_smooth_div 0 0 1 0 1 2 0 0
  have eb := log_smooth_div 2 0 0 0 0 2 0 0
  norm_num at ev ea eb
  have hv : Real.log (21/4) ≤ 1.658229 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (5/18) ≤ -1.280933 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (4/9) ≤ -0.810930 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 7/100) (q := 1/10) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 17/200)),
    sq_nonneg (x - 17/200), mul_nonneg (sq_nonneg (x - 17/200)) (sq_nonneg (x - 17/200)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_two {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 1/10 ≤ x)
    (h2 : x ≤ 3/25) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 1 1 1 0 0 0 0 1
  have ea := log_smooth_div 0 0 0 0 2 0 0 0
  have eb := log_smooth_div 0 3 0 1 4 0 2 0
  norm_num at ev ea eb
  have hv : Real.log (30/7) ≤ 1.455288 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (1/4) ≤ -1.386294 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (189/400) ≤ -0.749717 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 1/10) (q := 3/25) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 11/100)),
    sq_nonneg (x - 11/100), mul_nonneg (sq_nonneg (x - 11/100)) (sq_nonneg (x - 11/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_three {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 3/25 ≤ x)
    (h2 : x ≤ 7/50) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 3 0 1 1 0 2 0
  have ea := log_smooth_div 0 0 0 1 1 1 1 0
  have eb := log_smooth_div 3 0 1 0 0 4 0 0
  norm_num at ev ea eb
  have hv : Real.log (189/50) ≤ 1.329725 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (7/30) ≤ -1.455287 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (40/81) ≤ -0.705569 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 3/25) (q := 7/50) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 13/100)),
    sq_nonneg (x - 13/100), mul_nonneg (sq_nonneg (x - 13/100)) (sq_nonneg (x - 13/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_four {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 7/50 ≤ x)
    (h2 : x ≤ 31/200) : -38 / 100000 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 4 3 0 0 0 0 3 0
  have ea := log_smooth_div 0 1 0 0 1 0 0 1
  have eb := log_smooth_div 6 0 0 0 0 0 3 0
  norm_num at ev ea eb
  have hv : Real.log (432/125) ≤ 1.240112 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (3/14) ≤ -1.540444 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (64/125) ≤ -0.669430 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 7/50) (q := 31/200) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 59/400)),
    sq_nonneg (x - 59/400), mul_nonneg (sq_nonneg (x - 59/400)) (sq_nonneg (x - 59/400)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_five {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 31/200 ≤ x)
    (h2 : x ≤ 17/100) : -38 / 100000 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 4 0 0 0 0 2 0
  have ea := log_smooth_div 0 0 0 0 0 0 1 0
  have eb := log_smooth_div 0 1 0 1 3 0 1 0
  norm_num at ev ea eb
  have hv : Real.log (81/25) ≤ 1.175574 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (1/5) ≤ -1.609437 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (21/40) ≤ -0.644356 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 31/200) (q := 17/100) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 13/80)),
    sq_nonneg (x - 13/80), mul_nonneg (sq_nonneg (x - 13/80)) (sq_nonneg (x - 13/80)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_six {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 17/100 ≤ x)
    (h2 : x ≤ 9/50) : -38 / 100000 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 0 2 4 0 0 0
  have ea := log_smooth_div 0 1 0 0 4 0 0 0
  have eb := log_smooth_div 3 0 0 0 0 1 1 0
  norm_num at ev ea eb
  have hv : Real.log (49/16) ≤ 1.119232 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (3/16) ≤ -1.673976 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (8/15) ≤ -0.628608 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 17/100) (q := 9/50) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 7/40)),
    sq_nonneg (x - 7/40), mul_nonneg (sq_nonneg (x - 7/40)) (sq_nonneg (x - 7/40)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_seven {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 9/50 ≤ x)
    (h2 : x ≤ 19/100) : -38 / 100000 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 1 0 2 1 0 2 0
  have ea := log_smooth_div 3 0 0 0 0 2 1 0
  have eb := log_smooth_div 0 0 1 1 6 0 0 0
  norm_num at ev ea eb
  have hv : Real.log (147/50) ≤ 1.078410 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (8/45) ≤ -1.727220 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (35/64) ≤ -0.603534 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 9/50) (q := 19/100) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 37/200)),
    sq_nonneg (x - 37/200), mul_nonneg (sq_nonneg (x - 37/200)) (sq_nonneg (x - 37/200)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_eight {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 19/100 ≤ x)
    (h2 : x ≤ 1/5) : -38 / 100000 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 2 0 1 0 0 0 0 1
  have ea := log_smooth_div 0 0 0 0 1 1 0 0
  have eb := log_smooth_div 0 0 1 0 0 2 0 0
  norm_num at ev ea eb
  have hv : Real.log (20/7) ≤ 1.049823 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (1/6) ≤ -1.791759 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (5/9) ≤ -0.587786 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 19/100) (q := 1/5) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 39/200)),
    sq_nonneg (x - 39/200), mul_nonneg (sq_nonneg (x - 39/200)) (sq_nonneg (x - 39/200)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_nine {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 1/5 ≤ x)
    (h2 : x ≤ 21/100) : -38 / 100000 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 2 0 2 5 0 1 0
  have ea := log_smooth_div 0 0 1 0 5 0 0 0
  have eb := log_smooth_div 0 2 0 0 4 0 0 0
  norm_num at ev ea eb
  have hv : Real.log (441/160) ≤ 1.013872 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (5/32) ≤ -1.856297 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (9/16) ≤ -0.575364 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 1/5) (q := 21/100) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 41/200)),
    sq_nonneg (x - 41/200), mul_nonneg (sq_nonneg (x - 41/200)) (sq_nonneg (x - 41/200)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_ten {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 21/100 ≤ x)
    (h2 : x ≤ 11/50) : -38 / 100000 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 1 2 0 2 0 0 1
  have ea := log_smooth_div 0 0 0 1 4 1 0 0
  have eb := log_smooth_div 3 2 0 0 0 0 3 0
  norm_num at ev ea eb
  have hv : Real.log (75/28) ≤ 0.985284 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (7/48) ≤ -1.925290 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (72/125) ≤ -0.551647 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 21/100) (q := 11/50) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 43/200)),
    sq_nonneg (x - 43/200), mul_nonneg (sq_nonneg (x - 43/200)) (sq_nonneg (x - 43/200)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_eleven {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 11/50 ≤ x)
    (h2 : x ≤ 23/100) : -38 / 100000 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 3 0 4 1 0 0
  have ea := log_smooth_div 3 1 0 0 0 0 2 1
  have eb := log_smooth_div 0 0 0 1 2 1 0 0
  norm_num at ev ea eb
  have hv : Real.log (125/48) ≤ 0.957114 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (24/175) ≤ -1.986732 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (7/12) ≤ -0.538996 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 11/50) (q := 23/100) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 9/40)),
    sq_nonneg (x - 9/40), mul_nonneg (sq_nonneg (x - 9/40)) (sq_nonneg (x - 9/40)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_twelve {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 23/100 ≤ x)
    (h2 : x ≤ 6/25) : -38 / 100000 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 4 0 0 5 0 0 0
  have ea := log_smooth_div 4 0 0 0 0 0 3 0
  have eb := log_smooth_div 0 1 0 0 0 0 1 0
  norm_num at ev ea eb
  have hv : Real.log (81/32) ≤ 0.928714 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (16/125) ≤ -2.055724 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (3/5) ≤ -0.510825 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 23/100) (q := 6/25) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 47/200)),
    sq_nonneg (x - 47/200), mul_nonneg (sq_nonneg (x - 47/200)) (sq_nonneg (x - 47/200)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_thirteen {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 6/25 ≤ x)
    (h2 : x ≤ 51/200) : -38 / 100000 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 0 2 2 0 1 0
  have ea := log_smooth_div 2 0 0 0 0 0 1 1
  have eb := log_smooth_div 0 5 0 0 4 0 2 0
  norm_num at ev ea eb
  have hv : Real.log (49/20) ≤ 0.896089 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (4/35) ≤ -2.169053 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (243/400) ≤ -0.498403 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 6/25) (q := 51/200) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 99/400)),
    sq_nonneg (x - 99/400), mul_nonneg (sq_nonneg (x - 99/400)) (sq_nonneg (x - 99/400)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_fourteen {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 51/200 ≤ x)
    (h2 : x ≤ 27/100) : -38 / 100000 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 6 0 0 0 0 3 0 0
  have ea := log_smooth_div 0 0 0 0 1 0 1 0
  have eb := log_smooth_div 0 0 1 0 3 0 0 0
  norm_num at ev ea eb
  have hv : Real.log (64/27) ≤ 0.863047 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (1/10) ≤ -2.302585 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (5/8) ≤ -0.470003 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 51/200) (q := 27/100) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 21/80)),
    sq_nonneg (x - 21/80), mul_nonneg (sq_nonneg (x - 21/80)) (sq_nonneg (x - 21/80)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_fifteen {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 27/100 ≤ x)
    (h2 : x ≤ 57/200) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 5 2 0 0 0 0 3 0
  have ea := log_smooth_div 0 3 0 0 6 0 1 0
  have eb := log_smooth_div 4 0 0 0 0 0 2 0
  norm_num at ev ea eb
  have hv : Real.log (288/125) ≤ 0.834647 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (27/320) ≤ -2.472484 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (16/25) ≤ -0.446287 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 27/100) (q := 57/200) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 111/400)),
    sq_nonneg (x - 111/400), mul_nonneg (sq_nonneg (x - 111/400)) (sq_nonneg (x - 111/400)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_sixteen {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 57/200 ≤ x)
    (h2 : x ≤ 3/10) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 3 0 3 0 0 1
  have ea := log_smooth_div 0 0 1 0 3 2 0 0
  have eb := log_smooth_div 5 0 0 0 0 0 0 2
  norm_num at ev ea eb
  have hv : Real.log (125/56) ≤ 0.802963 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (5/72) ≤ -2.667227 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (32/49) ≤ -0.426084 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 57/200) (q := 3/10) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 117/400)),
    sq_nonneg (x - 117/400), mul_nonneg (sq_nonneg (x - 117/400)) (sq_nonneg (x - 117/400)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_seventeenA {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 3/10 ≤ x)
    (h2 : x ≤ 123/400) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 1 1 4 0 0 0
  have ea := log_smooth_div 0 0 0 1 3 1 1 0
  have eb := log_smooth_div 1 0 0 0 0 1 0 0
  norm_num at ev ea eb
  have hv : Real.log (35/16) ≤ 0.782760 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (7/120) ≤ -2.841581 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (2/3) ≤ -0.405465 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 3/10) (q := 123/400) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 243/800)),
    sq_nonneg (x - 243/800), mul_nonneg (sq_nonneg (x - 243/800)) (sq_nonneg (x - 243/800)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_seventeenB {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 123/400 ≤ x)
    (h2 : x ≤ 63/200) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 1 3 0 0 0 0 2 0
  have ea := log_smooth_div 0 4 0 0 6 0 2 0
  have eb := log_smooth_div 0 3 0 0 3 0 1 0
  norm_num at ev ea eb
  have hv : Real.log (54/25) ≤ 0.770109 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (81/1600) ≤ -2.983309 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (27/40) ≤ -0.393042 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 123/400) (q := 63/200) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 249/800)),
    sq_nonneg (x - 249/800), mul_nonneg (sq_nonneg (x - 249/800)) (sq_nonneg (x - 249/800)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_eighteen {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 63/200 ≤ x)
    (h2 : x ≤ 13/40) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 5 0 0 0 0 1 1 0
  have ea := log_smooth_div 0 1 0 1 2 0 3 0
  have eb := log_smooth_div 0 0 0 2 3 2 0 0
  norm_num at ev ea eb
  have hv : Real.log (32/15) ≤ 0.757686 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (21/500) ≤ -3.170085 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (49/72) ≤ -0.384845 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 63/200) (q := 13/40) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 8/25)),
    sq_nonneg (x - 8/25), mul_nonneg (sq_nonneg (x - 8/25)) (sq_nonneg (x - 8/25)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_nineteen {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 13/40 ≤ x)
    (h2 : x ≤ 333/1000) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 1 0 1 1 0 1 0
  have ea := log_smooth_div 0 0 0 0 1 1 1 0
  have eb := log_smooth_div 0 0 2 0 2 2 0 0
  norm_num at ev ea eb
  have hv : Real.log (21/10) ≤ 0.741938 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (1/30) ≤ -3.401197 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (25/36) ≤ -0.364642 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 13/40) (q := 333/1000) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 329/1000)),
    sq_nonneg (x - 329/1000), mul_nonneg (sq_nonneg (x - 329/1000)) (sq_nonneg (x - 329/1000)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_twenty {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 333/1000 ≤ x)
    (h2 : x ≤ 169/500) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 4 4 0 0 0 0 4 0
  have ea := log_smooth_div 1 0 0 0 0 1 2 0
  have eb := log_smooth_div 0 0 0 1 1 0 1 0
  norm_num at ev ea eb
  have hv : Real.log (1296/625) ≤ 0.729287 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (2/75) ≤ -3.624340 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (7/10) ≤ -0.356674 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 333/1000) (q := 169/500) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 671/2000)),
    sq_nonneg (x - 671/2000), mul_nonneg (sq_nonneg (x - 671/2000)) (sq_nonneg (x - 671/2000)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_twentyOne {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 169/500 ≤ x)
    (h2 : x ≤ 171/500) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 2 0 3 0 0 5 0 0
  have ea := log_smooth_div 0 0 0 0 0 2 1 0
  have eb := log_smooth_div 0 0 0 1 1 0 1 0
  norm_num at ev ea eb
  have hv : Real.log (500/243) ≤ 0.721548 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (1/45) ≤ -3.806662 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (7/10) ≤ -0.356674 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 169/500) (q := 171/500) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 17/50)),
    sq_nonneg (x - 17/50), mul_nonneg (sq_nonneg (x - 17/50)) (sq_nonneg (x - 17/50)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_twentyTwo {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 171/500 ≤ x)
    (h2 : x ≤ 173/500) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 8 0 0 0 0 0 3 0
  have ea := log_smooth_div 0 2 0 0 2 0 3 0
  have eb := log_smooth_div 5 0 0 0 0 2 1 0
  norm_num at ev ea eb
  have hv : Real.log (256/125) ≤ 0.716864 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (9/500) ≤ -4.017383 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (32/45) ≤ -0.340926 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 171/500) (q := 173/500) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 43/125)),
    sq_nonneg (x - 43/125), mul_nonneg (sq_nonneg (x - 43/125)) (sq_nonneg (x - 43/125)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_twentyThree {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 173/500 ≤ x)
    (h2 : x ≤ 7/20) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 2 0 2 0 0 0 0 2
  have ea := log_smooth_div 0 0 0 1 2 0 3 0
  have eb := log_smooth_div 5 0 0 0 0 2 1 0
  norm_num at ev ea eb
  have hv : Real.log (100/49) ≤ 0.713351 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (7/500) ≤ -4.268697 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (32/45) ≤ -0.340926 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 173/500) (q := 7/20) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 87/250)),
    sq_nonneg (x - 87/250), mul_nonneg (sq_nonneg (x - 87/250)) (sq_nonneg (x - 87/250)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_twentyFour {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 7/20 ≤ x)
    (h2 : x ≤ 353/1000) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 4 0 0 3 0 1 0
  have ea := log_smooth_div 0 1 0 1 4 0 3 0
  have eb := log_smooth_div 5 0 0 0 0 2 1 0
  norm_num at ev ea eb
  have hv : Real.log (81/40) ≤ 0.705570 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (21/2000) ≤ -4.556379 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (32/45) ≤ -0.340926 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 7/20) (q := 353/1000) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 703/2000)),
    sq_nonneg (x - 703/2000), mul_nonneg (sq_nonneg (x - 703/2000)) (sq_nonneg (x - 703/2000)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_nonneg_twentyFive {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 353/1000 ≤ x)
    (h2 : x ≤ 89/250) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 4 0 0 3 0 1 0
  have ea := log_smooth_div 0 1 0 0 4 0 2 0
  have eb := log_smooth_div 5 0 0 0 0 2 1 0
  norm_num at ev ea eb
  have hv : Real.log (81/40) ≤ 0.705570 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (3/400) ≤ -4.892852 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (32/45) ≤ -0.340926 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (lendFoldNumerator_ge_tangent (p := 353/1000) (q := 89/250) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 709/2000)),
    sq_nonneg (x - 709/2000), mul_nonneg (sq_nonneg (x - 709/2000)) (sq_nonneg (x - 709/2000)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem lendFoldNumerator_edgeA {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 89/250 ≤ x)
    (h2 : x ≤ 179/500) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (89/250 + 181 / 500) - Real.log (89/250) ≤ 701575 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (89/250 + 181 / 500) / (89/250) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2719448 / 1000000 ≤ -(1 / 2) * Real.log ((7241 / 20000) ^ 2 - (89/250) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (7241 / 20000) ^ 2 - (89/250) ^ 2 by norm_num)
      (show (0 : ℝ) < 27/6250 by norm_num)
    have e := log_smooth_div 0 3 0 0 1 0 5 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := lendFoldNumerator_ge_monotone (p := 89/250) (q := 179/500) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 357/1000)),
    sq_nonneg (x - 357/1000)]

theorem lendFoldNumerator_edgeB {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 179/500 ≤ x)
    (h2 : x ≤ 9/25) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (179/500 + 181 / 500) - Real.log (179/500) ≤ 698734 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (179/500 + 181 / 500) / (179/500) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2918697 / 1000000 ≤ -(1 / 2) * Real.log ((7241 / 20000) ^ 2 - (179/500) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (7241 / 20000) ^ 2 - (179/500) ^ 2 by norm_num)
      (show (0 : ℝ) < 9/3125 by norm_num)
    have e := log_smooth_div 0 2 0 0 0 0 5 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := lendFoldNumerator_ge_monotone (p := 179/500) (q := 9/25) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 359/1000)),
    sq_nonneg (x - 359/1000)]

theorem lendFoldNumerator_edgeC {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 9/25 ≤ x)
    (h2 : x ≤ 181/500) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (9/25 + 181 / 500) - Real.log (9/25) ≤ 695925 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (9/25 + 181 / 500) / (9/25) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 3257776 / 1000000 ≤ -(1 / 2) * Real.log ((7241 / 20000) ^ 2 - (9/25) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (7241 / 20000) ^ 2 - (9/25) ^ 2 by norm_num)
      (show (0 : ℝ) < 147/100000 by norm_num)
    have e := log_smooth_div 0 1 0 2 5 0 5 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := lendFoldNumerator_ge_monotone (p := 9/25) (q := 181/500) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  refine le_trans ?_ hmono
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 361/1000)),
    sq_nonneg (x - 361/1000)]
/-- The numerator near the origin, `0 < x ≤ 11/250`. -/
theorem lendFoldNumerator_nonneg_origin {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 0 < x)
    (h2 : x ≤ 11 / 250) : 0 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hxr : x ≤ 181 / 500 := by linarith
  have hℓ : 207 / 100 ≤ Real.log (x + 181 / 500) - Real.log x := by
    rw [← Real.log_div (by linarith) h1.ne']
    have h8 : Real.log 8 ≤ Real.log ((x + 181 / 500) / x) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ h1]; linarith)
    have e8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith
  have hlam : 1015956 / 1000000 ≤
      -(1 / 2) * Real.log (7241 / 20000 - x) - 1 / 2 * Real.log (7241 / 20000 + x) := by
    have e : -(1 / 2) * Real.log (7241 / 20000 - x) - 1 / 2 * Real.log (7241 / 20000 + x) =
        -(1 / 2) * Real.log ((7241 / 20000) ^ 2 - x ^ 2) := by
      rw [show (7241 / 20000 : ℝ) ^ 2 - x ^ 2 = (7241 / 20000 - x) * (7241 / 20000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hm : Real.log ((7241 / 20000) ^ 2 - x ^ 2) ≤ Real.log ((7241 / 20000) ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have hR : Real.log ((7241 / 20000 : ℝ) ^ 2) = 2 * Real.log (7241 / 20000) := by
      rw [Real.log_pow]; norm_num
    have ht := log_le_tangent (show (0 : ℝ) < 7241 / 20000 by norm_num) (show (0 : ℝ) < 36 / 100 by norm_num)
    have e7 := log_smooth_div 0 2 0 0 0 0 2 0
    norm_num at e7 ht
    rw [e7] at ht
    linarith
  have hc : 0 ≤ 1 / 500 - 29 / 30 * x ^ 2 - 16 / 7 * x ^ 4 := by nlinarith [pow_le_pow_left₀ h1.le h2 4]
  have hp2 : (x + 181 / 500) ^ 2 ≤ (11 / 250 + 181 / 500) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 181 / 500) ^ 3 ≤ (11 / 250 + 181 / 500) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := lendFoldGauge_ge h1.le hxr
  have hA : (1 / 500 - 29 / 30 * x ^ 2 - 16 / 7 * x ^ 4) * (207 / 100) ≤
      (1 / 500 - 29 / 30 * x ^ 2 - 16 / 7 * x ^ 4) * (Real.log (x + 181 / 500) - Real.log x) :=
    mul_le_mul_of_nonneg_left hℓ hc
  have hB : quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x *
        (1015956 / 1000000 - 241517 / 100000 - 1 / 40000 - (11 / 250 + 181 / 500) ^ 2 / 48 -
          5 * (11 / 250 + 181 / 500) ^ 3 / 192 + (2 * x ^ 2 + (7241 / 20000) ^ 2) / 48 - 347 / 20000) ≤
      quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x *
        (-(1 / 2) * Real.log (7241 / 20000 - x) - 1 / 2 * Real.log (7241 / 20000 + x) - κ - 1 / 40000 -
          (x + 181 / 500) ^ 2 / 48 - 5 * (x + 181 / 500) ^ 3 / 192 + (2 * x ^ 2 + (7241 / 20000) ^ 2) / 48 - 347 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hpoly : 0 ≤ (1 / 500 - 29 / 30 * x ^ 2 - 16 / 7 * x ^ 4) * (207 / 100) + quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x *
        (1015956 / 1000000 - 241517 / 100000 - 1 / 40000 - (11 / 250 + 181 / 500) ^ 2 / 48 -
          5 * (11 / 250 + 181 / 500) ^ 3 / 192 + (2 * x ^ 2 + (7241 / 20000) ^ 2) / 48 - 347 / 20000) +
      lendFoldPoly x + firstOrderSurplus (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) (181 / 500) x - 16 / 25 * (4 / 125 * (181 / 500) ^ 5) := by
    unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
    nlinarith [mul_nonneg h1.le (sub_nonneg.2 h2), sq_nonneg x,
      mul_nonneg (mul_nonneg h1.le h1.le) (sub_nonneg.2 h2), pow_nonneg h1.le 3, pow_nonneg h1.le 4,
      pow_nonneg h1.le 5, pow_nonneg h1.le 6, pow_nonneg h1.le 7]
  unfold lendFoldNumerator
  linarith

/-- The numerator on a collar `[p, q] ⊆ [11/250, 7/100]`: `ℓ` between its endpoint values. -/
theorem lendFoldNumerator_ge_collar {κ x p q Llo Lhi Llam : ℝ} (hp : 11 / 250 ≤ p) (hpx : p ≤ x)
    (hxq : x ≤ q) (hq : q ≤ 7 / 100)
    (hlo : Llo ≤ Real.log (x + 181 / 500) - Real.log x)
    (hhi : Real.log (x + 181 / 500) - Real.log x ≤ Lhi)
    (hlam : Llam ≤ -(1 / 2) * Real.log (7241 / 20000 - x) - 1 / 2 * Real.log (7241 / 20000 + x))
    (hκ : κ ≤ 241517 / 100000) :
    1 / 500 * Llo - (29 / 30 * x ^ 2 + 16 / 7 * x ^ 4) * Lhi +
        quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x * (Llam - 241517 / 100000 - 1 / 40000 - (q + 181 / 500) ^ 2 / 48 -
          5 * (q + 181 / 500) ^ 3 / 192 + (2 * x ^ 2 + (7241 / 20000) ^ 2) / 48 - 347 / 20000) +
        lendFoldPoly x + firstOrderSurplus (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) (181 / 500) x - 16 / 25 * (4 / 125 * (181 / 500) ^ 5) ≤
      lendFoldNumerator κ x := by
  have hx0 : 0 < x := by linarith
  have hxr : x ≤ 181 / 500 := by linarith
  have hp2 : (x + 181 / 500) ^ 2 ≤ (q + 181 / 500) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 181 / 500) ^ 3 ≤ (q + 181 / 500) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := lendFoldGauge_ge hx0.le hxr
  have hw : 0 ≤ 29 / 30 * x ^ 2 + 16 / 7 * x ^ 4 := by positivity
  have hA : 1 / 500 * Llo - (29 / 30 * x ^ 2 + 16 / 7 * x ^ 4) * Lhi ≤
      (1 / 500 - 29 / 30 * x ^ 2 - 16 / 7 * x ^ 4) * (Real.log (x + 181 / 500) - Real.log x) := by
    nlinarith [mul_le_mul_of_nonneg_left hhi hw]
  have hB : quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x * (Llam - 241517 / 100000 - 1 / 40000 - (q + 181 / 500) ^ 2 / 48 -
          5 * (q + 181 / 500) ^ 3 / 192 + (2 * x ^ 2 + (7241 / 20000) ^ 2) / 48 - 347 / 20000) ≤
      quarticGauge (1 / 500) (59 / 100) (-29 / 30) (-21 / 100) (-16 / 7) x *
        (-(1 / 2) * Real.log (7241 / 20000 - x) - 1 / 2 * Real.log (7241 / 20000 + x) - κ - 1 / 40000 -
          (x + 181 / 500) ^ 2 / 48 - 5 * (x + 181 / 500) ^ 3 / 192 + (2 * x ^ 2 + (7241 / 20000) ^ 2) / 48 - 347 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold lendFoldNumerator
  linarith

/-- The window ratio `log((x + 181/500)/x)` on a collar, from both endpoints. -/
theorem lendFoldWindowRatio_bounds {x p q : ℝ} (hp : 0 < p) (hpx : p ≤ x) (hxq : x ≤ q) :
    Real.log (q + 181 / 500) - Real.log q ≤ Real.log (x + 181 / 500) - Real.log x ∧
      Real.log (x + 181 / 500) - Real.log x ≤ Real.log (p + 181 / 500) - Real.log p := by
  have hx0 : 0 < x := by linarith
  have hq0 : 0 < q := by linarith
  rw [← Real.log_div (by linarith) hx0.ne', ← Real.log_div (by linarith) hq0.ne',
    ← Real.log_div (by linarith) hp.ne']
  constructor
  · exact Real.log_le_log (by positivity) (by rw [div_le_div_iff₀ hq0 hx0]; nlinarith)
  · exact Real.log_le_log (by positivity) (by rw [div_le_div_iff₀ hx0 hp]; nlinarith)

theorem lendFoldNumerator_hubA_collarA {κ x : ℝ} (hκ : κ ≤ 241517 / 100000)
    (h1 : 11 / 250 ≤ x) (h2 : x ≤ 57 / 1000) : 173 / 100000 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  obtain ⟨hr1, hr2⟩ := lendFoldWindowRatio_bounds (by norm_num) h1 h2
  have hlo : 1993642 / 1000000 ≤ Real.log (x + 181 / 500) - Real.log x := by
    refine le_trans ?_ hr1
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_ge_tangent (show (0 : ℝ) < (57 / 1000 + 181 / 500) / (57 / 1000) by norm_num)
      (show (0 : ℝ) < 7 by norm_num)
    norm_num at ht ⊢
    linarith
  have hhi : Real.log (x + 181 / 500) - Real.log x ≤ 2222478 / 1000000 := by
    refine le_trans hr2 ?_
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (11 / 250 + 181 / 500) / (11 / 250) by norm_num)
      (show (0 : ℝ) < 9 by norm_num)
    have e9 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
    norm_num at ht ⊢
    linarith
  have hlam : 1023143 / 1000000 ≤
      -(1 / 2) * Real.log (7241 / 20000 - x) - 1 / 2 * Real.log (7241 / 20000 + x) := by
    have e : -(1 / 2) * Real.log (7241 / 20000 - x) - 1 / 2 * Real.log (7241 / 20000 + x) =
        -(1 / 2) * Real.log ((7241 / 20000) ^ 2 - x ^ 2) := by
      rw [show (7241 / 20000 : ℝ) ^ 2 - x ^ 2 = (7241 / 20000 - x) * (7241 / 20000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hm : Real.log ((7241 / 20000) ^ 2 - x ^ 2) ≤ Real.log ((7241 / 20000) ^ 2 - (11 / 250) ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have ht := log_le_tangent (show (0 : ℝ) < (7241 / 20000) ^ 2 - (11 / 250) ^ 2 by norm_num)
      (show (0 : ℝ) < 1 / 8 by norm_num)
    have e := log_smooth_div 0 0 0 0 3 0 0 0
    norm_num at e ht
    rw [e] at ht
    linarith
  refine le_trans ?_ (lendFoldNumerator_ge_collar (p := 11 / 250) (q := 57 / 1000) le_rfl h1 h2
    (by norm_num) hlo hhi hlam hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 5 / 100)),
    sq_nonneg (x - 5 / 100)]

theorem lendFoldNumerator_hubA_collarB {κ x : ℝ} (hκ : κ ≤ 241517 / 100000)
    (h1 : 57 / 1000 ≤ x) (h2 : x ≤ 127 / 2000) : 173 / 100000 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  obtain ⟨hr1, hr2⟩ := lendFoldWindowRatio_bounds (by norm_num) h1 h2
  have hlo : 1901256 / 1000000 ≤ Real.log (x + 181 / 500) - Real.log x := by
    refine le_trans ?_ hr1
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_ge_tangent (show (0 : ℝ) < (127 / 2000 + 181 / 500) / (127 / 2000) by norm_num)
      (show (0 : ℝ) < 7 by norm_num)
    norm_num at ht ⊢
    linarith
  have hhi : Real.log (x + 181 / 500) - Real.log x ≤ 1996036 / 1000000 := by
    refine le_trans hr2 ?_
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (57 / 1000 + 181 / 500) / (57 / 1000) by norm_num)
      (show (0 : ℝ) < 7 by norm_num)
    norm_num at ht ⊢
    linarith
  have hlam : 1028395 / 1000000 ≤
      -(1 / 2) * Real.log (7241 / 20000 - x) - 1 / 2 * Real.log (7241 / 20000 + x) := by
    have e : -(1 / 2) * Real.log (7241 / 20000 - x) - 1 / 2 * Real.log (7241 / 20000 + x) =
        -(1 / 2) * Real.log ((7241 / 20000) ^ 2 - x ^ 2) := by
      rw [show (7241 / 20000 : ℝ) ^ 2 - x ^ 2 = (7241 / 20000 - x) * (7241 / 20000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hm : Real.log ((7241 / 20000) ^ 2 - x ^ 2) ≤ Real.log ((7241 / 20000) ^ 2 - (57 / 1000) ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have ht := log_le_tangent (show (0 : ℝ) < (7241 / 20000) ^ 2 - (57 / 1000) ^ 2 by norm_num)
      (show (0 : ℝ) < 1 / 8 by norm_num)
    have e := log_smooth_div 0 0 0 0 3 0 0 0
    norm_num at e ht
    rw [e] at ht
    linarith
  refine le_trans ?_ (lendFoldNumerator_ge_collar (p := 57 / 1000) (q := 127 / 2000) (by norm_num) h1
    h2 (by norm_num) hlo hhi hlam hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 241 / 4000)),
    sq_nonneg (x - 241 / 4000)]

theorem lendFoldNumerator_hubA_collarC {κ x : ℝ} (hκ : κ ≤ 241517 / 100000)
    (h1 : 127 / 2000 ≤ x) (h2 : x ≤ 7 / 100) : 173 / 100000 ≤ lendFoldNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  obtain ⟨hr1, hr2⟩ := lendFoldWindowRatio_bounds (by norm_num) h1 h2
  have hlo : 1819537 / 1000000 ≤ Real.log (x + 181 / 500) - Real.log x := by
    refine le_trans ?_ hr1
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_ge_tangent (show (0 : ℝ) < (7 / 100 + 181 / 500) / (7 / 100) by norm_num)
      (show (0 : ℝ) < 6 by norm_num)
    have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    norm_num at ht ⊢
    linarith
  have hhi : Real.log (x + 181 / 500) - Real.log x ≤ 1903166 / 1000000 := by
    refine le_trans hr2 ?_
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (127 / 2000 + 181 / 500) / (127 / 2000) by norm_num)
      (show (0 : ℝ) < 7 by norm_num)
    norm_num at ht ⊢
    linarith
  have hlam : 1031528 / 1000000 ≤
      -(1 / 2) * Real.log (7241 / 20000 - x) - 1 / 2 * Real.log (7241 / 20000 + x) := by
    have e : -(1 / 2) * Real.log (7241 / 20000 - x) - 1 / 2 * Real.log (7241 / 20000 + x) =
        -(1 / 2) * Real.log ((7241 / 20000) ^ 2 - x ^ 2) := by
      rw [show (7241 / 20000 : ℝ) ^ 2 - x ^ 2 = (7241 / 20000 - x) * (7241 / 20000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hm : Real.log ((7241 / 20000) ^ 2 - x ^ 2) ≤ Real.log ((7241 / 20000) ^ 2 - (127 / 2000) ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have ht := log_le_tangent (show (0 : ℝ) < (7241 / 20000) ^ 2 - (127 / 2000) ^ 2 by norm_num)
      (show (0 : ℝ) < 1 / 8 by norm_num)
    have e := log_smooth_div 0 0 0 0 3 0 0 0
    norm_num at e ht
    rw [e] at ht
    linarith
  refine le_trans ?_ (lendFoldNumerator_ge_collar (p := 127 / 2000) (q := 7 / 100) (by norm_num) h1
    h2 le_rfl hlo hhi hlam hκ)
  unfold quarticGauge lendFoldPoly firstOrderSurplus firstMomentAnti zerothMomentAnti quarticSlope
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 267 / 4000)),
    sq_nonneg (x - 267 / 4000)]

/-- **The numerator on the origin hub** `[11/250, 7/100]` exceeds `173/100000`. -/
theorem lendFoldNumerator_hubA {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 11 / 250 ≤ x)
    (h2 : x ≤ 7 / 100) : 173 / 100000 ≤ lendFoldNumerator κ x := by
  rcases le_or_gt x (57 / 1000) with h | h
  · exact lendFoldNumerator_hubA_collarA hκ h1 h
  rcases le_or_gt x (127 / 2000) with h' | h'
  · exact lendFoldNumerator_hubA_collarB hκ h.le h'
  · exact lendFoldNumerator_hubA_collarC hκ h'.le h2

/-- **The numerator is nonnegative on `[7/100, 7/50]`.** -/
theorem lendFoldNumerator_nonneg_lower {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 7 / 100 ≤ x)
    (h2 : x ≤ 7 / 50) : 0 ≤ lendFoldNumerator κ x := by
  rcases le_or_gt x (1 / 10) with k0 | k0
  · exact lendFoldNumerator_nonneg_one hκ h1 k0
  rcases le_or_gt x (3 / 25) with k1 | k1
  · exact lendFoldNumerator_nonneg_two hκ k0.le k1
  · exact lendFoldNumerator_nonneg_three hκ k1.le h2

/-- **The numerator on the middle `[7/50, 27/100]`** exceeds `−38/100000`. -/
theorem lendFoldNumerator_middle {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 7 / 50 ≤ x)
    (h2 : x ≤ 27 / 100) : -38 / 100000 ≤ lendFoldNumerator κ x := by
  rcases le_or_gt x (31 / 200) with k3 | k3
  · exact lendFoldNumerator_nonneg_four hκ h1 k3
  rcases le_or_gt x (17 / 100) with k4 | k4
  · exact lendFoldNumerator_nonneg_five hκ k3.le k4
  rcases le_or_gt x (9 / 50) with k5 | k5
  · exact lendFoldNumerator_nonneg_six hκ k4.le k5
  rcases le_or_gt x (19 / 100) with k6 | k6
  · exact lendFoldNumerator_nonneg_seven hκ k5.le k6
  rcases le_or_gt x (1 / 5) with k7 | k7
  · exact lendFoldNumerator_nonneg_eight hκ k6.le k7
  rcases le_or_gt x (21 / 100) with k8 | k8
  · exact lendFoldNumerator_nonneg_nine hκ k7.le k8
  rcases le_or_gt x (11 / 50) with k9 | k9
  · exact lendFoldNumerator_nonneg_ten hκ k8.le k9
  rcases le_or_gt x (23 / 100) with k10 | k10
  · exact lendFoldNumerator_nonneg_eleven hκ k9.le k10
  rcases le_or_gt x (6 / 25) with k11 | k11
  · exact lendFoldNumerator_nonneg_twelve hκ k10.le k11
  rcases le_or_gt x (51 / 200) with k12 | k12
  · exact lendFoldNumerator_nonneg_thirteen hκ k11.le k12
  · exact lendFoldNumerator_nonneg_fourteen hκ k12.le h2

/-- **The numerator is nonnegative on `[27/100, 181/500]`.** -/
theorem lendFoldNumerator_nonneg_upper {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 27 / 100 ≤ x)
    (h2 : x ≤ 181 / 500) : 0 ≤ lendFoldNumerator κ x := by
  rcases le_or_gt x (57 / 200) with k14 | k14
  · exact lendFoldNumerator_nonneg_fifteen hκ h1 k14
  rcases le_or_gt x (3 / 10) with k15 | k15
  · exact lendFoldNumerator_nonneg_sixteen hκ k14.le k15
  rcases le_or_gt x (123 / 400) with k16a | k16a
  · exact lendFoldNumerator_nonneg_seventeenA hκ k15.le k16a
  rcases le_or_gt x (63 / 200) with k16 | k16
  · exact lendFoldNumerator_nonneg_seventeenB hκ k16a.le k16
  rcases le_or_gt x (13 / 40) with k17 | k17
  · exact lendFoldNumerator_nonneg_eighteen hκ k16.le k17
  rcases le_or_gt x (333 / 1000) with k18 | k18
  · exact lendFoldNumerator_nonneg_nineteen hκ k17.le k18
  rcases le_or_gt x (169 / 500) with k19 | k19
  · exact lendFoldNumerator_nonneg_twenty hκ k18.le k19
  rcases le_or_gt x (171 / 500) with k20 | k20
  · exact lendFoldNumerator_nonneg_twentyOne hκ k19.le k20
  rcases le_or_gt x (173 / 500) with k21 | k21
  · exact lendFoldNumerator_nonneg_twentyTwo hκ k20.le k21
  rcases le_or_gt x (7 / 20) with k22 | k22
  · exact lendFoldNumerator_nonneg_twentyThree hκ k21.le k22
  rcases le_or_gt x (353 / 1000) with k23 | k23
  · exact lendFoldNumerator_nonneg_twentyFour hκ k22.le k23
  rcases le_or_gt x (89 / 250) with k24 | k24
  · exact lendFoldNumerator_nonneg_twentyFive hκ k23.le k24
  rcases le_or_gt x (179 / 500) with e0 | e0
  · exact lendFoldNumerator_edgeA hκ k24.le e0
  rcases le_or_gt x (9 / 25) with e1 | e1
  · exact lendFoldNumerator_edgeB hκ e0.le e1
  · exact lendFoldNumerator_edgeC hκ e1.le h2

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
