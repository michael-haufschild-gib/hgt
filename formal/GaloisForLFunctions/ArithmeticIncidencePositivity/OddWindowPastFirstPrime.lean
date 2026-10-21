import GaloisForLFunctions.ArithmeticIncidencePositivity.FirstPrimeWindowOddStrip
import GaloisForLFunctions.ArithmeticIncidencePositivity.CurvedFoldOddWindowPositivity

/-!
# Odd-sector Weil positivity past `½ log 2`: the prime atom on the edge strip

The window `[−347/1000, 347/1000]` is the first one on which the prime `2` acts: `2 · 0.347 > log 2`.
For odd tests the atom lives on the edge strip `S = [log 2 − 347/1000, 347/1000]` and costs at most
`Λ(2)/√2 ≤ 0.4902` per unit of mass there (`FirstPrimeWindowOddStrip`). The plateau of radius
`R = 139/400` keeps its archimedean potential, which is logarithmically large on `S`, and the curved
fold with the quartic gauge

    h(y) = 1/500 + (119/200) y − y² − (3/10) y³ − (5/2) y⁴

(`QuarticGaugeSurplusPotential`; in units of the window, `0.017 + 1.715 s − s² − 0.108 s³ − 0.30 s⁴`,
flatter than the cubic of `CurvedFoldOddWindowPositivity` and peaked at `s ≈ 0.64`) pays the deficit
of the flat fold in the middle of the window. Multiplying the potential by `h`, the two logarithms
merge into the even part `1/500 − x² − (5/2) x⁴` of `h`, and the potential exceeds `489/20000` on
`(0, 347/1000]` and `489/20000 + 0.4902` on `[0.346, 0.347] ⊇ S` (`firstPrimeNumerator_nonneg`,
`firstPrimeNumerator_strip`), by tangent lines at 7-smooth anchors on nineteen intervals.

**Theorem** (`fullZeroForm_ge_of_odd_support_le_pastFirstPrime`). Every odd `F ∈ C²_c` vanishing
outside `[−347/1000, 347/1000]` satisfies `Ẑ(F) ≥ (1/100) ∫ F²`. In the coordinates of the arithmetic
criticality theory: `J_M(u) + V_μ(u) ≥ 0` for every even profile `u` with `M u` supported past
`½ log 2`, in every odd gauge `M`, with the prime atom `Λ(2)/√2` paid on the first prime window by the
plateau potential and the folded surplus, without a pole-free margin.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The gauge and the numerator -/

theorem firstPrimeGauge_ge {x : ℝ} (hx0 : 0 ≤ x) (hxr : x ≤ 347 / 1000) :
    1 / 500 ≤ quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x := by
  unfold quarticGauge
  have h : 0 ≤ 119 / 200 - x - 3 / 10 * x ^ 2 - 5 / 2 * x ^ 3 := by nlinarith [pow_le_pow_left₀ hx0 hxr 3]
  nlinarith [mul_nonneg hx0 h]

theorem firstPrimeGauge_divDiff_le {u v : ℝ} (hu0 : 0 ≤ u) (hur : u ≤ 347 / 1000) (hv0 : 0 ≤ v)
    (hvr : v ≤ 347 / 1000) :
    |119 / 200 + -1 * (u + v) + -3 / 10 * (u ^ 2 + u * v + v ^ 2) +
      -5 / 2 * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3)| ≤ 63 / 100 := by
  have h1 := mul_nonneg hu0 hv0
  have h2 : u ^ 3 ≤ (347 / 1000) ^ 3 := pow_le_pow_left₀ hu0 hur 3
  have h3 : v ^ 3 ≤ (347 / 1000) ^ 3 := pow_le_pow_left₀ hv0 hvr 3
  have h4 : u ^ 2 * v ≤ (347 / 1000) ^ 3 := by nlinarith [mul_le_mul (pow_le_pow_left₀ hu0 hur 2) hvr hv0 (by positivity)]
  have h5 : u * v ^ 2 ≤ (347 / 1000) ^ 3 := by nlinarith [mul_le_mul hur (pow_le_pow_left₀ hv0 hvr 2) (by positivity) (by norm_num)]
  have h6 : 0 ≤ u ^ 2 * v := by positivity
  have h7 : 0 ≤ u * v ^ 2 := by positivity
  have h8 : 0 ≤ u ^ 3 := by positivity
  have h9 : 0 ≤ v ^ 3 := by positivity
  rw [abs_le]; constructor <;> nlinarith

/-- The polynomial part of the principal surplus of the quartic gauge. -/
def firstPrimePoly (x : ℝ) : ℝ :=
  119 / 200 * x + -1 * (3 / 2 * x ^ 2 - 347 / 1000 * x) +
    -3 / 10 * (11 / 6 * x ^ 3 - (347 / 1000) ^ 2 * x / 2) +
    -5 / 2 * (25 / 12 * x ^ 4 - 347 / 1000 * x ^ 3 - (347 / 1000) ^ 3 * x / 3)

/-- The numerator of the potential past `½ log 2` (`κ` stands for `log 2 + γ + log π`). -/
def firstPrimeNumerator (κ x : ℝ) : ℝ :=
  (1 / 500 - x ^ 2 - 5 / 2 * x ^ 4) * (Real.log (x + 347 / 1000) - Real.log x) +
    quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x *
      (-(1 / 2) * Real.log (139 / 400 - x) - 1 / 2 * Real.log (139 / 400 + x) - κ - 1 / 4000 -
        (x + 347 / 1000) ^ 2 / 48 - 5 * (x + 347 / 1000) ^ 3 / 192 - 489 / 20000) +
    firstPrimePoly x - 63 / 100 * surplusRemainder (347 / 1000) x

/-- **Tangent form of the numerator** on `[p, q] ⊆ [7/100, 347/1000]`. -/
theorem firstPrimeNumerator_ge_tangent {κ x p q v a b Lv La Lb : ℝ} (hp : 7 / 100 ≤ p)
    (hpx : p ≤ x) (hxq : x ≤ q) (hq : q ≤ 347 / 1000) (hv : 0 < v) (ha : 0 < a) (hb : 0 < b)
    (hLv : Real.log v ≤ Lv) (hLa : Real.log a ≤ La) (hLb : Real.log b ≤ Lb)
    (hκ : κ ≤ 241517 / 100000) :
    (1 / 500 - x ^ 2 - 5 / 2 * x ^ 4) * (Lv + 1 / v - 1) +
        347 / 1000 / v * (1 / (500 * q) - x - 5 / 2 * x ^ 3) +
        quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x *
          (-(1 / 2) * (La + (139 / 400 - x) / a - 1) - 1 / 2 * (Lb + (139 / 400 + x) / b - 1) -
            241517 / 100000 - 1 / 4000 - (q + 347 / 1000) ^ 2 / 48 -
            5 * (q + 347 / 1000) ^ 3 / 192 - 489 / 20000) +
        firstPrimePoly x - 63 / 100 * surplusRemainder (347 / 1000) x ≤
      firstPrimeNumerator κ x := by
  have hx0 : 0 < x := by linarith
  have hxr : x ≤ 347 / 1000 := le_trans hxq hq
  have hℓ : Real.log (x + 347 / 1000) - Real.log x ≤ Lv + (1 + 347 / 1000 / x) / v - 1 := by
    rw [← Real.log_div (by linarith) hx0.ne']
    have e : (x + 347 / 1000) / x = 1 + 347 / 1000 / x := by field_simp
    rw [e]
    have := log_le_tangent (show 0 < 1 + 347 / 1000 / x by positivity) hv
    linarith
  have hc : 1 / 500 - x ^ 2 - 5 / 2 * x ^ 4 ≤ 0 := by nlinarith [pow_nonneg hx0.le 4]
  have h1 : (1 / 500 - x ^ 2 - 5 / 2 * x ^ 4) * (Lv + (1 + 347 / 1000 / x) / v - 1) ≤
      (1 / 500 - x ^ 2 - 5 / 2 * x ^ 4) * (Real.log (x + 347 / 1000) - Real.log x) :=
    mul_le_mul_of_nonpos_left hℓ hc
  have h1' : (1 / 500 - x ^ 2 - 5 / 2 * x ^ 4) * (Lv + 1 / v - 1) +
      347 / 1000 / v * (1 / (500 * q) - x - 5 / 2 * x ^ 3) ≤
      (1 / 500 - x ^ 2 - 5 / 2 * x ^ 4) * (Lv + (1 + 347 / 1000 / x) / v - 1) := by
    have e : (1 / 500 - x ^ 2 - 5 / 2 * x ^ 4) * (Lv + (1 + 347 / 1000 / x) / v - 1) =
        (1 / 500 - x ^ 2 - 5 / 2 * x ^ 4) * (Lv + 1 / v - 1) +
          347 / 1000 / v * (1 / (500 * x) - x - 5 / 2 * x ^ 3) := by
      field_simp; ring
    rw [e]
    have hqx : 1 / (500 * q) ≤ 1 / (500 * x) := one_div_le_one_div_of_le (by positivity) (by linarith)
    have hv' : 0 ≤ 347 / 1000 / v := by positivity
    nlinarith
  have hla : -(1 / 2) * (La + (139 / 400 - x) / a - 1) ≤ -(1 / 2) * Real.log (139 / 400 - x) := by
    have := log_le_tangent (show (0 : ℝ) < 139 / 400 - x by linarith) ha
    linarith
  have hlb : -(1 / 2) * (Lb + (139 / 400 + x) / b - 1) ≤ -(1 / 2) * Real.log (139 / 400 + x) := by
    have := log_le_tangent (show (0 : ℝ) < 139 / 400 + x by linarith) hb
    linarith
  have hp2 : (x + 347 / 1000) ^ 2 ≤ (q + 347 / 1000) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 347 / 1000) ^ 3 ≤ (q + 347 / 1000) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := firstPrimeGauge_ge hx0.le hxr
  have h2 : quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x *
        (-(1 / 2) * (La + (139 / 400 - x) / a - 1) - 1 / 2 * (Lb + (139 / 400 + x) / b - 1) -
          241517 / 100000 - 1 / 4000 - (q + 347 / 1000) ^ 2 / 48 -
          5 * (q + 347 / 1000) ^ 3 / 192 - 489 / 20000) ≤
      quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x *
        (-(1 / 2) * Real.log (139 / 400 - x) - 1 / 2 * Real.log (139 / 400 + x) - κ - 1 / 4000 -
          (x + 347 / 1000) ^ 2 / 48 - 5 * (x + 347 / 1000) ^ 3 / 192 - 489 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold firstPrimeNumerator
  linarith

/-- **Monotone form of the numerator** on `[p, q] ⊆ [7/100, 347/1000]`, with an optional strip
charge `s ≥ 0` per unit of gauge. -/
theorem firstPrimeNumerator_ge_monotone {κ x p q Lℓ Llam s : ℝ} (hp : 7 / 100 ≤ p) (hpx : p ≤ x)
    (hxq : x ≤ q) (hq : q ≤ 347 / 1000)
    (hLℓ : Real.log (p + 347 / 1000) - Real.log p ≤ Lℓ)
    (hLlam : Llam ≤ -(1 / 2) * Real.log ((139 / 400) ^ 2 - p ^ 2)) (hκ : κ ≤ 241517 / 100000) :
    (1 / 500 - x ^ 2 - 5 / 2 * x ^ 4) * Lℓ +
        quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x *
          (Llam - 241517 / 100000 - 1 / 4000 - (q + 347 / 1000) ^ 2 / 48 -
            5 * (q + 347 / 1000) ^ 3 / 192 - 489 / 20000 - s) +
        firstPrimePoly x - 63 / 100 * surplusRemainder (347 / 1000) x ≤
      firstPrimeNumerator κ x - s * quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 < x := by linarith
  have hxr : x ≤ 347 / 1000 := le_trans hxq hq
  have hℓ : Real.log (x + 347 / 1000) - Real.log x ≤ Lℓ := by
    rw [← Real.log_div (by linarith) hx0.ne']
    rw [← Real.log_div (by linarith) hp0.ne'] at hLℓ
    refine le_trans (Real.log_le_log (by positivity) ?_) hLℓ
    rw [div_le_div_iff₀ hx0 hp0]; nlinarith
  have hc : 1 / 500 - x ^ 2 - 5 / 2 * x ^ 4 ≤ 0 := by nlinarith [pow_nonneg hx0.le 4]
  have h1 := mul_le_mul_of_nonpos_left hℓ hc
  have hlam : Llam ≤ -(1 / 2) * Real.log (139 / 400 - x) - 1 / 2 * Real.log (139 / 400 + x) := by
    have e : -(1 / 2) * Real.log (139 / 400 - x) - 1 / 2 * Real.log (139 / 400 + x) =
        -(1 / 2) * Real.log ((139 / 400) ^ 2 - x ^ 2) := by
      rw [show (139 / 400 : ℝ) ^ 2 - x ^ 2 = (139 / 400 - x) * (139 / 400 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hmono : Real.log ((139 / 400) ^ 2 - x ^ 2) ≤ Real.log ((139 / 400) ^ 2 - p ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    linarith
  have hp2 : (x + 347 / 1000) ^ 2 ≤ (q + 347 / 1000) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 347 / 1000) ^ 3 ≤ (q + 347 / 1000) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := firstPrimeGauge_ge hx0.le hxr
  have h2 : quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x *
        (Llam - 241517 / 100000 - 1 / 4000 - (q + 347 / 1000) ^ 2 / 48 -
          5 * (q + 347 / 1000) ^ 3 / 192 - 489 / 20000 - s) ≤
      quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x *
        (-(1 / 2) * Real.log (139 / 400 - x) - 1 / 2 * Real.log (139 / 400 + x) - κ - 1 / 4000 -
          (x + 347 / 1000) ^ 2 / 48 - 5 * (x + 347 / 1000) ^ 3 / 192 - 489 / 20000 - s) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold firstPrimeNumerator
  nlinarith

theorem firstPrimeNumerator_nonneg_one {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 7/100 ≤ x)
    (h2 : x ≤ 1/10) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ea := log_smooth_div 0 1 0 1 4 0 1 0
  have eb := log_smooth_div 0 0 0 1 4 0 0 0
  norm_num at ea eb
  have hv : Real.log (5) ≤ 1.609438 := by linarith [l5.2]
  have ha : Real.log (21/80) ≤ -1.337504 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (7/16) ≤ -0.826678 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (firstPrimeNumerator_ge_tangent (p := 7/100) (q := 1/10) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 17/200)),
    sq_nonneg (x - 17/200), mul_nonneg (sq_nonneg (x - 17/200)) (sq_nonneg (x - 17/200)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem firstPrimeNumerator_nonneg_two {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 1/10 ≤ x)
    (h2 : x ≤ 13/100) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 2 0 0 0 0 0 0 0
  have ea := log_smooth_div 0 0 0 1 1 1 1 0
  have eb := log_smooth_div 0 0 2 0 1 3 0 0
  norm_num at ev ea eb
  have hv : Real.log (4) ≤ 1.386295 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (7/30) ≤ -1.455287 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (25/54) ≤ -0.770107 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (firstPrimeNumerator_ge_tangent (p := 1/10) (q := 13/100) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 23/200)),
    sq_nonneg (x - 23/200), mul_nonneg (sq_nonneg (x - 23/200)) (sq_nonneg (x - 23/200)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem firstPrimeNumerator_nonneg_three {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 13/100 ≤ x)
    (h2 : x ≤ 4/25) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 3 0 0 3 0 0 0
  have ea := log_smooth_div 0 4 0 0 4 0 2 0
  have eb := log_smooth_div 0 0 0 2 2 0 2 0
  norm_num at ev ea eb
  have hv : Real.log (27/8) ≤ 1.216396 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (81/400) ≤ -1.597015 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (49/100) ≤ -0.713349 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (firstPrimeNumerator_ge_tangent (p := 13/100) (q := 4/25) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 29/200)),
    sq_nonneg (x - 29/200), mul_nonneg (sq_nonneg (x - 29/200)) (sq_nonneg (x - 29/200)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem firstPrimeNumerator_nonneg_four {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 4/25 ≤ x)
    (h2 : x ≤ 9/50) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ea := log_smooth_div 3 0 0 0 0 2 1 0
  have eb := log_smooth_div 1 0 0 1 0 3 0 0
  norm_num at ea eb
  have hv : Real.log (3) ≤ 1.098613 := by linarith [l3.2]
  have ha : Real.log (8/45) ≤ -1.727220 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (14/27) ≤ -0.656779 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (firstPrimeNumerator_ge_tangent (p := 4/25) (q := 9/50) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 17/100)),
    sq_nonneg (x - 17/100), mul_nonneg (sq_nonneg (x - 17/100)) (sq_nonneg (x - 17/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem firstPrimeNumerator_nonneg_five {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 9/50 ≤ x)
    (h2 : x ≤ 1/5) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 1 0 0 1 0 0 1 0
  have ea := log_smooth_div 0 2 0 1 4 0 2 0
  have eb := log_smooth_div 0 3 0 0 1 0 2 0
  norm_num at ev ea eb
  have hv : Real.log (14/5) ≤ 1.029620 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (63/400) ≤ -1.848329 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (27/50) ≤ -0.616186 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (firstPrimeNumerator_ge_tangent (p := 9/50) (q := 1/5) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 19/100)),
    sq_nonneg (x - 19/100), mul_nonneg (sq_nonneg (x - 19/100)) (sq_nonneg (x - 19/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem firstPrimeNumerator_nonneg_six {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 1/5 ≤ x)
    (h2 : x ≤ 11/50) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 3 0 0 0 0 1 0 0
  have ea := log_smooth_div 3 1 0 0 0 0 2 1
  have eb := log_smooth_div 0 0 1 0 0 2 0 0
  norm_num at ev ea eb
  have hv : Real.log (8/3) ≤ 0.980830 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (24/175) ≤ -1.986732 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (5/9) ≤ -0.587786 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (firstPrimeNumerator_ge_tangent (p := 1/5) (q := 11/50) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 21/100)),
    sq_nonneg (x - 21/100), mul_nonneg (sq_nonneg (x - 21/100)) (sq_nonneg (x - 21/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem firstPrimeNumerator_nonneg_seven {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 11/50 ≤ x)
    (h2 : x ≤ 6/25) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 1 0 1 0 0 0
  have ea := log_smooth_div 0 0 0 1 2 1 1 0
  have eb := log_smooth_div 3 2 0 0 0 0 3 0
  norm_num at ev ea eb
  have hv : Real.log (5/2) ≤ 0.916291 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (7/60) ≤ -2.148434 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (72/125) ≤ -0.551647 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (firstPrimeNumerator_ge_tangent (p := 11/50) (q := 6/25) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 23/100)),
    sq_nonneg (x - 23/100), mul_nonneg (sq_nonneg (x - 23/100)) (sq_nonneg (x - 23/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem firstPrimeNumerator_nonneg_eight {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 6/25 ≤ x)
    (h2 : x ≤ 13/50) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 2 1 0 0 0 0 1 0
  have ea := log_smooth_div 0 0 0 1 3 2 0 0
  have eb := log_smooth_div 0 1 0 0 0 0 1 0
  norm_num at ev ea eb
  have hv : Real.log (12/5) ≤ 0.875469 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (7/72) ≤ -2.330755 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (3/5) ≤ -0.510825 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (firstPrimeNumerator_ge_tangent (p := 6/25) (q := 13/50) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 1/4)),
    sq_nonneg (x - 1/4), mul_nonneg (sq_nonneg (x - 1/4)) (sq_nonneg (x - 1/4)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem firstPrimeNumerator_nonneg_nine {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 13/50 ≤ x)
    (h2 : x ≤ 7/25) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 4 0 0 0 0 0 0 1
  have ea := log_smooth_div 0 0 1 0 6 0 0 0
  have eb := log_smooth_div 0 0 1 0 3 0 0 0
  norm_num at ev ea eb
  have hv : Real.log (16/7) ≤ 0.826679 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (5/64) ≤ -2.549445 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (5/8) ≤ -0.470003 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (firstPrimeNumerator_ge_tangent (p := 13/50) (q := 7/25) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 27/100)),
    sq_nonneg (x - 27/100), mul_nonneg (sq_nonneg (x - 27/100)) (sq_nonneg (x - 27/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem firstPrimeNumerator_nonneg_ten {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 7/25 ≤ x)
    (h2 : x ≤ 3/10) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 1 1 4 0 0 0
  have ea := log_smooth_div 1 0 0 0 0 0 1 1
  have eb := log_smooth_div 4 0 0 0 0 0 2 0
  norm_num at ev ea eb
  have hv : Real.log (35/16) ≤ 0.782760 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (2/35) ≤ -2.862200 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (16/25) ≤ -0.446287 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (firstPrimeNumerator_ge_tangent (p := 7/25) (q := 3/10) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 29/100)),
    sq_nonneg (x - 29/100), mul_nonneg (sq_nonneg (x - 29/100)) (sq_nonneg (x - 29/100)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem firstPrimeNumerator_nonneg_eleven {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 3/10 ≤ x)
    (h2 : x ≤ 63/200) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 5 0 0 0 0 1 1 0
  have ea := log_smooth_div 0 0 0 0 0 0 2 0
  have eb := log_smooth_div 0 1 0 1 5 0 0 0
  norm_num at ev ea eb
  have hv : Real.log (32/15) ≤ 0.757686 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (1/25) ≤ -3.218875 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (21/32) ≤ -0.421213 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (firstPrimeNumerator_ge_tangent (p := 3/10) (q := 63/200) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 123/400)),
    sq_nonneg (x - 123/400), mul_nonneg (sq_nonneg (x - 123/400)) (sq_nonneg (x - 123/400)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem firstPrimeNumerator_nonneg_twelve {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 63/200 ≤ x)
    (h2 : x ≤ 13/40) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 2 0 2 1 0 0
  have ea := log_smooth_div 0 0 0 1 1 0 3 0
  have eb := log_smooth_div 1 0 0 0 0 1 0 0
  norm_num at ev ea eb
  have hv : Real.log (25/12) ≤ 0.733970 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (7/250) ≤ -3.575550 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (2/3) ≤ -0.405465 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (firstPrimeNumerator_ge_tangent (p := 63/200) (q := 13/40) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 8/25)),
    sq_nonneg (x - 8/25), mul_nonneg (sq_nonneg (x - 8/25)) (sq_nonneg (x - 8/25)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem firstPrimeNumerator_nonneg_thirteen {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 13/40 ≤ x)
    (h2 : x ≤ 333/1000) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 3 2 0 0 0 0 1 1
  have ea := log_smooth_div 0 1 0 0 5 0 1 0
  have eb := log_smooth_div 0 3 0 0 3 0 1 0
  norm_num at ev ea eb
  have hv : Real.log (72/35) ≤ 0.721319 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (3/160) ≤ -3.976561 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (27/40) ≤ -0.393042 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (firstPrimeNumerator_ge_tangent (p := 13/40) (q := 333/1000) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 329/1000)),
    sq_nonneg (x - 329/1000), mul_nonneg (sq_nonneg (x - 329/1000)) (sq_nonneg (x - 329/1000)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem firstPrimeNumerator_nonneg_fourteen {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 333/1000 ≤ x)
    (h2 : x ≤ 169/500) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 4 0 0 3 0 1 0
  have ea := log_smooth_div 0 1 0 0 1 0 3 0
  have eb := log_smooth_div 3 1 0 0 0 0 1 1
  norm_num at ev ea eb
  have hv : Real.log (81/40) ≤ 0.705570 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (3/250) ≤ -4.422848 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (24/35) ≤ -0.377294 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (firstPrimeNumerator_ge_tangent (p := 333/1000) (q := 169/500) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 671/2000)),
    sq_nonneg (x - 671/2000), mul_nonneg (sq_nonneg (x - 671/2000)) (sq_nonneg (x - 671/2000)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]

theorem firstPrimeNumerator_nonneg_edgeA {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 169/500 ≤ x)
    (h2 : x ≤ 17/50) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (169/500 + 347 / 1000) - Real.log (169/500) ≤ 706461 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (169/500 + 347 / 1000) / (169/500) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2517028 / 1000000 ≤ -(1 / 2) * Real.log ((139 / 400) ^ 2 - (169/500) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (139 / 400) ^ 2 - (169/500) ^ 2 by norm_num)
      (show (0 : ℝ) < 81/12500 by norm_num)
    have e := log_smooth_div 0 4 0 0 2 0 5 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := firstPrimeNumerator_ge_monotone (s := 0) (p := 169/500) (q := 17/50) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  simp only [zero_mul, sub_zero] at hmono
  refine le_trans ?_ hmono
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 339/1000)),
    sq_nonneg (x - 339/1000)]

theorem firstPrimeNumerator_nonneg_edgeB {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 17/50 ≤ x)
    (h2 : x ≤ 171/500) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (17/50 + 347 / 1000) - Real.log (17/50) ≤ 703442 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (17/50 + 347 / 1000) / (17/50) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2633760 / 1000000 ≤ -(1 / 2) * Real.log ((139 / 400) ^ 2 - (17/50) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (139 / 400) ^ 2 - (17/50) ^ 2 by norm_num)
      (show (0 : ℝ) < 16/3125 by norm_num)
    have e := log_smooth_div 4 0 0 0 0 0 5 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := firstPrimeNumerator_ge_monotone (s := 0) (p := 17/50) (q := 171/500) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  simp only [zero_mul, sub_zero] at hmono
  refine le_trans ?_ hmono
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 341/1000)),
    sq_nonneg (x - 341/1000)]

theorem firstPrimeNumerator_nonneg_edgeC {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 171/500 ≤ x)
    (h2 : x ≤ 43/125) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (171/500 + 347 / 1000) - Real.log (171/500) ≤ 700458 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (171/500 + 347 / 1000) / (171/500) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2787395 / 1000000 ≤ -(1 / 2) * Real.log ((139 / 400) ^ 2 - (171/500) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (139 / 400) ^ 2 - (171/500) ^ 2 by norm_num)
      (show (0 : ℝ) < 189/50000 by norm_num)
    have e := log_smooth_div 0 3 0 1 4 0 5 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := firstPrimeNumerator_ge_monotone (s := 0) (p := 171/500) (q := 43/125) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  simp only [zero_mul, sub_zero] at hmono
  refine le_trans ?_ hmono
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 343/1000)),
    sq_nonneg (x - 343/1000)]

theorem firstPrimeNumerator_nonneg_edgeD {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 43/125 ≤ x)
    (h2 : x ≤ 173/500) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (43/125 + 347 / 1000) - Real.log (43/125) ≤ 697508 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (43/125 + 347 / 1000) / (43/125) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 3011924 / 1000000 ≤ -(1 / 2) * Real.log ((139 / 400) ^ 2 - (43/125) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (139 / 400) ^ 2 - (43/125) ^ 2 by norm_num)
      (show (0 : ℝ) < 3/1250 by norm_num)
    have e := log_smooth_div 0 1 0 0 1 0 4 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := firstPrimeNumerator_ge_monotone (s := 0) (p := 43/125) (q := 173/500) (by norm_num) h1 h2
    (by norm_num) hLℓ hLlam hκ
  simp only [zero_mul, sub_zero] at hmono
  refine le_trans ?_ hmono
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 345/1000)),
    sq_nonneg (x - 345/1000)]

/-- **The strip.** On `[0.346, 0.347]` the numerator pays the atom: it exceeds `0.4902 h(x)`. -/
theorem firstPrimeNumerator_strip {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 173 / 500 ≤ x)
    (h2 : x ≤ 347 / 1000) : 4902 / 10000 * quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (173 / 500 + 347 / 1000) - Real.log (173 / 500) ≤ 694593 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (173 / 500 + 347 / 1000) / (173 / 500) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 3434125 / 1000000 ≤ -(1 / 2) * Real.log ((139 / 400) ^ 2 - (173 / 500) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (139 / 400) ^ 2 - (173 / 500) ^ 2 by norm_num)
      (show (0 : ℝ) < 21 / 20000 by norm_num)
    have e := log_smooth_div 0 1 0 1 5 0 4 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  have hmono := firstPrimeNumerator_ge_monotone (s := 4902 / 10000) (p := 173 / 500)
    (q := 347 / 1000) (by norm_num) h1 h2 le_rfl hLℓ hLlam hκ
  have hpoly : 0 ≤ (1 / 500 - x ^ 2 - 5 / 2 * x ^ 4) * (694593 / 1000000) +
      quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x * (3434125 / 1000000 - 241517 / 100000 - 1 / 4000 -
        (347 / 1000 + 347 / 1000) ^ 2 / 48 - 5 * (347 / 1000 + 347 / 1000) ^ 3 / 192 -
        489 / 20000 - 4902 / 10000) +
      firstPrimePoly x - 63 / 100 * surplusRemainder (347 / 1000) x := by
    unfold quarticGauge firstPrimePoly surplusRemainder
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
      mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 3465 / 10000)),
      sq_nonneg (x - 3465 / 10000)]
  linarith

/-- The numerator near the origin, `0 < x ≤ 11/250`. -/
theorem firstPrimeNumerator_nonneg_origin {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 0 < x)
    (h2 : x ≤ 11 / 250) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hxr : x ≤ 347 / 1000 := by linarith
  have hℓ : 207 / 100 ≤ Real.log (x + 347 / 1000) - Real.log x := by
    rw [← Real.log_div (by linarith) h1.ne']
    have h8 : Real.log 8 ≤ Real.log ((x + 347 / 1000) / x) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ h1]; linarith)
    have e8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith
  have hlam : 1056964 / 1000000 ≤
      -(1 / 2) * Real.log (139 / 400 - x) - 1 / 2 * Real.log (139 / 400 + x) := by
    have e : -(1 / 2) * Real.log (139 / 400 - x) - 1 / 2 * Real.log (139 / 400 + x) =
        -(1 / 2) * Real.log ((139 / 400) ^ 2 - x ^ 2) := by
      rw [show (139 / 400 : ℝ) ^ 2 - x ^ 2 = (139 / 400 - x) * (139 / 400 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hm : Real.log ((139 / 400) ^ 2 - x ^ 2) ≤ Real.log ((139 / 400) ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have hR : Real.log ((139 / 400 : ℝ) ^ 2) = 2 * Real.log (139 / 400) := by
      rw [Real.log_pow]; norm_num
    have ht := log_le_tangent (show (0 : ℝ) < 139 / 400 by norm_num) (show (0 : ℝ) < 7 / 20 by norm_num)
    have e7 := log_smooth_div 0 0 0 1 2 0 1 0
    norm_num at e7 ht
    rw [e7] at ht
    linarith
  have hc : 0 ≤ 1 / 500 - x ^ 2 - 5 / 2 * x ^ 4 := by nlinarith [pow_le_pow_left₀ h1.le h2 4]
  have hp2 : (x + 347 / 1000) ^ 2 ≤ (11 / 250 + 347 / 1000) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 347 / 1000) ^ 3 ≤ (11 / 250 + 347 / 1000) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := firstPrimeGauge_ge h1.le hxr
  have hA : (1 / 500 - x ^ 2 - 5 / 2 * x ^ 4) * (207 / 100) ≤
      (1 / 500 - x ^ 2 - 5 / 2 * x ^ 4) * (Real.log (x + 347 / 1000) - Real.log x) :=
    mul_le_mul_of_nonneg_left hℓ hc
  have hB : quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x *
        (1056964 / 1000000 - 241517 / 100000 - 1 / 4000 - (11 / 250 + 347 / 1000) ^ 2 / 48 -
          5 * (11 / 250 + 347 / 1000) ^ 3 / 192 - 489 / 20000) ≤
      quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x *
        (-(1 / 2) * Real.log (139 / 400 - x) - 1 / 2 * Real.log (139 / 400 + x) - κ - 1 / 4000 -
          (x + 347 / 1000) ^ 2 / 48 - 5 * (x + 347 / 1000) ^ 3 / 192 - 489 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hpoly : 0 ≤ (1 / 500 - x ^ 2 - 5 / 2 * x ^ 4) * (207 / 100) + quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x *
        (1056964 / 1000000 - 241517 / 100000 - 1 / 4000 - (11 / 250 + 347 / 1000) ^ 2 / 48 -
          5 * (11 / 250 + 347 / 1000) ^ 3 / 192 - 489 / 20000) +
      firstPrimePoly x - 63 / 100 * surplusRemainder (347 / 1000) x := by
    unfold quarticGauge firstPrimePoly surplusRemainder
    nlinarith [mul_nonneg h1.le (sub_nonneg.2 h2), sq_nonneg x,
      mul_nonneg (mul_nonneg h1.le h1.le) (sub_nonneg.2 h2), pow_nonneg h1.le 3, pow_nonneg h1.le 4]
  unfold firstPrimeNumerator
  linarith

/-- The numerator on a collar `[p, q] ⊆ [11/250, 7/100]`: `ℓ` between its endpoint values. -/
theorem firstPrimeNumerator_ge_collar {κ x p q Llo Lhi Llam : ℝ} (hp : 11 / 250 ≤ p) (hpx : p ≤ x)
    (hxq : x ≤ q) (hq : q ≤ 7 / 100)
    (hlo : Llo ≤ Real.log (x + 347 / 1000) - Real.log x)
    (hhi : Real.log (x + 347 / 1000) - Real.log x ≤ Lhi)
    (hlam : Llam ≤ -(1 / 2) * Real.log (139 / 400 - x) - 1 / 2 * Real.log (139 / 400 + x))
    (hκ : κ ≤ 241517 / 100000) :
    1 / 500 * Llo - (x ^ 2 + 5 / 2 * x ^ 4) * Lhi +
        quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x * (Llam - 241517 / 100000 - 1 / 4000 - (q + 347 / 1000) ^ 2 / 48 -
          5 * (q + 347 / 1000) ^ 3 / 192 - 489 / 20000) +
        firstPrimePoly x - 63 / 100 * surplusRemainder (347 / 1000) x ≤
      firstPrimeNumerator κ x := by
  have hx0 : 0 < x := by linarith
  have hxr : x ≤ 347 / 1000 := by linarith
  have hp2 : (x + 347 / 1000) ^ 2 ≤ (q + 347 / 1000) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 347 / 1000) ^ 3 ≤ (q + 347 / 1000) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := firstPrimeGauge_ge hx0.le hxr
  have hw : 0 ≤ x ^ 2 + 5 / 2 * x ^ 4 := by positivity
  have hA : 1 / 500 * Llo - (x ^ 2 + 5 / 2 * x ^ 4) * Lhi ≤
      (1 / 500 - x ^ 2 - 5 / 2 * x ^ 4) * (Real.log (x + 347 / 1000) - Real.log x) := by
    nlinarith [mul_le_mul_of_nonneg_left hhi hw]
  have hB : quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x * (Llam - 241517 / 100000 - 1 / 4000 - (q + 347 / 1000) ^ 2 / 48 -
          5 * (q + 347 / 1000) ^ 3 / 192 - 489 / 20000) ≤
      quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x *
        (-(1 / 2) * Real.log (139 / 400 - x) - 1 / 2 * Real.log (139 / 400 + x) - κ - 1 / 4000 -
          (x + 347 / 1000) ^ 2 / 48 - 5 * (x + 347 / 1000) ^ 3 / 192 - 489 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold firstPrimeNumerator
  linarith

/-- The window ratio `log((x + r)/x)` on a collar, from both endpoints. -/
theorem windowRatio_bounds {x p q : ℝ} (hp : 0 < p) (hpx : p ≤ x) (hxq : x ≤ q) :
    Real.log (q + 347 / 1000) - Real.log q ≤ Real.log (x + 347 / 1000) - Real.log x ∧
      Real.log (x + 347 / 1000) - Real.log x ≤ Real.log (p + 347 / 1000) - Real.log p := by
  have hx0 : 0 < x := by linarith
  have hq0 : 0 < q := by linarith
  rw [← Real.log_div (by linarith) hx0.ne', ← Real.log_div (by linarith) hq0.ne',
    ← Real.log_div (by linarith) hp.ne']
  constructor
  · exact Real.log_le_log (by positivity) (by rw [div_le_div_iff₀ hq0 hx0]; nlinarith)
  · exact Real.log_le_log (by positivity) (by rw [div_le_div_iff₀ hx0 hp]; nlinarith)

theorem firstPrimeNumerator_nonneg_collarA {κ x : ℝ} (hκ : κ ≤ 241517 / 100000)
    (h1 : 11 / 250 ≤ x) (h2 : x ≤ 57 / 1000) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  obtain ⟨hr1, hr2⟩ := windowRatio_bounds (by norm_num) h1 h2
  have hlo : 1958286 / 1000000 ≤ Real.log (x + 347 / 1000) - Real.log x := by
    refine le_trans ?_ hr1
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_ge_tangent (show (0 : ℝ) < (57 / 1000 + 347 / 1000) / (57 / 1000) by norm_num)
      (show (0 : ℝ) < 7 by norm_num)
    norm_num at ht ⊢
    linarith
  have hhi : Real.log (x + 347 / 1000) - Real.log x ≤ 2190238 / 1000000 := by
    refine le_trans hr2 ?_
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (11 / 250 + 347 / 1000) / (11 / 250) by norm_num)
      (show (0 : ℝ) < 8 by norm_num)
    have e8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    norm_num at ht ⊢
    linarith
  have hlam : 1065047 / 1000000 ≤
      -(1 / 2) * Real.log (139 / 400 - x) - 1 / 2 * Real.log (139 / 400 + x) := by
    have e : -(1 / 2) * Real.log (139 / 400 - x) - 1 / 2 * Real.log (139 / 400 + x) =
        -(1 / 2) * Real.log ((139 / 400) ^ 2 - x ^ 2) := by
      rw [show (139 / 400 : ℝ) ^ 2 - x ^ 2 = (139 / 400 - x) * (139 / 400 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hm : Real.log ((139 / 400) ^ 2 - x ^ 2) ≤ Real.log ((139 / 400) ^ 2 - (11 / 250) ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have ht := log_le_tangent (show (0 : ℝ) < (139 / 400) ^ 2 - (11 / 250) ^ 2 by norm_num)
      (show (0 : ℝ) < 3 / 25 by norm_num)
    have e := log_smooth_div 0 1 0 0 0 0 2 0
    norm_num at e ht
    rw [e] at ht
    linarith
  refine le_trans ?_ (firstPrimeNumerator_ge_collar (p := 11 / 250) (q := 57 / 1000) le_rfl h1 h2
    (by norm_num) hlo hhi hlam hκ)
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 5 / 100)),
    sq_nonneg (x - 5 / 100)]

theorem firstPrimeNumerator_nonneg_collarB {κ x : ℝ} (hκ : κ ≤ 241517 / 100000)
    (h1 : 57 / 1000 ≤ x) (h2 : x ≤ 7 / 100) : 0 ≤ firstPrimeNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  obtain ⟨hr1, hr2⟩ := windowRatio_bounds (by norm_num) h1 h2
  have hlo : 1784565 / 1000000 ≤ Real.log (x + 347 / 1000) - Real.log x := by
    refine le_trans ?_ hr1
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_ge_tangent (show (0 : ℝ) < (7 / 100 + 347 / 1000) / (7 / 100) by norm_num)
      (show (0 : ℝ) < 6 by norm_num)
    have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    norm_num at ht ⊢
    linarith
  have hhi : Real.log (x + 347 / 1000) - Real.log x ≤ 1958442 / 1000000 := by
    refine le_trans hr2 ?_
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (57 / 1000 + 347 / 1000) / (57 / 1000) by norm_num)
      (show (0 : ℝ) < 7 by norm_num)
    norm_num at ht ⊢
    linarith
  have hlam : 1070518 / 1000000 ≤
      -(1 / 2) * Real.log (139 / 400 - x) - 1 / 2 * Real.log (139 / 400 + x) := by
    have e : -(1 / 2) * Real.log (139 / 400 - x) - 1 / 2 * Real.log (139 / 400 + x) =
        -(1 / 2) * Real.log ((139 / 400) ^ 2 - x ^ 2) := by
      rw [show (139 / 400 : ℝ) ^ 2 - x ^ 2 = (139 / 400 - x) * (139 / 400 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hm : Real.log ((139 / 400) ^ 2 - x ^ 2) ≤ Real.log ((139 / 400) ^ 2 - (57 / 1000) ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have ht := log_le_tangent (show (0 : ℝ) < (139 / 400) ^ 2 - (57 / 1000) ^ 2 by norm_num)
      (show (0 : ℝ) < 3 / 25 by norm_num)
    have e := log_smooth_div 0 1 0 0 0 0 2 0
    norm_num at e ht
    rw [e] at ht
    linarith
  refine le_trans ?_ (firstPrimeNumerator_ge_collar (p := 57 / 1000) (q := 7 / 100) (by norm_num) h1
    h2 le_rfl hlo hhi hlam hκ)
  unfold quarticGauge firstPrimePoly surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 635 / 10000)),
    sq_nonneg (x - 635 / 10000)]

/-- **The numerator is nonnegative on `(0, 347/1000]`.** -/
theorem firstPrimeNumerator_nonneg {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (hx0 : 0 < x)
    (hxr : x ≤ 347 / 1000) : 0 ≤ firstPrimeNumerator κ x := by
  rcases le_or_gt x (11 / 250) with h | h
  · exact firstPrimeNumerator_nonneg_origin hκ hx0 h
  rcases le_or_gt x (57 / 1000) with h' | h'
  · exact firstPrimeNumerator_nonneg_collarA hκ h.le h'
  rcases le_or_gt x (7 / 100) with h0 | h0
  · exact firstPrimeNumerator_nonneg_collarB hκ h'.le h0
  rcases le_or_gt x (1 / 10) with h1 | h1
  · exact firstPrimeNumerator_nonneg_one hκ h0.le h1
  rcases le_or_gt x (13 / 100) with h2 | h2
  · exact firstPrimeNumerator_nonneg_two hκ h1.le h2
  rcases le_or_gt x (4 / 25) with h3 | h3
  · exact firstPrimeNumerator_nonneg_three hκ h2.le h3
  rcases le_or_gt x (9 / 50) with h4 | h4
  · exact firstPrimeNumerator_nonneg_four hκ h3.le h4
  rcases le_or_gt x (1 / 5) with h5 | h5
  · exact firstPrimeNumerator_nonneg_five hκ h4.le h5
  rcases le_or_gt x (11 / 50) with h6 | h6
  · exact firstPrimeNumerator_nonneg_six hκ h5.le h6
  rcases le_or_gt x (6 / 25) with h7 | h7
  · exact firstPrimeNumerator_nonneg_seven hκ h6.le h7
  rcases le_or_gt x (13 / 50) with h8 | h8
  · exact firstPrimeNumerator_nonneg_eight hκ h7.le h8
  rcases le_or_gt x (7 / 25) with h9 | h9
  · exact firstPrimeNumerator_nonneg_nine hκ h8.le h9
  rcases le_or_gt x (3 / 10) with h10 | h10
  · exact firstPrimeNumerator_nonneg_ten hκ h9.le h10
  rcases le_or_gt x (63 / 200) with h11 | h11
  · exact firstPrimeNumerator_nonneg_eleven hκ h10.le h11
  rcases le_or_gt x (13 / 40) with h12 | h12
  · exact firstPrimeNumerator_nonneg_twelve hκ h11.le h12
  rcases le_or_gt x (333 / 1000) with h13 | h13
  · exact firstPrimeNumerator_nonneg_thirteen hκ h12.le h13
  rcases le_or_gt x (169 / 500) with h14 | h14
  · exact firstPrimeNumerator_nonneg_fourteen hκ h13.le h14
  rcases le_or_gt x (17 / 50) with h15 | h15
  · exact firstPrimeNumerator_nonneg_edgeA hκ h14.le h15
  rcases le_or_gt x (171 / 500) with h16 | h16
  · exact firstPrimeNumerator_nonneg_edgeB hκ h15.le h16
  rcases le_or_gt x (43 / 125) with h17 | h17
  · exact firstPrimeNumerator_nonneg_edgeC hκ h16.le h17
  rcases le_or_gt x (173 / 500) with h18 | h18
  · exact firstPrimeNumerator_nonneg_edgeD hκ h17.le h18
  · have := firstPrimeNumerator_strip hκ h18.le hxr
    have hh := firstPrimeGauge_ge (by linarith) hxr
    nlinarith

/-! ### The potential with the atom -/

/-- **The potential past `½ log 2`.** On `(0, 347/1000]` the killing, the quartic surplus potential and
the plateau potential of radius `139/400` exceed `489/20000`, and on the strip
`S = [log 2 − 347/1000, 347/1000]` they also pay the atom `Λ(2)/√2`. -/
theorem firstPrime_potential_ge {x : ℝ} (hx0 : 0 < x) (hxr : x ≤ 347 / 1000) :
    489 / 20000 + vonMangoldtAtom 2 * (Icc (Real.log 2 - 347 / 1000) (347 / 1000)).indicator 1 x ≤
      2 * (archLevyAntideriv x - archLevyAntideriv (x + 347 / 1000)) +
        surplusPotential (quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2)) (347 / 1000) x +
        (archLevyAntideriv (139 / 400 - x) + archLevyAntideriv (139 / 400 + x) -
          2 * windowEdgeFunction 0 - 2 * archConstantReal) := by
  have hh := firstPrimeGauge_ge hx0.le hxr
  have hh0 : 0 < quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x := by linarith
  have hU := mul_surplusPotential_quarticGauge_ge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2)
    hx0 hxr (by norm_num) hh0 fun u v hu0 hur hv0 hvr => firstPrimeGauge_divDiff_le hu0 hur hv0 hvr
  have hΩx := archLevyAntideriv_ge hx0
  have hΩr := archLevyAntideriv_le_expansion (show 0 < x + 347 / 1000 by linarith)
  have hΩa := archLevyAntideriv_ge (show 0 < 139 / 400 - x by linarith)
  have hΩb := archLevyAntideriv_ge (show 0 < 139 / 400 + x by linarith)
  have hγ := RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have hπ := log_pi_le_11448
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hκ : Real.log 2 + Real.eulerMascheroniConstant + Real.log Real.pi ≤ 241517 / 100000 := by
    linarith
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e1 : Real.log (x / 4) = Real.log x - 2 * Real.log 2 := by
    rw [Real.log_div hx0.ne' (by norm_num), l4]
  have e2 : Real.log ((x + 347 / 1000) / 4) = Real.log (x + 347 / 1000) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  have e3 : Real.log ((139 / 400 - x) / 4) = Real.log (139 / 400 - x) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  have e4 : Real.log ((139 / 400 + x) / 4) = Real.log (139 / 400 + x) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  rw [e1] at hΩx
  rw [e2] at hΩr
  rw [e3] at hΩa
  rw [e4] at hΩb
  rw [windowEdgeFunction_zero]
  unfold archConstantReal
  set κ := Real.log 2 + Real.eulerMascheroniConstant + Real.log Real.pi with hκdef
  set V : ℝ := (Real.log (x + 347 / 1000) - Real.log x) +
    (-(1 / 2) * Real.log (139 / 400 - x) - 1 / 2 * Real.log (139 / 400 + x)) - κ - 1 / 4000 -
    (x + 347 / 1000) ^ 2 / 48 - 5 * (x + 347 / 1000) ^ 3 / 192 with hV
  set U := surplusPotential (quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2)) (347 / 1000) x with hUdef
  have hkey : quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x * (V - 489 / 20000) +
      (quarticSurplusMain (119 / 200) (-1) (-3 / 10) (-5 / 2) (347 / 1000) x -
        63 / 100 * surplusRemainder (347 / 1000) x) = firstPrimeNumerator κ x := by
    rw [hV]; unfold firstPrimeNumerator quarticSurplusMain cubicSurplusMain firstPrimePoly quarticGauge
    ring
  -- the charge `s` of the strip
  set s : ℝ := vonMangoldtAtom 2 * (Icc (Real.log 2 - 347 / 1000) (347 / 1000)).indicator 1 x with hs
  have hsh : s * quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x ≤ firstPrimeNumerator κ x := by
    obtain ⟨hΛ0, hΛ1⟩ := vonMangoldtAtom_two_bounds
    by_cases hS : x ∈ Icc (Real.log 2 - 347 / 1000) (347 / 1000)
    · have hx346 : 173 / 500 ≤ x := by linarith [hS.1]
      have hstrip := firstPrimeNumerator_strip hκ hx346 hxr
      rw [hs, Set.indicator_of_mem hS, Pi.one_apply, mul_one]
      have := mul_le_mul_of_nonneg_right hΛ1 hh0.le
      linarith
    · rw [hs, Set.indicator_of_notMem hS, mul_zero, zero_mul]
      exact firstPrimeNumerator_nonneg hκ hx0 hxr
  have hVU : 489 / 20000 + s ≤ V + U := by
    have h1 : quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x * (489 / 20000 + s) ≤ quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x * (V + U) := by
      have e : quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x * (V + U) = quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x * (V - 489 / 20000) + quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x * U +
          489 / 20000 * quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2) x := by ring
      rw [e]
      linarith
    exact le_of_mul_le_mul_left h1 hh0
  have hW : V + U ≤ 2 * (archLevyAntideriv x - archLevyAntideriv (x + 347 / 1000)) + U +
      (archLevyAntideriv (139 / 400 - x) + archLevyAntideriv (139 / 400 + x) -
        2 * (3 / 2 * Real.log 2 + Real.pi / 4) -
        2 * ((Real.eulerMascheroniConstant + Real.log Real.pi) / 2)) := by
    rw [hV]; linarith
  linarith

/-! ### Odd-sector positivity past `½ log 2` -/

/-- **Weil positivity of every odd test supported in `[−347/1000, 347/1000]`.** The window crosses
`½ log 2`: the prime atom `Λ(2)/√2` acts on the edge strip and is paid there. Every odd `F ∈ C²_c`
vanishing outside `[−347/1000, 347/1000]` satisfies `Ẑ(F) ≥ (1/100) ∫ F²`. -/
theorem fullZeroForm_ge_of_odd_support_le_pastFirstPrime {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, 347 / 1000 < |x| → F x = 0) :
    1 / 100 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  set r : ℝ := 347 / 1000 with hrdef
  set R : ℝ := 139 / 400 with hRdef
  set δ : ℝ := R - r with hδdef
  have hδ : 0 < δ := by rw [hδdef, hRdef, hrdef]; norm_num
  set P := plateauGauge R δ with hPdef
  have hPd : ContDiff ℝ 2 P := contDiff_plateauGauge R δ
  have hPcs : HasCompactSupport P := hasCompactSupport_plateauGauge hδ
  have hP0 : ∀ y, 0 ≤ P y := plateauGauge_nonneg R δ
  have hP1 : ∀ y, P y ≤ 1 := plateauGauge_le_one R δ
  have hPB : ∀ y, R ≤ |y| → P y = 0 := fun y hy => plateauGauge_eq_zero hδ hy
  have hPr : ∀ y, |y| ≤ r → P y = 1 := fun y hy =>
    plateauGauge_eq_one hδ (by rw [hδdef]; linarith)
  have hPe : ∀ y, P (-y) = P y := fun y => by
    simp only [hPdef, plateauGauge, sub_neg_eq_add, ← sub_eq_add_neg]
    ring
  have hFr : ∀ x, F x ≠ 0 → |x| ≤ r := fun x hx => by
    by_contra h
    exact hx (hsupp x (not_le.mp h))
  have hFM : ∀ x, F x ≠ 0 → P x = 1 := fun x hx => hPr x (hFr x hx)
  have hFB : ∀ x, R ≤ |x| → F x = 0 := fun x hx => hsupp x (by
    simp only [hrdef, hRdef] at hx ⊢; linarith)
  obtain ⟨KF, -, hKF⟩ := exists_lipschitz_bound_of_compactSupport (hF.of_le (by norm_num)) hFc
  have hFL : ∀ a b, |F a - F b| ≤ KF * |a - b| := fun a b => hKF b a
  obtain ⟨KM, -, hKM⟩ := exists_lipschitz_bound_of_compactSupport (hPd.of_le (by norm_num)) hPcs
  have hPL : ∀ a b, |P a - P b| ≤ KM * |a - b| := fun a b => hKM b a
  have hR0 : 0 < R := by rw [hRdef]; norm_num
  have hR1 : 2 * R ≤ 1 := by rw [hRdef]; norm_num
  have hR3 : 2 * R < Real.log 3 := by have := log_three_bounds.1; rw [hRdef]; linarith
  -- representation with the prime `2`, fold with surplus
  have hQ := markovEnergy_eq_gauge_window hF hFc hPd hPcs hP1 hP0 hPB hFM
  have hJ := signedJumpEnergy_eq_arch_add_two (F := F) hPB hR3
  obtain ⟨hIU, hfold⟩ := fourKilling_add_surplusPotential_le_archJump hPd.continuous hF.continuous
    hPe hodd hP0 hP1 hPB hFB hFL hR0 hR1 (r := r) (by rw [hrdef]; norm_num)
    (by rw [hrdef, hRdef]; norm_num) hPr hFr hPcs (continuous_quarticGauge _ _ _ _ _)
    (a₀ := 1 / 500) (by norm_num) (fun x hx0 hxr => firstPrimeGauge_ge hx0 hxr) (L := 63 / 100)
    (fun x y hx0 hxr hy0 hyr => by
      rw [quarticGauge_sub, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (firstPrimeGauge_divDiff_le hx0 hxr hy0 hyr) (abs_nonneg _))
  have hZ : fullZeroForm F = markovEnergy (fun x => (F x : ℂ)) - 2 * oddPoleMoment F ^ 2 := by
    unfold fullZeroForm
    rw [evenPoleMoment_eq_zero_of_odd hodd]
    ring
  have hdec8 : ∀ y, |P y| ≤ Real.exp (8 * R) * Real.exp (-(8 * |y|)) := by
    intro y
    by_cases hy : |y| < R
    · rw [abs_of_nonneg (hP0 y), ← Real.exp_add]
      exact (hP1 y).trans (Real.one_le_exp (by nlinarith))
    · rw [hPB y (not_lt.mp hy), abs_zero]
      positivity
  have hW : Continuous fun x => -poleFreeWeilOperator P x :=
    (continuous_poleFreeWeilOperator hPd.continuous hPL hdec8).neg
  set G : ℝ → ℝ := fun x => F x ^ 2 * P x * -poleFreeWeilOperator P x with hGdef
  have hGi : Integrable G :=
    (((hF.continuous.pow 2).mul hPd.continuous).mul hW).integrable_of_hasCompactSupport
      ((hasCompactSupport_sq hFc).mul_right.mul_right)
  -- the prime potential and the prime-returned potential `G₁`
  obtain ⟨hΛ0, hΛ1⟩ := vonMangoldtAtom_two_bounds
  set L : ℝ := Real.log 2 with hLdef
  set Λ₂ : ℝ := vonMangoldtAtom 2 with hΛdef
  set Pr : ℝ → ℝ := fun x => F x ^ 2 * P x * (P (x + L) + P (x - L)) with hPrdef
  have hPri : Integrable Pr :=
    ((((hF.continuous.pow 2).mul hPd.continuous).mul
      ((hPd.continuous.comp (continuous_id.add continuous_const)).add
        (hPd.continuous.comp (continuous_id.sub continuous_const))))).integrable_of_hasCompactSupport
      ((hasCompactSupport_sq hFc).mul_right.mul_right)
  set G₁ : ℝ → ℝ := fun x => F x ^ 2 * P x * (-poleFreeWeilOperator P x + profilePrimeSum P x)
    with hG₁def
  have hG₁eq : ∀ x, G₁ x = G x + Λ₂ * Pr x := fun x => by
    simp only [hG₁def, hGdef, hPrdef]
    by_cases h : F x = 0
    · rw [h]; ring
    · have hx : |x| < R := by have := hFr x h; rw [hrdef] at this; rw [hRdef]; linarith
      rw [profilePrimeSum_eq_two hPB hR3 hx]
      ring
  have hG₁i : Integrable G₁ := by
    have : G₁ = fun x => G x + Λ₂ * Pr x := funext hG₁eq
    rw [this]; exact hGi.add (hPri.const_mul Λ₂)
  have hG₁e : ∀ x, G₁ (-x) = G₁ x := fun x => by
    simp only [hG₁def, hodd, hPe, poleFreeWeilOperator_neg hPe, profilePrimeSum_neg hPe, neg_sq]
  have hG₁int := integral_eq_two_mul_Ioi_of_even hG₁i hG₁e
  have hGsplit : (∫ x, G x) = (∫ x, G₁ x) - Λ₂ * ∫ x, Pr x := by
    have : (fun x => G₁ x) = fun x => G x + Λ₂ * Pr x := funext hG₁eq
    rw [this, integral_add hGi (hPri.const_mul Λ₂), MeasureTheory.integral_const_mul]
    ring
  -- the atom on the strip
  have hprime : gaugeJumpProfile P F L - ∫ x, Pr x = -2 * ∫ x, F x * F (x + L) :=
    gaugeJumpProfile_sub_primePotential_eq hPd.continuous hF.continuous hFc hFM L
  have hprimeΛ : Λ₂ * gaugeJumpProfile P F L - Λ₂ * ∫ x, Pr x = -2 * (Λ₂ * ∫ x, F x * F (x + L)) := by
    rw [← mul_sub, hprime]; ring
  have hstrip := integral_mul_shift_le_strip hF.continuous hFc hodd (r := r) (L := L)
    (fun x hx => hsupp x (by rw [hrdef] at hx; exact hx))
  set S := Icc (L - r) r with hSdef
  have hS0 : S ⊆ Ioi 0 := fun x hx => by
    have := Real.log_two_gt_d9; simp only [hSdef, hLdef, hrdef, mem_Icc] at hx
    exact mem_Ioi.mpr (by linarith [hx.1])
  have hSint : (∫ x in S, F x ^ 2) = ∫ x in Ioi (0 : ℝ), S.indicator (fun y => F y ^ 2) x := by
    rw [setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.mpr hS0]
  have hF2 : Integrable fun x => F x ^ 2 :=
    (hF.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)
  have hF2e : ∀ x, (fun x => F x ^ 2) (-x) = F x ^ 2 := fun x => by simp only [hodd, neg_sq]
  have hF2int := integral_eq_two_mul_Ioi_of_even hF2 hF2e
  have hHi := integrableOn_sq_mul_antideriv_sub hF.continuous hodd hFB hFL hR1
    (r := r) (by rw [hrdef]; norm_num) (by rw [hrdef, hRdef]; norm_num)
  have hSi : IntegrableOn (fun x => S.indicator (fun y => F y ^ 2) x) (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Icc).mpr (hF.continuous.pow 2).integrableOn_Icc).integrableOn
  -- pointwise potential on the half line
  set c₀ : ℝ := 489 / 20000 with hc₀
  have hpt : ∀ x ∈ Ioi (0 : ℝ), c₀ * F x ^ 2 + Λ₂ * S.indicator (fun y => F y ^ 2) x ≤
      2 * (F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r))) +
        F x ^ 2 * surplusPotential (quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2)) r x + G₁ x := by
    intro x hx
    have hx0 : 0 < x := hx
    by_cases h : F x = 0
    · have : S.indicator (fun y => F y ^ 2) x = 0 := by
        by_cases hS : x ∈ S
        · rw [Set.indicator_of_mem hS, h]; ring
        · rw [Set.indicator_of_notMem hS]
      have h0 : F x ^ 2 = 0 := by rw [h]; ring
      simp only [hG₁def, this, h0, mul_zero, zero_mul, add_zero, le_refl]
    · have hxr : x ≤ r := by
        have := hFr x h; rwa [abs_of_pos hx0] at this
      have hxR : |x| < R := by rw [abs_of_pos hx0, hRdef]; rw [hrdef] at hxr; linarith
      have hW' := neg_poleFreeWeilOperator_add_primeSum_ge hPd.continuous hPL hP1 hPB hxR (hFM x h)
      have hV : c₀ + Λ₂ * S.indicator 1 x ≤
          2 * (archLevyAntideriv x - archLevyAntideriv (x + r)) +
            surplusPotential (quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2)) r x +
            (archLevyAntideriv (R - x) + archLevyAntideriv (R + x) -
              2 * windowEdgeFunction 0 - 2 * archConstantReal) :=
        firstPrime_potential_ge hx0 (by rw [hrdef] at hxr; exact hxr)
      have hind : S.indicator (fun y => F y ^ 2) x = S.indicator 1 x * F x ^ 2 := by
        by_cases hS : x ∈ S
        · rw [Set.indicator_of_mem hS, Set.indicator_of_mem hS, Pi.one_apply, one_mul]
        · rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem hS, zero_mul]
      rw [hind]
      simp only [hG₁def, hFM x h, mul_one]
      have hF0 := sq_nonneg (F x)
      have k1 := mul_le_mul_of_nonneg_left hW' hF0
      have k2 := mul_le_mul_of_nonneg_left hV hF0
      linarith
  have hsum : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + F x ^ 2 * surplusPotential (quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2)) r x + G₁ x) (Ioi 0) :=
    ((hHi.const_mul 2).add hIU).add hG₁i.integrableOn
  have hH2 : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r)))) (Ioi 0) := hHi.const_mul 2
  have hH2U : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + F x ^ 2 * surplusPotential (quarticGauge (1 / 500) (119 / 200) (-1) (-3 / 10) (-5 / 2)) r x) (Ioi 0) := hH2.add hIU
  have hlhs : IntegrableOn (fun x => c₀ * F x ^ 2 + Λ₂ * S.indicator (fun y => F y ^ 2) x) (Ioi 0) :=
    (hF2.integrableOn.const_mul c₀).add (hSi.const_mul Λ₂)
  have hmono := setIntegral_mono_on hlhs hsum measurableSet_Ioi hpt
  rw [integral_add hH2U hG₁i.integrableOn, integral_add hH2 hIU, integral_const_mul,
    integral_add (hF2.integrableOn.const_mul c₀) (hSi.const_mul Λ₂), integral_const_mul,
    integral_const_mul, ← hSint] at hmono
  -- the odd pole moment
  have hS := sq_oddPoleMoment_le_cosh hR0.le hF.continuous hFc hPd.continuous hPcs hP0 hP1 hPB hFM
  have hcosh : Real.cosh (R / 2) ^ 2 ≤ 1030672 / 1000000 := by
    have h1 := Real.cosh_le_exp_half_sq (R / 2)
    have h2 : (R / 2) ^ 2 / 2 ≤ 151 / 10000 := by rw [hRdef]; norm_num
    have h3 : Real.exp ((R / 2) ^ 2 / 2) ≤ Real.exp (151 / 10000) := Real.exp_le_exp.mpr h2
    have h4 : Real.exp (151 / 10000) ≤ 101522 / 100000 := by
      have := Real.exp_bound' (show (0 : ℝ) ≤ 151 / 10000 by norm_num)
        (show (151 / 10000 : ℝ) ≤ 1 by norm_num) (show 0 < 3 by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
      norm_num at this ⊢
      linarith
    have h5 : Real.cosh (R / 2) ≤ 101522 / 100000 := by linarith
    have h6 := Real.cosh_pos (R / 2)
    nlinarith
  have hpole : 2 * oddPoleMoment F ^ 2 ≤ 289 / 20000 * ∫ x, F x ^ 2 := by
    have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
    have hR3' : R ^ 3 / 6 * Real.cosh (R / 2) ^ 2 ≤ 289 / 40000 := by
      have : R ^ 3 / 6 = (139 / 400) ^ 3 / 6 := by rw [hRdef]
      rw [this]
      have := mul_le_mul_of_nonneg_left hcosh (show (0 : ℝ) ≤ (139 / 400) ^ 3 / 6 by norm_num)
      linarith
    have h2 := mul_le_mul_of_nonneg_right hR3' hI0
    linarith
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hstripΛ := mul_le_mul_of_nonneg_left hstrip hΛ0
  rw [hc₀] at hmono
  rw [hZ, hQ, hJ, hGsplit]
  linarith [hfold, hmono, hG₁int, hF2int, hpole, hprimeΛ, hstripΛ]

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
