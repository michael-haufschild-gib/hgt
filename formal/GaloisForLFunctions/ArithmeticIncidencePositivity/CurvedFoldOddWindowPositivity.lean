import GaloisForLFunctions.ArithmeticIncidencePositivity.CubicGaugeSurplusPotential

/-!
# Odd-sector Weil positivity on `[−17/50, 17/50]`: a curved fold gauge

The folded odd plateau (`OddPlateauFoldedWindowPositivity`) keeps only the killing of the crossing
pairs; its potential has a deficit at the golden point and stops near `0.297`. The surplus of the
same-side pairs over their crossing partners (`FoldedSurplusGroundStatePotential`) pays this deficit
once it is transformed in a curved gauge. With the cubic gauge

    h(y) = 1/500 + (3/5) y − y² − (6/5) y³,

peaked at `y ≈ 0.216 ≈ (17/50)/φ`, the surplus potential obeys
`h(x) U_h(x) ≥ N(x) − (3/5) ρ(x)` (`mul_surplusPotential_cubicGauge_ge`), with `N` the closed form of
`CubicGaugeSurplusPotential` and `ρ` the remainder of the Lévy density beyond `1/(2t)`. Adding the
killing `2(Ω(x) − Ω(x + r))`, the plateau potential `Ω(R − x) + Ω(R + x) − 2E(0) − (γ + log π)` and
multiplying by `h(x)`, the logarithm `ℓ = log((x + r)/x)` of the killing combines with the
logarithm of `N` into the single coefficient `1/500 − x²` (the even part of `h`), and the total
potential is at least `471/20000` exactly when the numerator

    (1/500 − x²) ℓ + h(x)(−½ log(R² − x²) − log 2 − γ − log π − 1/4000 − (x + r)²/48 − 5(x + r)³/192
      − 471/20000) + (12617/12500) x − (3/2) x² − (11/5) x³ − (3/5) ρ(x)

is nonnegative (`curvedOddNumerator_nonneg`, `r = 17/50`, `R = 681/2000`). On fifteen intervals the
logarithms are replaced by tangent lines at 7-smooth anchors (`log_le_tangent`, the anchors' logarithms
from those of `2, 3, 5, 7`) and the resulting quartics are nonnegative.

**Theorem** (`fullZeroForm_ge_of_odd_support_le_curved`). Every odd `F ∈ C²_c` vanishing outside
`[−17/50, 17/50]` satisfies `Ẑ(F) ≥ (1/100) ∫ F²`: `J_M(u) + V_μ(u) ≥ 0` for every even profile with
`M u` supported there, in every odd gauge. The window reaches `0.98` of `½ log 2`, the first window
on which the prime `2` acts.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### Logarithms of the small primes -/

theorem log_three_bounds : 1.0986122 < Real.log 3 ∧ Real.log 3 < 1.0986123 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(1 / 4 : ℝ)| < 1 by norm_num) 13
  rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, abs_le] at h
  have e : Real.log (3 / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [e] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  constructor <;> linarith [h.1, h.2]

theorem log_five_bounds : 1.6094379 < Real.log 5 ∧ Real.log 5 < 1.6094380 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(1 / 5 : ℝ)| < 1 by norm_num) 11
  rw [show (1 : ℝ) - 1 / 5 = 4 / 5 by norm_num, abs_le] at h
  have e : Real.log (4 / 5) = 2 * Real.log 2 - Real.log 5 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [e] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  constructor <;> linarith [h.1, h.2]

theorem log_seven_bounds : 1.9459101 < Real.log 7 ∧ Real.log 7 < 1.9459102 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(1 / 8 : ℝ)| < 1 by norm_num) 8
  rw [show (1 : ℝ) - 1 / 8 = 7 / 8 by norm_num, abs_le] at h
  have e : Real.log (7 / 8) = Real.log 7 - 3 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast; ring
  rw [e] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  constructor <;> linarith [h.1, h.2]

/-- The logarithm of a 7-smooth ratio. -/
theorem log_smooth_div (a b c d e f g h : ℕ) :
    Real.log ((2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d : ℝ) / (2 ^ e * 3 ^ f * 5 ^ g * 7 ^ h)) =
      ((a : ℝ) - e) * Real.log 2 + ((b : ℝ) - f) * Real.log 3 + ((c : ℝ) - g) * Real.log 5 +
        ((d : ℝ) - h) * Real.log 7 := by
  rw [Real.log_div (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  ring

theorem log_pi_le_11448 : Real.log Real.pi ≤ 11448 / 10000 := by
  rw [Real.log_le_iff_le_exp Real.pi_pos]
  have he := Real.exp_one_gt_d9
  have hT := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1448 / 10000 by norm_num) 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hT
  norm_num at hT
  have hsplit : Real.exp (11448 / 10000) = Real.exp 1 * Real.exp (1448 / 10000) := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  nlinarith [Real.pi_lt_d6, Real.exp_pos 1, Real.exp_pos (1448 / 10000)]

/-- The tangent bound `log y ≤ log s + y/s − 1`. -/
theorem log_le_tangent {y s : ℝ} (hy : 0 < y) (hs : 0 < s) :
    Real.log y ≤ Real.log s + y / s - 1 := by
  have := Real.log_le_sub_one_of_pos (div_pos hy hs)
  rw [Real.log_div hy.ne' hs.ne'] at this
  linarith

/-- The reciprocal tangent bound `log y ≥ log s + 1 − s/y`. -/
theorem log_ge_tangent {y s : ℝ} (hy : 0 < y) (hs : 0 < s) :
    Real.log s + 1 - s / y ≤ Real.log y := by
  have := Real.log_le_sub_one_of_pos (div_pos hs hy)
  rw [Real.log_div hs.ne' hy.ne'] at this
  linarith

/-! ### The gauge and the numerator -/

theorem curvedGauge_ge {x : ℝ} (hx0 : 0 ≤ x) (hxr : x ≤ 17 / 50) :
    1 / 500 ≤ cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5) x := by
  unfold cubicGauge
  have h : 0 ≤ 3 / 5 - x - 6 / 5 * x ^ 2 := by nlinarith
  nlinarith [mul_nonneg hx0 h]

theorem curvedGauge_divDiff_le {u v : ℝ} (hu0 : 0 ≤ u) (hur : u ≤ 17 / 50) (hv0 : 0 ≤ v)
    (hvr : v ≤ 17 / 50) : |3 / 5 + -1 * (u + v) + -6 / 5 * (u ^ 2 + u * v + v ^ 2)| ≤ 3 / 5 := by
  rw [abs_le]; constructor <;> nlinarith [mul_nonneg hu0 hv0]

/-- The numerator of the curved odd potential (`κ` stands for `log 2 + γ + log π`). -/
def curvedOddNumerator (κ x : ℝ) : ℝ :=
  (1 / 500 - x ^ 2) * (Real.log (x + 17 / 50) - Real.log x) +
    cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5) x *
      (-(1 / 2) * Real.log (681 / 2000 - x) - 1 / 2 * Real.log (681 / 2000 + x) - κ - 1 / 4000 -
        (x + 17 / 50) ^ 2 / 48 - 5 * (x + 17 / 50) ^ 3 / 192 - 471 / 20000) +
    (12617 / 12500 * x - 3 / 2 * x ^ 2 - 11 / 5 * x ^ 3) - 3 / 5 * surplusRemainder (17 / 50) x

/-- **Tangent form of the numerator.** On `[p, q] ⊆ [7/100, 17/50]`, with tangent anchors `v` for
`1 + r/x`, `a` for `R − x` and `b` for `R + x`. -/
theorem curvedOddNumerator_ge_tangent {κ x p q v a b Lv La Lb : ℝ} (hp : 7 / 100 ≤ p)
    (hpx : p ≤ x) (hxq : x ≤ q) (hq : q ≤ 17 / 50) (hv : 0 < v) (ha : 0 < a) (hb : 0 < b)
    (hLv : Real.log v ≤ Lv) (hLa : Real.log a ≤ La) (hLb : Real.log b ≤ Lb)
    (hκ : κ ≤ 241517 / 100000) :
    (1 / 500 - x ^ 2) * (Lv + 1 / v - 1) + 17 / 50 / v * (1 / (500 * q) - x) +
        cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5) x *
          (-(1 / 2) * (La + (681 / 2000 - x) / a - 1) - 1 / 2 * (Lb + (681 / 2000 + x) / b - 1) -
            241517 / 100000 - 1 / 4000 - (q + 17 / 50) ^ 2 / 48 - 5 * (q + 17 / 50) ^ 3 / 192 -
            471 / 20000) +
        (12617 / 12500 * x - 3 / 2 * x ^ 2 - 11 / 5 * x ^ 3) - 3 / 5 * surplusRemainder (17 / 50) x ≤
      curvedOddNumerator κ x := by
  have hx0 : 0 < x := by linarith
  have hxr : x ≤ 17 / 50 := le_trans hxq hq
  have hℓ : Real.log (x + 17 / 50) - Real.log x ≤ Lv + (1 + 17 / 50 / x) / v - 1 := by
    rw [← Real.log_div (by linarith) hx0.ne']
    have e : (x + 17 / 50) / x = 1 + 17 / 50 / x := by field_simp
    rw [e]
    have := log_le_tangent (show 0 < 1 + 17 / 50 / x by positivity) hv
    linarith
  have hc : 1 / 500 - x ^ 2 ≤ 0 := by nlinarith
  have h1 : (1 / 500 - x ^ 2) * (Lv + (1 + 17 / 50 / x) / v - 1) ≤
      (1 / 500 - x ^ 2) * (Real.log (x + 17 / 50) - Real.log x) :=
    mul_le_mul_of_nonpos_left hℓ hc
  have h1' : (1 / 500 - x ^ 2) * (Lv + 1 / v - 1) + 17 / 50 / v * (1 / (500 * q) - x) ≤
      (1 / 500 - x ^ 2) * (Lv + (1 + 17 / 50 / x) / v - 1) := by
    have e : (1 / 500 - x ^ 2) * (Lv + (1 + 17 / 50 / x) / v - 1) =
        (1 / 500 - x ^ 2) * (Lv + 1 / v - 1) + 17 / 50 / v * (1 / (500 * x) - x) := by
      field_simp; ring
    rw [e]
    have hqx : 1 / (500 * q) ≤ 1 / (500 * x) := one_div_le_one_div_of_le (by positivity) (by linarith)
    have hv' : 0 ≤ 17 / 50 / v := by positivity
    nlinarith
  have hla : -(1 / 2) * (La + (681 / 2000 - x) / a - 1) ≤ -(1 / 2) * Real.log (681 / 2000 - x) := by
    have := log_le_tangent (show (0 : ℝ) < 681 / 2000 - x by linarith) ha
    linarith
  have hlb : -(1 / 2) * (Lb + (681 / 2000 + x) / b - 1) ≤ -(1 / 2) * Real.log (681 / 2000 + x) := by
    have := log_le_tangent (show (0 : ℝ) < 681 / 2000 + x by linarith) hb
    linarith
  have hp2 : (x + 17 / 50) ^ 2 ≤ (q + 17 / 50) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 17 / 50) ^ 3 ≤ (q + 17 / 50) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := curvedGauge_ge hx0.le hxr
  have h2 : cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5) x *
        (-(1 / 2) * (La + (681 / 2000 - x) / a - 1) - 1 / 2 * (Lb + (681 / 2000 + x) / b - 1) -
          241517 / 100000 - 1 / 4000 - (q + 17 / 50) ^ 2 / 48 - 5 * (q + 17 / 50) ^ 3 / 192 -
          471 / 20000) ≤
      cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5) x *
        (-(1 / 2) * Real.log (681 / 2000 - x) - 1 / 2 * Real.log (681 / 2000 + x) - κ - 1 / 4000 -
          (x + 17 / 50) ^ 2 / 48 - 5 * (x + 17 / 50) ^ 3 / 192 - 471 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold curvedOddNumerator
  linarith

/-- **Monotone form of the numerator.** On `[p, q] ⊆ [7/100, 17/50]`, with upper bound `Lℓ` for the
window ratio at `p` and lower bound `Llam` for `−½ log(R² − p²)`. -/
theorem curvedOddNumerator_ge_monotone {κ x p q Lℓ Llam : ℝ} (hp : 7 / 100 ≤ p) (hpx : p ≤ x)
    (hxq : x ≤ q) (hq : q ≤ 17 / 50)
    (hLℓ : Real.log (p + 17 / 50) - Real.log p ≤ Lℓ)
    (hLlam : Llam ≤ -(1 / 2) * Real.log ((681 / 2000) ^ 2 - p ^ 2)) (hκ : κ ≤ 241517 / 100000) :
    (1 / 500 - x ^ 2) * Lℓ +
        cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5) x *
          (Llam - 241517 / 100000 - 1 / 4000 - (q + 17 / 50) ^ 2 / 48 - 5 * (q + 17 / 50) ^ 3 / 192 -
            471 / 20000) +
        (12617 / 12500 * x - 3 / 2 * x ^ 2 - 11 / 5 * x ^ 3) - 3 / 5 * surplusRemainder (17 / 50) x ≤
      curvedOddNumerator κ x := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 < x := by linarith
  have hxr : x ≤ 17 / 50 := le_trans hxq hq
  have hℓ : Real.log (x + 17 / 50) - Real.log x ≤ Lℓ := by
    rw [← Real.log_div (by linarith) hx0.ne']
    rw [← Real.log_div (by linarith) hp0.ne'] at hLℓ
    refine le_trans (Real.log_le_log (by positivity) ?_) hLℓ
    rw [div_le_div_iff₀ hx0 hp0]; nlinarith
  have hc : 1 / 500 - x ^ 2 ≤ 0 := by nlinarith
  have h1 := mul_le_mul_of_nonpos_left hℓ hc
  have hlam : Llam ≤ -(1 / 2) * Real.log (681 / 2000 - x) - 1 / 2 * Real.log (681 / 2000 + x) := by
    have e : -(1 / 2) * Real.log (681 / 2000 - x) - 1 / 2 * Real.log (681 / 2000 + x) =
        -(1 / 2) * Real.log ((681 / 2000) ^ 2 - x ^ 2) := by
      rw [show (681 / 2000 : ℝ) ^ 2 - x ^ 2 = (681 / 2000 - x) * (681 / 2000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hmono : Real.log ((681 / 2000) ^ 2 - x ^ 2) ≤ Real.log ((681 / 2000) ^ 2 - p ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    linarith
  have hp2 : (x + 17 / 50) ^ 2 ≤ (q + 17 / 50) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 17 / 50) ^ 3 ≤ (q + 17 / 50) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := curvedGauge_ge hx0.le hxr
  have h2 : cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5) x *
        (Llam - 241517 / 100000 - 1 / 4000 - (q + 17 / 50) ^ 2 / 48 - 5 * (q + 17 / 50) ^ 3 / 192 -
          471 / 20000) ≤
      cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5) x *
        (-(1 / 2) * Real.log (681 / 2000 - x) - 1 / 2 * Real.log (681 / 2000 + x) - κ - 1 / 4000 -
          (x + 17 / 50) ^ 2 / 48 - 5 * (x + 17 / 50) ^ 3 / 192 - 471 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  unfold curvedOddNumerator
  linarith

theorem curvedOddNumerator_nonneg_one {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 7/100 ≤ x)
    (h2 : x ≤ 1/10) : 0 ≤ curvedOddNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ea := log_smooth_div 0 0 0 0 2 0 0 0
  have eb := log_smooth_div 0 1 0 0 0 0 0 1
  norm_num at ea eb
  have hv : Real.log (5) ≤ 1.609438 := by linarith [l5.2]
  have ha : Real.log (1/4) ≤ -1.386294 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (3/7) ≤ -0.847297 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (curvedOddNumerator_ge_tangent (p := 7/100) (q := 1/10) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold cubicGauge surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 17/200)),
    sq_nonneg (x - 17/200), mul_nonneg (sq_nonneg (x - 17/200)) (sq_nonneg (x - 17/200))]

theorem curvedOddNumerator_nonneg_two {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 1/10 ≤ x)
    (h2 : x ≤ 13/100) : 0 ≤ curvedOddNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 2 0 0 0 0 0 0 0
  have ea := log_smooth_div 0 2 0 0 3 0 1 0
  have eb := log_smooth_div 4 0 0 0 0 0 1 1
  norm_num at ev ea eb
  have hv : Real.log (4) ≤ 1.386295 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (9/40) ≤ -1.491654 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (16/35) ≤ -0.782759 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (curvedOddNumerator_ge_tangent (p := 1/10) (q := 13/100) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold cubicGauge surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 23/200)),
    sq_nonneg (x - 23/200), mul_nonneg (sq_nonneg (x - 23/200)) (sq_nonneg (x - 23/200))]

theorem curvedOddNumerator_nonneg_three {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 13/100 ≤ x)
    (h2 : x ≤ 4/25) : 0 ≤ curvedOddNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 1 0 1 0 0 1 0 0
  have ea := log_smooth_div 0 0 0 1 2 2 0 0
  have eb := log_smooth_div 0 0 1 1 3 2 0 0
  norm_num at ev ea eb
  have hv : Real.log (10/3) ≤ 1.203973 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (7/36) ≤ -1.637608 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (35/72) ≤ -0.721317 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (curvedOddNumerator_ge_tangent (p := 13/100) (q := 4/25) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold cubicGauge surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 29/200)),
    sq_nonneg (x - 29/200), mul_nonneg (sq_nonneg (x - 29/200)) (sq_nonneg (x - 29/200))]

theorem curvedOddNumerator_nonneg_four {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 4/25 ≤ x)
    (h2 : x ≤ 19/100) : 0 ≤ curvedOddNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ea := log_smooth_div 0 0 0 0 1 1 0 0
  have eb := log_smooth_div 1 2 0 0 0 0 1 1
  norm_num at ea eb
  have hv : Real.log (3) ≤ 1.098613 := by linarith [l3.2]
  have ha : Real.log (1/6) ≤ -1.791759 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (18/35) ≤ -0.664976 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (curvedOddNumerator_ge_tangent (p := 4/25) (q := 19/100) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold cubicGauge surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 7/40)),
    sq_nonneg (x - 7/40), mul_nonneg (sq_nonneg (x - 7/40)) (sq_nonneg (x - 7/40))]

theorem curvedOddNumerator_nonneg_five {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 19/100 ≤ x)
    (h2 : x ≤ 11/50) : 0 ≤ curvedOddNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 3 0 0 0 0 1 0 0
  have ea := log_smooth_div 0 3 0 0 3 0 2 0
  have eb := log_smooth_div 0 0 1 1 6 0 0 0
  norm_num at ev ea eb
  have hv : Real.log (8/3) ≤ 0.980830 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (27/200) ≤ -2.002480 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (35/64) ≤ -0.603534 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (curvedOddNumerator_ge_tangent (p := 19/100) (q := 11/50) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold cubicGauge surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 41/200)),
    sq_nonneg (x - 41/200), mul_nonneg (sq_nonneg (x - 41/200)) (sq_nonneg (x - 41/200))]

theorem curvedOddNumerator_nonneg_six {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 11/50 ≤ x)
    (h2 : x ≤ 6/25) : 0 ≤ curvedOddNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 1 0 1 0 0 0
  have ea := log_smooth_div 0 0 0 1 6 0 0 0
  have eb := log_smooth_div 2 0 0 0 0 0 0 1
  norm_num at ev ea eb
  have hv : Real.log (5/2) ≤ 0.916291 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (7/64) ≤ -2.212972 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (4/7) ≤ -0.559615 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (curvedOddNumerator_ge_tangent (p := 11/50) (q := 6/25) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold cubicGauge surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 23/100)),
    sq_nonneg (x - 23/100), mul_nonneg (sq_nonneg (x - 23/100)) (sq_nonneg (x - 23/100))]

theorem curvedOddNumerator_nonneg_seven {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 6/25 ≤ x)
    (h2 : x ≤ 13/50) : 0 ≤ curvedOddNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 0 1 0 1 0 0
  have ea := log_smooth_div 0 2 0 0 2 0 2 0
  have eb := log_smooth_div 4 0 0 0 0 3 0 0
  norm_num at ev ea eb
  have hv : Real.log (7/3) ≤ 0.847298 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (9/100) ≤ -2.407945 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (16/27) ≤ -0.523247 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (curvedOddNumerator_ge_tangent (p := 6/25) (q := 13/50) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold cubicGauge surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 1/4)),
    sq_nonneg (x - 1/4), mul_nonneg (sq_nonneg (x - 1/4)) (sq_nonneg (x - 1/4))]

theorem curvedOddNumerator_nonneg_eight {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 13/50 ≤ x)
    (h2 : x ≤ 7/25) : 0 ≤ curvedOddNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 2 0 0 2 0 0 0
  have ea := log_smooth_div 0 0 0 1 2 0 2 0
  have eb := log_smooth_div 0 0 0 2 4 0 1 0
  norm_num at ev ea eb
  have hv : Real.log (9/4) ≤ 0.810931 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (7/100) ≤ -2.659259 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (49/80) ≤ -0.490206 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (curvedOddNumerator_ge_tangent (p := 13/50) (q := 7/25) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold cubicGauge surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 27/100)),
    sq_nonneg (x - 27/100), mul_nonneg (sq_nonneg (x - 27/100)) (sq_nonneg (x - 27/100))]

theorem curvedOddNumerator_nonneg_nine {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 7/25 ≤ x)
    (h2 : x ≤ 3/10) : 0 ≤ curvedOddNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 1 1 4 0 0 0
  have ea := log_smooth_div 0 0 0 0 2 0 1 0
  have eb := log_smooth_div 0 2 0 1 2 0 2 0
  norm_num at ev ea eb
  have hv : Real.log (35/16) ≤ 0.782760 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (1/20) ≤ -2.995732 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (63/100) ≤ -0.462035 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (curvedOddNumerator_ge_tangent (p := 7/25) (q := 3/10) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold cubicGauge surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 29/100)),
    sq_nonneg (x - 29/100), mul_nonneg (sq_nonneg (x - 29/100)) (sq_nonneg (x - 29/100))]

theorem curvedOddNumerator_nonneg_ten {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 3/10 ≤ x)
    (h2 : x ≤ 63/200) : 0 ≤ curvedOddNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 1 0 1 1 0 1 0
  have ea := log_smooth_div 0 0 0 0 1 1 1 0
  have eb := log_smooth_div 0 4 0 0 0 0 3 0
  norm_num at ev ea eb
  have hv : Real.log (21/10) ≤ 0.741938 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (1/30) ≤ -3.401197 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (81/125) ≤ -0.433864 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (curvedOddNumerator_ge_tangent (p := 3/10) (q := 63/200) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold cubicGauge surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 123/400)),
    sq_nonneg (x - 123/400), mul_nonneg (sq_nonneg (x - 123/400)) (sq_nonneg (x - 123/400))]

theorem curvedOddNumerator_nonneg_eleven {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 63/200 ≤ x)
    (h2 : x ≤ 13/40) : 0 ≤ curvedOddNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 3 2 0 0 0 0 1 1
  have ea := log_smooth_div 0 0 0 0 1 0 2 0
  have eb := log_smooth_div 1 0 0 0 0 1 0 0
  norm_num at ev ea eb
  have hv : Real.log (72/35) ≤ 0.721319 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (1/50) ≤ -3.912022 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (2/3) ≤ -0.405465 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (curvedOddNumerator_ge_tangent (p := 63/200) (q := 13/40) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold cubicGauge surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 8/25)),
    sq_nonneg (x - 8/25), mul_nonneg (sq_nonneg (x - 8/25)) (sq_nonneg (x - 8/25))]

theorem curvedOddNumerator_nonneg_twelve {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 13/40 ≤ x)
    (h2 : x ≤ 33/100) : 0 ≤ curvedOddNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have ev := log_smooth_div 0 0 0 2 3 1 0 0
  have ea := log_smooth_div 0 0 0 0 4 0 1 0
  have eb := log_smooth_div 1 0 0 0 0 1 0 0
  norm_num at ev ea eb
  have hv : Real.log (49/24) ≤ 0.713767 := by rw [ev]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have ha : Real.log (1/80) ≤ -4.382026 := by rw [ea]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  have hb : Real.log (2/3) ≤ -0.405465 := by rw [eb]; linarith [l3.1, l3.2, l5.1, l5.2, l7.1, l7.2]
  refine le_trans ?_ (curvedOddNumerator_ge_tangent (p := 13/40) (q := 33/100) (by norm_num) h1 h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv ha hb hκ)
  unfold cubicGauge surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 131/400)),
    sq_nonneg (x - 131/400), mul_nonneg (sq_nonneg (x - 131/400)) (sq_nonneg (x - 131/400))]

/-- The numerator near the origin, `0 < x ≤ 11/250`: the coefficient `1/500 − x²` is positive and
`ℓ ≥ log 8`. -/
theorem curvedOddNumerator_nonneg_origin {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 0 < x)
    (h2 : x ≤ 11 / 250) : 0 ≤ curvedOddNumerator κ x := by
  have l3 := log_three_bounds
  have l2a := Real.log_two_gt_d9
  have hxr : x ≤ 17 / 50 := by linarith
  have hℓ : 207 / 100 ≤ Real.log (x + 17 / 50) - Real.log x := by
    rw [← Real.log_div (by linarith) h1.ne']
    have h8 : Real.log 8 ≤ Real.log ((x + 17 / 50) / x) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ h1]; linarith)
    have e8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith
  have hlam : 1077112 / 1000000 ≤
      -(1 / 2) * Real.log (681 / 2000 - x) - 1 / 2 * Real.log (681 / 2000 + x) := by
    have e : -(1 / 2) * Real.log (681 / 2000 - x) - 1 / 2 * Real.log (681 / 2000 + x) =
        -(1 / 2) * Real.log ((681 / 2000) ^ 2 - x ^ 2) := by
      rw [show (681 / 2000 : ℝ) ^ 2 - x ^ 2 = (681 / 2000 - x) * (681 / 2000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hm : Real.log ((681 / 2000) ^ 2 - x ^ 2) ≤ Real.log ((681 / 2000) ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have hR : Real.log ((681 / 2000 : ℝ) ^ 2) = 2 * Real.log (681 / 2000) := by
      rw [Real.log_pow]; norm_num
    have ht := log_le_tangent (show (0 : ℝ) < 681 / 2000 by norm_num) (show (0 : ℝ) < 1 / 3 by norm_num)
    have e3 : Real.log (1 / 3) = -Real.log 3 := by rw [one_div, Real.log_inv]
    rw [e3] at ht
    norm_num at ht
    linarith
  have hc : 0 ≤ 1 / 500 - x ^ 2 := by nlinarith
  have hp2 : (x + 17 / 50) ^ 2 ≤ (11 / 250 + 17 / 50) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 17 / 50) ^ 3 ≤ (11 / 250 + 17 / 50) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := curvedGauge_ge h1.le hxr
  have hA : (1 / 500 - x ^ 2) * (207 / 100) ≤ (1 / 500 - x ^ 2) * (Real.log (x + 17 / 50) - Real.log x) :=
    mul_le_mul_of_nonneg_left hℓ hc
  have hB : cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5) x *
        (1077112 / 1000000 - 241517 / 100000 - 1 / 4000 - (11 / 250 + 17 / 50) ^ 2 / 48 -
          5 * (11 / 250 + 17 / 50) ^ 3 / 192 - 471 / 20000) ≤
      cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5) x *
        (-(1 / 2) * Real.log (681 / 2000 - x) - 1 / 2 * Real.log (681 / 2000 + x) - κ - 1 / 4000 -
          (x + 17 / 50) ^ 2 / 48 - 5 * (x + 17 / 50) ^ 3 / 192 - 471 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hpoly : 0 ≤ (1 / 500 - x ^ 2) * (207 / 100) + cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5) x *
        (1077112 / 1000000 - 241517 / 100000 - 1 / 4000 - (11 / 250 + 17 / 50) ^ 2 / 48 -
          5 * (11 / 250 + 17 / 50) ^ 3 / 192 - 471 / 20000) +
      (12617 / 12500 * x - 3 / 2 * x ^ 2 - 11 / 5 * x ^ 3) - 3 / 5 * surplusRemainder (17 / 50) x := by
    unfold cubicGauge surplusRemainder
    nlinarith [mul_nonneg h1.le (sub_nonneg.2 h2), sq_nonneg x, mul_nonneg (mul_nonneg h1.le h1.le)
      (sub_nonneg.2 h2)]
  unfold curvedOddNumerator
  linarith

/-- The numerator on `[11/250, 7/100]`: `ℓ` between its values at the endpoints. -/
theorem curvedOddNumerator_nonneg_collar {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 11 / 250 ≤ x)
    (h2 : x ≤ 7 / 100) : 0 ≤ curvedOddNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hx0 : 0 < x := by linarith
  have hxr : x ≤ 17 / 50 := by linarith
  have hℓ : Real.log (x + 17 / 50) - Real.log x = Real.log (1 + 17 / 50 / x) := by
    rw [← Real.log_div (by linarith) hx0.ne']
    congr 1; field_simp
  -- `ℓ(x) ≥ ℓ(7/100) = log(41/7) ≥ log 6 + 1 − 42/41`
  have hlow : 1767369 / 1000000 ≤ Real.log (x + 17 / 50) - Real.log x := by
    rw [hℓ]
    have hq : (17 / 50 : ℝ) / (7 / 100) ≤ 17 / 50 / x := div_le_div_of_nonneg_left (by norm_num) hx0 h2
    have hm : Real.log (41 / 7) ≤ Real.log (1 + 17 / 50 / x) :=
      Real.log_le_log (by norm_num) (by norm_num at hq ⊢; linarith)
    have ht := log_ge_tangent (show (0 : ℝ) < 41 / 7 by norm_num) (show (0 : ℝ) < 6 by norm_num)
    have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    norm_num at ht
    linarith
  -- `ℓ(x) ≤ ℓ(11/250) = log(96/11) ≤ log 8 + 1/11`
  have hup : Real.log (x + 17 / 50) - Real.log x ≤ 2170351 / 1000000 := by
    rw [hℓ]
    have hq : (17 / 50 : ℝ) / x ≤ 17 / 50 / (11 / 250) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1
    have hm : Real.log (1 + 17 / 50 / x) ≤ Real.log (96 / 11) :=
      Real.log_le_log (by positivity) (by norm_num at hq ⊢; linarith)
    have ht := log_le_tangent (show (0 : ℝ) < 96 / 11 by norm_num) (show (0 : ℝ) < 8 by norm_num)
    have e8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    norm_num at ht
    linarith
  -- `λ(x) ≥ λ(11/250)`
  have hlam : 1085715 / 1000000 ≤
      -(1 / 2) * Real.log (681 / 2000 - x) - 1 / 2 * Real.log (681 / 2000 + x) := by
    have e : -(1 / 2) * Real.log (681 / 2000 - x) - 1 / 2 * Real.log (681 / 2000 + x) =
        -(1 / 2) * Real.log ((681 / 2000) ^ 2 - x ^ 2) := by
      rw [show (681 / 2000 : ℝ) ^ 2 - x ^ 2 = (681 / 2000 - x) * (681 / 2000 + x) by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [e]
    have hm : Real.log ((681 / 2000) ^ 2 - x ^ 2) ≤ Real.log ((681 / 2000) ^ 2 - (11 / 250) ^ 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have ht := log_le_tangent (show (0 : ℝ) < (681 / 2000) ^ 2 - (11 / 250) ^ 2 by norm_num)
      (show (0 : ℝ) < 9 / 80 by norm_num)
    have e := log_smooth_div 0 2 0 0 4 0 1 0
    norm_num at e ht
    rw [e] at ht
    linarith
  have hp2 : (x + 17 / 50) ^ 2 ≤ (7 / 100 + 17 / 50) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp3 : (x + 17 / 50) ^ 3 ≤ (7 / 100 + 17 / 50) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hh := curvedGauge_ge hx0.le hxr
  have hA : 1 / 500 * (1767369 / 1000000) - x ^ 2 * (2170351 / 1000000) ≤
      (1 / 500 - x ^ 2) * (Real.log (x + 17 / 50) - Real.log x) := by
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith [mul_le_mul_of_nonneg_left hup hx2]
  have hB : cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5) x *
        (1085715 / 1000000 - 241517 / 100000 - 1 / 4000 - (7 / 100 + 17 / 50) ^ 2 / 48 -
          5 * (7 / 100 + 17 / 50) ^ 3 / 192 - 471 / 20000) ≤
      cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5) x *
        (-(1 / 2) * Real.log (681 / 2000 - x) - 1 / 2 * Real.log (681 / 2000 + x) - κ - 1 / 4000 -
          (x + 17 / 50) ^ 2 / 48 - 5 * (x + 17 / 50) ^ 3 / 192 - 471 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hpoly : 0 ≤ 1 / 500 * (1767369 / 1000000) - x ^ 2 * (2170351 / 1000000) +
      cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5) x *
        (1085715 / 1000000 - 241517 / 100000 - 1 / 4000 - (7 / 100 + 17 / 50) ^ 2 / 48 -
          5 * (7 / 100 + 17 / 50) ^ 3 / 192 - 471 / 20000) +
      (12617 / 12500 * x - 3 / 2 * x ^ 2 - 11 / 5 * x ^ 3) - 3 / 5 * surplusRemainder (17 / 50) x := by
    unfold cubicGauge surplusRemainder
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
      mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 57 / 1000)),
      sq_nonneg (x - 57 / 1000)]
  unfold curvedOddNumerator
  linarith

/-- The numerator on `[33/100, 42/125]`, by monotonicity. -/
theorem curvedOddNumerator_nonneg_edge {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 33 / 100 ≤ x)
    (h2 : x ≤ 42 / 125) : 0 ≤ curvedOddNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (33 / 100 + 17 / 50) - Real.log (33 / 100) ≤ 708299 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (33 / 100 + 17 / 50) / (33 / 100) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2478047 / 1000000 ≤ -(1 / 2) * Real.log ((681 / 2000) ^ 2 - (33 / 100) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (681 / 2000) ^ 2 - (33 / 100) ^ 2 by norm_num)
      (show (0 : ℝ) < 7 / 1000 by norm_num)
    have e := log_smooth_div 0 0 0 1 3 0 3 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  refine le_trans ?_ (curvedOddNumerator_ge_monotone (p := 33 / 100) (q := 42 / 125) (by norm_num)
    h1 h2 (by norm_num) hLℓ hLlam hκ)
  unfold cubicGauge surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 333 / 1000)),
    sq_nonneg (x - 333 / 1000)]

/-- The numerator on `[42/125, 17/50]`, by monotonicity. -/
theorem curvedOddNumerator_nonneg_rim {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (h1 : 42 / 125 ≤ x)
    (h2 : x ≤ 17 / 50) : 0 ≤ curvedOddNumerator κ x := by
  have l3 := log_three_bounds
  have l5 := log_five_bounds
  have l7 := log_seven_bounds
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hLℓ : Real.log (42 / 125 + 17 / 50) - Real.log (42 / 125) ≤ 699100 / 1000000 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have ht := log_le_tangent (show (0 : ℝ) < (42 / 125 + 17 / 50) / (42 / 125) by norm_num)
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    linarith
  have hLlam : 2897196 / 1000000 ≤ -(1 / 2) * Real.log ((681 / 2000) ^ 2 - (42 / 125) ^ 2) := by
    have ht := log_le_tangent (show (0 : ℝ) < (681 / 2000) ^ 2 - (42 / 125) ^ 2 by norm_num)
      (show (0 : ℝ) < 3 / 1000 by norm_num)
    have e := log_smooth_div 0 1 0 0 3 0 3 0
    norm_num at e ht ⊢
    rw [e] at ht
    linarith
  refine le_trans ?_ (curvedOddNumerator_ge_monotone (p := 42 / 125) (q := 17 / 50) (by norm_num)
    h1 h2 (by norm_num) hLℓ hLlam hκ)
  unfold cubicGauge surplusRemainder
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (x - 338 / 1000)),
    sq_nonneg (x - 338 / 1000)]

/-- **The numerator is nonnegative on `(0, 17/50]`.** -/
theorem curvedOddNumerator_nonneg {κ x : ℝ} (hκ : κ ≤ 241517 / 100000) (hx0 : 0 < x)
    (hxr : x ≤ 17 / 50) : 0 ≤ curvedOddNumerator κ x := by
  rcases le_or_gt x (11 / 250) with h | h
  · exact curvedOddNumerator_nonneg_origin hκ hx0 h
  rcases le_or_gt x (7 / 100) with h' | h'
  · exact curvedOddNumerator_nonneg_collar hκ h.le h'
  rcases le_or_gt x (1 / 10) with h1 | h1
  · exact curvedOddNumerator_nonneg_one hκ h'.le h1
  rcases le_or_gt x (13 / 100) with h2 | h2
  · exact curvedOddNumerator_nonneg_two hκ h1.le h2
  rcases le_or_gt x (4 / 25) with h3 | h3
  · exact curvedOddNumerator_nonneg_three hκ h2.le h3
  rcases le_or_gt x (19 / 100) with h4 | h4
  · exact curvedOddNumerator_nonneg_four hκ h3.le h4
  rcases le_or_gt x (11 / 50) with h5 | h5
  · exact curvedOddNumerator_nonneg_five hκ h4.le h5
  rcases le_or_gt x (6 / 25) with h6 | h6
  · exact curvedOddNumerator_nonneg_six hκ h5.le h6
  rcases le_or_gt x (13 / 50) with h7 | h7
  · exact curvedOddNumerator_nonneg_seven hκ h6.le h7
  rcases le_or_gt x (7 / 25) with h8 | h8
  · exact curvedOddNumerator_nonneg_eight hκ h7.le h8
  rcases le_or_gt x (3 / 10) with h9 | h9
  · exact curvedOddNumerator_nonneg_nine hκ h8.le h9
  rcases le_or_gt x (63 / 200) with h10 | h10
  · exact curvedOddNumerator_nonneg_ten hκ h9.le h10
  rcases le_or_gt x (13 / 40) with h11 | h11
  · exact curvedOddNumerator_nonneg_eleven hκ h10.le h11
  rcases le_or_gt x (33 / 100) with h12 | h12
  · exact curvedOddNumerator_nonneg_twelve hκ h11.le h12
  rcases le_or_gt x (42 / 125) with h13 | h13
  · exact curvedOddNumerator_nonneg_edge hκ h12.le h13
  · exact curvedOddNumerator_nonneg_rim hκ h13.le hxr

/-! ### The potential -/

/-- **The curved folded potential on `(0, 17/50]`.** The killing, the surplus potential of the cubic
gauge and the plateau potential of radius `681/2000` add up to at least `471/20000`. -/
theorem curvedOdd_potential_ge {x : ℝ} (hx0 : 0 < x) (hxr : x ≤ 17 / 50) :
    471 / 20000 ≤ 2 * (archLevyAntideriv x - archLevyAntideriv (x + 17 / 50)) +
      surplusPotential (cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5)) (17 / 50) x +
      (archLevyAntideriv (681 / 2000 - x) + archLevyAntideriv (681 / 2000 + x) -
        2 * windowEdgeFunction 0 - 2 * archConstantReal) := by
  have hh := curvedGauge_ge hx0.le hxr
  have hh0 : 0 < cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5) x := by linarith
  have hU := mul_surplusPotential_cubicGauge_ge (1 / 500) (3 / 5) (-1) (-6 / 5) hx0 hxr
    (by norm_num) hh0 fun u v hu0 hur hv0 hvr => curvedGauge_divDiff_le hu0 hur hv0 hvr
  have hΩx := archLevyAntideriv_ge hx0
  have hΩr := archLevyAntideriv_le_expansion (show 0 < x + 17 / 50 by linarith)
  have hΩa := archLevyAntideriv_ge (show 0 < 681 / 2000 - x by linarith)
  have hΩb := archLevyAntideriv_ge (show 0 < 681 / 2000 + x by linarith)
  have hγ := RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have hπ := log_pi_le_11448
  have hl2 := Real.log_two_lt_d9
  have hκ : Real.log 2 + Real.eulerMascheroniConstant + Real.log Real.pi ≤ 241517 / 100000 := by
    linarith
  have hN := curvedOddNumerator_nonneg hκ hx0 hxr
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have e1 : Real.log (x / 4) = Real.log x - 2 * Real.log 2 := by
    rw [Real.log_div hx0.ne' (by norm_num), l4]
  have e2 : Real.log ((x + 17 / 50) / 4) = Real.log (x + 17 / 50) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  have e3 : Real.log ((681 / 2000 - x) / 4) = Real.log (681 / 2000 - x) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  have e4 : Real.log ((681 / 2000 + x) / 4) = Real.log (681 / 2000 + x) - 2 * Real.log 2 := by
    rw [Real.log_div (by linarith) (by norm_num), l4]
  rw [e1] at hΩx
  rw [e2] at hΩr
  rw [e3] at hΩa
  rw [e4] at hΩb
  rw [windowEdgeFunction_zero]
  unfold archConstantReal
  set V : ℝ := (Real.log (x + 17 / 50) - Real.log x) +
    (-(1 / 2) * Real.log (681 / 2000 - x) - 1 / 2 * Real.log (681 / 2000 + x)) -
    (Real.log 2 + Real.eulerMascheroniConstant + Real.log Real.pi) - 1 / 4000 -
    (x + 17 / 50) ^ 2 / 48 - 5 * (x + 17 / 50) ^ 3 / 192 with hV
  set U := surplusPotential (cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5)) (17 / 50) x with hUdef
  have hkey : cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5) x * (V - 471 / 20000) +
      (cubicSurplusMain (3 / 5) (-1) (-6 / 5) (17 / 50) x - 3 / 5 * surplusRemainder (17 / 50) x) =
        curvedOddNumerator (Real.log 2 + Real.eulerMascheroniConstant + Real.log Real.pi) x := by
    rw [hV]; unfold curvedOddNumerator cubicSurplusMain cubicGauge; ring
  have hVU : 471 / 20000 ≤ V + U := by
    have h1 : cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5) x * (471 / 20000) ≤
        cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5) x * (V + U) := by nlinarith
    exact le_of_mul_le_mul_left h1 hh0
  have hW : V + U ≤ 2 * (archLevyAntideriv x - archLevyAntideriv (x + 17 / 50)) + U +
      (archLevyAntideriv (681 / 2000 - x) + archLevyAntideriv (681 / 2000 + x) -
        2 * (3 / 2 * Real.log 2 + Real.pi / 4) -
        2 * ((Real.eulerMascheroniConstant + Real.log Real.pi) / 2)) := by
    rw [hV]; linarith
  linarith

/-! ### Odd-sector positivity on `[−17/50, 17/50]` -/

/-- **Weil positivity of every odd test supported in `[−17/50, 17/50]`.** Every odd `F ∈ C²_c`
vanishing outside `[−17/50, 17/50]` satisfies `Ẑ(F) ≥ (1/100) ∫ F²`. -/
theorem fullZeroForm_ge_of_odd_support_le_curved {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, 17 / 50 < |x| → F x = 0) :
    1 / 100 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  set r : ℝ := 17 / 50 with hrdef
  set R : ℝ := 681 / 2000 with hRdef
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
  have hlog2 : 2 * R < Real.log 2 := by
    have := Real.log_two_gt_d9; rw [hRdef]; linarith
  -- representation, fold with surplus, potential
  have hQ := markovEnergy_eq_gauge_window hF hFc hPd hPcs hP1 hP0 hPB hFM
  have hJ := signedJumpEnergy_eq_arch_of_window (F := F) hPB hlog2
  obtain ⟨hIU, hfold⟩ := fourKilling_add_surplusPotential_le_archJump hPd.continuous hF.continuous
    hPe hodd hP0 hP1 hPB hFB hFL hR0 hR1 (r := r) (by rw [hrdef]; norm_num)
    (by rw [hrdef, hRdef]; norm_num) hPr hFr hPcs (continuous_cubicGauge _ _ _ _)
    (a₀ := 1 / 500) (by norm_num) (fun x hx0 hxr => curvedGauge_ge hx0 hxr) (L := 3 / 5)
    (fun x y hx0 hxr hy0 hyr => by
      rw [cubicGauge_sub, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (curvedGauge_divDiff_le hx0 hxr hy0 hyr) (abs_nonneg _))
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
  have hGe : ∀ x, G (-x) = G x := fun x => by
    simp only [hGdef, hodd, hPe, poleFreeWeilOperator_neg hPe, neg_sq]
  have hF2 : Integrable fun x => F x ^ 2 :=
    (hF.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)
  have hF2e : ∀ x, (fun x => F x ^ 2) (-x) = F x ^ 2 := fun x => by simp only [hodd, neg_sq]
  have hGint := integral_eq_two_mul_Ioi_of_even hGi hGe
  have hF2int := integral_eq_two_mul_Ioi_of_even hF2 hF2e
  have hHi := integrableOn_sq_mul_antideriv_sub hF.continuous hodd hFB hFL hR1
    (r := r) (by rw [hrdef]; norm_num) (by rw [hrdef, hRdef]; norm_num)
  -- pointwise potential on the half line
  set c₀ : ℝ := 471 / 20000 with hc₀
  have hpt : ∀ x ∈ Ioi (0 : ℝ), c₀ * F x ^ 2 ≤
      2 * (F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r))) +
        F x ^ 2 * surplusPotential (cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5)) r x + G x := by
    intro x hx
    have hx0 : 0 < x := hx
    by_cases h : F x = 0
    · simp [hGdef, h]
    · have hxr : x ≤ r := by
        have := hFr x h; rwa [abs_of_pos hx0] at this
      have hxR : |x| < R := by rw [abs_of_pos hx0, hRdef]; rw [hrdef] at hxr; linarith
      have hW' := neg_poleFreeWeilOperator_ge_antideriv hPd.continuous hPL hP1 hPB hlog2 hxR
        (hFM x h)
      have hV := curvedOdd_potential_ge hx0 (by rw [hrdef] at hxr; exact hxr)
      simp only [hGdef, hFM x h, mul_one]
      have hF0 := sq_nonneg (F x)
      rw [hRdef, hrdef] at *
      nlinarith [mul_le_mul_of_nonneg_left hW' hF0, mul_le_mul_of_nonneg_left hV hF0]
  have hsum : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + F x ^ 2 * surplusPotential
        (cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5)) r x + G x) (Ioi 0) :=
    ((hHi.const_mul 2).add hIU).add hGi.integrableOn
  have hH2 : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r)))) (Ioi 0) := hHi.const_mul 2
  have hH2U : IntegrableOn (fun x => 2 * (F x ^ 2 * (archLevyAntideriv x -
      archLevyAntideriv (x + r))) + F x ^ 2 * surplusPotential
        (cubicGauge (1 / 500) (3 / 5) (-1) (-6 / 5)) r x) (Ioi 0) := hH2.add hIU
  have hmono := setIntegral_mono_on (hF2.integrableOn.const_mul c₀) hsum measurableSet_Ioi hpt
  rw [integral_add hH2U hGi.integrableOn, integral_add hH2 hIU, integral_const_mul,
    integral_const_mul] at hmono
  -- the odd pole moment
  have hS := sq_oddPoleMoment_le_cosh hR0.le hF.continuous hFc hPd.continuous hPcs hP0 hP1 hPB hFM
  have hcosh : Real.cosh (R / 2) ^ 2 ≤ 10294335 / 10000000 := by
    have h1 := Real.cosh_le_exp_half_sq (R / 2)
    have h2 : (R / 2) ^ 2 / 2 ≤ 145 / 10000 := by rw [hRdef]; norm_num
    have h3 : Real.exp ((R / 2) ^ 2 / 2) ≤ Real.exp (145 / 10000) := Real.exp_le_exp.mpr h2
    have h4 : Real.exp (145 / 10000) ≤ 101461 / 100000 := by
      have := Real.exp_bound' (show (0 : ℝ) ≤ 145 / 10000 by norm_num)
        (show (145 / 10000 : ℝ) ≤ 1 by norm_num) (show 0 < 3 by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
      norm_num at this ⊢
      linarith
    have h5 : Real.cosh (R / 2) ≤ 101461 / 100000 := by linarith
    have h6 := Real.cosh_pos (R / 2)
    nlinarith
  have hpole : 2 * oddPoleMoment F ^ 2 ≤ 271 / 20000 * ∫ x, F x ^ 2 := by
    have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
    have hR3 : R ^ 3 / 6 * Real.cosh (R / 2) ^ 2 ≤ 271 / 40000 := by
      have : R ^ 3 / 6 = (681 / 2000) ^ 3 / 6 := by rw [hRdef]
      rw [this]
      nlinarith [hcosh]
    nlinarith [mul_le_mul_of_nonneg_right hR3 hI0]
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [hc₀] at hmono
  rw [hZ, hQ, hJ]
  linarith [hfold, hmono, hGint, hF2int, hpole]

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
