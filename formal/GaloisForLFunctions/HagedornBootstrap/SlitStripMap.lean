import GaloisForLFunctions.HagedornBootstrap.BootstrapSlope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The slit strip and its conformal map

The bootstrap potential lives on the strip `|Im b| < 1/2` slit along `|Re b| ≥ x*`. The map

  `b(z) = (1/2π) log((z − 1)/(z(z + 1)))`

sends the upper half-plane onto the slit strip. This file proves the boundary arithmetic of
`r(z) = (z − 1)/(z(z + 1))`:

* the vacuum preimages `√2 − 1 = tan(π/8)` and `−1 − √2` have `r = −1`, so `b(√2 − 1) = i/2`;
* the tips: `r(1 − √2) = (1 + √2)²` and `r(1 + √2) = (√2 − 1)²`, so `b(1 ∓ √2) = ±x*`;
* the tips are the critical points: `r'/r = −(z² − 2z − 1)/(z(z − 1)(z + 1))`;
* folding: on `(−1, 0)`, `r ≥ (1 + √2)²` with equality only at the tip, so the interval covers
  the right slit `[x*, ∞)` twice; on `(1, ∞)`, `r ≤ (√2 − 1)²`; on `(0, 1)` and `(−∞, −1)`,
  `r < 0` (the edges `Im b = ±1/2`);
* preimages: `r(z) = w` iff `w z² + (w − 1) z + 1 = 0`.
-/

noncomputable section

open Real

namespace GaloisForLFunctions.HagedornBootstrap

/-- The rational part of the slit-strip map. -/
def slitRatio {K : Type*} [Field K] (z : K) : K := (z - 1) / (z * (z + 1))

theorem sqrt_two_sq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem one_lt_sqrt_two : 1 < √2 := by
  rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem sqrt_two_lt_two : √2 < 2 := by
  rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- The vacuum preimage: `r(√2 − 1) = −1`. -/
theorem slitRatio_vacuum : slitRatio (√2 - 1) = -1 := by
  have h := sqrt_two_sq
  have h1 : (√2 - 1) * (√2 - 1 + 1) ≠ 0 := by
    rw [show √2 - 1 + 1 = √2 by ring]; nlinarith [one_lt_sqrt_two]
  unfold slitRatio
  rw [div_eq_iff h1]
  nlinarith

/-- The mirror vacuum preimage: `r(−1 − √2) = −1`. -/
theorem slitRatio_vacuum' : slitRatio (-1 - √2) = -1 := by
  have h := sqrt_two_sq
  have h1 : (-1 - √2) * (-1 - √2 + 1) ≠ 0 := by
    rw [show -1 - √2 + 1 = -√2 by ring]; nlinarith [one_lt_sqrt_two]
  unfold slitRatio
  rw [div_eq_iff h1]
  nlinarith

/-- The right tip: `r(1 − √2) = (1 + √2)²`. -/
theorem slitRatio_rightTip : slitRatio (1 - √2) = (1 + √2) ^ 2 := by
  have h := sqrt_two_sq
  have h1 : (1 - √2) * (1 - √2 + 1) ≠ 0 := by
    apply mul_ne_zero <;> nlinarith [one_lt_sqrt_two, sqrt_two_lt_two]
  unfold slitRatio
  rw [div_eq_iff h1]
  nlinarith

/-- The left tip: `r(1 + √2) = (√2 − 1)²`. -/
theorem slitRatio_leftTip : slitRatio (1 + √2) = (√2 - 1) ^ 2 := by
  have h := sqrt_two_sq
  have h1 : (1 + √2) * (1 + √2 + 1) ≠ 0 := by
    have := Real.sqrt_nonneg 2; positivity
  unfold slitRatio
  rw [div_eq_iff h1]
  nlinarith

/-- `b(1 − √2) = x*`: the right tip of the slit strip. -/
theorem slitMap_rightTip : Real.log (slitRatio (1 - √2)) / (2 * π) = bootstrapTip := by
  rw [slitRatio_rightTip, Real.log_pow, bootstrapTip, Real.arsinh]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  norm_num
  field_simp

/-- `b(1 + √2) = −x*`: the left tip. -/
theorem slitMap_leftTip : Real.log (slitRatio (1 + √2)) / (2 * π) = -bootstrapTip := by
  have hinv : √2 - 1 = (1 + √2)⁻¹ := eq_inv_of_mul_eq_one_left (by nlinarith [sqrt_two_sq])
  rw [slitRatio_leftTip, hinv, inv_pow, Real.log_inv, neg_div, ← slitRatio_rightTip,
    slitMap_rightTip]

/-- The vacuum: `b(√2 − 1) = i/2`. -/
theorem slitMap_vacuum :
    Complex.log ((slitRatio (√2 - 1) : ℝ) : ℂ) / (2 * π) = Complex.I / 2 := by
  rw [slitRatio_vacuum]
  push_cast
  rw [Complex.log_neg_one]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- The vacuum preimage is the eighth-turn point `tan(π/8) = √2 − 1`. -/
theorem tan_pi_div_eight : Real.tan (π / 8) = √2 - 1 := by
  rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_eight, Real.cos_pi_div_eight]
  have h2 := sqrt_two_sq
  have hp : 0 < 2 + √2 := by positivity
  have hm : 0 < 2 - √2 := by linarith [sqrt_two_lt_two]
  rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [div_eq_iff (Real.sqrt_pos.mpr hp).ne']
  -- `√(2 − √2) = (√2 − 1)√(2 + √2)`: both sides are nonnegative with equal squares
  have hnn : 0 ≤ (√2 - 1) * √(2 + √2) := by
    have := one_lt_sqrt_two; have := Real.sqrt_nonneg (2 + √2)
    exact mul_nonneg (by linarith) this
  rw [← Real.sqrt_sq hnn, mul_pow, Real.sq_sqrt hp.le]
  congr 1
  nlinarith

theorem slitRatio_tan_pi_div_eight : slitRatio (Real.tan (π / 8)) = -1 := by
  rw [tan_pi_div_eight, slitRatio_vacuum]

/-- The logarithmic derivative of `r`; its zeros `1 ± √2` are the slit tips. -/
theorem slitRatio_logDeriv {z : ℝ} (h0 : z ≠ 0) (h1 : z - 1 ≠ 0) (h2 : z + 1 ≠ 0) :
    1 / (z - 1) - 1 / z - 1 / (z + 1) = -(z ^ 2 - 2 * z - 1) / (z * (z - 1) * (z + 1)) := by
  field_simp
  ring

theorem tip_quadratic (z : ℝ) : z ^ 2 - 2 * z - 1 = (z - (1 + √2)) * (z - (1 - √2)) := by
  nlinarith [sqrt_two_sq]

/-- **Folding at the right tip.** On `(−1, 0)`, `r(σ) − (1 + √2)² = −(3 + 2√2)(σ − (1 − √2))²/(σ(σ+1)) ≥ 0`. -/
theorem slitRatio_sub_rightTip {σ : ℝ} (h0 : σ ≠ 0) (h1 : σ + 1 ≠ 0) :
    slitRatio σ - (1 + √2) ^ 2 = -((3 + 2 * √2) * (σ - (1 - √2)) ^ 2) / (σ * (σ + 1)) := by
  unfold slitRatio
  rw [div_sub' (mul_ne_zero h0 h1)]
  congr 1
  linear_combination (-1 + 3 * σ - σ ^ 2 + 2 * √2) * sqrt_two_sq

theorem rightTip_le_slitRatio {σ : ℝ} (h1 : -1 < σ) (h0 : σ < 0) : (1 + √2) ^ 2 ≤ slitRatio σ := by
  have hs := slitRatio_sub_rightTip h0.ne (by linarith)
  have hden : σ * (σ + 1) < 0 := mul_neg_of_neg_of_pos h0 (by linarith)
  have hnum : 0 ≤ (3 + 2 * √2) * (σ - (1 - √2)) ^ 2 := by
    have := Real.sqrt_nonneg 2; positivity
  have : 0 ≤ -((3 + 2 * √2) * (σ - (1 - √2)) ^ 2) / (σ * (σ + 1)) :=
    div_nonneg_of_nonpos (by linarith) hden.le
  linarith

/-- On `(−1, 0)` the map stays on the right slit: `b(σ) ≥ x*`. -/
theorem bootstrapTip_le_slitMap {σ : ℝ} (h1 : -1 < σ) (h0 : σ < 0) :
    bootstrapTip ≤ Real.log (slitRatio σ) / (2 * π) := by
  rw [← slitMap_rightTip]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [slitRatio_rightTip]
  exact Real.log_le_log (by positivity) (rightTip_le_slitRatio h1 h0)

/-- **Folding at the left tip.** On `(1, ∞)`, `r(σ) ≤ (√2 − 1)²`. -/
theorem slitRatio_le_leftTip {σ : ℝ} (h1 : 1 < σ) : slitRatio σ ≤ (√2 - 1) ^ 2 := by
  have h2 := sqrt_two_sq
  have hden : 0 < σ * (σ + 1) := by positivity
  unfold slitRatio
  rw [div_le_iff₀ hden]
  nlinarith [sq_nonneg (σ - (1 + √2)), mul_nonneg (show (0 : ℝ) ≤ 3 - 2 * √2 by nlinarith)
    (sq_nonneg (σ - (1 + √2)))]

/-- The edges: on `(0, 1)` and `(−∞, −1)` the ratio is negative, so `Im b = ±1/2`. -/
theorem slitRatio_neg_of_mem_edges {σ : ℝ} (h : (0 < σ ∧ σ < 1) ∨ σ < -1) : slitRatio σ < 0 := by
  unfold slitRatio
  rcases h with ⟨h0, h1⟩ | h
  · exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  · exact div_neg_of_neg_of_pos (by linarith) (by nlinarith)

/-- **Preimages:** `r(z) = w` iff `w z² + (w − 1) z + 1 = 0`. -/
theorem slitRatio_eq_iff {K : Type*} [Field K] {z w : K} (h0 : z ≠ 0) (h1 : z + 1 ≠ 0) :
    slitRatio z = w ↔ w * z ^ 2 + (w - 1) * z + 1 = 0 := by
  unfold slitRatio
  rw [div_eq_iff (mul_ne_zero h0 h1)]
  constructor <;> intro h <;> linear_combination (-1 : K) * h

end GaloisForLFunctions.HagedornBootstrap
