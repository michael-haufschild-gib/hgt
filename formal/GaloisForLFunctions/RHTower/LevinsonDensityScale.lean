import Mathlib

/-!
# Lower-order comparisons against the scale `T log T`

Levinson's density passage compares every term of the window inequality against the natural scale
`T log T`.  This file isolates the two elementary comparisons that occur: a polynomial-in-`log T`
plus linear-in-`T` expression is `o(T log T)`, and the scale is stable under a unit shift of the
height.
-/

open Filter Topology

namespace RHTower

theorem eventually_log_le_mul {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, Real.log T ≤ η * T := by
  have h := Real.isLittleO_log_id_atTop.def hη
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with T hT hT1
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hT
  have h1 : Real.log T ≤ |Real.log T| := le_abs_self _
  have h2 : |(id T)| = T := by simpa using abs_of_nonneg (by linarith : (0 : ℝ) ≤ T)
  simp only [id_eq] at hT h2
  rw [h2] at hT
  linarith

/-- Every fixed combination of `1`, `log T`, `(log T)²` and `T` is `o(T log T)`. -/
theorem eventually_lower_order_le {a b d e : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, a + b * Real.log T + d * (Real.log T) ^ 2 + e * T
      ≤ η * (T * Real.log T) := by
  have hdlog := eventually_log_le_mul (η := η / (4 * (d + 1))) (by positivity)
  filter_upwards [hdlog, eventually_ge_atTop (Real.exp (4 * e / η + 1)),
    eventually_ge_atTop (4 * a / η + 1), eventually_ge_atTop (4 * b / η + 1),
    eventually_ge_atTop (3 : ℝ)] with T hTd hTe hTa hTb hT3
  have hT0 : (0 : ℝ) < T := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have hexp : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hloge : 4 * e / η ≤ Real.log T := by
    have hle : Real.exp (4 * e / η + 1) ≤ T := hTe
    have hlogle : 4 * e / η + 1 ≤ Real.log T := by
      rw [← Real.log_exp (4 * e / η + 1)]
      exact Real.log_le_log (Real.exp_pos _) hle
    linarith
  have h1 : a ≤ (η / 4) * (T * Real.log T) := by
    have hTa' : 4 * a / η ≤ T := by linarith
    have hmul : 4 * a ≤ η * T := by
      rw [div_le_iff₀ hη] at hTa'
      linarith
    nlinarith [hlog1, hη, hT0]
  have h2 : b * Real.log T ≤ (η / 4) * (T * Real.log T) := by
    have hTb' : 4 * b / η ≤ T := by linarith
    have hmul : 4 * b ≤ η * T := by
      rw [div_le_iff₀ hη] at hTb'
      linarith
    nlinarith [hlog1, hη, hT0]
  have h3 : d * (Real.log T) ^ 2 ≤ (η / 4) * (T * Real.log T) := by
    have hstep : d * Real.log T ≤ (η / 4) * T := by
      have hdd : (0 : ℝ) < d + 1 := by linarith
      have hmono := mul_le_mul_of_nonneg_left hTd hd
      have hfrac : d / (d + 1) ≤ 1 := by
        rw [div_le_one hdd]; linarith
      have hfrac0 : (0 : ℝ) ≤ d / (d + 1) := by positivity
      have hXnn : (0 : ℝ) ≤ (η / 4) * T := by positivity
      have heq : d * (η / (4 * (d + 1)) * T) = (d / (d + 1)) * ((η / 4) * T) := by
        field_simp
      have hcalc : d * (η / (4 * (d + 1)) * T) ≤ (η / 4) * T := by
        rw [heq]
        nlinarith [hfrac, hfrac0, hXnn]
      linarith
    nlinarith [hlog1, hT0]
  have h4 : e * T ≤ (η / 4) * (T * Real.log T) := by
    have hmul : 4 * e ≤ η * Real.log T := by
      rw [div_le_iff₀ hη] at hloge
      linarith
    nlinarith [hT0]
  linarith

/-- The scale `T log T` is stable under a unit shift of the height. -/
theorem eventually_scale_shift {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ U ∈ Set.Icc T (T + 1),
      U * Real.log U ≤ (1 + η) * (T * Real.log T) := by
  filter_upwards [eventually_lower_order_le (a := 2) (b := 1) (d := 0) (e := 0)
      (by norm_num) le_rfl hη,
    eventually_ge_atTop (3 : ℝ)] with T hTlow hT3 U hU
  have hT0 : (0 : ℝ) < T := by linarith
  have hU0 : (0 : ℝ) < U := by linarith [hU.1]
  have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogU : Real.log U ≤ Real.log (T + 1) := Real.log_le_log hU0 hU.2
  have hsplit : Real.log (T + 1) ≤ Real.log T + 1 / T := by
    have hpos : (0 : ℝ) < (T + 1) / T := by positivity
    have hdiv : Real.log ((T + 1) / T) ≤ (T + 1) / T - 1 :=
      Real.log_le_sub_one_of_pos hpos
    have hval : (T + 1) / T - 1 = 1 / T := by
      field_simp
      ring
    rw [Real.log_div (by linarith) (by linarith)] at hdiv
    rw [hval] at hdiv
    linarith
  have hUlog : U * Real.log U ≤ (T + 1) * (Real.log T + 1 / T) := by
    have h1 : Real.log U ≤ Real.log T + 1 / T := le_trans hlogU hsplit
    have h2 : (0 : ℝ) ≤ Real.log T + 1 / T := by positivity
    calc U * Real.log U ≤ U * (Real.log T + 1 / T) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hU0)
      _ ≤ (T + 1) * (Real.log T + 1 / T) := mul_le_mul_of_nonneg_right hU.2 h2
  have hexp : (T + 1) * (Real.log T + 1 / T)
      = T * Real.log T + (Real.log T + 1 + 1 / T) := by
    field_simp
    ring
  have hinv : 1 / T ≤ 1 := by
    rw [div_le_one hT0]; linarith
  have hlow : Real.log T + 1 + 1 / T ≤ η * (T * Real.log T) := by
    have := hTlow
    norm_num at this
    linarith
  rw [hexp] at hUlog
  linarith

end RHTower
