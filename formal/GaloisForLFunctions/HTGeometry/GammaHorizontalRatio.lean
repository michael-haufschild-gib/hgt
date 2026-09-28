import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The Gamma modulus along a horizontal line

For `a > 0` and real `b`, the Gauss product gives
`Γ(a)/|Γ(a + ib)| = ∏_{j ≥ 0} (1 + b²/(a+j)²)^{1/2}`. Comparing the logarithmic sum with
`∫_a^∞ log(1 + b²/y²) dy = 2|b| arctan(|b|/a) - a log(1 + b²/a²)` yields the explicit bound

```text
Γ(a) ≤ |Γ(a + ib)| · exp[(1 - a)/2 · log(1 + b²/a²) + |b| arctan(|b|/a)],
```

with no Stirling asymptotics. For `a ≥ 1` the exponent is at most `|b| arctan(|b|/a)`.
-/

open Complex Filter Topology Set

namespace HTGeometry

noncomputable section

/-- The primitive `G(y) = y log(1 + b²/y²) + 2|b| arctan(y/|b|)` of `log(1 + b²/y²)`. -/
def gammaRatioPrimitive (b y : ℝ) : ℝ :=
  y * Real.log (1 + b ^ 2 / y ^ 2) + 2 * |b| * Real.arctan (y / |b|)

theorem hasDerivAt_gammaRatioPrimitive {b y : ℝ} (hb : b ≠ 0) (hy : 0 < y) :
    HasDerivAt (gammaRatioPrimitive b) (Real.log (1 + b ^ 2 / y ^ 2)) y := by
  have hb' : 0 < |b| := abs_pos.mpr hb
  have hbb : |b| ^ 2 = b ^ 2 := sq_abs b
  have h1 : HasDerivAt (fun y : ℝ => 1 + b ^ 2 / y ^ 2) (-(2 * b ^ 2 / y ^ 3)) y := by
    have := ((hasDerivAt_const y (b ^ 2)).div (hasDerivAt_pow 2 y)
      (pow_ne_zero 2 hy.ne')).const_add 1
    refine this.congr_deriv ?_
    norm_num
    field_simp
  have hpos : 0 < 1 + b ^ 2 / y ^ 2 := by positivity
  have h2 := (hasDerivAt_id y).mul (h1.log hpos.ne')
  have h3 := ((Real.hasDerivAt_arctan (y / |b|)).comp y
    ((hasDerivAt_id y).div_const |b|)).const_mul (2 * |b|)
  refine (h2.add h3).congr_deriv ?_
  simp only [id]
  have hy2 : (y / |b|) ^ 2 = y ^ 2 / b ^ 2 := by rw [div_pow, hbb]
  rw [hy2]
  field_simp
  ring

theorem log_one_add_sq_div_nonneg (b y : ℝ) : 0 ≤ Real.log (1 + b ^ 2 / y ^ 2) :=
  Real.log_nonneg (by have : 0 ≤ b ^ 2 / y ^ 2 := by positivity
                      linarith)

theorem antitoneOn_log_one_add_sq_div (b : ℝ) :
    AntitoneOn (fun y : ℝ => Real.log (1 + b ^ 2 / y ^ 2)) (Ioi 0) := by
  intro x hx y hy hxy
  simp only [mem_Ioi] at hx hy
  refine Real.log_le_log (by positivity) ?_
  have : b ^ 2 / y ^ 2 ≤ b ^ 2 / x ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg b) (by positivity) (pow_le_pow_left₀ hx.le hxy 2)
  linarith

theorem integral_log_one_add_sq_div_eq {a b A : ℝ} (hb : b ≠ 0) (ha : 0 < a) (hA : a ≤ A) :
    ∫ y in a..A, Real.log (1 + b ^ 2 / y ^ 2) =
      gammaRatioPrimitive b A - gammaRatioPrimitive b a := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => ?_) ?_
  · rw [uIcc_of_le hA] at hy
    exact hasDerivAt_gammaRatioPrimitive hb (ha.trans_le hy.1)
  · refine ContinuousOn.intervalIntegrable fun y hy => ?_
    rw [uIcc_of_le hA] at hy
    have hy0 : 0 < y := ha.trans_le hy.1
    have hc : ContinuousAt (fun y : ℝ => 1 + b ^ 2 / y ^ 2) y :=
      continuousAt_const.add (continuousAt_const.div (continuousAt_id.pow 2)
        (pow_ne_zero 2 hy0.ne'))
    exact (hc.log (by positivity)).continuousWithinAt

theorem tendsto_gammaRatioPrimitive {b : ℝ} (hb : b ≠ 0) :
    Tendsto (gammaRatioPrimitive b) atTop (𝓝 (Real.pi * |b|)) := by
  have hb' : 0 < |b| := abs_pos.mpr hb
  have h1 : Tendsto (fun y : ℝ => y * Real.log (1 + b ^ 2 / y ^ 2)) atTop (𝓝 0) := by
    have hup : Tendsto (fun y : ℝ => b ^ 2 / y) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero' ?_ ?_ hup
    · filter_upwards [eventually_gt_atTop 0] with y hy
      exact mul_nonneg hy.le (log_one_add_sq_div_nonneg b y)
    · filter_upwards [eventually_gt_atTop 0] with y hy
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + b ^ 2 / y ^ 2 by positivity)
      calc y * Real.log (1 + b ^ 2 / y ^ 2) ≤ y * (b ^ 2 / y ^ 2) :=
            mul_le_mul_of_nonneg_left (by linarith) hy.le
        _ = b ^ 2 / y := by field_simp
  have h2 : Tendsto (fun y : ℝ => 2 * |b| * Real.arctan (y / |b|)) atTop
      (𝓝 (2 * |b| * (Real.pi / 2))) :=
    ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (tendsto_id.atTop_div_const hb')).const_mul _
  have := h1.add h2
  rw [zero_add, show 2 * |b| * (Real.pi / 2) = Real.pi * |b| by ring] at this
  exact this

theorem gammaRatioPrimitive_le {b A : ℝ} (hb : b ≠ 0) (hA : 0 < A) :
    gammaRatioPrimitive b A ≤ Real.pi * |b| := by
  refine ge_of_tendsto (tendsto_gammaRatioPrimitive hb) ?_
  filter_upwards [eventually_ge_atTop A] with A' hA'
  have := integral_log_one_add_sq_div_eq hb hA hA'
  have hnn : 0 ≤ ∫ y in A..A', Real.log (1 + b ^ 2 / y ^ 2) :=
    intervalIntegral.integral_nonneg hA' fun y _ => log_one_add_sq_div_nonneg b y
  linarith

/-- `∫_a^A log(1 + b²/y²) dy ≤ 2|b| arctan(|b|/a) - a log(1 + b²/a²)` for `0 < a ≤ A`. -/
theorem integral_log_one_add_sq_div_le {a b A : ℝ} (ha : 0 < a) (hA : a ≤ A) :
    ∫ y in a..A, Real.log (1 + b ^ 2 / y ^ 2) ≤
      2 * |b| * Real.arctan (|b| / a) - a * Real.log (1 + b ^ 2 / a ^ 2) := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hb' : 0 < |b| := abs_pos.mpr hb
  rw [integral_log_one_add_sq_div_eq hb ha hA]
  have h1 := gammaRatioPrimitive_le hb (ha.trans_le hA)
  have h2 := Real.arctan_inv_of_pos (show 0 < a / |b| by positivity)
  rw [inv_div] at h2
  simp only [gammaRatioPrimitive] at h1 ⊢
  rw [h2]
  linarith

/-- The Gamma horizontal ratio exponent
`B(a, b) = (1 - a)/2 · log(1 + b²/a²) + |b| arctan(|b|/a)`. -/
def gammaRatioBound (a b : ℝ) : ℝ :=
  (1 - a) / 2 * Real.log (1 + b ^ 2 / a ^ 2) + |b| * Real.arctan (|b| / a)

theorem norm_ofReal_add_mul_I_eq_mul_sqrt (x b : ℝ) (hx : 0 < x) :
    ‖(x : ℂ) + b * I‖ = x * Real.sqrt (1 + b ^ 2 / x ^ 2) := by
  rw [Complex.norm_add_mul_I, show x ^ 2 + b ^ 2 = x ^ 2 * (1 + b ^ 2 / x ^ 2) by field_simp,
    Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx.le]

/-- The finite Euler product: `|Γ_n(a + ib)| · ∏_{j ≤ n} (1 + b²/(a+j)²)^{1/2} = Γ_n(a)`. -/
theorem norm_GammaSeq_mul_prod {a : ℝ} (ha : 0 < a) (b : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖GammaSeq ((a : ℂ) + b * I) n‖ *
        ∏ j ∈ Finset.range (n + 1), Real.sqrt (1 + b ^ 2 / (a + j) ^ 2) =
      ‖GammaSeq (a : ℂ) n‖ := by
  have hj : ∀ j : ℕ, 0 < a + j := fun j => by positivity
  have hprod1 : ‖∏ j ∈ Finset.range (n + 1), ((a : ℂ) + b * I + j)‖ =
      (∏ j ∈ Finset.range (n + 1), (a + j)) *
        ∏ j ∈ Finset.range (n + 1), Real.sqrt (1 + b ^ 2 / (a + j) ^ 2) := by
    rw [norm_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [show (a : ℂ) + b * I + j = ((a + j : ℝ) : ℂ) + b * I by push_cast; ring,
      norm_ofReal_add_mul_I_eq_mul_sqrt _ _ (hj j)]
  have hprod2 : ‖∏ j ∈ Finset.range (n + 1), ((a : ℂ) + j)‖ = ∏ j ∈ Finset.range (n + 1), (a + j) := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [show (a : ℂ) + j = ((a + j : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (hj j).le]
  have hP : 0 < ∏ j ∈ Finset.range (n + 1), (a + j) := Finset.prod_pos fun j _ => hj j
  have hQ : 0 < ∏ j ∈ Finset.range (n + 1), Real.sqrt (1 + b ^ 2 / (a + j) ^ 2) :=
    Finset.prod_pos fun j _ => Real.sqrt_pos.mpr (by positivity)
  simp only [GammaSeq, norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos hn, hprod1, hprod2,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero]
  field_simp
  simp only [add_zero, zero_mul, sub_self]
  ring

/-- `∏_{j ≤ n} (1 + b²/(a+j)²)^{1/2} ≤ exp B(a, b)` for every `n`. -/
theorem prod_sqrt_le_exp_gammaRatioBound {a : ℝ} (ha : 0 < a) (b : ℝ) (n : ℕ) :
    ∏ j ∈ Finset.range (n + 1), Real.sqrt (1 + b ^ 2 / (a + j) ^ 2) ≤
      Real.exp (gammaRatioBound a b) := by
  have hpos : ∀ j : ℕ, 0 < Real.sqrt (1 + b ^ 2 / (a + j) ^ 2) := fun j =>
    Real.sqrt_pos.mpr (by positivity)
  rw [← Real.exp_log (Finset.prod_pos fun j _ => hpos j), Real.exp_le_exp,
    Real.log_prod (fun j _ => (hpos j).ne')]
  have hsq : ∀ j : ℕ, Real.log (Real.sqrt (1 + b ^ 2 / (a + j) ^ 2)) =
      Real.log (1 + b ^ 2 / (a + j) ^ 2) / 2 := by
    intro j
    rw [Real.log_sqrt (by positivity)]
  simp only [hsq]
  rw [Finset.sum_range_succ', ← Finset.sum_div]
  have hanti : AntitoneOn (fun y : ℝ => Real.log (1 + b ^ 2 / y ^ 2)) (Icc a (a + n)) :=
    (antitoneOn_log_one_add_sq_div b).mono fun y hy => ha.trans_le hy.1
  have hsum := hanti.sum_le_integral
  have hint := integral_log_one_add_sq_div_le (b := b) ha (show a ≤ a + n by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  have hsum' : ∑ i ∈ Finset.range n, Real.log (1 + b ^ 2 / (a + ↑(i + 1)) ^ 2) ≤
      2 * |b| * Real.arctan (|b| / a) - a * Real.log (1 + b ^ 2 / a ^ 2) := hsum.trans hint
  simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one] at hsum' ⊢
  rw [gammaRatioBound]
  have : ∑ i ∈ Finset.range n, Real.log (1 + b ^ 2 / (a + (↑i + 1)) ^ 2) ≤
      2 * |b| * Real.arctan (|b| / a) - a * Real.log (1 + b ^ 2 / a ^ 2) := hsum'
  linarith

/-- **The Gamma horizontal ratio bound.** For `a > 0` and real `b`,
`Γ(a) ≤ |Γ(a + ib)| · exp[(1 - a)/2 · log(1 + b²/a²) + |b| arctan(|b|/a)]`. -/
theorem Gamma_le_norm_Gamma_mul_exp {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.Gamma a ≤ ‖Complex.Gamma ((a : ℂ) + b * I)‖ * Real.exp (gammaRatioBound a b) := by
  have h1 : Tendsto (fun n => ‖GammaSeq (a : ℂ) n‖) atTop (𝓝 ‖Complex.Gamma (a : ℂ)‖) :=
    (Complex.GammaSeq_tendsto_Gamma _).norm
  have h2 : Tendsto (fun n => ‖GammaSeq ((a : ℂ) + b * I) n‖ * Real.exp (gammaRatioBound a b))
      atTop (𝓝 (‖Complex.Gamma ((a : ℂ) + b * I)‖ * Real.exp (gammaRatioBound a b))) :=
    (Complex.GammaSeq_tendsto_Gamma _).norm.mul_const _
  rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_of_nonneg (Real.Gamma_pos_of_pos ha).le]
    at h1
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [← norm_GammaSeq_mul_prod ha b hn]
  exact mul_le_mul_of_nonneg_left (prod_sqrt_le_exp_gammaRatioBound ha b n) (norm_nonneg _)

theorem gammaRatioBound_le {a b : ℝ} (ha : 1 ≤ a) :
    gammaRatioBound a b ≤ |b| * Real.arctan (|b| / a) := by
  have := log_one_add_sq_div_nonneg b a
  have h : (1 - a) / 2 * Real.log (1 + b ^ 2 / a ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) this
  rw [gammaRatioBound]; linarith

end

end HTGeometry
