import Mathlib

/-!
# The integral `∫_0^∞ {x}²/x² dx = log 2π - γ`

On `(0, 1)` the integrand is `1`; on `(n, n+1)` it is `(x - n)²/x²` with antiderivative
`x - 2n log x - n²/x`, so `∫_n^{n+1} = 2 - 1/(n+1) - 2n (log(n+1) - log n)`.  Summing,
`∫_0^N {x}²/x² dx = 2N - H_N - 2N log N + 2 log N!`, which equals
`2 log s_N + log 2 - (H_N - log N)` for the Stirling sequence `s_N = N!/(√(2N)(N/e)^N)`.
Stirling's formula `s_N → √π` and `H_N - log N → γ` give the limit `log 2π - γ`.
-/

open Real MeasureTheory Set Filter Topology intervalIntegral

namespace RHTower

noncomputable section

/-- The integrand `{x}²/x²`. -/
def fractSqDiv (x : ℝ) : ℝ := Int.fract x ^ 2 / x ^ 2

theorem fractSqDiv_nonneg (x : ℝ) : 0 ≤ fractSqDiv x := by
  unfold fractSqDiv; positivity

theorem fractSqDiv_le {x : ℝ} (hx : 0 < x) : fractSqDiv x ≤ 2 * (1 + x ^ 2)⁻¹ := by
  unfold fractSqDiv
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  have h2 : Int.fract x ≤ x := by
    have := Int.floor_nonneg.mpr hx.le
    unfold Int.fract
    have : (0 : ℝ) ≤ (⌊x⌋ : ℝ) := by exact_mod_cast this
    linarith
  have hsq1 : Int.fract x ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ h0 h2 2
  have hsq2 : Int.fract x ^ 2 ≤ 1 := by nlinarith
  rw [show 2 * (1 + x ^ 2)⁻¹ = 2 / (1 + x ^ 2) by ring,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem measurable_fractSqDiv : Measurable fractSqDiv :=
  (measurable_fract.pow_const 2).div (measurable_id.pow_const 2)

theorem integrableOn_fractSqDiv_Ioi : IntegrableOn fractSqDiv (Ioi 0) := by
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul 2).integrableOn)
    measurable_fractSqDiv.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun x hx => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (fractSqDiv_nonneg x)]
  exact fractSqDiv_le hx

theorem intervalIntegrable_fractSqDiv {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable fractSqDiv volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact integrableOn_fractSqDiv_Ioi.mono_set fun x hx => lt_of_le_of_lt ha hx.1

theorem integral_fractSqDiv_zero_one : ∫ x in (0 : ℝ)..1, fractSqDiv x = 1 := by
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by rw [ae_iff]; simp
  have h : ∫ x in (0 : ℝ)..1, fractSqDiv x = ∫ x in (0 : ℝ)..1, (1 : ℝ) := by
    refine integral_congr_ae (hae.mono fun x hx hmem => ?_)
    rw [uIoc_of_le zero_le_one] at hmem
    have hx1 : x < 1 := lt_of_le_of_ne hmem.2 hx
    unfold fractSqDiv
    rw [Int.fract_eq_self.mpr ⟨hmem.1.le, hx1⟩, div_self (pow_ne_zero 2 hmem.1.ne')]
  rw [h]
  simp

/-- `∫_n^{n+1} {x}²/x² dx = 2 - 1/(n+1) - 2n (log(n+1) - log n)` for `n ≥ 1`. -/
theorem integral_fractSqDiv_succ {n : ℕ} (hn : 1 ≤ n) :
    ∫ x in (n : ℝ)..(n + 1), fractSqDiv x
      = 2 - 1 / ((n : ℝ) + 1) - 2 * n * (Real.log ((n : ℝ) + 1) - Real.log n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (n : ℝ) + 1 := by rw [ae_iff]; simp
  have h : ∫ x in (n : ℝ)..(n + 1), fractSqDiv x
      = ∫ x in (n : ℝ)..(n + 1), (1 - 2 * n / x + (n : ℝ) ^ 2 / x ^ 2) := by
    refine integral_congr_ae (hae.mono fun x hx hmem => ?_)
    rw [uIoc_of_le (by linarith)] at hmem
    have hx1 : x < (n : ℝ) + 1 := lt_of_le_of_ne hmem.2 hx
    have hxpos : 0 < x := lt_trans hn0 hmem.1
    have hfr : Int.fract x = x - n := by
      rw [Int.fract, show ⌊x⌋ = (n : ℤ) by
        rw [Int.floor_eq_iff]; push_cast; exact ⟨hmem.1.le, hx1⟩]
      push_cast; ring
    unfold fractSqDiv
    rw [hfr]
    field_simp
    ring
  rw [h]
  have hderiv : ∀ x ∈ uIcc (n : ℝ) (n + 1), HasDerivAt
      (fun x : ℝ => x - 2 * n * Real.log x - (n : ℝ) ^ 2 / x)
      (1 - 2 * n / x + (n : ℝ) ^ 2 / x ^ 2) x := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have hxpos : 0 < x := lt_of_lt_of_le hn0 hx.1
    have h1 : HasDerivAt (fun y : ℝ => y - 2 * n * Real.log y - (n : ℝ) ^ 2 * y⁻¹)
        (1 - 2 * n * x⁻¹ - (n : ℝ) ^ 2 * (-(x ^ 2)⁻¹)) x :=
      ((hasDerivAt_id' x).sub
        ((Real.hasDerivAt_log hxpos.ne').const_mul (2 * (n : ℝ)))).sub
        ((hasDerivAt_inv hxpos.ne').const_mul ((n : ℝ) ^ 2))
    have e1 : (fun y : ℝ => y - 2 * n * Real.log y - (n : ℝ) ^ 2 / y)
        = (fun y : ℝ => y - 2 * n * Real.log y - (n : ℝ) ^ 2 * y⁻¹) := by
      funext y; ring
    rw [e1]
    refine h1.congr_deriv ?_
    field_simp
    ring
  have hcont : ContinuousOn (fun x : ℝ => 1 - 2 * n / x + (n : ℝ) ^ 2 / x ^ 2)
      (uIcc (n : ℝ) (n + 1)) := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have hxpos : 0 < x := lt_of_lt_of_le hn0 hx.1
    exact (by fun_prop (disch := positivity) : ContinuousAt
      (fun x : ℝ => 1 - 2 * n / x + (n : ℝ) ^ 2 / x ^ 2) x).continuousWithinAt
  rw [integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  field_simp
  ring

/-- The closed form of the partial integrals. -/
theorem integral_fractSqDiv_zero_nat {N : ℕ} (hN : 1 ≤ N) :
    ∫ x in (0 : ℝ)..N, fractSqDiv x
      = 2 * N - (harmonic N : ℝ) - 2 * N * Real.log N + 2 * Real.log (N.factorial : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => simp [integral_fractSqDiv_zero_one]; norm_num
  | succ m hm ih =>
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [← integral_add_adjacent_intervals (b := (m : ℝ))
      (intervalIntegrable_fractSqDiv le_rfl (by positivity))
      (intervalIntegrable_fractSqDiv (by positivity) (by push_cast; linarith)), ih]
    push_cast
    rw [integral_fractSqDiv_succ hm, harmonic_succ, Nat.factorial_succ]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
    field_simp
    ring

/-- **`∫_0^∞ {x}²/x² dx = log 2π - γ`.** -/
theorem integral_fractSqDiv_Ioi :
    ∫ x in Ioi (0 : ℝ), fractSqDiv x = Real.log (2 * π) - eulerMascheroniConstant := by
  have hlim := intervalIntegral_tendsto_integral_Ioi (μ := volume) 0 integrableOn_fractSqDiv_Ioi
    tendsto_natCast_atTop_atTop
  have hst := Stirling.tendsto_stirlingSeq_sqrt_pi
  have hlogst : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n)) atTop
      (𝓝 (Real.log √π)) :=
    (Real.continuousAt_log (by positivity)).tendsto.comp hst
  have hS : Tendsto (fun n : ℕ => 2 * Real.log (Stirling.stirlingSeq n) + Real.log 2
      - ((harmonic n : ℝ) - Real.log n)) atTop
      (𝓝 (2 * Real.log √π + Real.log 2 - eulerMascheroniConstant)) :=
    ((hlogst.const_mul 2).add_const _).sub Real.tendsto_harmonic_sub_log
  have heq : ∀ᶠ n : ℕ in atTop, ∫ x in (0 : ℝ)..(n : ℝ), fractSqDiv x
      = 2 * Real.log (Stirling.stirlingSeq n) + Real.log 2 - ((harmonic n : ℝ) - Real.log n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [integral_fractSqDiv_zero_nat hn, Stirling.log_stirlingSeq_formula,
      Real.log_div hn0.ne' (Real.exp_pos 1).ne', Real.log_exp,
      Real.log_mul (by norm_num) hn0.ne']
    ring
  have hval : 2 * Real.log √π + Real.log 2 - eulerMascheroniConstant
      = Real.log (2 * π) - eulerMascheroniConstant := by
    rw [Real.log_sqrt Real.pi_pos.le, Real.log_mul (by norm_num) Real.pi_pos.ne']
    ring
  rw [← hval]
  exact tendsto_nhds_unique hlim (hS.congr' (heq.mono fun n hn => hn.symm))

end

end RHTower
