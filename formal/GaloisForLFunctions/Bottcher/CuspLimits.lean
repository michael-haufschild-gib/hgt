/-
# Cusp behaviour of the theta nullwerte at `i∞`

The Jacobi quartic defect `F = θ₃⁴ − θ₂⁴ − θ₄⁴` (`QuarticDefect.lean`) is a weight-2 `Γ(2)` form; to
conclude `F ≡ 0` (the quartic identity) one needs its vanishing at the cusps. This file establishes
the `i∞` cusp limits of the nullwerte along the modular-forms cusp filter `comap Complex.im atTop`:

* `tendsto_thetaThree_atImInfty : θ₃ → 1`,
* `tendsto_thetaFour_atImInfty  : θ₄ → 1`,

both from mathlib's one-variable bound `norm_jacobiTheta_sub_one_le` (`θ₄ = θ₃(·+1)`), squeezed by
`tendsto_jacobiTheta_bound` (`2/(1−e^{−πy})·e^{−πy} → 0`). With `θ₂ → 0` (next), `F → 1 − 0 − 1 = 0`
at `i∞`; combined with `quarticDefect_add_one`/`_S` (transport to the other cusps) this leaves the
single absent input "weight-2 `Γ(2)` cusp form is `0`" (`dim S₂(Γ(2)) = 0`).

Consumes `ModularLambda`. Mathlib only otherwise.
-/
import GaloisForLFunctions.Bottcher.ModularLambda
open Complex Filter Topology
open scoped Real
namespace Bottcher

theorem tendsto_exp_neg_pi_im :
    Tendsto (fun τ : ℂ => Real.exp (-π * τ.im)) (comap Complex.im atTop) (𝓝 0) :=
  Real.tendsto_exp_atBot.comp
    (Filter.Tendsto.neg_mul_atTop (by simp [Real.pi_pos] : (-π : ℝ) < 0)
      tendsto_const_nhds tendsto_comap)

theorem tendsto_jacobiTheta_bound :
    Tendsto (fun τ : ℂ => 2 / (1 - Real.exp (-π * τ.im)) * Real.exp (-π * τ.im))
      (comap Complex.im atTop) (𝓝 0) := by
  have hcont : ContinuousAt (fun u : ℝ => 2 / (1 - u) * u) 0 := by
    apply ContinuousAt.mul _ continuousAt_id
    exact ContinuousAt.div continuousAt_const (by fun_prop) (by norm_num)
  have := hcont.tendsto.comp tendsto_exp_neg_pi_im
  simpa only [Function.comp_def, sub_zero, div_one, mul_zero] using this

theorem tendsto_thetaThree_atImInfty :
    Tendsto thetaThree (comap Complex.im atTop) (𝓝 1) := by
  have hsub : Tendsto (fun τ => thetaThree τ - 1) (comap Complex.im atTop) (𝓝 0) := by
    apply squeeze_zero_norm' _ tendsto_jacobiTheta_bound
    filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0:ℝ))] with τ hτ
    rw [thetaThree, ← jacobiTheta_eq_jacobiTheta₂]
    exact norm_jacobiTheta_sub_one_le hτ
  simpa using hsub.add_const 1

theorem tendsto_thetaFour_atImInfty :
    Tendsto thetaFour (comap Complex.im atTop) (𝓝 1) := by
  have hsub : Tendsto (fun τ => thetaFour τ - 1) (comap Complex.im atTop) (𝓝 0) := by
    apply squeeze_zero_norm' _ tendsto_jacobiTheta_bound
    filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0:ℝ))] with τ hτ
    have hτ1 : 0 < (τ + 1).im := by simpa using hτ
    rw [← thetaThree_add_one, thetaThree, ← jacobiTheta_eq_jacobiTheta₂]
    have := norm_jacobiTheta_sub_one_le hτ1
    simpa using this
  simpa using hsub.add_const 1

end Bottcher


namespace Bottcher

theorem summable_exp_neg_half (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℤ => Real.exp (-π * ((n : ℝ) ^ (2 : ℕ) + n) * y)) := by
  apply Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) ?_
    (summable_pow_mul_jacobiTheta₂_term_bound (y / 2) hy 0)
  intro n
  rw [pow_zero, one_mul]
  apply Real.exp_le_exp.mpr
  have hz : (0 : ℤ) ≤ |n| + n := by linarith [neg_abs_le n]
  have h : (0 : ℝ) ≤ ((|n| : ℤ) : ℝ) + (n : ℝ) := by exact_mod_cast hz
  nlinarith [mul_nonneg (mul_pos Real.pi_pos hy).le h]

theorem quad_nonneg (n : ℤ) : (0 : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) + n := by
  have hq : (0 : ℤ) ≤ n ^ (2 : ℕ) + n := by
    by_cases h : 0 ≤ n
    · nlinarith [mul_nonneg h h]
    · push Not at h
      nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ -n) (by omega : (0:ℤ) ≤ -(n+1))]
  exact_mod_cast hq

theorem norm_thetaTwo_le {τ : ℂ} (hτ : 0 < τ.im) :
    ‖thetaTwo τ‖ ≤ Real.exp (-π * τ.im / 4) * ∑' n : ℤ, Real.exp (-π * ((n : ℝ) ^ (2 : ℕ) + n) * τ.im) := by
  unfold thetaTwo
  rw [norm_mul]
  have hpf : ‖Complex.exp ((Real.pi : ℂ) * I * τ / 4)‖ = Real.exp (-π * τ.im / 4) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_im, Complex.mul_re]
  rw [hpf]
  have hsummN : Summable (fun n : ℤ => ‖jacobiTheta₂_term n (τ / 2) τ‖) := by
    simp only [norm_jacobiTheta₂_half_term]; exact summable_exp_neg_half τ.im hτ
  have hbound : ‖jacobiTheta₂ (τ / 2) τ‖ ≤ ∑' n : ℤ, Real.exp (-π * ((n : ℝ) ^ (2 : ℕ) + n) * τ.im) := by
    rw [jacobiTheta₂]
    refine (norm_tsum_le_tsum_norm hsummN).trans ?_
    rw [tsum_congr (fun n => norm_jacobiTheta₂_half_term τ n)]
  gcongr

theorem tendsto_exp_neg_pi_im_div4 :
    Tendsto (fun τ : ℂ => Real.exp (-π * τ.im / 4)) (comap Complex.im atTop) (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  have heq : (fun τ : ℂ => -π * τ.im / 4) = fun τ : ℂ => (-π / 4) * τ.im := by funext τ; ring
  rw [heq]
  exact Filter.Tendsto.neg_mul_atTop (by have := Real.pi_pos; linarith : (-π / 4 : ℝ) < 0)
    tendsto_const_nhds tendsto_comap

theorem tendsto_thetaTwo_atImInfty :
    Tendsto thetaTwo (comap Complex.im atTop) (𝓝 0) := by
  have hb : ∀ᶠ τ : ℂ in comap Complex.im atTop,
      ‖thetaTwo τ‖ ≤ Real.exp (-π * τ.im / 4) * ∑' n : ℤ, Real.exp (-π * ((n : ℝ) ^ (2 : ℕ) + n)) := by
    filter_upwards [tendsto_comap.eventually (eventually_ge_atTop (1:ℝ))] with τ hτ
    refine (norm_thetaTwo_le (by linarith : 0 < τ.im)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply Summable.tsum_mono (summable_exp_neg_half τ.im (by linarith))
      (by simpa using summable_exp_neg_half 1 (by norm_num))
    intro n
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (quad_nonneg n))
      (by linarith : (0:ℝ) ≤ τ.im - 1)]
  have htend : Tendsto
      (fun τ : ℂ => Real.exp (-π * τ.im / 4) * ∑' n : ℤ, Real.exp (-π * ((n : ℝ) ^ (2 : ℕ) + n)))
      (comap Complex.im atTop) (𝓝 0) := by
    have h := tendsto_exp_neg_pi_im_div4.mul_const (∑' n : ℤ, Real.exp (-π * ((n : ℝ) ^ (2 : ℕ) + n)))
    simpa using h
  exact squeeze_zero_norm' hb htend

end Bottcher
