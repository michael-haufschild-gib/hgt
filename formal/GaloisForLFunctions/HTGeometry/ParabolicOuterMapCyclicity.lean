import GaloisForLFunctions.HTGeometry.HardyTwoCyclicity
import GaloisForLFunctions.HTGeometry.ParabolicOrbitFamilyIndependence

/-!
# The bounded outer map of a Herglotz function is cyclic in `H²`

The exponent `sigma = (m - i)/(m + i)` of a Herglotz function maps the half-plane into the unit disc,
so `O = exp (sigma o cayley)` satisfies `exp (-1) < ‖O‖ < exp 1` on the disc: both `O` and `1/O` are
bounded.  Multiplication by such a factor is an invertible bounded operator on `H²`, hence `O` is
cyclic — the polynomial multiples of `O` are dense.

This is the cyclicity half of the card's first item, and it needs no outer-function theory: the
classical route through Beurling's theorem is replaced by invertibility.
-/

open MeasureTheory Complex Filter Topology Set
open scoped Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m : ℂ → ℂ}

theorem herglotzSigma_eq_cayleyToDisc (z : ℂ) : herglotzSigma m z = cayleyToDisc (m z) := rfl

theorem norm_herglotzSigma_lt_one (hmPos : ∀ z : ℂ, 0 < z.im → 0 < (m z).im) {z : ℂ}
    (hz : 0 < z.im) : ‖herglotzSigma m z‖ < 1 := by
  rw [herglotzSigma_eq_cayleyToDisc]
  exact norm_cayleyToDisc_lt_one (hmPos z hz)

private theorem analyticAt_cayleyToUpper {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    AnalyticAt ℂ cayleyToUpper w := by
  have hw1 : ‖w‖ < 1 := by
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact hw
  have hden : (1 : ℂ) - w ≠ 0 := by
    intro hcon
    have hweq : w = 1 := by linear_combination -hcon
    rw [hweq] at hw1
    simp at hw1
  have h1 : AnalyticAt ℂ (fun w : ℂ => Complex.I * (1 + w)) w :=
    analyticAt_const.mul (analyticAt_const.add analyticAt_id)
  have h2 : AnalyticAt ℂ (fun w : ℂ => 1 - w) w := analyticAt_const.sub analyticAt_id
  exact h1.div h2 hden

theorem analyticOnNhd_herglotzSigma (hmA : AnalyticOnNhd ℂ m {z : ℂ | 0 < z.im})
    (hmPos : ∀ z : ℂ, 0 < z.im → 0 < (m z).im) :
    AnalyticOnNhd ℂ (herglotzSigma m) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hden : m z + Complex.I ≠ 0 := add_I_ne_zero_of_im_pos (hmPos z hz)
  exact (hmA z hz).sub analyticAt_const |>.div ((hmA z hz).add analyticAt_const) hden

/-- The outer orbit map is analytic on the disc. -/
theorem analyticOnNhd_outerOrbitMap (hmA : AnalyticOnNhd ℂ m {z : ℂ | 0 < z.im})
    (hmPos : ∀ z : ℂ, 0 < z.im → 0 < (m z).im) :
    AnalyticOnNhd ℂ (outerOrbitMap m) (Metric.ball 0 1) := by
  intro w hw
  have hw1 : ‖w‖ < 1 := by
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact hw
  have hmem : cayleyToUpper w ∈ {z : ℂ | 0 < z.im} := im_cayleyToUpper_pos hw1
  have hcomp : AnalyticAt ℂ (fun w => herglotzSigma m (cayleyToUpper w)) w :=
    (analyticOnNhd_herglotzSigma hmA hmPos _ hmem).comp (analyticAt_cayleyToUpper hw)
  exact hcomp.cexp

theorem outerOrbitMap_ne_zero (w : ℂ) : outerOrbitMap m w ≠ 0 :=
  Complex.exp_ne_zero _

/-- **Equation (9).**  On the disc the outer orbit map and its reciprocal are bounded by `exp 1`. -/
theorem norm_outerOrbitMap_le (hmPos : ∀ z : ℂ, 0 < z.im → 0 < (m z).im) {w : ℂ}
    (hw : w ∈ Metric.ball (0 : ℂ) 1) : ‖outerOrbitMap m w‖ ≤ Real.exp 1 := by
  have hw1 : ‖w‖ < 1 := by
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact hw
  have hmem : 0 < (cayleyToUpper w).im := im_cayleyToUpper_pos hw1
  have hlt := norm_herglotzSigma_lt_one hmPos hmem
  have hre : (herglotzSigma m (cayleyToUpper w)).re ≤ 1 :=
    le_trans (Complex.re_le_norm _) hlt.le
  rw [outerOrbitMap, Complex.norm_exp]
  exact Real.exp_le_exp.mpr hre

theorem norm_inv_outerOrbitMap_le (hmPos : ∀ z : ℂ, 0 < z.im → 0 < (m z).im) {w : ℂ}
    (hw : w ∈ Metric.ball (0 : ℂ) 1) : ‖(outerOrbitMap m w)⁻¹‖ ≤ Real.exp 1 := by
  have hw1 : ‖w‖ < 1 := by
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact hw
  have hmem : 0 < (cayleyToUpper w).im := im_cayleyToUpper_pos hw1
  have hlt := norm_herglotzSigma_lt_one hmPos hmem
  have hre : -(herglotzSigma m (cayleyToUpper w)).re ≤ 1 := by
    have habs : |(herglotzSigma m (cayleyToUpper w)).re| ≤ ‖herglotzSigma m (cayleyToUpper w)‖ :=
      Complex.abs_re_le_norm _
    have := abs_le.mp habs
    linarith [this.1, hlt.le]
  rw [outerOrbitMap, ← Complex.exp_neg, Complex.norm_exp, Complex.neg_re]
  exact Real.exp_le_exp.mpr hre

theorem normSq_outerOrbitMap_le (hmPos : ∀ z : ℂ, 0 < z.im → 0 < (m z).im) {w : ℂ}
    (hw : w ∈ Metric.ball (0 : ℂ) 1) : ‖outerOrbitMap m w‖ ^ 2 ≤ Real.exp 1 ^ 2 := by
  refine pow_le_pow_left₀ (norm_nonneg _) (norm_outerOrbitMap_le hmPos hw) 2

theorem normSq_inv_outerOrbitMap_le (hmPos : ∀ z : ℂ, 0 < z.im → 0 < (m z).im) {w : ℂ}
    (hw : w ∈ Metric.ball (0 : ℂ) 1) : ‖(outerOrbitMap m w)⁻¹‖ ^ 2 ≤ Real.exp 1 ^ 2 := by
  refine pow_le_pow_left₀ (norm_nonneg _) (norm_inv_outerOrbitMap_le hmPos hw) 2

/-- **The outer orbit map is cyclic in `H²`.**  Its polynomial multiples approximate every `H²`
function in the coefficient norm. -/
theorem tendsto_tsum_normSq_coeff_sub_polynomial_mul_outerOrbitMap
    (hmA : AnalyticOnNhd ℂ m {z : ℂ | 0 < z.im}) (hmPos : ∀ z : ℂ, 0 < z.im → 0 < (m z).im)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    {R₀ : NNReal} (hR₀0 : 0 < R₀) (hR₀1 : (R₀ : ℝ) < 1)
    (hfsum : Summable fun k => ‖(cauchyPowerSeries f 0 R₀).coeff k‖ ^ 2) :
    Tendsto (fun N => ∑' k, ‖(cauchyPowerSeries
        (fun z => f z - Polynomial.eval z
          (hardyApproxPoly (fun z => f z / outerOrbitMap m z) R₀ N) * outerOrbitMap m z)
        0 R₀).coeff k‖ ^ 2) atTop (𝓝 0) :=
  tendsto_tsum_normSq_coeff_sub_polynomial_mul (analyticOnNhd_outerOrbitMap hmA hmPos) hf
    (fun z _ => outerOrbitMap_ne_zero z) (by positivity)
    (fun z hz => normSq_outerOrbitMap_le hmPos hz) (by positivity)
    (fun z hz => normSq_inv_outerOrbitMap_le hmPos hz) hR₀0 hR₀1 hfsum

end

end GaloisForLFunctions.HTGeometry
