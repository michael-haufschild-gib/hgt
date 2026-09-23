import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric

/-!
# Connes' complex-place fibre integral

Formalization of the complex-place computations of Appendix II of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068,

used there to identify Connes' principal value `∫'` (Theorem V.3) with Weil's `Pfw` at an
archimedean complex place.

* `connes_circle_fiber_integral_of_lt_one`, `connes_circle_fiber_integral_of_one_lt` -
  Appendix II (44).  Integrating `|1 - u|_ℂ^{-1}` over the fibres of the module map
  `ℂ* → ℝ_{>0}` gives `1/(1 - |z|²)` inside the unit disc and `1/(|z|² - 1)` outside it.  The
  interior case is the mean value property of the Herglotz transform `(1 + ζz)/(1 - ζz)` of the
  disc, whose real part is the Poisson kernel; the exterior case follows from the circle reflection
  `‖1 - ζ z‖ = ‖z‖ ‖1 - ζ (conj z)^{-1}‖`.
* `connes_neg_four_integral_log_sin` - Appendix II (53).  The log-sine integral
  `-4 ∫₀^{π/2} log sin u du = 2π log 2` computing the limiting excess area in the
  `j(ε) = 2π log(1/ε) + o(1)` estimate.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open MeasureTheory Metric Complex Real

/-- The Herglotz transform of the disc used in Connes' Appendix II (44). -/
def connesHerglotz (z ζ : ℂ) : ℂ := (1 + ζ * z) / (1 - ζ * z)

theorem connesHerglotz_re {z ζ : ℂ} :
    (connesHerglotz z ζ).re = (1 - ‖ζ * z‖ ^ (2 : ℕ)) / ‖1 - ζ * z‖ ^ (2 : ℕ) := by
  set w : ℂ := ζ * z with hw
  rw [connesHerglotz, ← hw, Complex.div_re, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, zero_sub, zero_add]
  ring

theorem connesHerglotz_ne_zero_denom {z ζ : ℂ} (hz : ‖z‖ < 1) (hζ : ‖ζ‖ ≤ 1) :
    (1 : ℂ) - ζ * z ≠ 0 := by
  intro h
  have h1 : ζ * z = 1 := by linear_combination -h
  have : ‖ζ * z‖ = 1 := by rw [h1]; simp
  rw [norm_mul] at this
  nlinarith [norm_nonneg ζ, norm_nonneg z]

theorem diffContOnCl_connesHerglotz {z : ℂ} (hz : ‖z‖ < 1) :
    DiffContOnCl ℂ (connesHerglotz z) (ball (0 : ℂ) |(1 : ℝ)|) := by
  have habs : |(1 : ℝ)| = 1 := abs_one
  have hden : ∀ ζ ∈ closure (ball (0 : ℂ) |(1 : ℝ)|), (1 : ℂ) - ζ * z ≠ 0 := by
    intro ζ hζ
    rw [habs, closure_ball _ (one_ne_zero)] at hζ
    have : ‖ζ‖ ≤ 1 := by simpa [Complex.dist_eq] using hζ
    exact connesHerglotz_ne_zero_denom hz this
  constructor
  · refine DifferentiableOn.div (by fun_prop) (by fun_prop) ?_
    intro ζ hζ
    exact hden ζ (subset_closure hζ)
  · refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro ζ hζ
    exact hden ζ hζ

/-- **Appendix II (44).**  The fibre integral of `|1 - u|_ℂ^{-1}` over the unit circle, for a point
inside the disc: `(1/2π)∫₀^{2π} dθ / |1 - e^{iθ} z|² = 1/(1 - |z|²)`. -/
theorem connes_circle_fiber_integral_of_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), (‖1 - Complex.exp (θ * Complex.I) * z‖ ^ (2 : ℕ))⁻¹
      = 2 * Real.pi / (1 - ‖z‖ ^ (2 : ℕ)) := by
  have habs : |(1 : ℝ)| = 1 := abs_one
  have hmvp : Real.circleAverage (connesHerglotz z) 0 1 = connesHerglotz z 0 :=
    (diffContOnCl_connesHerglotz hz).circleAverage
  have hci : CircleIntegrable (connesHerglotz z) 0 1 := by
    refine ContinuousOn.circleIntegrable' ?_
    intro ζ hζ
    rw [habs, mem_sphere, Complex.dist_eq, sub_zero] at hζ
    have hden : (1 : ℂ) - ζ * z ≠ 0 := connesHerglotz_ne_zero_denom hz (le_of_eq hζ)
    have hnum : ContinuousAt (fun ζ : ℂ => 1 + ζ * z) ζ := by fun_prop
    have hdenc : ContinuousAt (fun ζ : ℂ => 1 - ζ * z) ζ := by fun_prop
    exact (hnum.div hdenc hden).continuousWithinAt
  have hre := ContinuousLinearMap.circleAverage_comp_comm Complex.reCLM hci
  rw [hmvp] at hre
  have hzero : connesHerglotz z 0 = 1 := by simp [connesHerglotz]
  rw [hzero] at hre
  simp only [Complex.reCLM_apply, Complex.one_re] at hre
  rw [Real.circleAverage_def] at hre
  have hpt : ∀ θ : ℝ, (Complex.reCLM ∘ connesHerglotz z) (circleMap 0 1 θ)
      = (1 - ‖z‖ ^ (2 : ℕ)) * (‖1 - Complex.exp (θ * Complex.I) * z‖ ^ (2 : ℕ))⁻¹ := by
    intro θ
    have hcm : circleMap 0 1 θ = Complex.exp (θ * Complex.I) := by simp [circleMap]
    have hnorm : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
      simp
    simp only [Function.comp_apply, Complex.reCLM_apply, hcm, connesHerglotz_re]
    rw [norm_mul, hnorm, one_mul, div_eq_mul_inv]
  simp only [hpt] at hre
  rw [intervalIntegral.integral_const_mul, smul_eq_mul] at hre
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hzpos : (0:ℝ) < 1 - ‖z‖ ^ (2 : ℕ) := by nlinarith [norm_nonneg z]
  have h2 : (1 - ‖z‖ ^ (2 : ℕ)) * ∫ θ in (0:ℝ)..(2 * Real.pi),
      (‖1 - Complex.exp (θ * Complex.I) * z‖ ^ (2 : ℕ))⁻¹ = 2 * Real.pi := by
    have h : (2 * Real.pi) * ((2 * Real.pi)⁻¹ * ((1 - ‖z‖ ^ (2 : ℕ)) *
        ∫ θ in (0:ℝ)..(2 * Real.pi), (‖1 - Complex.exp (θ * Complex.I) * z‖ ^ (2 : ℕ))⁻¹))
        = (2 * Real.pi) * 1 := by rw [hre]
    rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul, mul_one] at h
    exact h
  rw [eq_div_iff (ne_of_gt hzpos)]
  linear_combination h2

/-- Reflection identity for the circle: for `‖ζ‖ = 1` and `z ≠ 0`,
`‖1 - ζ z‖ = ‖z‖ ‖1 - ζ (conj z)⁻¹‖`. -/
theorem connes_norm_one_sub_mul_reflect {ζ z : ℂ} (hζ : ‖ζ‖ = 1) (hz : z ≠ 0) :
    ‖(1 : ℂ) - ζ * z‖ = ‖z‖ * ‖(1 : ℂ) - ζ * ((starRingEnd ℂ) z)⁻¹‖ := by
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h] at hζ; simp at hζ
  have hcz : (starRingEnd ℂ) z ≠ 0 := by simpa using hz
  have hconjζ : (starRingEnd ℂ) ζ = ζ⁻¹ := by
    have h1 : ζ * (starRingEnd ℂ) ζ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]; norm_num
    field_simp
    linear_combination h1
  have e1 : (starRingEnd ℂ) z * ((1 : ℂ) - ζ * ((starRingEnd ℂ) z)⁻¹)
      = (starRingEnd ℂ) z - ζ := by
    field_simp
  have e2 : ‖z‖ * ‖(1 : ℂ) - ζ * ((starRingEnd ℂ) z)⁻¹‖ = ‖(starRingEnd ℂ) z - ζ‖ := by
    rw [← e1, norm_mul, Complex.norm_conj]
  have e3 : ‖(starRingEnd ℂ) z - ζ‖ = ‖z - ζ⁻¹‖ := by
    have : (starRingEnd ℂ) ((starRingEnd ℂ) z - ζ) = z - ζ⁻¹ := by
      rw [map_sub, Complex.conj_conj, hconjζ]
    rw [← this, Complex.norm_conj]
  have e4 : ‖(1 : ℂ) - ζ * z‖ = ‖z - ζ⁻¹‖ := by
    have hfac : (1 : ℂ) - ζ * z = ζ * (ζ⁻¹ - z) := by field_simp
    rw [hfac, norm_mul, hζ, one_mul, norm_sub_rev]
  rw [e2, e3, e4]

/-- **Appendix II (44), exterior case.**  For a point outside the unit disc,
`(1/2π)∫₀^{2π} dθ / |1 - e^{iθ} z|² = 1/(|z|² - 1)`. -/
theorem connes_circle_fiber_integral_of_one_lt {z : ℂ} (hz : 1 < ‖z‖) :
    ∫ θ in (0:ℝ)..(2 * Real.pi), (‖1 - Complex.exp (θ * Complex.I) * z‖ ^ (2 : ℕ))⁻¹
      = 2 * Real.pi / (‖z‖ ^ (2 : ℕ) - 1) := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz; linarith
  set w : ℂ := ((starRingEnd ℂ) z)⁻¹ with hw
  have hnw : ‖w‖ = ‖z‖⁻¹ := by rw [hw, norm_inv, Complex.norm_conj]
  have hzpos : (0:ℝ) < ‖z‖ := lt_trans one_pos hz
  have hwlt : ‖w‖ < 1 := by
    rw [hnw, inv_lt_one₀ hzpos]; exact hz
  have hpt : ∀ θ : ℝ, (‖1 - Complex.exp (θ * Complex.I) * z‖ ^ (2 : ℕ))⁻¹
      = (‖z‖ ^ (2 : ℕ))⁻¹ * (‖1 - Complex.exp (θ * Complex.I) * w‖ ^ (2 : ℕ))⁻¹ := by
    intro θ
    have hζ : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by simp
    rw [connes_norm_one_sub_mul_reflect hζ hz0, ← hw, mul_pow, mul_inv]
  simp only [hpt]
  rw [intervalIntegral.integral_const_mul, connes_circle_fiber_integral_of_lt_one hwlt, hnw]
  have hz2 : (0:ℝ) < ‖z‖ ^ (2 : ℕ) := by positivity
  have hden : (0:ℝ) < ‖z‖ ^ (2 : ℕ) - 1 := by nlinarith
  field_simp

/-- **Appendix II (53).**  The log-sine integral that fixes the exceptional area in Connes'
comparison of `∫'` with Weil's `Pfw` at a complex place. -/
theorem connes_neg_four_integral_log_sin :
    -4 * ∫ u in (0:ℝ)..(Real.pi / 2), Real.log (Real.sin u) = 2 * Real.pi * Real.log 2 := by
  rw [integral_log_sin_zero_pi_div_two]
  ring


end

end GaloisForLFunctions.RHTower
