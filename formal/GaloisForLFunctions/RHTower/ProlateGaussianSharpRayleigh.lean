import GaloisForLFunctions.RHTower.ProlateGaussianTrial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Gaussian trial profile reaches the sharp `O(c)` threshold

The centred Gaussian `v = exp(−cx²/2)` has exact prolate action
`L_c v = (−c + 3cx² − c²x⁴)v`, so its Rayleigh numerator is
`−c ∫ v² + ∫ (3cx² − c²x⁴)e^{−cx²}`.

The correction is positive for a reason that needs no Gaussian moment evaluation: `x³e^{−cx²}` is an
exact primitive of `(3x² − 2cx⁴)e^{−cx²}`, so

`∫_{-1}^{1} (3x² − 2cx⁴)e^{−cx²} = 2e^{−c}` ,

and splitting `3cx² − c²x⁴ = (3c/2)x² + (c/2)(3x² − 2cx⁴)` gives

`∫_{-1}^{1} (3cx² − c²x⁴)e^{−cx²} = (3c/2)∫ x²e^{−cx²} + c e^{−c} > 0` .

Hence `⟨L_c v, v⟩ > −c ‖v‖²` for every positive bandwidth: the Gaussian's separation ratio is below
`1/c`, i.e. its oscillator separation constant `c·s` is below `1`.  This is the sharp scale, an
order of magnitude past the `c²/2` threshold that only sees `s < 1/2`.
-/

open Real MeasureTheory Set

namespace RHTower

/-- `x³e^{−cx²}` is an exact primitive of the quartic Gaussian combination. -/
theorem hasDerivAt_cubeGaussian (c x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 3 * Real.exp (-(c * y ^ 2)))
      ((3 * x ^ 2 - 2 * c * x ^ 4) * Real.exp (-(c * x ^ 2))) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(c * y ^ 2)) (-(c * (2 * x))) x := by
    have h := (hasDerivAt_pow 2 x).const_mul c
    have h2 := h.neg
    refine h2.congr_deriv ?_
    push_cast
    ring
  have he : HasDerivAt (fun y : ℝ => Real.exp (-(c * y ^ 2)))
      (Real.exp (-(c * x ^ 2)) * (-(c * (2 * x)))) x := h1.exp
  have hp : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    have := hasDerivAt_pow 3 x
    refine this.congr_deriv ?_
    push_cast
    ring
  refine (hp.mul he).congr_deriv ?_
  ring

/-- **Exact quartic moment identity.**  The primitive evaluates at the aperture endpoints. -/
theorem integral_quartic_gaussian (c : ℝ) :
    (∫ x in (-1 : ℝ)..1, (3 * x ^ 2 - 2 * c * x ^ 4) * Real.exp (-(c * x ^ 2)))
      = 2 * Real.exp (-c) := by
  have hcont : Continuous fun x : ℝ => (3 * x ^ 2 - 2 * c * x ^ 4) * Real.exp (-(c * x ^ 2)) := by
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ => y ^ 3 * Real.exp (-(c * y ^ 2)))
    (f' := fun x : ℝ => (3 * x ^ 2 - 2 * c * x ^ 4) * Real.exp (-(c * x ^ 2)))
    (a := (-1 : ℝ)) (b := (1 : ℝ)) (fun x _ => hasDerivAt_cubeGaussian c x)
    (hcont.intervalIntegrable _ _)
  rw [hFTC]
  norm_num
  ring

/-- **The Rayleigh correction is positive.** -/
theorem integral_gaussian_correction_pos {c : ℝ} (hc : 0 < c) :
    0 < ∫ x in (-1 : ℝ)..1, (3 * c * x ^ 2 - c ^ 2 * x ^ 4) * Real.exp (-(c * x ^ 2)) := by
  have hsplit : ∀ x : ℝ, (3 * c * x ^ 2 - c ^ 2 * x ^ 4) * Real.exp (-(c * x ^ 2))
      = (3 * c / 2) * (x ^ 2 * Real.exp (-(c * x ^ 2)))
        + (c / 2) * ((3 * x ^ 2 - 2 * c * x ^ 4) * Real.exp (-(c * x ^ 2))) := by
    intro x
    ring
  have hc1 : Continuous fun x : ℝ => x ^ 2 * Real.exp (-(c * x ^ 2)) := by fun_prop
  have hc2 : Continuous fun x : ℝ => (3 * x ^ 2 - 2 * c * x ^ 4) * Real.exp (-(c * x ^ 2)) := by
    fun_prop
  have heq : (∫ x in (-1 : ℝ)..1, (3 * c * x ^ 2 - c ^ 2 * x ^ 4) * Real.exp (-(c * x ^ 2)))
      = (3 * c / 2) * (∫ x in (-1 : ℝ)..1, x ^ 2 * Real.exp (-(c * x ^ 2)))
        + (c / 2) * ∫ x in (-1 : ℝ)..1, (3 * x ^ 2 - 2 * c * x ^ 4) * Real.exp (-(c * x ^ 2)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hc1.const_mul _).intervalIntegrable _ _)
        ((hc2.const_mul _).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun x _ => hsplit x
  rw [heq, integral_quartic_gaussian]
  have hnn : (0 : ℝ) ≤ ∫ x in (-1 : ℝ)..1, x ^ 2 * Real.exp (-(c * x ^ 2)) := by
    refine intervalIntegral.integral_nonneg (by norm_num) fun x _ => ?_
    positivity
  have hexp : (0 : ℝ) < Real.exp (-c) := Real.exp_pos _
  nlinarith

/-- **Sharp Gaussian Rayleigh bound.**  The Gaussian trial profile's prolate Rayleigh numerator
exceeds `−c` times its squared norm, for every positive bandwidth. -/
theorem prolate_gaussian_rayleigh_gt_neg_bandwidth {c : ℝ} (hc : 0 < c) :
    -c * (∫ x in (-1 : ℝ)..1, gaussianTrial c x * gaussianTrial c x)
      < ∫ x in (-1 : ℝ)..1, prolateSLAction c (gaussianTrial c) x * gaussianTrial c x := by
  have hpt : ∀ x : ℝ, prolateSLAction c (gaussianTrial c) x * gaussianTrial c x
      = -c * (gaussianTrial c x * gaussianTrial c x)
        + (3 * c * x ^ 2 - c ^ 2 * x ^ 4) * Real.exp (-(c * x ^ 2)) := by
    intro x
    rw [prolateSLAction_gaussianTrial]
    have hsq : gaussianTrial c x * gaussianTrial c x = Real.exp (-(c * x ^ 2)) :=
      gaussianTrial_sq c x
    rw [mul_assoc, hsq]
    ring
  have hv : Continuous (gaussianTrial c) := continuous_gaussianTrial c
  have hsqc : Continuous fun x : ℝ => gaussianTrial c x * gaussianTrial c x := hv.mul hv
  have hcorr : Continuous fun x : ℝ => (3 * c * x ^ 2 - c ^ 2 * x ^ 4) * Real.exp (-(c * x ^ 2)) := by
    fun_prop
  have heq : (∫ x in (-1 : ℝ)..1, prolateSLAction c (gaussianTrial c) x * gaussianTrial c x)
      = -c * (∫ x in (-1 : ℝ)..1, gaussianTrial c x * gaussianTrial c x)
        + ∫ x in (-1 : ℝ)..1, (3 * c * x ^ 2 - c ^ 2 * x ^ 4) * Real.exp (-(c * x ^ 2)) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hsqc.const_mul _).intervalIntegrable _ _)
        (hcorr.intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun x _ => hpt x
  rw [heq]
  have := integral_gaussian_correction_pos hc
  linarith

end RHTower
