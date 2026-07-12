import GaloisForLFunctions.RHTower.CCMCriticalMellinCompletedError

/-!
# Exponential-mode faithfulness of the critical-Mellin Volterra--Haar filter

The completed critical-Mellin adjacent-block observable is a fixed causal Volterra--Haar filter
of the normalized logarithmic Chebyshev error.  This file computes its exact transfer multiplier
on every complex exponential mode and proves that the multiplier has no zero in the open right
half-plane.  Thus the filter cannot censor any positive-growth mode.
-/

open Complex Set MeasureTheory

namespace RHTower

noncomputable section

/-- Equal-scale adjacent-block integral of one complex exponential mode. -/
def exponentialAdjacentBlock (L x : ℝ) (w : ℂ) : ℂ :=
  (∫ h in (x - L)..x, Complex.exp (w * h)) -
    ∫ h in (x - 2 * L)..(x - L), Complex.exp (w * h)

/-- Exact Haar transfer law for an exponential mode. -/
theorem exponentialAdjacentBlock_eq
    {L x : ℝ} {w : ℂ} (hw : w ≠ 0) :
    exponentialAdjacentBlock L x w =
      Complex.exp (w * x) * (1 - Complex.exp (-(w * L))) ^ 2 / w := by
  rw [exponentialAdjacentBlock,
    integral_exp_mul_complex hw,
    integral_exp_mul_complex hw]
  have h1 : Complex.exp (w * (((x - L : ℝ) : ℂ))) =
      Complex.exp (w * x) * Complex.exp (-(w * L)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp (w * (((x - 2 * L : ℝ) : ℂ))) =
      Complex.exp (w * x) * Complex.exp (-(w * L)) ^ 2 := by
    rw [pow_two, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h1, h2]
  field_simp

/-- Transfer multiplier of the error-dependent part of the critical-Mellin Volterra--Haar
observable. -/
def criticalMellinVolterraHaarMultiplier (L : ℝ) (w : ℂ) : ℂ :=
  -((2 * w + 1) * (1 - Complex.exp (-(w * L))) ^ 2) / (2 * w ^ 2)

/-- A positive-width Haar window does not erase a mode with positive real exponent. -/
theorem one_sub_exp_neg_mul_ne_zero
    {L : ℝ} (hL : 0 < L) {w : ℂ} (hw : 0 < w.re) :
    1 - Complex.exp (-(w * L)) ≠ 0 := by
  intro hzero
  have hexp : Complex.exp (-(w * L)) = 1 := (sub_eq_zero.mp hzero).symm
  have hnorm := congrArg norm hexp
  rw [Complex.norm_exp, norm_one] at hnorm
  have hre : (-(w * L)).re = 0 := (Real.exp_eq_one_iff _).mp hnorm
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero] at hre
  nlinarith

/-- **Right-half-plane filter faithfulness.**  The causal Volterra factor and the two equal-scale
Haar differences have no common zero at any positive-growth complex exponent. -/
theorem criticalMellinVolterraHaarMultiplier_ne_zero
    {L : ℝ} (hL : 0 < L) {w : ℂ} (hw : 0 < w.re) :
    criticalMellinVolterraHaarMultiplier L w ≠ 0 := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    norm_num at hw
  have htwo : 2 * w + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hwindow := one_sub_exp_neg_mul_ne_zero hL hw
  rw [criticalMellinVolterraHaarMultiplier]
  exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero htwo (pow_ne_zero 2 hwindow)))
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hw0))

/-- Error-dependent Volterra response to one exponential input mode. -/
def criticalMellinVolterraMode (w : ℂ) (h : ℝ) : ℂ :=
  -Complex.exp (w * h) - (1 / 2 : ℂ) *
    ∫ u in (0 : ℝ)..h, Complex.exp (w * u)

/-- Closed form of the causal Volterra response. -/
theorem criticalMellinVolterraMode_eq
    {w : ℂ} (hw : w ≠ 0) (h : ℝ) :
    criticalMellinVolterraMode w h =
      -((2 * w + 1) / (2 * w)) * Complex.exp (w * h) + 1 / (2 * w) := by
  rw [criticalMellinVolterraMode,
    integral_exp_mul_complex hw]
  norm_num
  field_simp
  ring

/-- Adjacent-block response of one Volterra exponential mode. -/
def criticalMellinVolterraModeAdjacentBlock (L x : ℝ) (w : ℂ) : ℂ :=
  (∫ h in (x - L)..x, criticalMellinVolterraMode w h) -
    ∫ h in (x - 2 * L)..(x - L), criticalMellinVolterraMode w h

/-- **Exact Volterra--Haar mode law.**  Every exponential input emerges with the same exponent,
multiplied by the explicit faithful transfer factor. -/
theorem criticalMellinVolterraModeAdjacentBlock_eq
    {L x : ℝ} {w : ℂ} (hw : w ≠ 0) :
    criticalMellinVolterraModeAdjacentBlock L x w =
      Complex.exp (w * x) * criticalMellinVolterraHaarMultiplier L w := by
  have hcont : Continuous fun h : ℝ => Complex.exp (w * h) := by fun_prop
  have hint1 : IntervalIntegrable (fun h : ℝ => Complex.exp (w * h)) volume (x - L) x :=
    hcont.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun h : ℝ => Complex.exp (w * h)) volume
      (x - 2 * L) (x - L) := hcont.intervalIntegrable _ _
  have hlinear :
      criticalMellinVolterraModeAdjacentBlock L x w =
        -((2 * w + 1) / (2 * w)) * exponentialAdjacentBlock L x w := by
    have hscaled1 : IntervalIntegrable
        (fun h : ℝ => -((2 * w + 1) / (2 * w)) * Complex.exp (w * h))
        volume (x - L) x := hint1.const_mul _
    have hscaled2 : IntervalIntegrable
        (fun h : ℝ => -((2 * w + 1) / (2 * w)) * Complex.exp (w * h))
        volume (x - 2 * L) (x - L) := hint2.const_mul _
    have hconst1 : IntervalIntegrable (fun _ : ℝ => 1 / (2 * w))
        volume (x - L) x := intervalIntegrable_const
    have hconst2 : IntervalIntegrable (fun _ : ℝ => 1 / (2 * w))
        volume (x - 2 * L) (x - L) := intervalIntegrable_const
    rw [criticalMellinVolterraModeAdjacentBlock]
    simp_rw [criticalMellinVolterraMode_eq hw]
    rw [intervalIntegral.integral_add hscaled1 hconst1,
      intervalIntegral.integral_add hscaled2 hconst2]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const,
      intervalIntegral.integral_const]
    simp [exponentialAdjacentBlock, sub_eq_add_neg]
    ring
  rw [hlinear, exponentialAdjacentBlock_eq hw,
    criticalMellinVolterraHaarMultiplier]
  field_simp

end

end RHTower
