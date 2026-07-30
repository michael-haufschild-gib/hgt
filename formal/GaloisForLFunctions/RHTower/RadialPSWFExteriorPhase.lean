import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The exact exterior phase of the radial prolate equation

For the radial PSWF equation, Dunster's exterior Liouville coordinate has speed

`sqrt ((z^2 - sigma^2) / (z^2 - 1))`.

This file defines that coordinate directly and proves its exact derivative and the uniform
nonstationary lower bound on the exterior ray.  These are elementary consequences of
`0 <= sigma <= 1`; no asymptotic expansion is used.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- The exact Liouville speed on the exterior radial ray. -/
def radialPSWFExteriorSpeed (sigma z : ℝ) : ℝ :=
  Real.sqrt ((z ^ 2 - sigma ^ 2) / (z ^ 2 - 1))

/-- The exterior phase, normalized to vanish at `z = 2`.  Its additive normalization is
irrelevant for oscillatory estimates. -/
def radialPSWFExteriorPhase (sigma z : ℝ) : ℝ :=
  ∫ u in 2..z, radialPSWFExteriorSpeed sigma u

theorem continuousAt_radialPSWFExteriorSpeed
    (sigma : ℝ) {z : ℝ} (hz : 1 < z) :
    ContinuousAt (radialPSWFExteriorSpeed sigma) z := by
  have hz0 : 0 < z := zero_lt_one.trans hz
  have hden : z ^ 2 - 1 ≠ 0 := by nlinarith [sq_pos_of_pos hz0]
  have hnum : ContinuousAt (fun x : ℝ => x ^ 2 - sigma ^ 2) z :=
    (continuousAt_id.pow 2).sub continuousAt_const
  have hdencont : ContinuousAt (fun x : ℝ => x ^ 2 - 1) z :=
    (continuousAt_id.pow 2).sub continuousAt_const
  exact Real.continuous_sqrt.continuousAt.comp (hnum.div hdencont hden)

theorem continuousOn_radialPSWFExteriorSpeed_uIcc
    (sigma : ℝ) {z : ℝ} (hz : 1 < z) :
    ContinuousOn (radialPSWFExteriorSpeed sigma) (uIcc 2 z) := by
  intro x hx
  apply (continuousAt_radialPSWFExteriorSpeed sigma ?_).continuousWithinAt
  rcases (mem_uIcc.mp hx) with hx | hx
  · exact one_lt_two.trans_le hx.1
  · exact hz.trans_le hx.1

/-- Exact derivative of the exterior Liouville phase. -/
theorem hasDerivAt_radialPSWFExteriorPhase
    (sigma : ℝ) {z : ℝ} (hz : 1 < z) :
    HasDerivAt (radialPSWFExteriorPhase sigma)
      (radialPSWFExteriorSpeed sigma z) z := by
  have hcont := continuousOn_radialPSWFExteriorSpeed_uIcc sigma hz
  exact intervalIntegral.integral_hasDerivAt_right
    hcont.intervalIntegrable
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun u hu => continuousAt_radialPSWFExteriorSpeed sigma hu) z hz)
    (continuousAt_radialPSWFExteriorSpeed sigma hz)

/-- The exterior speed is at least one: the radial phase never becomes stationary outside the
pole when the turning parameter lies in `[0,1]`. -/
theorem one_le_radialPSWFExteriorSpeed
    {sigma z : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 1) (hz : 1 < z) :
    1 ≤ radialPSWFExteriorSpeed sigma z := by
  have hz0 : 0 < z := zero_lt_one.trans hz
  have hden : 0 < z ^ 2 - 1 := by nlinarith [sq_pos_of_pos hz0]
  have hsigmaSq : sigma ^ 2 ≤ 1 := by nlinarith
  rw [radialPSWFExteriorSpeed, Real.one_le_sqrt]
  apply (le_div_iff₀ hden).2
  nlinarith

/-- Exact derivative after the radial dilation `z = k*x`. -/
theorem hasDerivAt_radialPSWFExteriorPhase_dilate
    (sigma k : ℝ) {x : ℝ} (hkx : 1 < k * x) :
    HasDerivAt (fun y : ℝ => radialPSWFExteriorPhase sigma (k * y))
      (k * radialPSWFExteriorSpeed sigma (k * x)) x := by
  simpa only [Function.comp_def, mul_one, mul_comm] using
    (hasDerivAt_radialPSWFExteriorPhase sigma hkx).comp x
      (HasDerivAt.const_mul k (hasDerivAt_id x))

/-- Uniform derivative floor for every positive radial dilation. -/
theorem radialPSWFExteriorPhase_dilate_deriv_floor
    {sigma k x : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (hk : 0 ≤ k) (hkx : 1 < k * x) :
    k ≤ k * radialPSWFExteriorSpeed sigma (k * x) := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (one_le_radialPSWFExteriorSpeed hsigma0 hsigma1 hkx) hk

/-- Bandwidth-scaled exterior phase and its exact derivative. -/
theorem hasDerivAt_radialPSWFExteriorBandwidthPhase_dilate
    (c sigma k : ℝ) {x : ℝ} (hkx : 1 < k * x) :
    HasDerivAt (fun y : ℝ => c * radialPSWFExteriorPhase sigma (k * y))
      (c * k * radialPSWFExteriorSpeed sigma (k * x)) x := by
  simpa only [mul_assoc] using
    (hasDerivAt_radialPSWFExteriorPhase_dilate sigma k hkx).const_mul c

end

end RHTower
