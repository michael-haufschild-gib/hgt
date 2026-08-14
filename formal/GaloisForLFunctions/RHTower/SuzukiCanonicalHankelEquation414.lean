import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelCompactMellinLogBridge
import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelNormalizationDerivative

/-!
# Suzuki (2012), equation (4.14)

This module proves the aperture canonical system for Suzuki's meromorphic Fredholm pair.  The
proof first identifies its two diagonal modes with the literal compact Mellin transforms and then
uses the all-aperture strong equation (4.13).  Hence the result holds at every `a > 1`, including
the arithmetic cusp apertures omitted by a classical pointwise differentiation argument.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-! ## Elementary aperture derivatives -/

/-- Real-aperture derivative of Suzuki's elementary factor `a^(iz)`. -/
theorem hasDerivAt_suzukiHankelAiz_aperture
    {a : ℝ} (ha : 0 < a) (z : ℂ) :
    HasDerivAt (fun b : ℝ => suzukiHankelAiz b z)
      (I * z * suzukiHankelAiz a z / (a : ℂ)) a := by
  have hlogR := Real.hasDerivAt_log ha.ne'
  have hlogC : HasDerivAt (fun b : ℝ => (Real.log b : ℂ))
      (((a⁻¹ : ℝ) : ℂ)) a := hlogR.ofReal_comp
  have h := (hlogC.const_mul (I * z)).cexp
  unfold suzukiHankelAiz
  convert h using 1
  push_cast
  field_simp [ha.ne']

/-- Real-aperture derivative of the coefficient `sqrt(a)/2`. -/
theorem hasDerivAt_suzukiHankelTildeCoefficient
    {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun b : ℝ => suzukiHankelTildeCoefficient b)
      (suzukiHankelTildeCoefficient a / (2 * (a : ℂ))) a := by
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt a)) a :=
    Real.hasDerivAt_sqrt ha.ne'
  have hreal : HasDerivAt (fun b : ℝ => Real.sqrt b / 2)
      ((1 / (2 * Real.sqrt a)) / 2) a := hsqrt.div_const 2
  have hcomplex := hreal.ofReal_comp
  unfold suzukiHankelTildeCoefficient
  convert hcomplex using 1
  push_cast
  have hsqrt0 : (Real.sqrt a : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr ha).ne'
  have haC : (a : ℂ) = (Real.sqrt a : ℂ) * Real.sqrt a := by
    norm_cast
    nlinarith [Real.sq_sqrt ha.le]
  rw [haC]
  field_simp

/-- At the moving endpoint, twice the square-root coefficient times the clamped Mellin density is
exactly `a^(iz)`.  This is the boundary cancellation in equation (4.14). -/
theorem two_suzukiHankelTildeCoefficient_mul_clampedMellinWeight_eq_Aiz
    {a : ℝ} (ha : 1 < a) (z : ℂ) :
    2 * suzukiHankelTildeCoefficient a *
        suzukiClampedMellinWeightValue (1 / (a + 1)) z a =
      suzukiHankelAiz a z := by
  have ha0 : 0 < a := by linarith
  have hclamp : 1 / (a + 1) ≤ a := by
    have hden : 0 < a + 1 := by linarith
    rw [div_le_iff₀ hden]
    nlinarith
  have hsqrt : Real.exp (Real.log a / 2) = Real.sqrt a := by
    rw [← Real.log_sqrt ha0.le,
      Real.exp_log (Real.sqrt_pos.mpr ha0)]
  rw [suzukiHankelTildeCoefficient, suzukiClampedMellinWeightValue,
    max_eq_right hclamp]
  push_cast
  rw [show ((Real.sqrt a : ℝ) : ℂ) =
      Complex.exp (((Real.log a / 2 : ℝ) : ℂ)) by
        rw [← Complex.ofReal_exp, hsqrt]]
  calc
    2 * (Complex.exp (((Real.log a / 2 : ℝ) : ℂ)) / 2) *
          Complex.exp ((-(1 / 2 : ℂ) + I * z) * (Real.log a : ℂ)) =
        Complex.exp (((Real.log a / 2 : ℝ) : ℂ)) *
          Complex.exp ((-(1 / 2 : ℂ) + I * z) * (Real.log a : ℂ)) := by
      ring
    _ = Complex.exp ((((Real.log a / 2 : ℝ) : ℂ)) +
          (-(1 / 2 : ℂ) + I * z) * (Real.log a : ℂ)) := by
      rw [Complex.exp_add]
    _ = suzukiHankelAiz a z := by
      unfold suzukiHankelAiz
      congr 1
      push_cast
      ring

/-! ## Diagonal compact-Mellin modes -/

/-- Positive diagonal mode underlying `tilde A`. -/
def suzukiHankelPositiveModeRight
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  suzukiHankelAiz a z -
    2 * suzukiHankelTildeCoefficient a *
      suzukiHankelCompactMellinRight SuzukiHankelSign.positive
        omega homega z a

/-- Negative diagonal mode underlying `tilde B`. -/
def suzukiHankelNegativeModeRight
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  suzukiHankelAiz a z +
    2 * suzukiHankelTildeCoefficient a *
      suzukiHankelCompactMellinRight SuzukiHankelSign.negative
        omega homega z a

@[simp] theorem suzukiHankelPositiveModeRight_of_one_lt
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiHankelPositiveModeRight omega homega z a =
      suzukiHankelAiz a z -
        2 * suzukiHankelTildeCoefficient a *
          suzukiHankelCompactMellin SuzukiHankelSign.positive
            omega a homega ha z := by
  simp [suzukiHankelPositiveModeRight,
    suzukiHankelCompactMellinRight, ha]

@[simp] theorem suzukiHankelNegativeModeRight_of_one_lt
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiHankelNegativeModeRight omega homega z a =
      suzukiHankelAiz a z +
        2 * suzukiHankelTildeCoefficient a *
          suzukiHankelCompactMellin SuzukiHankelSign.negative
            omega a homega ha z := by
  simp [suzukiHankelNegativeModeRight,
    suzukiHankelCompactMellinRight, ha]

/-- First diagonal form of the all-aperture compact-Mellin system. -/
theorem hasDerivAt_suzukiHankelPositiveModeRight
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelPositiveModeRight omega homega z)
      ((I * z * suzukiHankelNegativeModeRight omega homega z a -
          suzukiHankelMu omega a homega ha *
            suzukiHankelPositiveModeRight omega homega z a) / (a : ℂ)) a := by
  have hA := hasDerivAt_suzukiHankelAiz_aperture (show 0 < a by linarith) z
  have hk := hasDerivAt_suzukiHankelTildeCoefficient (show 0 < a by linarith)
  have hCp := hasDerivAt_suzukiHankelCompactMellinRight_coupled
    SuzukiHankelSign.positive homega ha z
  have hmul := (hk.const_mul 2).mul hCp
  have hmode := hA.sub hmul
  have hboundary :=
    two_suzukiHankelTildeCoefficient_mul_clampedMellinWeight_eq_Aiz ha z
  change HasDerivAt
    ((fun b : ℝ => suzukiHankelAiz b z) -
      (fun b : ℝ => 2 * suzukiHankelTildeCoefficient b) *
        suzukiHankelCompactMellinRight SuzukiHankelSign.positive
          omega homega z) _ a
  apply hmode.congr_deriv
  rw [suzukiHankelPositiveModeRight_of_one_lt homega ha z,
    suzukiHankelNegativeModeRight_of_one_lt homega ha z]
  rw [suzukiHankelCompactMellinRight, dif_pos ha]
  simp only [SuzukiHankelSign.coeff_positive,
    SuzukiHankelSign.opposite_positive]
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by linarith : 0 < a))
  rw [← hboundary]
  field_simp [haC]
  ring

/-- Second diagonal form of the all-aperture compact-Mellin system. -/
theorem hasDerivAt_suzukiHankelNegativeModeRight
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelNegativeModeRight omega homega z)
      ((suzukiHankelMu omega a homega ha *
          suzukiHankelNegativeModeRight omega homega z a +
        I * z * suzukiHankelPositiveModeRight omega homega z a) / (a : ℂ)) a := by
  have hA := hasDerivAt_suzukiHankelAiz_aperture (show 0 < a by linarith) z
  have hk := hasDerivAt_suzukiHankelTildeCoefficient (show 0 < a by linarith)
  have hCm := hasDerivAt_suzukiHankelCompactMellinRight_coupled
    SuzukiHankelSign.negative homega ha z
  have hmul := (hk.const_mul 2).mul hCm
  have hmode := hA.add hmul
  have hboundary :=
    two_suzukiHankelTildeCoefficient_mul_clampedMellinWeight_eq_Aiz ha z
  change HasDerivAt
    ((fun b : ℝ => suzukiHankelAiz b z) +
      (fun b : ℝ => 2 * suzukiHankelTildeCoefficient b) *
        suzukiHankelCompactMellinRight SuzukiHankelSign.negative
          omega homega z) _ a
  apply hmode.congr_deriv
  rw [suzukiHankelPositiveModeRight_of_one_lt homega ha z,
    suzukiHankelNegativeModeRight_of_one_lt homega ha z]
  rw [suzukiHankelCompactMellinRight, dif_pos ha]
  simp only [SuzukiHankelSign.coeff_negative,
    SuzukiHankelSign.opposite_negative]
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by linarith : 0 < a))
  rw [← hboundary]
  field_simp [haC]
  ring

/-! ## Identification with Suzuki's meromorphic pair -/

/-- Total aperture curve of Suzuki's meromorphic `tilde A`; its exterior value is irrelevant to
the derivative theorem on `a > 1`. -/
def suzukiHankelTildeAContinuationRight
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  if ha : 1 < a then
    suzukiHankelTildeAContinuation omega a homega ha z
  else 0

/-- Total aperture curve of Suzuki's meromorphic `tilde B`. -/
def suzukiHankelTildeBContinuationRight
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  if ha : 1 < a then
    suzukiHankelTildeBContinuation omega a homega ha z
  else 0

/-- Mode expression for `tilde A`. -/
def suzukiHankelTildeAModeRight
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  (suzukiHankelPositiveModeRight omega homega z a +
    suzukiCanonicalTheta omega z *
      suzukiHankelPositiveModeRight omega homega (-z) a) / 2

/-- Mode expression for `tilde B`. -/
def suzukiHankelTildeBModeRight
    (omega : ℝ) (homega : 1 < omega) (z : ℂ) (a : ℝ) : ℂ :=
  (-suzukiHankelNegativeModeRight omega homega z a +
    suzukiCanonicalTheta omega z *
      suzukiHankelNegativeModeRight omega homega (-z) a) / (2 * I)

/-- Exact Mellin-mode formula for Suzuki's meromorphic `tilde A`. -/
theorem suzukiHankelTildeAContinuation_eq_mode
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiHankelTildeAContinuation omega a homega ha z =
      suzukiHankelTildeAModeRight omega homega z a := by
  rw [suzukiHankelTildeAContinuation, suzukiHankelTildeEContinuation,
    suzukiHankelPsiContinuation, suzukiHankelTildeEStarContinuation,
    suzukiHankelTildeAModeRight,
    suzukiHankelPositiveModeRight_of_one_lt homega ha z,
    suzukiHankelPositiveModeRight_of_one_lt homega ha (-z),
    suzukiCompactL2Fourier_hankelPhiSumLog_eq_compactMellin_sum
      homega ha z,
    suzukiCompactL2Fourier_hankelPhiSumLog_eq_compactMellin_sum
      homega ha (-z),
    suzukiCompactL2Fourier_hankelPhiSumHankelLog_eq_compactMellin_difference
      homega ha z,
    suzukiCompactL2Fourier_hankelPhiSumHankelLog_eq_compactMellin_difference
      homega ha (-z)]
  ring

/-- Exact Mellin-mode formula for Suzuki's meromorphic `tilde B`. -/
theorem suzukiHankelTildeBContinuation_eq_mode
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiHankelTildeBContinuation omega a homega ha z =
      suzukiHankelTildeBModeRight omega homega z a := by
  rw [suzukiHankelTildeBContinuation, suzukiHankelTildeEContinuation,
    suzukiHankelPsiContinuation, suzukiHankelTildeEStarContinuation,
    suzukiHankelTildeBModeRight,
    suzukiHankelNegativeModeRight_of_one_lt homega ha z,
    suzukiHankelNegativeModeRight_of_one_lt homega ha (-z),
    suzukiCompactL2Fourier_hankelPhiSumLog_eq_compactMellin_sum
      homega ha z,
    suzukiCompactL2Fourier_hankelPhiSumLog_eq_compactMellin_sum
      homega ha (-z),
    suzukiCompactL2Fourier_hankelPhiSumHankelLog_eq_compactMellin_difference
      homega ha z,
    suzukiCompactL2Fourier_hankelPhiSumHankelLog_eq_compactMellin_difference
      homega ha (-z)]
  ring

@[simp] theorem suzukiHankelTildeAContinuationRight_of_one_lt
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiHankelTildeAContinuationRight omega homega z a =
      suzukiHankelTildeAContinuation omega a homega ha z := by
  simp [suzukiHankelTildeAContinuationRight, ha]

@[simp] theorem suzukiHankelTildeBContinuationRight_of_one_lt
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiHankelTildeBContinuationRight omega homega z a =
      suzukiHankelTildeBContinuation omega a homega ha z := by
  simp [suzukiHankelTildeBContinuationRight, ha]

/-! ## Equation (4.14) -/

/-- Mode form of the first canonical equation. -/
theorem hasDerivAt_suzukiHankelTildeAModeRight
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelTildeAModeRight omega homega z)
      ((z * suzukiHankelTildeBModeRight omega homega z a -
          suzukiHankelMu omega a homega ha *
            suzukiHankelTildeAModeRight omega homega z a) / (a : ℂ)) a := by
  have hp := hasDerivAt_suzukiHankelPositiveModeRight homega ha z
  have hpn := hasDerivAt_suzukiHankelPositiveModeRight homega ha (-z)
  have h := hp.add (hpn.const_mul (suzukiCanonicalTheta omega z))
    |>.div_const 2
  change HasDerivAt
    (fun b : ℝ =>
      (suzukiHankelPositiveModeRight omega homega z b +
        suzukiCanonicalTheta omega z *
          suzukiHankelPositiveModeRight omega homega (-z) b) / 2) _ a
  apply h.congr_deriv
  rw [suzukiHankelTildeAModeRight, suzukiHankelTildeBModeRight]
  have haC : (a : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < a))
  field_simp [haC, Complex.I_ne_zero]
  ring_nf
  simp only [I_sq]
  ring

/-- Mode form of the second canonical equation. -/
theorem hasDerivAt_suzukiHankelTildeBModeRight
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelTildeBModeRight omega homega z)
      ((suzukiHankelMu omega a homega ha *
          suzukiHankelTildeBModeRight omega homega z a -
        z * suzukiHankelTildeAModeRight omega homega z a) / (a : ℂ)) a := by
  have hm := hasDerivAt_suzukiHankelNegativeModeRight homega ha z
  have hmn := hasDerivAt_suzukiHankelNegativeModeRight homega ha (-z)
  have h := hm.neg.add (hmn.const_mul (suzukiCanonicalTheta omega z))
    |>.div_const (2 * I)
  change HasDerivAt
    (fun b : ℝ =>
      (-suzukiHankelNegativeModeRight omega homega z b +
        suzukiCanonicalTheta omega z *
          suzukiHankelNegativeModeRight omega homega (-z) b) / (2 * I)) _ a
  apply h.congr_deriv
  rw [suzukiHankelTildeAModeRight, suzukiHankelTildeBModeRight]
  have haC : (a : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < a))
  field_simp [haC, Complex.I_ne_zero]
  ring_nf

/-- **Suzuki (2012), equation (4.14), first row, all apertures.** -/
theorem hasDerivAt_suzukiHankelTildeAContinuationRight
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelTildeAContinuationRight omega homega z)
      ((z * suzukiHankelTildeBContinuationRight omega homega z a -
          suzukiHankelMu omega a homega ha *
            suzukiHankelTildeAContinuationRight omega homega z a) / (a : ℂ)) a := by
  have hmode := hasDerivAt_suzukiHankelTildeAModeRight homega ha z
  have heq : suzukiHankelTildeAContinuationRight omega homega z =ᶠ[𝓝 a]
      suzukiHankelTildeAModeRight omega homega z := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    rw [suzukiHankelTildeAContinuationRight_of_one_lt homega hb z,
      suzukiHankelTildeAContinuation_eq_mode homega hb z]
  have h := hmode.congr_of_eventuallyEq heq
  rw [suzukiHankelTildeAContinuationRight_of_one_lt homega ha z,
    suzukiHankelTildeBContinuationRight_of_one_lt homega ha z,
    suzukiHankelTildeAContinuation_eq_mode homega ha z,
    suzukiHankelTildeBContinuation_eq_mode homega ha z]
  exact h

/-- **Suzuki (2012), equation (4.14), second row, all apertures.** -/
theorem hasDerivAt_suzukiHankelTildeBContinuationRight
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    HasDerivAt (suzukiHankelTildeBContinuationRight omega homega z)
      ((suzukiHankelMu omega a homega ha *
          suzukiHankelTildeBContinuationRight omega homega z a -
        z * suzukiHankelTildeAContinuationRight omega homega z a) / (a : ℂ)) a := by
  have hmode := hasDerivAt_suzukiHankelTildeBModeRight homega ha z
  have heq : suzukiHankelTildeBContinuationRight omega homega z =ᶠ[𝓝 a]
      suzukiHankelTildeBModeRight omega homega z := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    rw [suzukiHankelTildeBContinuationRight_of_one_lt homega hb z,
      suzukiHankelTildeBContinuation_eq_mode homega hb z]
  have h := hmode.congr_of_eventuallyEq heq
  rw [suzukiHankelTildeAContinuationRight_of_one_lt homega ha z,
    suzukiHankelTildeBContinuationRight_of_one_lt homega ha z,
    suzukiHankelTildeAContinuation_eq_mode homega ha z,
    suzukiHankelTildeBContinuation_eq_mode homega ha z]
  exact h

/-- Literal first scalar identity printed in equation (4.14). -/
theorem suzuki2012_equation_four_one_four_first
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    -((a : ℂ) * deriv
        (suzukiHankelTildeAContinuationRight omega homega z) a +
      suzukiHankelMu omega a homega ha *
        suzukiHankelTildeAContinuation omega a homega ha z) =
      -z * suzukiHankelTildeBContinuation omega a homega ha z := by
  have h := (hasDerivAt_suzukiHankelTildeAContinuationRight
    homega ha z).deriv
  rw [h, suzukiHankelTildeAContinuationRight_of_one_lt homega ha z,
    suzukiHankelTildeBContinuationRight_of_one_lt homega ha z]
  have haC : (a : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < a))
  field_simp [haC]
  ring

/-- Literal second scalar identity printed in equation (4.14). -/
theorem suzuki2012_equation_four_one_four_second
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    -((a : ℂ) * deriv
        (suzukiHankelTildeBContinuationRight omega homega z) a -
      suzukiHankelMu omega a homega ha *
        suzukiHankelTildeBContinuation omega a homega ha z) =
      z * suzukiHankelTildeAContinuation omega a homega ha z := by
  have h := (hasDerivAt_suzukiHankelTildeBContinuationRight
    homega ha z).deriv
  rw [h, suzukiHankelTildeAContinuationRight_of_one_lt homega ha z,
    suzukiHankelTildeBContinuationRight_of_one_lt homega ha z]
  have haC : (a : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < a))
  field_simp [haC]
  ring

end RHTower
