import GaloisForLFunctions.RHTower.CCMCriticalMellinApertureResolvent

open Complex

namespace RHTower

noncomputable section

/-!
# Prime-Stokes / CCM unit-resolvent weld

This file formalizes the dependency-closed algebraic core of the prime-aperture Stokes law.
A fixed aperture has exact Fourier blind spots.  Unit exponential aperture averaging removes those
blind spots with an exact multiplier between `2` and `4`.  Independently, the normalized CCM
aperture average and the prime-Stokes exponential resolvent agree with opposite sign exactly at
unit rate.

These statements do not identify the resulting positive form with the complete Xi divisor form.
That Gamma/Calderón intertwining statement remains the open RH-bearing core.
-/

/-- Exponential-aperture resolvent supplied by the nested prime-Stokes residue. -/
def primeStokesExponentialApertureResolvent (a : ℝ) (w : ℂ) : ℂ :=
  (a : ℂ) / ((a : ℂ) + w)

/-- CCM exponential aperture average normalized by the rate of the probability law. -/
def normalizedCCMApertureResolvent (a : ℝ) (w : ℂ) : ℂ :=
  (a : ℂ) * criticalMellinApertureAveragedMultiplier a w

/-- Fourier multiplier of the residue Pick metric at one fixed aperture. -/
def primeStokesFixedActionFourierMultiplier (c ξ : ℝ) : ℝ :=
  2 + 2 * Real.cos (c * ξ)

/-- Fourier multiplier after unit exponential aperture averaging. -/
def primeStokesUnitAveragedFourierMultiplier (ξ : ℝ) : ℝ :=
  2 + 2 / (1 + ξ ^ 2)

theorem primeStokesFixedActionFourierMultiplier_pi_div_eq_zero
    {c : ℝ} (hc : c ≠ 0) :
    primeStokesFixedActionFourierMultiplier c (Real.pi / c) = 0 := by
  rw [primeStokesFixedActionFourierMultiplier]
  have hcπ : c * (Real.pi / c) = Real.pi := by
    field_simp [hc]
  rw [hcπ, Real.cos_pi]
  ring

theorem primeStokesUnitAveragedFourierMultiplier_mem_Icc (ξ : ℝ) :
    2 ≤ primeStokesUnitAveragedFourierMultiplier ξ ∧
      primeStokesUnitAveragedFourierMultiplier ξ ≤ 4 := by
  have hden : 0 < 1 + ξ ^ 2 := by positivity
  have hnonneg : 0 ≤ 2 / (1 + ξ ^ 2) :=
    div_nonneg (by norm_num) hden.le
  have hle : 2 / (1 + ξ ^ 2) ≤ 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg ξ]
  rw [primeStokesUnitAveragedFourierMultiplier]
  constructor <;> linarith

theorem normalizedCCMApertureResolvent_eq
    {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 0 < w.re) :
    normalizedCCMApertureResolvent a w =
      -(2 * w + 1) / (((a : ℂ) + w) * ((a : ℂ) + 2 * w)) := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have haw0 : (a : ℂ) + w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have ha2w0 : (a : ℂ) + 2 * w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  rw [normalizedCCMApertureResolvent,
    criticalMellinApertureAveragedMultiplier_eq ha hw]
  field_simp [ha0, haw0, ha2w0]

theorem normalizedCCMApertureResolvent_one_eq_neg_primeStokes
    {w : ℂ} (hw : 0 < w.re) :
    normalizedCCMApertureResolvent 1 w =
      -primeStokesExponentialApertureResolvent 1 w := by
  rw [normalizedCCMApertureResolvent,
    primeStokesExponentialApertureResolvent,
    criticalMellinApertureAveragedMultiplier_one_eq hw]
  simp [div_eq_mul_inv, add_comm]

theorem exponentialApertureRate_eq_one_of_resolvent_weld_at_one
    {a : ℝ} (ha : 0 < a)
    (h :
      normalizedCCMApertureResolvent a 1 =
        -primeStokesExponentialApertureResolvent a 1) :
    a = 1 := by
  have haOne : (a : ℂ) + 1 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    linarith
  have haTwo : (a : ℂ) + 2 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    linarith
  rw [normalizedCCMApertureResolvent_eq ha (by norm_num),
    primeStokesExponentialApertureResolvent] at h
  field_simp [haOne, haTwo] at h
  have hre := congrArg Complex.re h
  norm_num at hre
  nlinarith

theorem exponentialApertureResolventWeldAtOne_iff
    {a : ℝ} (ha : 0 < a) :
    normalizedCCMApertureResolvent a 1 =
        -primeStokesExponentialApertureResolvent a 1 ↔
      a = 1 := by
  constructor
  · exact exponentialApertureRate_eq_one_of_resolvent_weld_at_one ha
  · intro h
    subst a
    exact normalizedCCMApertureResolvent_one_eq_neg_primeStokes (by norm_num)

end

end RHTower
