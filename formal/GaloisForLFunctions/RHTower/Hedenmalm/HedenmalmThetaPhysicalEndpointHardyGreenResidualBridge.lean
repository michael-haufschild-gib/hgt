import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPhysicalEndpointLogarithmicBoundaryLaw
import GaloisForLFunctions.RHTower.ExceptionalDivisorHardyGreenMetric
import GaloisForLFunctions.HTGeometry.ExponentialLaplaceValue

/-!
# Route P physical-endpoint Hardy--Green residual bridge

The logarithmic endpoint profile is `1 - exp (-|a| x)` in prime time `x = log p`.  Its missing
tail is therefore `exp (-|a| x)`.  For an exceptional copy, coefficient `2 * sqrt 2` gives the
exact half-line energy

`8 * integral exp (-2 |a| x) dx = 4 / |a| = 2 / |Im rho|`.

This is precisely the exceptional Hardy--Green energy and the one-point transverse Cauchy energy
already isolated on the divisor side.  Since every zero lies in the open critical strip, every
off-line copy has energy strictly greater than four.  The resulting global four-unit residual
bound is equivalent to RH.

The residual is set to zero when the copy is neutral: at that point there is no exceptional
divisor mode.  All off-line identities carry an explicit nonzero-rate hypothesis, so this
piecewise convention does not smuggle a limiting assertion across the singular boundary.
-/

open MeasureTheory Set
open scoped BigOperators

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Exceptional tail missing from the physical-endpoint logarithmic profile.  It is activated
exactly for a nonneutral divisor copy. -/
def thetaPhysicalEndpointHardyGreenResidual
    (q : XiZeroCopy) (x : ℝ) : ℝ :=
  if primeDepthBVWoldXiCenteredRate q.1 = 0 then 0
  else 2 * Real.sqrt 2 *
    Real.exp (-|primeDepthBVWoldXiCenteredRate q.1| * x)

theorem thetaPhysicalEndpointHardyGreenResidual_eq_of_centeredRate_ne_zero
    (q : XiZeroCopy)
    (h : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) (x : ℝ) :
    thetaPhysicalEndpointHardyGreenResidual q x =
      2 * Real.sqrt 2 *
        Real.exp (-|primeDepthBVWoldXiCenteredRate q.1| * x) := by
  simp [thetaPhysicalEndpointHardyGreenResidual, h]

/-- At prime time, the residual is exactly the complementary power tail in the Route P endpoint
profile. -/
theorem thetaPhysicalEndpointHardyGreenResidual_at_prime_log
    (p : Nat.Primes) (q : XiZeroCopy)
    (h : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    thetaPhysicalEndpointHardyGreenResidual q (Real.log (p : ℝ)) =
      2 * Real.sqrt 2 *
        (p : ℝ) ^ (-|primeDepthBVWoldXiCenteredRate q.1|) := by
  rw [thetaPhysicalEndpointHardyGreenResidual_eq_of_centeredRate_ne_zero q h,
    Real.rpow_def_of_pos (by exact_mod_cast p.2.pos : (0 : ℝ) < p)]
  congr 2
  ring

/-- Exact square complement between the endpoint-normalized physical profile and its exceptional
Hardy--Green residual. -/
theorem thetaPhysicalEndpointHardyGreenResidual_complements_physical_profile
    (p : Nat.Primes) (q : XiZeroCopy)
    (h : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    8 * (Real.log (p : ℝ) *
      thetaPhysicalEndpointNormalizedHalfDensity p q ^ 2) =
      (2 * Real.sqrt 2 -
        thetaPhysicalEndpointHardyGreenResidual q (Real.log (p : ℝ))) ^ 2 := by
  have hsqrt : (2 * Real.sqrt 2) ^ 2 = 8 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [log_mul_thetaPhysicalEndpointNormalizedHalfDensity_sq,
    thetaPhysicalEndpointHardyGreenResidual_at_prime_log p q h]
  rw [show 2 * Real.sqrt 2 -
      2 * Real.sqrt 2 *
        (p : ℝ) ^ (-|primeDepthBVWoldXiCenteredRate q.1|) =
      2 * Real.sqrt 2 *
        (1 - (p : ℝ) ^ (-|primeDepthBVWoldXiCenteredRate q.1|)) by ring,
    mul_pow, hsqrt]

/-- Exact half-line residual energy in the centered-rate coordinate. -/
theorem integral_sq_thetaPhysicalEndpointHardyGreenResidual_eq_four_div_abs_centeredRate
    (q : XiZeroCopy)
    (h : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    (∫ x in Ioi (0 : ℝ),
      thetaPhysicalEndpointHardyGreenResidual q x ^ 2) =
      4 / |primeDepthBVWoldXiCenteredRate q.1| := by
  let d : ℝ := |primeDepthBVWoldXiCenteredRate q.1|
  have hd : 0 < d := abs_pos.mpr h
  have hpoint : ∀ x : ℝ,
      thetaPhysicalEndpointHardyGreenResidual q x ^ 2 =
        8 * Real.exp (-(2 * d * x)) := by
    intro x
    rw [thetaPhysicalEndpointHardyGreenResidual_eq_of_centeredRate_ne_zero q h,
      mul_pow, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show Real.exp (-|primeDepthBVWoldXiCenteredRate q.1| * x) ^ 2 =
        Real.exp (2 * (-|primeDepthBVWoldXiCenteredRate q.1| * x)) by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring]
    dsimp [d]
    rw [show (2 : ℝ) ^ 2 * 2 = 8 by norm_num]
    congr 1
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpoint x),
    integral_const_mul,
    GaloisForLFunctions.HTGeometry.integral_exp_neg_mul_Ioi_zero
      (mul_pos (by norm_num) hd)]
  dsimp [d]
  field_simp [hd.ne']
  ring_nf

/-- Coefficient-exact identification of the Route P residual with exceptional Hardy--Green
energy at transverse depth `|Im rho|`. -/
theorem integral_sq_thetaPhysicalEndpointHardyGreenResidual_eq_exceptionalHardyGreenEnergy
    (q : XiZeroCopy)
    (h : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    (∫ x in Ioi (0 : ℝ),
      thetaPhysicalEndpointHardyGreenResidual q x ^ 2) =
      GaloisForLFunctions.exceptionalHardyGreenEnergy
        |(xiSpectralPoint q).im| := by
  have him : |(xiSpectralPoint q).im| ≠ 0 := by
    rw [abs_ne_zero]
    intro him
    apply h
    rw [primeDepthBVWoldXiCenteredRate_eq_neg_two_spectralIm, him]
    norm_num
  rw [integral_sq_thetaPhysicalEndpointHardyGreenResidual_eq_four_div_abs_centeredRate q h,
    GaloisForLFunctions.exceptionalHardyGreenEnergy,
    primeDepthBVWoldXiCenteredRate_eq_neg_two_spectralIm]
  rw [abs_mul, abs_neg]
  norm_num
  field_simp [him]
  norm_num

/-- Same residual energy is the established one-point transverse Cauchy self-energy. -/
theorem integral_sq_thetaPhysicalEndpointHardyGreenResidual_eq_cauchy_self
    (q : XiZeroCopy)
    (h : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) (gamma : ℝ) :
    (∫ x in Ioi (0 : ℝ),
      thetaPhysicalEndpointHardyGreenResidual q x ^ 2) =
      4 * RHTower.transverseCauchyKernel
        |(xiSpectralPoint q).im| |(xiSpectralPoint q).im|
        (gamma - gamma) := by
  have him : (xiSpectralPoint q).im ≠ 0 := by
    intro him
    apply h
    rw [primeDepthBVWoldXiCenteredRate_eq_neg_two_spectralIm, him]
    norm_num
  rw [integral_sq_thetaPhysicalEndpointHardyGreenResidual_eq_exceptionalHardyGreenEnergy q h,
    GaloisForLFunctions.exceptionalHardyGreenEnergy_eq_cauchy_self
      (abs_pos.mpr him) gamma]

/-- Critical-strip geometry makes every exceptional Route P residual exceed the universal
four-unit threshold. -/
theorem four_lt_integral_sq_thetaPhysicalEndpointHardyGreenResidual
    (q : XiZeroCopy)
    (h : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    4 < (∫ x in Ioi (0 : ℝ),
      thetaPhysicalEndpointHardyGreenResidual q x ^ 2) := by
  have him : (xiSpectralPoint q).im ≠ 0 := by
    intro him
    apply h
    rw [primeDepthBVWoldXiCenteredRate_eq_neg_two_spectralIm, him]
    norm_num
  have hdelta : 0 < |(xiSpectralPoint q).im| := abs_pos.mpr him
  have hstrip := abs_im_xiSpectralPoint_lt_half q
  rw [integral_sq_thetaPhysicalEndpointHardyGreenResidual_eq_exceptionalHardyGreenEnergy q h,
    GaloisForLFunctions.exceptionalHardyGreenEnergy,
    lt_div_iff₀ hdelta]
  nlinarith

/-- Neutral copies carry no exceptional residual. -/
theorem thetaPhysicalEndpointHardyGreenResidual_eq_zero_of_boundaryFlux_zero
    (q : XiZeroCopy) (hflux : thetaXiRankTwoBoundaryFlux q = 0) (x : ℝ) :
    thetaPhysicalEndpointHardyGreenResidual q x = 0 := by
  have him :=
    (thetaXiRankTwoBoundaryFlux_eq_zero_iff_spectralIm_eq_zero q).mp hflux
  have hrate : primeDepthBVWoldXiCenteredRate q.1 = 0 := by
    rw [primeDepthBVWoldXiCenteredRate_eq_neg_two_spectralIm, him]
    norm_num
  simp [thetaPhysicalEndpointHardyGreenResidual, hrate]

/-- Source-side four-unit threshold demanded by the exceptional Hardy--Green bridge. -/
def ThetaPhysicalEndpointHardyGreenResidualFourBound : Prop :=
  ∀ q : XiZeroCopy,
    (∫ x in Ioi (0 : ℝ),
      thetaPhysicalEndpointHardyGreenResidual q x ^ 2) ≤ 4

/-- Global four-unit control of the Route P residual is exactly RH.  This isolates the remaining
source obligation without weakening it or hiding it behind an abstract premise. -/
theorem thetaPhysicalEndpointHardyGreenResidualFourBound_iff_riemannHypothesis :
    ThetaPhysicalEndpointHardyGreenResidualFourBound ↔ RiemannHypothesis := by
  rw [← thetaGreenBoundaryNeutral_iff_riemannHypothesis]
  constructor
  · intro hbound q
    by_contra hflux
    have him : (xiSpectralPoint q).im ≠ 0 := by
      exact fun him => hflux
        ((thetaXiRankTwoBoundaryFlux_eq_zero_iff_spectralIm_eq_zero q).mpr him)
    have hrate : primeDepthBVWoldXiCenteredRate q.1 ≠ 0 := by
      rw [primeDepthBVWoldXiCenteredRate_eq_neg_two_spectralIm]
      exact mul_ne_zero (by norm_num) him
    exact (not_lt_of_ge (hbound q))
      (four_lt_integral_sq_thetaPhysicalEndpointHardyGreenResidual q hrate)
  · intro hneutral q
    have hpoint :
        (fun x : ℝ => thetaPhysicalEndpointHardyGreenResidual q x ^ 2) =
          fun _ => 0 := by
      funext x
      rw [thetaPhysicalEndpointHardyGreenResidual_eq_zero_of_boundaryFlux_zero
        q (hneutral q) x]
      norm_num
    rw [hpoint]
    simp

end

end RHTower.HedenmalmThetaSource
