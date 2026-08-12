import GaloisForLFunctions.RHTower.HedenmalmThetaMovingHorizonAnalyticDoubletNoGo
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiTrueWienerHopfFactorization
import GaloisForLFunctions.RHTower.CCMQuartetPaleyWiener

/-!
# Source Hardy symmetric-square weld for the Route P moving-horizon channel

P-G35 showed that the full analytic reflection doublet contains one
prime-harmonic-or-worse channel.  The finite P-G34 channel therefore needed a
source-derived stable projection rather than an `abs`-selected divisor formula.

The strict-right Xi canonical product already supplies that projection: its
anti-causal Ward mode at the physical half-density endpoint is the
Paley--Wiener ray

`exp (-(1/2 + lambda) L)` with `Re lambda > 0`.

This module proves that P-G34 is not this ray itself.  It is its critically
renormalized symmetric square

`exp(L/2) * ‖ray L‖² = exp (-(1/2 + d) L)`,

where the theta grade is exactly `d = 2 Re lambda`.  Thus the apparent factor
two mismatch between the Xi Hardy rate and the theta rate is forced by the
symmetric square.  The moving-horizon connection then multiplies this
source-canonical profile by the same grade `d`, coefficient by coefficient at
every prime.  Every strict-right source factor contributes strictly positive
P-G34 energy; the remaining open problem is to force absence of that factor,
not to justify the stable channel.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Anti-causal Paley--Wiener ray of one source-selected strict-right Xi mode
at the physical half-density endpoint. -/
def thetaXiRightAntiCausalWardRay
    (q : XiRightZeroCopy) (L : ℝ) : ℂ :=
  Complex.exp
    (-((((1 / 2 : ℝ) : ℂ) + xiRightCenteredZero q) * (L : ℂ)))

/-- Route P grade is twice the transverse decay rate of the strict-right Xi
Hardy mode. -/
theorem primeDepthBVWoldXiCenteredRate_right_eq_two_mul_re
    (q : XiRightZeroCopy) :
    primeDepthBVWoldXiCenteredRate q.1.1 =
      2 * (xiRightCenteredZero q).re := by
  rw [primeDepthBVWoldXiCenteredRate, xiRightCenteredZero, xiSpectralPoint]
  simp [Complex.mul_re]
  ring

theorem primeDepthBVWoldXiCenteredRate_right_pos
    (q : XiRightZeroCopy) :
    0 < primeDepthBVWoldXiCenteredRate q.1.1 := by
  rw [primeDepthBVWoldXiCenteredRate_right_eq_two_mul_re]
  exact mul_pos (by norm_num) (xiRightCenteredZero_re_pos q)

/-- The ray integrates to the literal strict-right Ward resolvent mode. -/
theorem integral_thetaXiRightAntiCausalWardRay
    (q : XiRightZeroCopy) :
    (∫ L in Ioi (0 : ℝ), thetaXiRightAntiCausalWardRay q L) =
      (((1 / 2 : ℝ) : ℂ) + xiRightCenteredZero q)⁻¹ := by
  have hpos :
      0 < ((((1 / 2 : ℝ) : ℂ) + xiRightCenteredZero q)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [xiRightCenteredZero_re_pos q]
  simpa only [thetaXiRightAntiCausalWardRay] using
    (GaloisForLFunctions.RHTower.integral_Ioi_cexp_neg_mul hpos)

/-- The same integral is literally the anti-causal CCM resolvent after the
source-fixed Schwarz rotation. -/
theorem thetaXiRightAntiCausalWardRay_integral_eq_antiCausalResolvent
    (q : XiRightZeroCopy) :
    (∫ L in Ioi (0 : ℝ), thetaXiRightAntiCausalWardRay q L) =
      ccmAntiCausalResolvent ((starRingEnd ℂ) (xiRightCenteredZero q)) (1 / 2) := by
  rw [integral_thetaXiRightAntiCausalWardRay, ccmAntiCausalResolvent]
  simp

/-- Restoring the genus-one contact to the centered Ward mode gives twice the
same anti-causal ray integral. -/
theorem centeredWardMode_add_contact_eq_two_mul_integral_ray
    (q : XiRightZeroCopy) :
    xiCenteredAntiCausalWardModeResponse q ((1 / 2 : ℝ) : ℂ) +
        2 * (xiRightCenteredZero q)⁻¹ =
      2 * ∫ L in Ioi (0 : ℝ), thetaXiRightAntiCausalWardRay q L := by
  rw [integral_thetaXiRightAntiCausalWardRay,
    xiCenteredAntiCausalWardModeResponse]
  ring

theorem norm_sq_thetaXiRightAntiCausalWardRay
    (q : XiRightZeroCopy) (L : ℝ) :
    ‖thetaXiRightAntiCausalWardRay q L‖ ^ 2 =
      Real.exp (-(1 + 2 * (xiRightCenteredZero q).re) * L) := by
  rw [thetaXiRightAntiCausalWardRay, Complex.norm_exp]
  have hre :
      (-((((1 / 2 : ℝ) : ℂ) + xiRightCenteredZero q) * (L : ℂ))).re =
        -(1 / 2 + (xiRightCenteredZero q).re) * L := by
    simp [Complex.mul_re]
    ring
  rw [hre, pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Critical half-density renormalization of the Hardy-mode symmetric square. -/
def thetaXiRightHardySymmetricSquareProfile
    (q : XiRightZeroCopy) (L : ℝ) : ℝ :=
  Real.exp (L / 2) * ‖thetaXiRightAntiCausalWardRay q L‖ ^ 2

/-- **P-G36 symmetric-square law.** The critically renormalized source Hardy
square is exactly the stable Route P theta channel. -/
theorem thetaXiRightHardySymmetricSquareProfile_eq
    (q : XiRightZeroCopy) (L : ℝ) :
    thetaXiRightHardySymmetricSquareProfile q L =
      Real.exp
        (-(1 / 2 + primeDepthBVWoldXiCenteredRate q.1.1) * L) := by
  rw [thetaXiRightHardySymmetricSquareProfile,
    norm_sq_thetaXiRightAntiCausalWardRay,
    primeDepthBVWoldXiCenteredRate_right_eq_two_mul_re,
    ← Real.exp_add]
  congr 1
  ring

/-- Prime sampling of the source Hardy square is coefficient-identical to the
P-G34 twisted channel. -/
theorem thetaXiRightHardySymmetricSquareProfile_prime
    (q : XiRightZeroCopy) (p : Nat.Primes) :
    thetaXiRightHardySymmetricSquareProfile q (Real.log (p : ℝ)) =
      routeNGammaSewnTwistedCriticalChannelAmplitude
        (primeDepthBVWoldXiCenteredRate q.1.1) p := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hrate := primeDepthBVWoldXiCenteredRate_right_pos q
  rw [thetaXiRightHardySymmetricSquareProfile_eq,
    routeNGammaSewnTwistedCriticalChannelAmplitude,
    abs_of_pos hrate, Real.rpow_def_of_pos hp]
  congr 1
  ring

/-- On the strict-right source sector, the physical Ward half-density is the
universal carrier minus the source Hardy symmetric square. -/
theorem thetaWardContinuousHalfDensityProfile_right_eq_universal_sub_hardySquare
    (q : XiRightZeroCopy) (L : ℝ) :
    thetaWardContinuousHalfDensityProfile q.1 L =
      Real.exp (-L / 2) -
        thetaXiRightHardySymmetricSquareProfile q L := by
  have hrate := primeDepthBVWoldXiCenteredRate_right_pos q
  rw [thetaWardContinuousHalfDensityProfile,
    thetaWardHorizontalOrientation, if_pos hrate.le, one_mul,
    thetaXiRightHardySymmetricSquareProfile_eq, abs_of_pos hrate]

/-- The moving-horizon connection differentiates the source Hardy square and
returns the exact Route P grade multiplier. -/
theorem thetaMovingHorizonConnection_right_eq_depth_mul_hardySquare
    (q : XiRightZeroCopy) (L : ℝ) :
    thetaMovingHorizonConnection
        (thetaWardContinuousHalfDensityProfile q.1) L =
      primeDepthBVWoldXiCenteredRate q.1.1 *
        thetaXiRightHardySymmetricSquareProfile q L := by
  have hrate := primeDepthBVWoldXiCenteredRate_right_pos q
  rw [thetaMovingHorizonConnection_wardContinuousHalfDensityProfile,
    thetaWardHorizontalOrientation, if_pos hrate.le, one_mul,
    abs_of_pos hrate, thetaXiRightHardySymmetricSquareProfile_eq]

/-- Coefficient-exact prime weld between source Hardy square and P-G34. -/
theorem thetaMovingHorizonConnection_right_prime_eq_sourceHardySquare
    (q : XiRightZeroCopy) (p : Nat.Primes) :
    thetaMovingHorizonConnection
        (thetaWardContinuousHalfDensityProfile q.1)
        (Real.log (p : ℝ)) =
      primeDepthBVWoldXiCenteredRate q.1.1 *
        routeNGammaSewnTwistedCriticalChannelAmplitude
          (primeDepthBVWoldXiCenteredRate q.1.1) p := by
  rw [thetaMovingHorizonConnection_right_eq_depth_mul_hardySquare,
    thetaXiRightHardySymmetricSquareProfile_prime]

/-- Every actual strict-right source factor deposits strictly positive finite
P-G34 covariant energy. -/
theorem thetaWardMovingHorizonCovariantPrimeEnergy_right_pos
    (q : XiRightZeroCopy) :
    0 < thetaWardMovingHorizonCovariantPrimeEnergy q.1 := by
  rw [thetaWardMovingHorizonCovariantPrimeEnergy_pos_iff,
    thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate]
  exact mul_ne_zero
    (neg_ne_zero.mpr
      (mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q.1)).ne')
    (primeDepthBVWoldXiCenteredRate_right_pos q).ne'

end

end RHTower.HedenmalmThetaSource
