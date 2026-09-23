import GaloisForLFunctions.RHTower.HedenmalmThetaGreenHyperbolicGaugeNoGo
import GaloisForLFunctions.RHTower.RouteRDeningerBVGreenPositiveUnitComparison

/-!
# Theta / Route-R / Deninger positive-unit current bridge

The pointwise theta Green flux, Route R's actual adjacent-depth Hodge-mate
coefficient, and the reflected degree-six Deninger BV--Green boundary are the
same horizontal physical current up to explicit strictly positive units and
one orientation reversal.  No horizontal grade is divided out, so the
identities include the critical fibre.

This closes physical comparison and sign calibration across the three
receivers.  It does not annihilate their common current; a pre-divisor source
law is still required.
-/

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Positive calibration from Route R's adjacent Hodge-mate current to the
theta Green current. -/
def thetaRouteRHodgeMatePositiveUnit
    (p : Nat.Primes) (q : XiZeroCopy) : ℝ :=
  thetaSource.mass * thetaXiRootEnergy q /
    primeDepthBVWoldReesCoronaAdjacentAttenuation p

theorem thetaRouteRHodgeMatePositiveUnit_pos
    (p : Nat.Primes) (q : XiZeroCopy) :
    0 < thetaRouteRHodgeMatePositiveUnit p q := by
  exact div_pos
    (mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q))
    (primeDepthBVWoldReesCoronaAdjacentAttenuation_pos p)

/-- Route R's centered divisor grade is negative twice the theta transverse
spectral coordinate. -/
theorem primeDepthBVWoldXiCenteredRate_eq_neg_two_spectralIm
    (q : XiZeroCopy) :
    primeDepthBVWoldXiCenteredRate q.1 =
      -2 * (xiSpectralPoint q).im := by
  rw [primeDepthBVWoldXiCenteredRate, xiSpectralPoint_im_eq]
  ring

/-- **Exact P/R current merger.**  Theta Green flux is the negative of a
strictly positive unit times Route R's actual Hodge-mate coefficient. -/
theorem thetaXiRankTwoBoundaryFlux_eq_neg_positiveUnit_mul_routeRHodgeMate
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaXiRankTwoBoundaryFlux q =
      -thetaRouteRHodgeMatePositiveUnit p q *
        ccmRationalAdelicPrimeXiHodgeMateCoefficient p q.1 := by
  rw [thetaXiRankTwoBoundaryFlux_eq,
    ccmRationalAdelicPrimeXiHodgeMateCoefficient,
    primeDepthBVWoldReesCoronaWeight_adjacent_eq,
    primeDepthBVWoldXiCenteredRate_eq_neg_two_spectralIm,
    thetaRouteRHodgeMatePositiveUnit]
  field_simp [(primeDepthBVWoldReesCoronaAdjacentAttenuation_pos p).ne']

theorem thetaXiRankTwoBoundaryFlux_eq_zero_iff_routeRHodgeMate_eq_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaXiRankTwoBoundaryFlux q = 0 ↔
      ccmRationalAdelicPrimeXiHodgeMateCoefficient p q.1 = 0 := by
  rw [thetaXiRankTwoBoundaryFlux_eq_neg_positiveUnit_mul_routeRHodgeMate,
    mul_eq_zero]
  exact or_iff_right
    (neg_ne_zero.mpr (thetaRouteRHodgeMatePositiveUnit_pos p q).ne')

/-- A Route R same-fibre Hodge-mate annihilation is exactly positivity of the
corresponding individual Route P squared node. -/
theorem thetaXiReciprocalEigenvalue_sq_positiveReal_iff_routeRHodgeMate_eq_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    (∃ r : ℝ, 0 < r ∧ thetaXiReciprocalEigenvalue q ^ (2 : ℕ) = (r : ℂ)) ↔
      ccmRationalAdelicPrimeXiHodgeMateCoefficient p q.1 = 0 := by
  rw [thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero,
    thetaXiRankTwoBoundaryFlux_eq_zero_iff_routeRHodgeMate_eq_zero]

/-- Positive calibration from the literal reflected Deninger boundary to the
theta Green current. -/
def thetaDeningerBoundaryPositiveUnit
    (p : Nat.Primes) (q : XiZeroCopy) : ℝ :=
  thetaRouteRHodgeMatePositiveUnit p q /
    routeRDeningerBVGreenPositiveUnit p q.1

theorem thetaDeningerBoundaryPositiveUnit_pos
    (p : Nat.Primes) (q : XiZeroCopy) :
    0 < thetaDeningerBoundaryPositiveUnit p q := by
  exact div_pos (thetaRouteRHodgeMatePositiveUnit_pos p q)
    (routeRDeningerBVGreenPositiveUnit_pos p q.1)

/-- **Exact P/Deninger current merger.**  The theta Green flux is the negative
of a strictly positive unit times the literal reflected degree-six BV--Green
source boundary. -/
theorem thetaXiRankTwoBoundaryFlux_eq_neg_positiveUnit_mul_deningerBoundary
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaXiRankTwoBoundaryFlux q =
      -thetaDeningerBoundaryPositiveUnit p q *
        routeRDeningerBVGreenReflectedBoundary q.1 := by
  rw [thetaXiRankTwoBoundaryFlux_eq_neg_positiveUnit_mul_routeRHodgeMate,
    routeRDeningerBVGreenReflectedBoundary_eq_positiveUnit_mul,
    thetaDeningerBoundaryPositiveUnit]
  field_simp [(routeRDeningerBVGreenPositiveUnit_pos p q.1).ne']

theorem thetaXiRankTwoBoundaryFlux_eq_zero_iff_deningerBoundary_eq_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaXiRankTwoBoundaryFlux q = 0 ↔
      routeRDeningerBVGreenReflectedBoundary q.1 = 0 := by
  rw [thetaXiRankTwoBoundaryFlux_eq_neg_positiveUnit_mul_deningerBoundary,
    mul_eq_zero]
  exact or_iff_right
    (neg_ne_zero.mpr (thetaDeningerBoundaryPositiveUnit_pos p q).ne')

/-- Literal Deninger boundary annihilation is exactly positivity of the
corresponding individual Route P squared node. -/
theorem thetaXiReciprocalEigenvalue_sq_positiveReal_iff_deningerBoundary_eq_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    (∃ r : ℝ, 0 < r ∧ thetaXiReciprocalEigenvalue q ^ (2 : ℕ) = (r : ℂ)) ↔
      routeRDeningerBVGreenReflectedBoundary q.1 = 0 := by
  rw [thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero,
    thetaXiRankTwoBoundaryFlux_eq_zero_iff_deningerBoundary_eq_zero (p := p)]

end

end RHTower.HedenmalmThetaSource
