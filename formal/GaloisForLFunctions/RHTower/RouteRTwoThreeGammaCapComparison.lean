import GaloisForLFunctions.RHTower.RouteRPrimeCapArakelovBoundaryLaw
import GaloisForLFunctions.RHTower.DeningerCalderonWittSingularGammaTransgression
import GaloisForLFunctions.RHTower.GammaCoorientedPositiveConeNoShorting

/-!
# Route R two-prime Gamma/cap comparison

The canonical ordered `(2,3)` Calderon--Witt incidence is a literal exact
pre-divisor source witness.  Its reflection-odd Gamma transport and the
Route R physical essential-cap difference are not merely detectors with the
same zero set: after coorientation they obey an exact division-free
coefficient identity.

Writing `a` for the centered Xi grade, `C` for the nonzero Cartier leading
coefficient, and `G(a)` for the strictly positive cooriented source gauge,

```text
G(a) * (cap_2 - cap_3) = (-13/36) * gammaPort_23.
```

The number `-13/36` is the exact difference between the two physical cap
factors `3/4` and `10/9`.  The Gamma port is the constructed source transport
evaluated on the canonical cross-prime Milnor-incidence witness, multiplied
only by its source coorientation and the coefficient-faithful Xi Cartier
landing.

Thus the remaining Route R producer is no longer an unspecified positive
reader or comparison: it is singular Stokes descent of this explicit
transport on this explicit exact source witness.  This file classifies that
descent condition honestly; it does not assert it unconditionally.
-/

open Complex

namespace RHTower

noncomputable section

/-- The fixed source primes are distinct. -/
theorem routeRTwoPrime_ne_routeRThreePrime :
    routeRTwoPrime ≠ routeRThreePrime := by
  intro h
  have hval := congrArg (fun p : Nat.Primes => (p : Nat)) h
  norm_num [routeRTwoPrime, routeRThreePrime] at hval

/-- The positive cooriented Gamma gauge on the fixed `(2,3)` source face. -/
def routeRTwoThreeGammaCoorientedGauge (rho : XiDivisorSupport) : Real :=
  xiGammaEulerPrimitiveCoorientedReflectionGauge
    (primeDepthBVWoldXiCenteredRate rho)
    (routeRTwoPrime, 0) (routeRThreePrime, 0)

/-- The literal reflection-odd Calderon--Witt source transport on the canonical
`(2,3)` exact incidence, followed by source coorientation and the fixed Xi
Cartier coefficient landing. -/
def routeRTwoThreeGammaCartierTransportPort
    (rho : XiDivisorSupport) : Complex :=
  ((xiGammaEulerBoundaryHalfHeight routeRThreePrime 0 -
      xiGammaEulerBoundaryHalfHeight routeRTwoPrime 0 : Real) : Complex) *
    deningerCalderonWittGammaReflectionOddScalarTransport
      (primeDepthBVWoldXiCenteredRate rho)
      (deningerCalderonWittCrossPrimeGammaWitness
        routeRTwoPrime_ne_routeRThreePrime)
      routeRTwoPrime routeRThreePrime 0 0 *
    ccmRationalAdelicPrimeXiCartierCoefficient rho

/-- The actual source transport is exactly the cooriented Gamma exterior
times the coefficient-faithful Cartier landing. -/
theorem routeRTwoThreeGammaCartierTransportPort_eq
    (rho : XiDivisorSupport) :
    routeRTwoThreeGammaCartierTransportPort rho =
      (xiGammaEulerPrimitiveCoorientedReflectionOddExterior
        (primeDepthBVWoldXiCenteredRate rho)
        (routeRTwoPrime, 0) (routeRThreePrime, 0) : Complex) *
          ccmRationalAdelicPrimeXiCartierCoefficient rho := by
  rw [routeRTwoThreeGammaCartierTransportPort,
    deningerCalderonWittGammaReflectionOddScalarTransport_crossPrimeWitness]
  rw [xiGammaEulerPrimitiveCoorientedReflectionOddExterior]
  push_cast
  ring

/-- Source coorientation factors the transported port as centered grade times
a strictly positive source gauge, without division. -/
theorem routeRTwoThreeGammaCartierTransportPort_eq_centeredRate_mul_gauge
    (rho : XiDivisorSupport) :
    routeRTwoThreeGammaCartierTransportPort rho =
      ((primeDepthBVWoldXiCenteredRate rho *
          routeRTwoThreeGammaCoorientedGauge rho : Real) : Complex) *
        ccmRationalAdelicPrimeXiCartierCoefficient rho := by
  rw [routeRTwoThreeGammaCartierTransportPort_eq,
    xiGammaEulerPrimitiveCoorientedReflectionOddExterior_eq_mul_gauge]
  rfl

/-- The fixed `(2,3)` cooriented Gamma gauge is strictly positive at every Xi
divisor point. -/
theorem routeRTwoThreeGammaCoorientedGauge_pos
    (rho : XiDivisorSupport) :
    0 < routeRTwoThreeGammaCoorientedGauge rho := by
  rw [routeRTwoThreeGammaCoorientedGauge]
  exact xiGammaEulerPrimitiveCoorientedReflectionGauge_pos
    (primeDepthBVWoldXiCenteredRate rho)
    (routeRTwoPrime, 0) (routeRThreePrime, 0)
    (xiGammaEulerBoundaryHalfHeight_ne_of_primes_ne_sameDepth
      routeRTwoPrime_ne_routeRThreePrime 0)

/-- Exact physical cap difference at the two fixed primes.  The coefficient
`-13/36` is `3/4 - 10/9`. -/
theorem routeRTwoThreePrimeLogEssentialCapDifference_eq
    (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort routeRTwoPrime rho -
        ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort routeRThreePrime rho =
      (((-(13 : Real) / 36) * primeDepthBVWoldXiCenteredRate rho : Real) :
          Complex) * ccmRationalAdelicPrimeXiCartierCoefficient rho := by
  rw [ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort_eq,
    ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort_eq]
  simp only [routeRTwoPrime, routeRThreePrime]
  norm_num
  push_cast
  ring

/-- **Division-free Gamma/cap bridge.**  Positive source gauge times the
physical two-prime cap difference is exactly `-13/36` times the transported
canonical Calderon--Witt source port. -/
theorem routeRTwoThreeGammaCap_divisionFreeComparison
    (rho : XiDivisorSupport) :
    (routeRTwoThreeGammaCoorientedGauge rho : Complex) *
        (ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort routeRTwoPrime rho -
          ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort routeRThreePrime rho) =
      (-(13 : Complex) / 36) *
        routeRTwoThreeGammaCartierTransportPort rho := by
  rw [routeRTwoThreePrimeLogEssentialCapDifference_eq,
    routeRTwoThreeGammaCartierTransportPort_eq_centeredRate_mul_gauge]
  push_cast
  ring

/-- Vanishing of the explicit transported exact-source port is exactly
neutral Xi grade. -/
theorem routeRTwoThreeGammaCartierTransportPort_eq_zero_iff
    (rho : XiDivisorSupport) :
    routeRTwoThreeGammaCartierTransportPort rho = 0 ↔
      primeDepthBVWoldXiCenteredRate rho = 0 := by
  rw [routeRTwoThreeGammaCartierTransportPort_eq_centeredRate_mul_gauge,
    mul_eq_zero]
  constructor
  · rintro (h | h)
    · have hreal :
          primeDepthBVWoldXiCenteredRate rho *
              routeRTwoThreeGammaCoorientedGauge rho = 0 := by
          exact_mod_cast h
      exact (mul_eq_zero.mp hreal).resolve_right
        (routeRTwoThreeGammaCoorientedGauge_pos rho).ne'
    · exact False.elim
        (ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero rho h)
  · intro h
    left
    exact_mod_cast (mul_eq_zero.mpr (Or.inl h) :
      primeDepthBVWoldXiCenteredRate rho *
        routeRTwoThreeGammaCoorientedGauge rho = 0)

/-- Singular Stokes flatness for the one now-identified canonical Gamma
transport port. -/
def CCMRationalAdelicXiTwoThreeGammaSingularStokesFlat
    (rho : XiDivisorSupport) : Prop :=
  routeRTwoThreeGammaCartierTransportPort rho = 0

/-- The finite `(2,3)` singular Gamma law is exactly the all-prime physical
Arakelov cap boundary law. -/
theorem twoThreeGammaSingularStokesFlat_iff_primeCapArakelovBoundaryLaw
    (rho : XiDivisorSupport) :
    CCMRationalAdelicXiTwoThreeGammaSingularStokesFlat rho ↔
      CCMRationalAdelicXiPrimeCapArakelovBoundaryLaw rho := by
  rw [CCMRationalAdelicXiTwoThreeGammaSingularStokesFlat,
    routeRTwoThreeGammaCartierTransportPort_eq_zero_iff,
    primeCapArakelovBoundaryLaw_iff_centeredRate_eq_zero]

/-- Global singular Stokes flatness of the explicit transported source port. -/
def CCMRationalAdelicXiGlobalTwoThreeGammaSingularStokesFlat : Prop :=
  ∀ rho : XiDivisorSupport,
    CCMRationalAdelicXiTwoThreeGammaSingularStokesFlat rho

/-- Exact Route R endpoint for the identified different producer. -/
theorem globalTwoThreeGammaSingularStokesFlat_iff_riemannHypothesis :
    CCMRationalAdelicXiGlobalTwoThreeGammaSingularStokesFlat ↔
      RiemannHypothesis := by
  rw [← globalPrimeCapArakelovBoundaryLaw_iff_riemannHypothesis]
  constructor
  · intro h rho
    exact (twoThreeGammaSingularStokesFlat_iff_primeCapArakelovBoundaryLaw rho).mp
      (h rho)
  · intro h rho
    exact (twoThreeGammaSingularStokesFlat_iff_primeCapArakelovBoundaryLaw rho).mpr
      (h rho)

end

end RHTower
