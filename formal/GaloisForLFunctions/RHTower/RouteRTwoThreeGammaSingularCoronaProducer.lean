import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittCrossPrimeSingularCorona
import GaloisForLFunctions.RHTower.RouteRTwoThreeGammaCapComparison

/-!
# Route R singular-corona Gamma producer

The canonical `(2,3)` Gamma/cap port now acts on a genuine singular corona,
not on a renamed scalar.  The dense finite arithmetic witness core is killed
by the quotient, while the full-support completed-Xi horizon survives.  The
nonzero first Xi Cartier jet gives a coefficient-faithful physical lift of
that horizon.

The cooriented reflection-odd Gamma coefficient acts on the lift.  Its value
is exactly the previously identified Route R Gamma/Cartier port times the
nonzero corona horizon.  Consequently the singular-corona action vanishes
exactly at neutral Xi grade.

This closes the missing singular carrier and zero-hidden physical-lift
construction.  It does not assert the remaining source Stokes-flatness law:
proving that this explicit action vanishes on every divisor fibre is still
the RH-bearing theorem.
-/

open Complex

namespace RHTower

noncomputable section

/-- Source-only cooriented reflection-odd Gamma coefficient on the canonical
ordered `(2,3)` witness. -/
def routeRTwoThreeGammaSingularCoronaActionCoefficient
    (rho : XiDivisorSupport) : ℂ :=
  (xiGammaEulerPrimitiveCoorientedReflectionOddExterior
    (primeDepthBVWoldXiCenteredRate rho)
    (routeRTwoPrime, 0) (routeRThreePrime, 0) : ℂ)

/-- Scalar Gamma action on the singular cross-prime corona. -/
def routeRTwoThreeGammaSingularCoronaAction
    (rho : XiDivisorSupport) :
    DeningerCalderonWittCrossPrimeSingularCorona →ₗ[ℂ]
      DeningerCalderonWittCrossPrimeSingularCorona :=
  routeRTwoThreeGammaSingularCoronaActionCoefficient rho • LinearMap.id

/-- Coefficient-faithful fixed physical Xi lift in the singular corona. -/
def routeRTwoThreeGammaSingularCoronaPhysicalLift
    (rho : XiDivisorSupport) :
    DeningerCalderonWittCrossPrimeSingularCorona :=
  ccmRationalAdelicPrimeXiCartierCoefficient rho •
    deningerCalderonWittCrossPrimeSingularCoronaHorizon

/-- The fixed physical lift cannot be erased: both its Cartier coefficient
and its singular horizon class are nonzero. -/
theorem routeRTwoThreeGammaSingularCoronaPhysicalLift_ne_zero
    (rho : XiDivisorSupport) :
    routeRTwoThreeGammaSingularCoronaPhysicalLift rho ≠ 0 := by
  exact smul_ne_zero
    (ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero rho)
    deningerCalderonWittCrossPrimeSingularCoronaHorizon_ne_zero

/-- Exact action formula: the source Gamma action on the zero-hidden
physical lift is the explicit Gamma/Cartier port on the retained corona
horizon. -/
theorem routeRTwoThreeGammaSingularCoronaAction_physicalLift
    (rho : XiDivisorSupport) :
    routeRTwoThreeGammaSingularCoronaAction rho
        (routeRTwoThreeGammaSingularCoronaPhysicalLift rho) =
      routeRTwoThreeGammaCartierTransportPort rho •
        deningerCalderonWittCrossPrimeSingularCoronaHorizon := by
  rw [routeRTwoThreeGammaSingularCoronaAction,
    routeRTwoThreeGammaSingularCoronaPhysicalLift,
    LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
    routeRTwoThreeGammaCartierTransportPort_eq]
  rfl

/-- Singular-corona Stokes flatness for the actual fixed physical lift. -/
def CCMRationalAdelicXiTwoThreeGammaSingularCoronaFlat
    (rho : XiDivisorSupport) : Prop :=
  routeRTwoThreeGammaSingularCoronaAction rho
      (routeRTwoThreeGammaSingularCoronaPhysicalLift rho) = 0

/-- Exact pointwise frontier: the constructed singular-corona producer is
flat precisely at neutral centered grade. -/
theorem twoThreeGammaSingularCoronaFlat_iff_centeredRate_eq_zero
    (rho : XiDivisorSupport) :
    CCMRationalAdelicXiTwoThreeGammaSingularCoronaFlat rho ↔
      primeDepthBVWoldXiCenteredRate rho = 0 := by
  rw [CCMRationalAdelicXiTwoThreeGammaSingularCoronaFlat,
    routeRTwoThreeGammaSingularCoronaAction_physicalLift]
  constructor
  · intro hzero
    have hport : routeRTwoThreeGammaCartierTransportPort rho = 0 :=
      (smul_eq_zero.mp hzero).resolve_right
        deningerCalderonWittCrossPrimeSingularCoronaHorizon_ne_zero
    exact (routeRTwoThreeGammaCartierTransportPort_eq_zero_iff rho).1 hport
  · intro hrate
    rw [(routeRTwoThreeGammaCartierTransportPort_eq_zero_iff rho).2 hrate,
      zero_smul]

/-- The singular-corona law is the same explicit physical flatness condition
as the Gamma/cap comparison, now carried on a source-faithful singular
quotient. -/
theorem twoThreeGammaSingularCoronaFlat_iff_gammaSingularStokesFlat
    (rho : XiDivisorSupport) :
    CCMRationalAdelicXiTwoThreeGammaSingularCoronaFlat rho ↔
      CCMRationalAdelicXiTwoThreeGammaSingularStokesFlat rho := by
  rw [twoThreeGammaSingularCoronaFlat_iff_centeredRate_eq_zero,
    CCMRationalAdelicXiTwoThreeGammaSingularStokesFlat,
    routeRTwoThreeGammaCartierTransportPort_eq_zero_iff]

/-- Global singular-corona Stokes-flatness proposition. -/
def CCMRationalAdelicXiGlobalTwoThreeGammaSingularCoronaFlat : Prop :=
  ∀ rho : XiDivisorSupport,
    CCMRationalAdelicXiTwoThreeGammaSingularCoronaFlat rho

/-- Global flatness of the constructed singular corona is the exact Route R
endpoint.  This theorem classifies the remaining law; it does not assume or
prove that law. -/
theorem globalTwoThreeGammaSingularCoronaFlat_iff_riemannHypothesis :
    CCMRationalAdelicXiGlobalTwoThreeGammaSingularCoronaFlat ↔
      RiemannHypothesis := by
  rw [← globalTwoThreeGammaSingularStokesFlat_iff_riemannHypothesis]
  exact forall_congr' twoThreeGammaSingularCoronaFlat_iff_gammaSingularStokesFlat

end

end RHTower
