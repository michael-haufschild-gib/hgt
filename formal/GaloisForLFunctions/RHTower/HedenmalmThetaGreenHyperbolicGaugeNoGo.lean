import GaloisForLFunctions.RHTower.HedenmalmThetaGreenReflectionPairNoGo
import GaloisForLFunctions.RHTower.RouteRHyperbolicGaugePolarReductionNoGo

/-!
# Theta Green boundary / Route-R hyperbolic-gauge identification

The two lowest theta boundary moments form exactly Route R's retained
two-sector plane.  In this chart the rank-two theta Green current is the
split Hermitian pairing.  It is invariant under the horizontal boost with
weights `(+1,-1)`, whereas the fixed positive Euclidean polarization is
invariant for every vector only at neutral boost.

Consequently no zero-current predicate which factors through this conserved
hyperbolic form can select neutral horizontal grade on the prime-character
orbit.  A Route-P producer must add a source-selected, gauge-breaking positive
polarization before it folds the oriented source inverse to its square.
-/

open Complex

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- The theta boundary monopole/dipole pair in Route R's two-sector plane. -/
def thetaGreenBoundaryMomentPlane (g : H) : RouteRHyperbolicSourcePlane :=
  (pinnedMean g, pinnedCentered g)

/-- Conjugate dual of a two-sector boundary moment. -/
def thetaGreenConjugateMomentPlane (z : RouteRHyperbolicSourcePlane) :
    RouteRHyperbolicSourcePlane :=
  ((starRingEnd ℂ) z.1, (starRingEnd ℂ) z.2)

/-- Split Hermitian current on the common theta/Route-R hyperbolic plane. -/
def thetaGreenHyperbolicCurrent (z : RouteRHyperbolicSourcePlane) : ℂ :=
  -routeRSplitPoincarePairing (thetaGreenConjugateMomentPlane z) z

/-- Real horizontal boosts commute with the conjugate-dual moment chart. -/
theorem thetaGreenConjugateMomentPlane_gauge (a : ℝ)
    (z : RouteRHyperbolicSourcePlane) :
    thetaGreenConjugateMomentPlane (routeRHyperbolicSourceGauge a z) =
      routeRHyperbolicSourceGauge a (thetaGreenConjugateMomentPlane z) := by
  apply Prod.ext
  · simp only [thetaGreenConjugateMomentPlane,
      routeRHyperbolicSourceGauge_apply, map_mul, Complex.conj_ofReal]
  · simp only [thetaGreenConjugateMomentPlane,
      routeRHyperbolicSourceGauge_apply, map_mul, Complex.conj_ofReal]

/-- The split Hermitian current is invariant under every horizontal boost. -/
theorem thetaGreenHyperbolicCurrent_gauge (a : ℝ)
    (z : RouteRHyperbolicSourcePlane) :
    thetaGreenHyperbolicCurrent (routeRHyperbolicSourceGauge a z) =
      thetaGreenHyperbolicCurrent z := by
  rw [thetaGreenHyperbolicCurrent, thetaGreenConjugateMomentPlane_gauge,
    routeRSplitPoincarePairing_gauge]
  rfl

/-- **Exact cross-route identification.**  The theta rank-two Green current
is Route R's split Hermitian current in monopole/dipole coordinates. -/
theorem inner_pinnedBoundaryCLM_eq_thetaGreenHyperbolicCurrent (g : H) :
    (inner ℂ (pinnedBoundaryCLM g) g : ℂ) =
      thetaGreenHyperbolicCurrent (thetaGreenBoundaryMomentPlane g) := by
  simpa [thetaGreenHyperbolicCurrent, thetaGreenConjugateMomentPlane,
    thetaGreenBoundaryMomentPlane, routeRSplitPoincarePairing] using
      inner_pinnedBoundaryCLM_eq g

/-- The same split current is the incoming-minus-outgoing intensity. -/
theorem thetaGreenHyperbolicCurrent_eq_amplitudeDifference (g : H) :
    thetaGreenHyperbolicCurrent (thetaGreenBoundaryMomentPlane g) =
      ((‖pinnedInAmplitude g‖ : ℂ) ^ 2 -
        (‖pinnedOutAmplitude g‖ : ℂ) ^ 2) := by
  rw [← inner_pinnedBoundaryCLM_eq_thetaGreenHyperbolicCurrent,
    inner_pinnedBoundaryCLM_eq_amplitudes]

/-- Current neutrality is constant along every horizontal gauge orbit. -/
theorem thetaGreenHyperbolicCurrent_zero_gauge_iff (a : ℝ)
    (z : RouteRHyperbolicSourcePlane) :
    thetaGreenHyperbolicCurrent (routeRHyperbolicSourceGauge a z) = 0 ↔
      thetaGreenHyperbolicCurrent z = 0 := by
  rw [thetaGreenHyperbolicCurrent_gauge]

/-- **Gauge no-go.**  Conserved theta Green-current neutrality cannot
characterize neutral grade on an actual prime-character orbit. -/
theorem thetaGreenHyperbolicCurrent_not_neutralSelector
    (p : ℕ) (hp : 1 < p) :
    ¬ (∀ a, thetaGreenHyperbolicCurrent (routeRPrimeCharacterOrbit p a) = 0 ↔
      a = 0) := by
  exact routeR_gaugeInvariantPredicate_not_neutralSelector p hp
    (fun z => thetaGreenHyperbolicCurrent z = 0)
    (fun a z => thetaGreenHyperbolicCurrent_zero_gauge_iff a z)

/-- Fixed positive polarization breaks the horizontal gauge exactly away
from neutral boost. -/
theorem thetaGreenFixedPolarEnergy_gauge_eq_iff (a : ℝ) :
    (∀ z, routeRFixedPolarEnergy (routeRHyperbolicSourceGauge a z) =
      routeRFixedPolarEnergy z) ↔ a = 0 := by
  simpa [routeRTransportedPolarEnergy] using
    routeRTransportedPolarEnergy_eq_fixed_iff (-a)

end

end RHTower.HedenmalmThetaSource
