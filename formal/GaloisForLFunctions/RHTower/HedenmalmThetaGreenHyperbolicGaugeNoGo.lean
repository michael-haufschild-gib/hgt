import GaloisForLFunctions.RHTower.HedenmalmThetaGreenReflectionPairNoGo
import GaloisForLFunctions.RHTower.HedenmalmThetaQuantileBoundaryNull
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
      ((‖pinnedInAmplitude g‖ : ℂ) ^ (2 : ℕ) -
        (‖pinnedOutAmplitude g‖ : ℂ) ^ (2 : ℕ)) := by
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

/-! ## Canonical gauge-breaking null frame -/

/-- The theta quantile source is the centered-moment null axis. -/
theorem thetaGreenBoundaryMomentPlane_quantile :
    thetaGreenBoundaryMomentPlane thetaQuantileCoordinate =
      (0, pinnedFirstMoment thetaQuantileCoordinate) := by
  apply Prod.ext
  · exact pinnedMean_thetaQuantileCoordinate_eq_zero
  · exact pinnedCentered_thetaQuantileCoordinate_eq_firstMoment

/-- Applying the rank-two boundary operator to the quantile source gives
the transverse monopole null axis. -/
theorem thetaGreenBoundaryMomentPlane_boundary_quantile :
    thetaGreenBoundaryMomentPlane
        (pinnedBoundaryCLM thetaQuantileCoordinate) =
      (-pinnedFirstMoment thetaQuantileCoordinate, 0) := by
  rw [pinnedBoundaryCLM_thetaQuantileCoordinate_eq_dipole]
  apply Prod.ext
  · rw [thetaGreenBoundaryMomentPlane, pinnedMean_smul,
      pinnedMean_pinnedOne]
    simp
  · rw [thetaGreenBoundaryMomentPlane, pinnedCentered,
      pinnedFirstMoment_smul, pinnedMean_smul,
      pinnedFirstMoment_pinnedOne, pinnedMean_pinnedOne]
    ring

/-- Both source-selected axes are lightlike for the split Green current. -/
theorem thetaGreenQuantileNullFrame_current_zero :
    thetaGreenHyperbolicCurrent
          (thetaGreenBoundaryMomentPlane thetaQuantileCoordinate) = 0 ∧
      thetaGreenHyperbolicCurrent
          (thetaGreenBoundaryMomentPlane
            (pinnedBoundaryCLM thetaQuantileCoordinate)) = 0 := by
  rw [thetaGreenBoundaryMomentPlane_quantile,
    thetaGreenBoundaryMomentPlane_boundary_quantile]
  simp [thetaGreenHyperbolicCurrent, thetaGreenConjugateMomentPlane,
    routeRSplitPoincarePairing]

/-- The two canonical lightlike axes are independent; their determinant is
the nonzero square of the theta quantile dipole. -/
theorem thetaGreenQuantileNullFrame_det_ne_zero :
    let u := thetaGreenBoundaryMomentPlane thetaQuantileCoordinate
    let v := thetaGreenBoundaryMomentPlane
      (pinnedBoundaryCLM thetaQuantileCoordinate)
    u.1 * v.2 - u.2 * v.1 ≠ 0 := by
  rw [thetaGreenBoundaryMomentPlane_quantile,
    thetaGreenBoundaryMomentPlane_boundary_quantile]
  simp only [zero_mul, mul_neg, sub_neg_eq_add, zero_add]
  exact mul_ne_zero pinnedFirstMoment_thetaQuantileCoordinate_ne_zero
    pinnedFirstMoment_thetaQuantileCoordinate_ne_zero

/-- **Canonical theta polar selector.**  The fixed positive energy balances
the two source-selected null axes after a horizontal boost exactly at neutral
boost.  Thus theta data supplies an explicit gauge-breaking target frame. -/
theorem thetaGreenQuantileNullFrame_gauge_balanced_iff (a : ℝ) :
    routeRFixedPolarEnergy
        (routeRHyperbolicSourceGauge a
          (thetaGreenBoundaryMomentPlane thetaQuantileCoordinate)) =
      routeRFixedPolarEnergy
        (routeRHyperbolicSourceGauge a
          (thetaGreenBoundaryMomentPlane
            (pinnedBoundaryCLM thetaQuantileCoordinate))) ↔
      a = 0 := by
  rw [thetaGreenBoundaryMomentPlane_quantile,
    thetaGreenBoundaryMomentPlane_boundary_quantile]
  simp only [routeRFixedPolarEnergy, routeRHyperbolicSourceGauge_apply,
    mul_zero, Complex.normSq_zero, zero_add, add_zero, Complex.normSq_mul,
    Complex.normSq_neg, Complex.normSq_ofReal]
  let d : ℝ := Complex.normSq (pinnedFirstMoment thetaQuantileCoordinate)
  have hd : 0 < d := Complex.normSq_pos.mpr
    pinnedFirstMoment_thetaQuantileCoordinate_ne_zero
  constructor
  · intro h
    have hsquares : Real.exp (-a) ^ (2 : ℕ) = Real.exp a ^ (2 : ℕ) := by
      dsimp only [d] at hd
      nlinarith
    have hexp : Real.exp (-a) = Real.exp a := by
      nlinarith [Real.exp_pos (-a), Real.exp_pos a]
    have harg : -a = a := Real.exp_injective hexp
    linarith
  · rintro rfl
    simp

end

end RHTower.HedenmalmThetaSource
