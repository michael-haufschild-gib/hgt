import GaloisForLFunctions.HTGeometry.ReciprocalScaleNoether
import GaloisForLFunctions.RHTower.RouteRHyperbolicGaugeQuarticPhysicalProducer

/-!
# Canonical Noether action of the arithmetic hyperbolic carrier

The actual prime-depth Xi carrier admits the canonical reciprocal-scaling
action. Its conserved Noether charge is exactly the existing invariant
amplitude, and its charge norm square is the literal physical Stokes excess.

The real action density has an exact descent direction in its rate: the
conjugate arithmetic charge. It has a minimum over complex rates precisely
on the critical line. The action on its canonical trajectories is nevertheless
zero at every grade. Stationarity under variation of the independent rate
is therefore additional to both global symmetry and the canonical equations.
-/

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem routeRHyperbolicSourceGauge_eq_reciprocalScale (s : ℝ)
    (z : RouteRHyperbolicSourcePlane) :
    routeRHyperbolicSourceGauge s z = reciprocalScale s z := rfl

/-- The arithmetic source gauge is a continuous variational symmetry of the canonical action. -/
theorem routeRHyperbolicNoetherAction_symmetry (a : ℂ) (s : ℝ)
    (z : ℝ → RouteRHyperbolicSourcePlane) (l r : ℝ) :
    reciprocalScaleAction a (fun t => routeRHyperbolicSourceGauge s (z t)) l r =
      reciprocalScaleAction a z l r :=
  reciprocalScaleAction_symmetry a s z l r

/-- Noether's charge identifies the source amplitude without a comparison assumption. -/
theorem routeRHyperbolicNoetherCharge_eq_amplitude (z : RouteRHyperbolicSourcePlane) :
    reciprocalScaleCharge z = routeRHyperbolicInvariantAmplitude z := rfl

/-- The actual Xi arithmetic charge is conserved by the canonical flow. -/
theorem routeRXiHyperbolicNoetherCharge_conserved (rho : XiDivisorSupport) (a t : ℝ) :
    reciprocalScaleCharge (routeRHyperbolicSourceGauge (a * t)
      (routeRXiHyperbolicInvariantQuarticCarrier rho)) =
        routeRHyperbolicInvariantAmplitude (routeRXiHyperbolicInvariantQuarticCarrier rho) :=
  reciprocalScaleCharge_scale (a * t) _

/-- Differential conservation holds on every actual Xi carrier. -/
theorem hasDerivAt_routeRXiHyperbolicNoetherCharge
    (rho : XiDivisorSupport) (a t : ℝ) :
    HasDerivAt (fun u => reciprocalScaleCharge (routeRHyperbolicSourceGauge (a * u)
      (routeRXiHyperbolicInvariantQuarticCarrier rho))) 0 t :=
  hasDerivAt_reciprocalScaleCharge a t _

/-- The conserved charge has exactly the arithmetic physical excess as its norm square. -/
theorem routeRXiHyperbolicNoetherCharge_normSq (rho : XiDivisorSupport) (a t : ℝ) :
    Complex.normSq (reciprocalScaleCharge (routeRHyperbolicSourceGauge (a * t)
      (routeRXiHyperbolicInvariantQuarticCarrier rho))) =
        primeDepthBVWoldSourcePolarizationStokesExcess
          (primeDepthBVWoldXiCenteredRate rho)
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
          (iteratedDeriv (xiSupportMultiplicity rho) XiC (xiSpectralPointSupport rho)) := by
  rw [routeRXiHyperbolicNoetherCharge_conserved]
  exact routeRXiHyperbolicInvariantQuarticEnergy_eq_physicalExcess rho

/-- The full canonical action vanishes even before any critical-line selection. -/
theorem routeRXiHyperbolicNoetherAction_onShell
    (rho : XiDivisorSupport) (a l r : ℝ) :
    reciprocalScaleAction a
      (fun t => routeRHyperbolicSourceGauge (a * t)
        (routeRXiHyperbolicInvariantQuarticCarrier rho)) l r = 0 :=
  reciprocalScaleAction_onShell a _ l r

/-- Holding the arithmetic field jet fixed exposes its invariant charge under rate variation. -/
theorem routeRXiHyperbolicNoetherAction_rateDerivative
    (rho : XiDivisorSupport) (a : ℂ) (v : ℂ × ℂ) :
    deriv (fun b => reciprocalScaleLagrangian b
      (routeRXiHyperbolicInvariantQuarticCarrier rho) v) a =
        -routeRHyperbolicInvariantAmplitude (routeRXiHyperbolicInvariantQuarticCarrier rho) :=
  (hasDerivAt_reciprocalScaleLagrangian_rate a _ v).deriv

/-- Stationarity in the independent complex rate is exactly the critical-line condition. -/
theorem routeRXiHyperbolicNoetherAction_rateStationary_iff
    (rho : XiDivisorSupport) (a : ℂ) (v : ℂ × ℂ) :
    deriv (fun b => reciprocalScaleLagrangian b
      (routeRXiHyperbolicInvariantQuarticCarrier rho) v) a = 0 ↔
        (rho : ℂ).re = 1 / 2 := by
  rw [routeRXiHyperbolicNoetherAction_rateDerivative, neg_eq_zero,
    routeRXiHyperbolicInvariantAmplitude_eq_zero_iff]

/-- The conjugate Noether charge decreases the real action by the physical Stokes excess. -/
theorem routeRXiHyperbolicNoetherAction_chargeDescent
    (rho : XiDivisorSupport) (a : ℂ) (v : ℂ × ℂ) (t : ℝ) :
    (reciprocalScaleLagrangian
      (a + (t : ℂ) * (starRingEnd ℂ) (routeRHyperbolicInvariantAmplitude
        (routeRXiHyperbolicInvariantQuarticCarrier rho)))
      (routeRXiHyperbolicInvariantQuarticCarrier rho) v).re =
      (reciprocalScaleLagrangian a (routeRXiHyperbolicInvariantQuarticCarrier rho) v).re -
        t * primeDepthBVWoldSourcePolarizationStokesExcess
          (primeDepthBVWoldXiCenteredRate rho)
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
          (iteratedDeriv (xiSupportMultiplicity rho) XiC (xiSpectralPointSupport rho)) := by
  rw [← routeRXiHyperbolicInvariantQuarticEnergy_eq_physicalExcess]
  exact reciprocalScaleLagrangian_chargeDescent a _ v t

/-- A rate minimum exists for the arithmetic real action density exactly on the critical line. -/
theorem routeRXiHyperbolicNoetherAction_rateMinimum_iff
    (rho : XiDivisorSupport) (v : ℂ × ℂ) :
    (∃ a : ℂ, ∀ b : ℂ,
      (reciprocalScaleLagrangian a (routeRXiHyperbolicInvariantQuarticCarrier rho) v).re ≤
        (reciprocalScaleLagrangian b (routeRXiHyperbolicInvariantQuarticCarrier rho) v).re) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [reciprocalScaleLagrangian_rate_minimum_iff,
    routeRHyperbolicNoetherCharge_eq_amplitude,
    routeRXiHyperbolicInvariantAmplitude_eq_zero_iff]

/-- RH is exactly independent-rate stationarity of every actual Xi carrier. -/
theorem riemannHypothesis_iff_routeRXiHyperbolicNoetherAction_rateStationary :
    RiemannHypothesis ↔ ∀ rho : XiDivisorSupport,
      deriv (fun b => reciprocalScaleLagrangian b
        (routeRXiHyperbolicInvariantQuarticCarrier rho) (0, 0)) 0 = 0 := by
  rw [← routeRXiHyperbolicInvariantAmplitudeAnnihilated_iff_rh]
  change (∀ rho, routeRHyperbolicInvariantAmplitude
    (routeRXiHyperbolicInvariantQuarticCarrier rho) = 0) ↔ _
  simp only [routeRXiHyperbolicNoetherAction_rateDerivative, neg_eq_zero]

end RHTower
