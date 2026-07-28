import GaloisForLFunctions.HTGeometry.BlackHoleDressedLogSpectralClock

/-!
# Common normalized propagation clock in Schwarzschild Love response

Solon's all-order higher-multipole Schwarzschild response contains the channel phase

`P_(ell,s)(eta) = exp(2 * nu_(ell,s) * eta^2 * tau(eta))`.

The channel rate `nu_(ell,s)` carries the near-zone multipole and spin dependence, while the
dressed logarithm `tau` is the universal far-zone Newtonian clock. This module proves the exact
local value law: after division by `2*nu`, the logarithmic derivative of every nonzero-rate channel
phase is the same `(eta^2*tau)'`.

The result prevents the common hypertranscendental far-zone clock from being misidentified as
channel-specific horizon memory. The physical response formula is external to Lean; its analytic
consequence below is unconditional.
-/

open Filter Set Topology Function Complex

namespace GaloisForLFunctions

noncomputable section

/-- The exponential phase recovered algebraically from a nondegenerate higher-multipole
Schwarzschild Love response. -/
def blackHoleHigherMultipoleCommonPhase
    (nu : ℂ) (tau : ℂ → ℂ) (eta : ℂ) : ℂ :=
  Complex.exp (2 * nu * eta ^ 2 * tau eta)

/-- The logarithmic phase slope normalized by the channel rate `2*nu`. -/
def blackHoleHigherMultipoleNormalizedPhaseSlope
    (nu : ℂ) (tau : ℂ → ℂ) (eta : ℂ) : ℂ :=
  deriv (blackHoleHigherMultipoleCommonPhase nu tau) eta /
      blackHoleHigherMultipoleCommonPhase nu tau eta /
    (2 * nu)

/-- Derivative of the channel phase at every differentiability point of the dressed logarithm. -/
theorem hasDerivAt_blackHoleHigherMultipoleCommonPhase
    (nu : ℂ) {tau : ℂ → ℂ} {eta tau' : ℂ}
    (htau : HasDerivAt tau tau' eta) :
    HasDerivAt (blackHoleHigherMultipoleCommonPhase nu tau)
      (blackHoleHigherMultipoleCommonPhase nu tau eta *
        (2 * nu * (2 * eta * tau eta + eta ^ 2 * tau'))) eta := by
  have hetaSq : HasDerivAt (fun z : ℂ => z ^ 2) (2 * eta) eta := by
    simpa [mul_comm] using (hasDerivAt_id eta).pow 2
  have hproduct : HasDerivAt (fun z : ℂ => z ^ 2 * tau z)
      (2 * eta * tau eta + eta ^ 2 * tau') eta := by
    simpa only [Pi.mul_apply] using hetaSq.mul htau
  have harg : HasDerivAt (fun z : ℂ => 2 * nu * z ^ 2 * tau z)
      (2 * nu * (2 * eta * tau eta + eta ^ 2 * tau')) eta := by
    simpa only [mul_assoc] using hproduct.const_mul (2 * nu)
  simpa [blackHoleHigherMultipoleCommonPhase] using harg.cexp

/-- **Universal normalized Newtonian clock.** Every nonzero-rate channel has normalized
logarithmic slope `(eta^2*tau)'`, independent of spin and multipole data. -/
theorem blackHoleHigherMultipoleNormalizedPhaseSlope_eq_common
    (nu : ℂ) {tau : ℂ → ℂ} {eta tau' : ℂ}
    (hnu : nu ≠ 0) (htau : HasDerivAt tau tau' eta) :
    blackHoleHigherMultipoleNormalizedPhaseSlope nu tau eta =
      2 * eta * tau eta + eta ^ 2 * tau' := by
  rw [blackHoleHigherMultipoleNormalizedPhaseSlope,
    (hasDerivAt_blackHoleHigherMultipoleCommonPhase nu htau).deriv]
  field_simp [blackHoleHigherMultipoleCommonPhase, hnu, Complex.exp_ne_zero]

/-- **Channel-rank-one law.** Any two nonzero-rate higher-multipole phases have identical
rate-normalized logarithmic slopes. -/
theorem blackHoleHigherMultipoleNormalizedPhaseSlope_channel_independent
    (nu₁ nu₂ : ℂ) {tau : ℂ → ℂ} {eta tau' : ℂ}
    (hnu₁ : nu₁ ≠ 0) (hnu₂ : nu₂ ≠ 0)
    (htau : HasDerivAt tau tau' eta) :
    blackHoleHigherMultipoleNormalizedPhaseSlope nu₁ tau eta =
      blackHoleHigherMultipoleNormalizedPhaseSlope nu₂ tau eta := by
  rw [blackHoleHigherMultipoleNormalizedPhaseSlope_eq_common nu₁ hnu₁ htau,
    blackHoleHigherMultipoleNormalizedPhaseSlope_eq_common nu₂ hnu₂ htau]

end

end GaloisForLFunctions
