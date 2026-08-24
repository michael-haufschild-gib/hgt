import GaloisForLFunctions.RHTower.ThetaCuspHawkingAbsorptionInducedModeExcitation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingSchwarzschildJostIncidenceNoGo

/-!
# AIME/Jost incidence: bare mass response does not excite a theta dark mode

Absorption-induced mode excitation (AIME) is genuine nonlinear black-hole dynamics.  Absorbed
quadratic field energy shifts the black-hole mass, and the shifted mode basis produces a cubic
secular response.  The corresponding mass derivative is nonzero for every nonzero carrier,
nonzero absorption response, and nonzero observation time.

That coefficient-level fact is not yet mode excitation.  Genuine Schwarzschild Jost incidence
places a centered theta divisor `alpha = w + i a` at real scattering frequency `w`; `a` is source
tilt, not imaginary QNM frequency.  The theta source amplitude `XiC(w + i a)` vanishes, while the
real-axis Evans denominator is nonzero.  The optical identity then makes the same sector's horizon
flux vanish.

This file inserts those incidence facts into AIME.  It proves the exact three-way classification:

* bare real-carrier mass derivative is nonzero;
* source-dressed AIME response is zero;
* AIME driven by that same sector's absorbed horizon energy is zero.

**[FALSIFIED]** Evaluating the bare AIME coefficient at a complex Xi coordinate does not prove that
every Xi sector mixes.  It identifies neither that coordinate with a QNM nor a nonzero incoming
amplitude with the divisor mode.

**[POSITIVE SURVIVOR]** AIME leaves one genuinely Hawking-native producer: cross-mode projection.
Absorbed energy from a bright continuum/QNM mode can shift the geometry, but exciting a theta-dark
real-frequency sector additionally requires a nonzero overlap between the mass-shifted mode and
that sector.  This is precisely a two-frequency, nonstationary kernel; sector-local KMS, passivity,
and the diagonal self-frequency coefficient cannot supply it.

`[LITERATURE]` AIME and its absorbed-energy mass shift are from Sberna--Bosch--East--Green--Lehner,
arXiv:2112.11168.  Schwarzschild Jost source/denominator separation is from Casals--Ottewill,
arXiv:1112.2695, and Green--Hollands--Sberna--Toomani--Zimmerman, arXiv:2210.15935.

`[SCOPE]` Lean checks the exact coefficient/source/flux incidence.  It does not derive the missing
cross-mode radial overlap from second-order Einstein--Klein--Gordon or Teukolsky dynamics and does
not prove RH.
-/

open Complex

noncomputable section

namespace RHTower

/-- Theta source amplitude in the physically correct real-frequency/source-tilt coordinates. -/
def thetaCuspHawkingJostAIMESourceAmplitude (rho : XiDivisorSupport) : ℂ :=
  XiC ((thetaCuspHawkingPositiveJostFrequency rho : ℂ) +
    (thetaCuspHawkingPositiveJostTilt rho : ℂ) * I)

/-- Every divisor representative is dark in its real Schwarzschild scattering channel. -/
theorem thetaCuspHawkingJostAIMESourceAmplitude_eq_zero (rho : XiDivisorSupport) :
    thetaCuspHawkingJostAIMESourceAmplitude rho = 0 := by
  rw [thetaCuspHawkingJostAIMESourceAmplitude,
    thetaCuspHawkingPositiveJostCoordinate_eq]
  exact XiC_xiSpectralPointSupport_eq_zero_source _

/-- Bare AIME mass derivative evaluated at the physical positive real carrier frequency. -/
def thetaCuspHawkingJostAIMEBareCoefficient
    (rho : XiDivisorSupport) (M absorption t : ℝ) : ℂ :=
  schwarzschildAbsorptionInducedCubicCoefficient M absorption t
    (thetaCuspHawkingPositiveJostFrequency rho : ℂ)

/-- AIME's bare real-carrier mass derivative is nonzero under nondegenerate parameters. -/
theorem thetaCuspHawkingJostAIMEBareCoefficient_ne_zero
    (rho : XiDivisorSupport) {M absorption t : ℝ}
    (hM : M ≠ 0) (habsorption : absorption ≠ 0) (ht : t ≠ 0) :
    thetaCuspHawkingJostAIMEBareCoefficient rho M absorption t ≠ 0 := by
  apply schwarzschildAbsorptionInducedCubicCoefficient_ne_zero
    hM habsorption ht
  exact_mod_cast (ne_of_gt (thetaCuspHawkingPositiveJostFrequency_pos rho))

/-- Physical AIME contribution after multiplying the coefficient by the incoming theta mode. -/
def thetaCuspHawkingJostAIMESourceDressedResponse
    (rho : XiDivisorSupport) (M absorption t : ℝ) : ℂ :=
  thetaCuspHawkingJostAIMESourceAmplitude rho *
    thetaCuspHawkingJostAIMEBareCoefficient rho M absorption t

/-- A nonzero bare AIME coefficient cannot revive a source amplitude that is identically zero. -/
theorem thetaCuspHawkingJostAIMESourceDressedResponse_eq_zero
    (rho : XiDivisorSupport) (M absorption t : ℝ) :
    thetaCuspHawkingJostAIMESourceDressedResponse rho M absorption t = 0 := by
  rw [thetaCuspHawkingJostAIMESourceDressedResponse,
    thetaCuspHawkingJostAIMESourceAmplitude_eq_zero, zero_mul]

/-- Sector-local mass-response parameter sourced by its horizon-absorbed energy density. -/
def thetaCuspHawkingJostAIMESectorLocalAbsorption
    (rho : XiDivisorSupport) (rapidity response : ℝ) : ℝ :=
  response * thetaCuspHawkingPositiveJostHorizonEnergyDensity rho rapidity

/-- The optical theorem gives no sector-local absorbed mass at a theta divisor. -/
theorem thetaCuspHawkingJostAIMESectorLocalAbsorption_eq_zero
    (rho : XiDivisorSupport) (rapidity response : ℝ) :
    thetaCuspHawkingJostAIMESectorLocalAbsorption rho rapidity response = 0 := by
  rw [thetaCuspHawkingJostAIMESectorLocalAbsorption,
    (thetaCuspHawkingXiDivisor_zero_realAxisFlux rho rapidity).2, mul_zero]

/-- Self-absorption cannot activate AIME at a theta-dark real-frequency channel. -/
theorem thetaCuspHawkingJostAIMESelfAbsorbedCoefficient_eq_zero
    (rho : XiDivisorSupport) (M rapidity response t : ℝ) :
    schwarzschildAbsorptionInducedCubicCoefficient M
      (thetaCuspHawkingJostAIMESectorLocalAbsorption rho rapidity response) t
      (thetaCuspHawkingPositiveJostFrequency rho : ℂ) = 0 := by
  rw [thetaCuspHawkingJostAIMESectorLocalAbsorption_eq_zero]
  simp [schwarzschildAbsorptionInducedCubicCoefficient]

/-- **Exact AIME/Jost incidence.**  Bare susceptibility survives, but both ways of obtaining an
actual sector-local cubic response vanish at every theta divisor. -/
theorem thetaCuspHawkingJostAIME_incidenceClassification
    (rho : XiDivisorSupport) {M absorption t : ℝ}
    (hM : M ≠ 0) (habsorption : absorption ≠ 0) (ht : t ≠ 0)
    (rapidity response : ℝ) :
    thetaCuspHawkingJostAIMEBareCoefficient rho M absorption t ≠ 0 ∧
      thetaCuspHawkingJostAIMESourceDressedResponse rho M absorption t = 0 ∧
      schwarzschildAbsorptionInducedCubicCoefficient M
        (thetaCuspHawkingJostAIMESectorLocalAbsorption rho rapidity response) t
        (thetaCuspHawkingPositiveJostFrequency rho : ℂ) = 0 := by
  exact ⟨thetaCuspHawkingJostAIMEBareCoefficient_ne_zero rho hM habsorption ht,
    thetaCuspHawkingJostAIMESourceDressedResponse_eq_zero rho M absorption t,
    thetaCuspHawkingJostAIMESelfAbsorbedCoefficient_eq_zero
      rho M rapidity response t⟩

end RHTower
