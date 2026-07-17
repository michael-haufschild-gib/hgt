import GaloisForLFunctions.HTGeometry.ThermalCFTGammaResponseBoundary
import GaloisForLFunctions.HTGeometry.CoulombGammaPhaseClock

/-!
# Fermi-function Coulomb Gamma core

The relativistic Fermi function governing the Coulomb correction to beta decay contains

`exp(pi*xi) * |Gamma(eta+i*xi)|^2`.

This is equation (1) of R. J. Hill and R. Plestid, *Field Theory of the Fermi Function*,
arXiv:2309.07343.  Its Gamma--Boltzmann core is exactly the thermal-CFT KMS response after the
clock calibration `kappa = 2*pi*xi`.  It therefore obeys an exact charge-orientation detailed
balance law.

At integral angular-momentum weight, the Fermi magnitude core and the Coulomb scattering phase
are complementary observations of the same Gamma pair: multiplying them reconstructs the square
of the positive-orientation Gamma amplitude.  This is an observability relation, not temporal
evolution.  The remaining kinematic and nuclear-size factors in the full Fermi function are not
identified with the core defined here.
-/

open Complex

namespace GaloisForLFunctions

noncomputable section

/-- Gamma--Boltzmann core of the relativistic Fermi function. -/
def fermiCoulombGammaCoreValue (eta xi : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * xi) *
    Complex.Gamma (eta + Complex.I * xi) *
      Complex.Gamma (eta - Complex.I * xi)

/-- **Cross-domain clock calibration.**  The weak-decay Fermi Gamma core is literally the
thermal-CFT KMS response at calibrated frequency `kappa = 2*pi*xi`. -/
theorem fermiCoulombGammaCoreValue_eq_thermalCFTKMSResponseValue
    (eta xi : ℂ) :
    fermiCoulombGammaCoreValue eta xi =
      thermalCFTKMSResponseValue eta (2 * Real.pi * xi) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [fermiCoulombGammaCoreValue, thermalCFTKMSResponseValue,
    thermalCFTFrequencyResponseValue, gammaReflectionProductValue]
  have hz : Complex.I * (2 * Real.pi * xi) / (2 * Real.pi) =
      Complex.I * xi := by
    field_simp [hpi]
  rw [hz]
  have he : (-Real.pi * Complex.I) * (Complex.I * xi) =
      (Real.pi : ℂ) * xi := by
    rw [show (-Real.pi * Complex.I) * (Complex.I * xi) =
      -(Real.pi : ℂ) * ((Complex.I * Complex.I) * xi) by ring,
      Complex.I_mul_I]
    ring
  rw [he]
  ring

/-- **Exact charge-orientation detailed balance.**  Reversing the Coulomb parameter changes only
the elementary Boltzmann readout; the reflected Gamma product is even. -/
theorem fermiCoulombGammaCoreValue_neg (eta xi : ℂ) :
    fermiCoulombGammaCoreValue eta (-xi) =
      Complex.exp (-2 * Real.pi * xi) * fermiCoulombGammaCoreValue eta xi := by
  rw [fermiCoulombGammaCoreValue_eq_thermalCFTKMSResponseValue,
    fermiCoulombGammaCoreValue_eq_thermalCFTKMSResponseValue]
  have harg : 2 * (Real.pi : ℂ) * (-xi) =
      -(2 * (Real.pi : ℂ) * xi) := by ring
  rw [harg, thermalCFTKMSResponseValue_neg]
  congr 1
  ring

/-- **Magnitude--phase reconstruction.**  At the Coulomb partial-wave weight `ell+1`, multiplying
the weak-decay magnitude core by the unitary Coulomb phase reconstructs the squared
positive-orientation Gamma amplitude. -/
theorem fermiCoulombGammaCoreValue_mul_coulombPhaseValue
    (ell : ℕ) (xi : ℝ) :
    fermiCoulombGammaCoreValue (((ell + 1 : ℕ) : ℂ) : ℂ) (xi : ℂ) *
        coulombPhaseValue ell xi =
      Complex.exp ((Real.pi : ℂ) * (xi : ℂ)) *
        Complex.Gamma (((ell + 1 : ℕ) : ℂ) + Complex.I * (xi : ℂ)) ^ 2 := by
  have hp : (((ell + 1 : ℕ) : ℂ) + Complex.I * (xi : ℂ)) =
      (ell : ℂ) + 1 + (xi : ℂ) * Complex.I := by
    push_cast
    ring
  have hm : (((ell + 1 : ℕ) : ℂ) - Complex.I * (xi : ℂ)) =
      (ell : ℂ) + 1 - (xi : ℂ) * Complex.I := by
    push_cast
    ring
  have hden : Complex.Gamma
      ((ell : ℂ) + 1 - (xi : ℂ) * Complex.I) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp
    positivity
  rw [fermiCoulombGammaCoreValue, coulombPhaseValue]
  rw [hp, hm]
  field_simp [hden]

end

end GaloisForLFunctions
