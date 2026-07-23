import GaloisForLFunctions.HTGeometry.CoulombPhaseIntensityObservability
import GaloisForLFunctions.HTGeometry.DeSitterBogoliubovIntensityObservability

/-!
# Coulomb/de Sitter zero-mode observability universality

Every Coulomb partial wave is exactly a de Sitter type-I angular-zero Bogoliubov sector after the
branch-mass substitution m = 2 ell + 3/2.  Both Gamma shifts then equal ell + 1.  Original and
reflected carriers, intensity, orientation-sensitive phase, and Wigner--Smith clock coincide
across the two physical presentations.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- De Sitter branch mass that realizes Coulomb partial wave ell in angular mode zero. -/
def coulombDeSitterZeroModeBranchMass (ell : ℕ) : ℂ :=
  2 * (ell : ℂ) + 3 / 2

theorem deSitterLowerShift_zero_coulombBranchMass (ell : ℕ) :
    deSitterBogoliubovLowerShift (coulombDeSitterZeroModeBranchMass ell) 0 =
      ((ell + 1 : ℕ) : ℂ) := by
  rw [deSitterBogoliubovLowerShift, coulombDeSitterZeroModeBranchMass]
  push_cast
  ring

theorem deSitterUpperShift_zero_coulombBranchMass (ell : ℕ) :
    deSitterBogoliubovUpperShift (coulombDeSitterZeroModeBranchMass ell) 0 =
      ((ell + 1 : ℕ) : ℂ) := by
  rw [deSitterBogoliubovUpperShift, coulombDeSitterZeroModeBranchMass]
  push_cast
  ring

theorem deSitterZeroModeGammaCarrier_eq_coulombPhase (ell : ℕ) :
    deSitterTypeIStaticBogoliubovGammaCarrierMero
        (coulombDeSitterZeroModeBranchMass ell) 0 =
      coulombPhaseMero ell := by
  rw [deSitterTypeIStaticBogoliubovGammaCarrierMero_eq_observableAmplitude,
    coulombPhaseMero_eq_oppositeShiftQuotient,
    deSitterLowerShift_zero_coulombBranchMass,
    deSitterUpperShift_zero_coulombBranchMass]

theorem deSitterZeroModeReflectedCarrier_eq_coulombReflected (ell : ℕ) :
    deSitterTypeIStaticBogoliubovReflectedGammaCarrierMero
        (coulombDeSitterZeroModeBranchMass ell) 0 =
      coulombPhaseReflectedFrequencyMero ell := by
  unfold deSitterTypeIStaticBogoliubovReflectedGammaCarrierMero
  unfold coulombPhaseReflectedFrequencyMero
  rw [deSitterLowerShift_zero_coulombBranchMass,
    deSitterUpperShift_zero_coulombBranchMass]

theorem deSitterZeroModeIntensity_eq_coulombIntensity (ell : ℕ) :
    deSitterTypeIStaticBogoliubovIntensityMero
        (coulombDeSitterZeroModeBranchMass ell) 0 =
      coulombPhaseIntensityObservationMero ell := by
  unfold deSitterTypeIStaticBogoliubovIntensityMero
  unfold coulombPhaseIntensityObservationMero
  rw [deSitterLowerShift_zero_coulombBranchMass,
    deSitterUpperShift_zero_coulombBranchMass]

theorem deSitterZeroModePhase_eq_coulombOrientation (ell : ℕ) :
    deSitterTypeIStaticBogoliubovPhaseMero
        (coulombDeSitterZeroModeBranchMass ell) 0 =
      coulombPhaseOrientationObservationMero ell := by
  unfold deSitterTypeIStaticBogoliubovPhaseMero
  unfold coulombPhaseOrientationObservationMero
  rw [deSitterLowerShift_zero_coulombBranchMass,
    deSitterUpperShift_zero_coulombBranchMass]

theorem deSitterZeroModeWignerSmith_eq_coulombWignerSmith (ell : ℕ) :
    deSitterTypeIStaticBogoliubovWignerSmithLogClockMero
        (coulombDeSitterZeroModeBranchMass ell) 0 =
      coulombWignerSmithLogClockMero ell := by
  unfold deSitterTypeIStaticBogoliubovWignerSmithLogClockMero
  unfold coulombWignerSmithLogClockMero
  rw [deSitterZeroModeGammaCarrier_eq_coulombPhase]

/-- **Coulomb/de Sitter zero-mode observability universality.**  Full phase/intensity/delay
observation tuple is identical under the branch-mass embedding, and common intensity is one. -/
theorem coulombDeSitter_zeroModeObservabilityUniversality (ell : ℕ) :
    deSitterTypeIStaticBogoliubovGammaCarrierMero
        (coulombDeSitterZeroModeBranchMass ell) 0 =
        coulombPhaseMero ell ∧
      deSitterTypeIStaticBogoliubovReflectedGammaCarrierMero
        (coulombDeSitterZeroModeBranchMass ell) 0 =
        coulombPhaseReflectedFrequencyMero ell ∧
      deSitterTypeIStaticBogoliubovIntensityMero
        (coulombDeSitterZeroModeBranchMass ell) 0 =
        coulombPhaseIntensityObservationMero ell ∧
      deSitterTypeIStaticBogoliubovPhaseMero
        (coulombDeSitterZeroModeBranchMass ell) 0 =
        coulombPhaseOrientationObservationMero ell ∧
      deSitterTypeIStaticBogoliubovWignerSmithLogClockMero
        (coulombDeSitterZeroModeBranchMass ell) 0 =
        coulombWignerSmithLogClockMero ell ∧
      deSitterTypeIStaticBogoliubovIntensityMero
        (coulombDeSitterZeroModeBranchMass ell) 0 = 1 :=
  ⟨deSitterZeroModeGammaCarrier_eq_coulombPhase ell,
    deSitterZeroModeReflectedCarrier_eq_coulombReflected ell,
    deSitterZeroModeIntensity_eq_coulombIntensity ell,
    deSitterZeroModePhase_eq_coulombOrientation ell,
    deSitterZeroModeWignerSmith_eq_coulombWignerSmith ell,
    (deSitterZeroModeIntensity_eq_coulombIntensity ell).trans
      (coulombPhaseIntensityObservationMero_eq_one ell)⟩

end

end GaloisForLFunctions
