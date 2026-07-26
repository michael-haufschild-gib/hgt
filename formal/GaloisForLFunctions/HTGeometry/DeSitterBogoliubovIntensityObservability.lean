import GaloisForLFunctions.HTGeometry.DeSitterBogoliubovGammaBoundary
import GaloisForLFunctions.HTGeometry.WignerSmithLogClockObservability
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# De Sitter Bogoliubov phase--intensity observability

Sato--Suzuki equation (3.7) gives a type-I-global to static-patch de Sitter Gamma carrier

`A(z) = Gamma(z+a) / Gamma(-z+b)`,

where `z=-i*omega/2` and the two shifts differ by the angular integer `ell`.  This module applies
the general reflected-frequency theorem.  The product `A(z)A(-z)` is an explicit DA
sine--Pochhammer gauge, whereas `A(z)/A(-z)` is HT for every mass branch and angular mode.

Thus an intensity-only finite differential observation cannot recover the orientation-sensitive
phase.  The result concerns the observer's clock readout across global and static coordinates; it
does not classify de Sitter temporal evolution itself.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- Lower Gamma shift in the Sato--Suzuki type-I global-to-static coefficient. -/
def deSitterBogoliubovLowerShift (branchMass : ℂ) (ell : ℕ) : ℂ :=
  1 / 4 + branchMass / 2 - (ell : ℂ) / 2

/-- Upper Gamma shift in the Sato--Suzuki type-I global-to-static coefficient. -/
def deSitterBogoliubovUpperShift (branchMass : ℂ) (ell : ℕ) : ℂ :=
  1 / 4 + branchMass / 2 + (ell : ℂ) / 2

/-- The two physical shifts differ by exactly the angular integer. -/
theorem deSitterBogoliubovUpperShift_eq_lower_add_ell
    (branchMass : ℂ) (ell : ℕ) :
    deSitterBogoliubovUpperShift branchMass ell =
      deSitterBogoliubovLowerShift branchMass ell + (ell : ℂ) := by
  unfold deSitterBogoliubovUpperShift deSitterBogoliubovLowerShift
  ring

/-- The reflected-frequency de Sitter Gamma carrier `A(-z)`. -/
def deSitterTypeIStaticBogoliubovReflectedGammaCarrierMero
    (branchMass : ℂ) (ell : ℕ) : meroField Set.univ :=
  gammaOppositeShiftReflectedFrequencyMero
    (deSitterBogoliubovLowerShift branchMass ell)
    (deSitterBogoliubovUpperShift branchMass ell)

/-- The reflected-frequency intensity channel `A(z)A(-z)`. -/
def deSitterTypeIStaticBogoliubovIntensityMero
    (branchMass : ℂ) (ell : ℕ) : meroField Set.univ :=
  gammaOppositeShiftIntensityMero
    (deSitterBogoliubovLowerShift branchMass ell)
    (deSitterBogoliubovUpperShift branchMass ell)

/-- The orientation-sensitive phase channel `A(z)/A(-z)`. -/
def deSitterTypeIStaticBogoliubovPhaseMero
    (branchMass : ℂ) (ell : ℕ) : meroField Set.univ :=
  gammaOppositeShiftPhaseMero
    (deSitterBogoliubovLowerShift branchMass ell)
    (deSitterBogoliubovUpperShift branchMass ell)

/-- Wigner--Smith logarithmic delay of the de Sitter global-to-static Gamma carrier. -/
def deSitterTypeIStaticBogoliubovWignerSmithLogClockMero
    (branchMass : ℂ) (ell : ℕ) : meroField Set.univ :=
  HTGeometry.wignerSmithLogClock
    (deSitterTypeIStaticBogoliubovGammaCarrierMero branchMass ell)

/-- The previously formalized de Sitter carrier is the general opposite-shift amplitude. -/
theorem deSitterTypeIStaticBogoliubovGammaCarrierMero_eq_observableAmplitude
    (branchMass : ℂ) (ell : ℕ) :
    deSitterTypeIStaticBogoliubovGammaCarrierMero branchMass ell =
      gammaOppositeShiftQuotientMero
        (deSitterBogoliubovLowerShift branchMass ell)
        (deSitterBogoliubovUpperShift branchMass ell) := by
  rfl

/-- **De Sitter Wigner--Smith value relation.**  The delay is the exact difference of the two
oppositely oriented Gamma logarithmic derivatives. -/
theorem deSitterTypeIStaticBogoliubovWignerSmithLogClockMero_eq_orientedLogDerivatives
    (branchMass : ℂ) (ell : ℕ) :
    deSitterTypeIStaticBogoliubovWignerSmithLogClockMero branchMass ell =
      digammaShiftMero (deSitterBogoliubovLowerShift branchMass ell) -
        gammaNegativeLogDerivativeMero
          (deSitterBogoliubovUpperShift branchMass ell) := by
  rw [deSitterTypeIStaticBogoliubovWignerSmithLogClockMero,
    deSitterTypeIStaticBogoliubovGammaCarrierMero_eq_observableAmplitude]
  exact gammaOppositeShiftWignerSmithLogMero_eq_orientedLogDerivatives _ _

/-- **Exact de Sitter intensity value relation.**  Angular integrality removes every Gamma factor
from the reflected-frequency intensity and leaves the explicit sine--Pochhammer gauge. -/
theorem deSitterTypeIStaticBogoliubovIntensityMero_eq_shiftGauge
    (branchMass : ℂ) (ell : ℕ) :
    deSitterTypeIStaticBogoliubovIntensityMero branchMass ell =
      gammaReflectionIntegerShiftGaugeMero
        (deSitterBogoliubovLowerShift branchMass ell) ell := by
  unfold deSitterTypeIStaticBogoliubovIntensityMero
  rw [deSitterBogoliubovUpperShift_eq_lower_add_ell,
    gammaOppositeShiftIntensityMero_eq_integerShiftGauge]

/-- Every mass branch and angular mode has DA reflected-frequency intensity. -/
theorem differentialAlgebraicOver_deSitterTypeIStaticBogoliubovIntensityMero
    (branchMass : ℂ) (ell : ℕ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (deSitterTypeIStaticBogoliubovIntensityMero branchMass ell) := by
  rw [deSitterTypeIStaticBogoliubovIntensityMero_eq_shiftGauge]
  exact differentialAlgebraicOver_gammaReflectionIntegerShiftGaugeMero _ ell

/-- Every mass branch and angular mode retains HT in its orientation-sensitive phase. -/
theorem hypertranscendentalOver_deSitterTypeIStaticBogoliubovPhaseMero
    (branchMass : ℂ) (ell : ℕ) :
    HypertranscendentalOver (RatFunc ℂ)
      (deSitterTypeIStaticBogoliubovPhaseMero branchMass ell) := by
  exact hypertranscendentalOver_gammaOppositeShiftPhaseMero _ _

/-- Every mass branch and angular mode also retains HT in the observable Wigner--Smith delay. -/
theorem hypertranscendentalOver_deSitterTypeIStaticBogoliubovWignerSmithLogClockMero
    (branchMass : ℂ) (ell : ℕ) :
    HypertranscendentalOver (RatFunc ℂ)
      (deSitterTypeIStaticBogoliubovWignerSmithLogClockMero branchMass ell) := by
  rw [deSitterTypeIStaticBogoliubovWignerSmithLogClockMero,
    HTGeometry.hypertranscendentalOver_wignerSmithLogClock_iff]
  exact hypertranscendentalOver_deSitterTypeIStaticBogoliubovGammaCarrierMero
    branchMass ell

/-- The two observation channels recover the square of the exact de Sitter amplitude. -/
theorem deSitterTypeIStaticBogoliubovPhase_mul_intensity
    (branchMass : ℂ) (ell : ℕ) :
    deSitterTypeIStaticBogoliubovPhaseMero branchMass ell *
        deSitterTypeIStaticBogoliubovIntensityMero branchMass ell =
      (deSitterTypeIStaticBogoliubovGammaCarrierMero branchMass ell) ^ 2 := by
  exact gammaOppositeShiftPhase_mul_intensity _ _

/-- No DA multiplicative calibration turns the reflected-frequency carrier into the original
de Sitter amplitude. -/
theorem deSitterTypeIStaticBogoliubovGammaCarrierMero_ne_da_mul_reflected
    (branchMass : ℂ) (ell : ℕ) (g : meroField Set.univ)
    (hg : DifferentialAlgebraicOver (RatFunc ℂ) g) :
    deSitterTypeIStaticBogoliubovGammaCarrierMero branchMass ell ≠
      g * deSitterTypeIStaticBogoliubovReflectedGammaCarrierMero branchMass ell := by
  intro heq
  apply hypertranscendentalOver_deSitterTypeIStaticBogoliubovPhaseMero branchMass ell
  have hphase : deSitterTypeIStaticBogoliubovPhaseMero branchMass ell = g := by
    unfold deSitterTypeIStaticBogoliubovPhaseMero
    unfold deSitterTypeIStaticBogoliubovReflectedGammaCarrierMero at heq
    rw [deSitterTypeIStaticBogoliubovGammaCarrierMero_eq_observableAmplitude] at heq
    unfold gammaOppositeShiftPhaseMero
    rw [heq]
    exact mul_div_cancel_right₀ g
      (gammaOppositeShiftReflectedFrequencyMero_ne_zero _ _)
  rw [hphase]
  exact hg

/-- **Finite-observation non-recovery.**  Rational clocks and the complete de Sitter intensity,
closed under finitely many field operations and differentiations, cannot reconstruct the phase.
An orientation-sensitive realization must contain an HT non-intensity source. -/
theorem no_scalarAwareFiniteDifferentialCircuit_deSitterPhase_from_intensity
    (branchMass : ℂ) (ell : ℕ) :
    ¬ HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ)
        (fun a => a = deSitterTypeIStaticBogoliubovIntensityMero branchMass ell))
      (deSitterTypeIStaticBogoliubovPhaseMero branchMass ell) := by
  intro hcircuit
  obtain ⟨a, ha, hHT⟩ :=
    HTGeometry.exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit
      (hypertranscendentalOver_deSitterTypeIStaticBogoliubovPhaseMero branchMass ell)
      hcircuit
  rw [ha] at hHT
  exact hHT
    (differentialAlgebraicOver_deSitterTypeIStaticBogoliubovIntensityMero
      branchMass ell)

/-- **Positive de Sitter delay boundary.**  Rational clocks and complete DA intensity cannot
finitely reconstruct the HT Wigner--Smith delay. -/
theorem no_scalarAwareFiniteDifferentialCircuit_deSitterWignerSmith_from_intensity
    (branchMass : ℂ) (ell : ℕ) :
    ¬ HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ)
        (fun a => a = deSitterTypeIStaticBogoliubovIntensityMero branchMass ell))
      (deSitterTypeIStaticBogoliubovWignerSmithLogClockMero branchMass ell) := by
  exact HTGeometry.no_scalarAwareFiniteDifferentialCircuit_wignerSmith_from_daObservation
    (deSitterTypeIStaticBogoliubovGammaCarrierMero branchMass ell)
    (deSitterTypeIStaticBogoliubovIntensityMero branchMass ell)
    (hypertranscendentalOver_deSitterTypeIStaticBogoliubovGammaCarrierMero
      branchMass ell)
    (differentialAlgebraicOver_deSitterTypeIStaticBogoliubovIntensityMero
      branchMass ell)

end

end GaloisForLFunctions
