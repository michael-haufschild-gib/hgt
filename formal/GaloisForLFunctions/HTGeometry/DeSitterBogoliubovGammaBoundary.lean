import GaloisForLFunctions.HTGeometry.GammaOrientationQuotientBoundary
import GaloisForLFunctions.HTGeometry.MeromorphicExponentialGaugeDA
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# De Sitter Bogoliubov Gamma boundary

The exact type-I-global to static-patch scalar Bogoliubov coefficient in four-dimensional de
Sitter space contains, after the frequency calibration `z = -i*omega/2`, a carrier

`Gamma(z+a) / Gamma(-z+b)`.

Euler reflection changes the negative-orientation denominator into a positive-orientation Gamma
factor.  Thus the two orbit charges add rather than cancel.  If their shifts are separated they
give two charge-one orbits; if they differ by an integer they give one charge-two orbit.  The
carrier is therefore unconditionally hypertranscendental for every pair of shifts.  Any elementary
exponential readout gauge preserves this conclusion.

The theorem classifies the exact frequency observable relating two de Sitter clocks.  It does not
assert that cosmic time evolution itself is hypertranscendental.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- The variable Gamma carrier in Sato--Suzuki equation (3.7).  `branchMass` represents the
signed mass index `±nu`; `ell` is the angular momentum and `z=-i*omega/2`. -/
def deSitterTypeIStaticBogoliubovGammaCarrierMero
    (branchMass : ℂ) (ell : ℕ) : meroField Set.univ :=
  gammaOppositeShiftQuotientMero
    (1 / 4 + branchMass / 2 - (ell : ℂ) / 2)
    (1 / 4 + branchMass / 2 + (ell : ℂ) / 2)

/-- The elementary frequency phase multiplying the exact de Sitter Gamma carrier. -/
def deSitterTypeIStaticBogoliubovReadoutMero
    (branchMass lambda : ℂ) (ell : ℕ) : meroField Set.univ :=
  physicalExponentialMero lambda *
    deSitterTypeIStaticBogoliubovGammaCarrierMero branchMass ell

/-- Every mass branch and angular mode has an HT global-to-static de Sitter Gamma carrier. -/
theorem hypertranscendentalOver_deSitterTypeIStaticBogoliubovGammaCarrierMero
    (branchMass : ℂ) (ell : ℕ) :
    HypertranscendentalOver (RatFunc ℂ)
      (deSitterTypeIStaticBogoliubovGammaCarrierMero branchMass ell) := by
  exact hypertranscendentalOver_gammaOppositeShiftQuotientMero _ _

/-- Exponential frequency phases do not hide the de Sitter carrier's HT source. -/
theorem hypertranscendentalOver_deSitterTypeIStaticBogoliubovReadoutMero
    (branchMass lambda : ℂ) (ell : ℕ) :
    HypertranscendentalOver (RatFunc ℂ)
      (deSitterTypeIStaticBogoliubovReadoutMero branchMass lambda ell) := by
  rw [deSitterTypeIStaticBogoliubovReadoutMero, mul_comm]
  exact (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    (differentialAlgebraicOver_physicalExponentialMero lambda)
    (physicalExponentialMero_ne_zero lambda)).2
      (hypertranscendentalOver_deSitterTypeIStaticBogoliubovGammaCarrierMero
        branchMass ell)

/-- **Positive source extraction for de Sitter readout circuits.**  Any scalar-aware finite
differential circuit realizing the exact readout must contain an HT non-scalar atom. -/
theorem exists_hypertranscendental_atom_of_deSitterBogoliubovReadoutCircuit
    (branchMass lambda : ℂ) (ell : ℕ)
    {Atom : meroField Set.univ → Prop}
    (hcircuit : HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ) Atom)
      (deSitterTypeIStaticBogoliubovReadoutMero branchMass lambda ell)) :
    ∃ a : meroField Set.univ,
      Atom a ∧ HypertranscendentalOver (RatFunc ℂ) a :=
  HTGeometry.exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit
    (hypertranscendentalOver_deSitterTypeIStaticBogoliubovReadoutMero
      branchMass lambda ell) hcircuit

end

end GaloisForLFunctions
