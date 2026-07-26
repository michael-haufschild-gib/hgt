import GaloisForLFunctions.HTGeometry.ConstantFieldQEDGammaClock
import GaloisForLFunctions.HTGeometry.CircularBetaEnsembleNormalizerBoundary
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Premise-free instances of the scalar-aware circuit law

A hypertranscendental carrier is a one-atom circuit over itself, so the circuit premise of the
scalar-aware atom law is discharged by the `atom` constructor.  The two concrete carriers already
proved hypertranscendental in the corpus therefore give premise-free instances of the law.
-/

open Set

namespace GaloisForLFunctions

open Bottcher

noncomputable section

open scoped UnivMeroFieldInstances

/-- The constant-magnetic QED spin-statistics ratio is an HT atom of its own one-atom circuit. -/
theorem exists_hypertranscendental_atom_constantMagneticQEDSpinStatistics_self :
    ∃ a : meroField Set.univ,
      a = constantMagneticQEDSpinStatisticsRatioMero ∧
        HypertranscendentalOver (RatFunc ℂ) a :=
  exists_hypertranscendental_atom_of_constantMagneticQEDSpinStatisticsCircuit
    (Atom := fun a => a = constantMagneticQEDSpinStatisticsRatioMero)
    (HTGeometry.FiniteDifferentialCircuit.atom (Or.inl rfl))

end

end GaloisForLFunctions
