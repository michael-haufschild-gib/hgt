import GaloisForLFunctions.HTGeometry.ConstantFieldQEDGammaClock
import GaloisForLFunctions.HTGeometry.CircularBetaEnsembleNormalizerBoundary

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

local instance circuitAtomDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance circuitAtomDifferential :
    Differential (meroField Set.univ) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance circuitAtomRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance circuitAtomRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance circuitAtomDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

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

#print axioms GaloisForLFunctions.exists_hypertranscendental_atom_constantMagneticQEDSpinStatistics_self
