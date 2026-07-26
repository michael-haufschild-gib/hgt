import GaloisForLFunctions.HTGeometry.CoulombPhaseIntensityObservability
import GaloisForLFunctions.HTGeometry.DeSitterBogoliubovIntensityObservability
import GaloisForLFunctions.HTGeometry.HorizonBogoliubovGammaObservability
import GaloisForLFunctions.HTGeometry.FamilyDifferentialCircuitBlindnessUniversalityLaw
import GaloisForLFunctions.RHTower.ZetaGammaPhaseIntensityObservability

/-!
# Joint Gamma intensity-atlas circuit-blindness universality

Four differentially algebraic Gamma intensity channels are made jointly available to one finite
differential circuit.  Even this enlarged cross-system palette cannot recover any of ten
orientation-sensitive Coulomb, de Sitter, horizon, or centered zeta--Gamma observables.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace RHTower

open GaloisForLFunctions Bottcher Polynomial

noncomputable section

local instance jointGammaIntensityAtlasDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance jointGammaIntensityAtlasDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance jointGammaIntensityAtlasRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance jointGammaIntensityAtlasRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance jointGammaIntensityAtlasDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance jointGammaIntensityAtlasCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- Four jointly available differentially algebraic intensity channels. -/
inductive JointGammaIntensityChannel
  | coulomb
  | deSitter
  | horizon
  | centeredZetaGamma

/-- Ten orientation-sensitive phase, delay, and projective channels. -/
inductive JointGammaOrientedChannel
  | coulombPhase
  | coulombWignerSmith
  | deSitterPhase
  | deSitterWignerSmith
  | horizonPhase
  | horizonWignerSmith
  | centeredZetaGammaPhase
  | centeredZetaGammaWignerSmith
  | centeredZetaGammaProjectiveConnection
  | centeredZetaGammaSchwarzian

/-- Joint intensity palette spanning Coulomb, de Sitter, horizon, and centered zeta--Gamma
systems. -/
def jointGammaIntensityAtlas (branchMass : ℂ) (ell : ℕ) :
    JointGammaIntensityChannel → meroField Set.univ
  | .coulomb => coulombPhaseIntensityObservationMero ell
  | .deSitter => deSitterTypeIStaticBogoliubovIntensityMero branchMass ell
  | .horizon => horizonBogoliubovGammaIntensityCoreMero
  | .centeredZetaGamma => centeredZetaGammaIntensityObservationMero

/-- Orientation-sensitive targets tested against the shared intensity palette. -/
def jointGammaOrientedObservableAtlas (branchMass : ℂ) (ell : ℕ) :
    JointGammaOrientedChannel → meroField Set.univ
  | .coulombPhase => coulombPhaseOrientationObservationMero ell
  | .coulombWignerSmith => coulombWignerSmithLogClockMero ell
  | .deSitterPhase => deSitterTypeIStaticBogoliubovPhaseMero branchMass ell
  | .deSitterWignerSmith =>
      deSitterTypeIStaticBogoliubovWignerSmithLogClockMero branchMass ell
  | .horizonPhase => horizonBogoliubovGammaPhaseQuotientMero
  | .horizonWignerSmith => horizonBogoliubovGammaWignerSmithLogClockMero
  | .centeredZetaGammaPhase => centeredZetaGammaPhaseObservationMero
  | .centeredZetaGammaWignerSmith => centeredZetaGammaWignerSmithLogClockMero
  | .centeredZetaGammaProjectiveConnection =>
      centeredZetaGammaProjectiveHorizonConnectionMero
  | .centeredZetaGammaSchwarzian => centeredZetaGammaProjectiveSchwarzianMero

/-- Complete joint-atlas certificate: every observation is DA, every oriented target is HT, and
the entire target atlas is blind to scalar-aware finite circuits allowed to mix all four
observations. -/
structure JointGammaIntensityAtlasCircuitBlindnessCertificate
    (branchMass : ℂ) (ell : ℕ) : Prop where
  observation_differentialAlgebraic :
    ∀ i, DifferentialAlgebraicOver (RatFunc ℂ)
      (jointGammaIntensityAtlas branchMass ell i)
  target_hypertranscendental :
    ∀ j, HypertranscendentalOver (RatFunc ℂ)
      (jointGammaOrientedObservableAtlas branchMass ell j)
  circuit_blindness :
    ∀ j, ¬ HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ)
        (fun a => a ∈ Set.range (jointGammaIntensityAtlas branchMass ell)))
      (jointGammaOrientedObservableAtlas branchMass ell j)

/-- **Joint Gamma intensity-atlas circuit-blindness universality law.**  For every angular mode
and de Sitter mass branch, freely mixing all four DA intensity systems still cannot produce any
of the ten HT oriented observables by a scalar-aware finite differential circuit. -/
theorem jointGammaIntensityAtlas_circuitBlindnessUniversality
    (branchMass : ℂ) (ell : ℕ) :
    JointGammaIntensityAtlasCircuitBlindnessCertificate branchMass ell := by
  have hObservation :
      ∀ i, DifferentialAlgebraicOver (RatFunc ℂ)
        (jointGammaIntensityAtlas branchMass ell i) := by
    intro i
    cases i with
    | coulomb =>
        exact differentialAlgebraicOver_coulombPhaseIntensityObservationMero ell
    | deSitter =>
        exact
          differentialAlgebraicOver_deSitterTypeIStaticBogoliubovIntensityMero branchMass ell
    | horizon =>
        exact differentialAlgebraicOver_horizonBogoliubovGammaIntensityCoreMero
    | centeredZetaGamma =>
        exact differentialAlgebraicOver_centeredZetaGammaIntensityObservationMero
  have hTarget :
      ∀ j, HypertranscendentalOver (RatFunc ℂ)
        (jointGammaOrientedObservableAtlas branchMass ell j) := by
    intro j
    cases j with
    | coulombPhase =>
        exact hypertranscendentalOver_coulombPhaseOrientationObservationMero ell
    | coulombWignerSmith =>
        exact hypertranscendentalOver_coulombWignerSmithLogClockMero ell
    | deSitterPhase =>
        exact hypertranscendentalOver_deSitterTypeIStaticBogoliubovPhaseMero branchMass ell
    | deSitterWignerSmith =>
        exact
          hypertranscendentalOver_deSitterTypeIStaticBogoliubovWignerSmithLogClockMero
            branchMass ell
    | horizonPhase =>
        exact hypertranscendentalOver_horizonBogoliubovGammaPhaseQuotientMero
    | horizonWignerSmith =>
        exact hypertranscendentalOver_horizonBogoliubovGammaWignerSmithLogClockMero
    | centeredZetaGammaPhase =>
        exact hypertranscendentalOver_centeredZetaGammaPhaseObservationMero
    | centeredZetaGammaWignerSmith =>
        exact hypertranscendentalOver_centeredZetaGammaWignerSmithLogClockMero
    | centeredZetaGammaProjectiveConnection =>
        exact hypertranscendentalOver_centeredZetaGammaProjectiveHorizonConnectionMero
    | centeredZetaGammaSchwarzian =>
        exact hypertranscendentalOver_centeredZetaGammaProjectiveSchwarzianMero
  exact ⟨hObservation, hTarget,
    HTGeometry.no_scalarAwareFiniteDifferentialCircuit_from_differentialAlgebraic_family_all
      (jointGammaIntensityAtlas branchMass ell) hObservation
      (jointGammaOrientedObservableAtlas branchMass ell) hTarget⟩

end

end RHTower
