import GaloisForLFunctions.HTGeometry.DispersivePDE.ScalarSolitons
import GaloisForLFunctions.HTGeometry.DispersivePDE.TheGrossPitaevskiiCorrectorOfTheKdVPulse
import GaloisForLFunctions.HTGeometry.DispersivePDE.PairedCriticalBubblesAndTheKerrThreshold
import GaloisForLFunctions.HTGeometry.DispersivePDE.TheEnergyGapOfFourUnequalCriticalBubbles
import GaloisForLFunctions.HTGeometry.DispersivePDE.TheGeometricMeanThresholdForFourUnequalModes
import GaloisForLFunctions.HTGeometry.DispersivePDE.HowFourSynchronizedAmplitudesMoveWithTheCoupling
import GaloisForLFunctions.HTGeometry.DispersivePDE.TheCriticalCouplingPoleOfFourSynchronizedModes
import GaloisForLFunctions.HTGeometry.DispersivePDE.TheLoadParameterOfWeightedCriticalModes
import GaloisForLFunctions.HTGeometry.DispersivePDE.TheGeometricThresholdForWeightedCriticalModes
import GaloisForLFunctions.HTGeometry.DispersivePDE.TheCriticalProfileOfWeightedSynchronizedModes
import GaloisForLFunctions.HTGeometry.DispersivePDE.NLSSolitons
import GaloisForLFunctions.HTGeometry.DispersivePDE.FDNLSApplications
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaApplications
import GaloisForLFunctions.HTGeometry.DispersivePDE.MondalElectronAcousticKP
import GaloisForLFunctions.HTGeometry.DispersivePDE.CubicHierarchyResonance
import GaloisForLFunctions.HTGeometry.DispersivePDE.CubicGraphThreeWave
import GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScatteringBoundary
import GaloisForLFunctions.HTGeometry.DispersivePDE.ReflectionDiscriminant
import GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScatteringAllOrders
import GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScatteringComplementaryPhases
import GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScatteringSubsetExpansion
import GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScatteringHirotaFlow
import GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScatteringTau
import GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScatteringDeterminantFlow
import GaloisForLFunctions.HTGeometry.DispersivePDE.MondalElectronAcousticBreathers
import GaloisForLFunctions.HTGeometry.DispersivePDE.MondalElectronAcousticCoefficients
import GaloisForLFunctions.HTGeometry.DispersivePDE.MondalElectronAcousticSuperposition
import GaloisForLFunctions.HTGeometry.DispersivePDE.MondalElectronAcousticLumpSingularity
import GaloisForLFunctions.HTGeometry.BelinskiZakharovJacobiTodaBridge
import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovTwoPoleBridge

/-!
# Closed dispersive-PDE and soliton atlas

One assumption-free certificate gathers the continuous scalar equations, cubic NLS profiles,
fractional discrete NLS modes, and existing inverse-scattering/Toda soliton structures used in the
corpus.  Every field is a closed proposition; analytic regularity is carried by derivative witnesses
inside the corresponding jets.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE

open GaloisForLFunctions.HTGeometry.FDNLS

/-- Closed atlas spanning the new PDE profiles and pre-existing corpus soliton structures. -/
structure ClosedDispersiveAtlas : Prop where
  brizardElastica : BrizardElastica.ClosedAtlas.{0}
  kdv : SolvesKdV kdvSolitonJet
  potentialKdV : SolvesPotentialKdV potentialKdVPulseJet
  modifiedKdV : SolvesModifiedKdV modifiedKdVKinkJet
  airy : SolvesAiry airyWaveJet
  kawahara : SolvesScaledKawahara kawaharaSolitonJet
  linearKawahara : SolvesLinearKawahara kawaharaLinearWaveJet
  kpI : SolvesKP (-1) kpLineSolitonJet
  kpII : SolvesKP 1 kpLineSolitonJet
  mondalGeneralKP : ∀ α δ ρ k slope shift : ℝ,
    SolvesGeneralKP α δ ρ (mondalSolitonJet α δ ρ k slope shift)
  mondalOneTauHirota : ∀ δ ρ k slope shift : ℝ,
    SolvesHirotaKP δ ρ
      (mondalOneExponentialTauJet (mondalFrequency δ ρ k slope) k (k * slope) shift)
  mondalTwoTauHirota : ∀ δ ρ k₁ slope₁ shift₁ k₂ slope₂ shift₂ : ℝ,
    SolvesHirotaKP δ ρ
      (mondalCorrectedTwoExponentialTauJet δ ρ k₁ slope₁ shift₁ k₂ slope₂ shift₂)
  mondalLumpHirota : ∀ beta gammaLog r b d m : ℝ,
    SolvesHirotaKP beta (-Real.exp gammaLog)
      (mondalCorrectedLumpTauJet beta gammaLog r b d m)
  mondalPrintedRightTimeReverse : ∀ β γ k slope shift : ℝ,
    SolvesHirotaKPTimeReversed (-β) γ
      (mondalOneExponentialTauJet
        (mondalPrintedRightFrequency β γ k slope) k (k * slope) shift)
  mondalPrintedLeftTimeReverse : ∀ β γ k slope shift : ℝ,
    SolvesHirotaKPTimeReversed β (-γ)
      (mondalOneExponentialTauJet
        (mondalPrintedLeftFrequency β γ k slope) k (k * slope) shift)
  mondalPrintedRightTwoTimeReverse : ∀ β γ k₁ slope₁ shift₁ k₂ slope₂ shift₂ : ℝ,
    SolvesHirotaKPTimeReversed (-β) γ
      (mondalPrintedRightTwoTauJet β γ k₁ slope₁ shift₁ k₂ slope₂ shift₂)
  mondalPrintedLeftTwoTimeReverse : ∀ β γ k₁ slope₁ shift₁ k₂ slope₂ shift₂ : ℝ,
    SolvesHirotaKPTimeReversed β (-γ)
      (mondalPrintedLeftTwoTauJet β γ k₁ slope₁ shift₁ k₂ slope₂ shift₂)
  mondalPhysicalLumpTauZero : ∀ q p s : ℝ,
    mondalPhysicalLumpTau q p s 0
      (Real.sqrt (-mondalPhysicalLumpOffset q p s)) 0 = 0
  mondalNegativeBetaLumpTauZero : ∀ betaLog gammaLog r b d m : ℝ,
    (mondalCorrectedLumpTauJet (-Real.exp betaLog) gammaLog r b d m).u 0
      (mondalLumpZeroX betaLog gammaLog r b d m)
      (mondalLumpZeroY betaLog gammaLog r b d m) = 0
  mondalPrintedLumpRejected : ¬ SolvesHirotaKP (-1) (-1) mondalPrintedLumpWitness
  mondalPhysicalBreatherTauZero : ∀ betaLog gammaLog mLog n slopeIm : ℝ,
    ∃ z : ℂ,
      mondalRealBreatherTau
        (mondalPhysicalBreatherInteraction betaLog gammaLog mLog n slopeIm) z = 0
  mondalPositiveBreatherTauNonzero : ∀ a : ℝ, ∀ z : ℂ,
    mondalRealBreatherTau (mondalPositiveBreatherInteraction a) z ≠ 0
  mondalSubcriticalPhasePositive : ∀ q p r : ℝ,
    0 < mondalPhaseCorrectionRatio q p (mondalSubcriticalTemperatureAmplitude q p r)
  mondalCriticalPhaseZero : ∀ q p : ℝ,
    mondalPhaseCorrectionRatio q p (mondalCriticalTemperatureAmplitude q p) = 0
  mondalSupercriticalPhaseNegative : ∀ q p r : ℝ,
    mondalPhaseCorrectionRatio q p (mondalSupercriticalTemperatureAmplitude q p r) < 0
  mondalConcentrationSlopeAtZeroPositive : ∀ q s : ℝ,
    0 < mondalAmplitudeConcentrationSlope q s 0
  mondalConcentrationSlopeAtOneNegative : ∀ q s : ℝ,
    mondalAmplitudeConcentrationSlope q s 1 < 0
  mondalRaisedTemperatureLowersAmplitude : ∀ q p s r : ℝ,
    mondalAmplitudeAtConcentration q (mondalRaisedTemperatureAmplitude s r)
        (mondalHotConcentration p) <
      mondalAmplitudeAtConcentration q s (mondalHotConcentration p)
  mondalRaisedKappaRaisesAmplitude : ∀ q p s r : ℝ,
    mondalAmplitudeAtConcentration q s (mondalHotConcentration p) <
      mondalAmplitudeAtConcentration (mondalRaisedKappaParameter q r) s
        (mondalHotConcentration p)
  mondalDirectSuperpositionRejected :
    ¬ SolvesGeneralKP 6 1 3 mondalCanonicalDoubledJet
  shriraPesenson : ∀ α β γ₁ γ₂ ε : ℝ,
    SolvesShriraPesenson α β γ₁ γ₂ ε shriraPesensonTiltJet
  brightNLS : SolvesFocusingNLS nlsBrightSolitonJet
  darkNLS : SolvesDefocusingNLS nlsDarkSolitonJet
  planeNLS : SolvesFocusingNLS nlsPlaneWaveJet
  focusingFDNLS : IsLatticeNLSSolution 0 1 (quasiRieszKernel 1) singleSiteFDNLS
  defocusingFDNLS :
    IsLatticeNLSSolution 0 (-1) (quasiRieszKernel 1) singleSiteFDNLSDefocusing
  focusingFDNLSPower : ∀ t : ℝ, latticePower (singleSiteFDNLS t) = 1
  defocusingFDNLSPower : ∀ t : ℝ, latticePower (singleSiteFDNLSDefocusing t) = 1
  focusingFDNLSConservation : ∀ t₁ t₂ : ℝ,
    latticePower (singleSiteFDNLS t₁) = latticePower (singleSiteFDNLS t₂) ∧
      latticeHamiltonian 0 1 (quasiRieszKernel 1) (singleSiteFDNLS t₁) =
        latticeHamiltonian 0 1 (quasiRieszKernel 1) (singleSiteFDNLS t₂)
  miuraPlus : ∀ t x : ℝ,
    modifiedKdVKinkJet.ux t x + modifiedKdVKink t x ^ (2 : ℕ) = 1
  miuraMinus : ∀ t x : ℝ,
    modifiedKdVKink t x ^ (2 : ℕ) - modifiedKdVKinkJet.ux t x =
      1 - 2 * solitonQ (x + 2 * t)
  schrodingerProfile : ∀ x : ℝ,
    solitonA2 x + 2 * solitonQ x * solitonA x = solitonA x
  bzZeroCurvature : ∀ residue rho z : ℝ,
    belinskiZakharovZeroCurvature
      (belinskiZakharovNilpotentLaxU residue)
      (belinskiZakharovNilpotentLaxV residue) rho z = 0
  jacobiToda :
    JacobiTodaDeriv belinskiZakharovJacobiTodaA belinskiZakharovJacobiTodaB
      belinskiZakharovJacobiTodaAPrime belinskiZakharovJacobiTodaBPrime
  bzTwoPoleUnimodular : ∀ spectral pole₁ residue₁ pole₂ residue₂ : ℝ,
    (belinskiZakharovTwoPoleDressing spectral pole₁ residue₁ pole₂ residue₂).det = 1

/-- Assumption-free inhabitant of the full dispersive/soliton atlas. -/
theorem closedDispersiveAtlas : ClosedDispersiveAtlas where
  brizardElastica := BrizardElastica.closedAtlas
  kdv := kdvSoliton_solves
  potentialKdV := potentialKdVPulse_solves
  modifiedKdV := modifiedKdVKink_solves
  airy := airyWave_solves
  kawahara := kawaharaSoliton_solves
  linearKawahara := kawaharaLinearWave_solves
  kpI := kpLineSoliton_solves_KPI
  kpII := kpLineSoliton_solves_KPII
  mondalGeneralKP := mondalSoliton_solves
  mondalOneTauHirota := mondalOneExponentialTau_corrected_solvesHirota
  mondalTwoTauHirota := mondalCorrectedTwoExponentialTau_solvesHirota
  mondalLumpHirota := mondalCorrectedLumpTau_solvesHirota
  mondalPrintedRightTimeReverse := mondalPrintedRightOneTau_solvesTimeReversedHirota
  mondalPrintedLeftTimeReverse := mondalPrintedLeftOneTau_solvesTimeReversedHirota
  mondalPrintedRightTwoTimeReverse := mondalPrintedRightTwoTau_solvesTimeReversedHirota
  mondalPrintedLeftTwoTimeReverse := mondalPrintedLeftTwoTau_solvesTimeReversedHirota
  mondalPhysicalLumpTauZero := mondalPhysicalLumpTau_has_zero
  mondalNegativeBetaLumpTauZero := mondalCorrectedNegativeBetaLumpTau_has_zero
  mondalPrintedLumpRejected := mondalPrintedLumpWitness_not_solvesHirota
  mondalPhysicalBreatherTauZero := mondalPhysicalBreatherTau_has_zero
  mondalPositiveBreatherTauNonzero := mondalPositiveBreatherTau_ne_zero
  mondalSubcriticalPhasePositive := mondalPhaseCorrectionRatio_subcritical_pos
  mondalCriticalPhaseZero := mondalPhaseCorrectionRatio_critical_zero
  mondalSupercriticalPhaseNegative := mondalPhaseCorrectionRatio_supercritical_neg
  mondalConcentrationSlopeAtZeroPositive := mondalAmplitudeConcentrationSlope_zero_pos
  mondalConcentrationSlopeAtOneNegative := mondalAmplitudeConcentrationSlope_one_neg
  mondalRaisedTemperatureLowersAmplitude := mondalAmplitude_raisedTemperature_decreases
  mondalRaisedKappaRaisesAmplitude := mondalAmplitude_raisedKappa_increases
  mondalDirectSuperpositionRejected := mondalCanonicalDoubled_not_solves
  shriraPesenson := shriraPesensonTilt_solves_all
  brightNLS := nlsBrightSoliton_solves
  darkNLS := nlsDarkSoliton_solves
  planeNLS := nlsPlaneWave_solves
  focusingFDNLS := singleSiteFDNLS_solves
  defocusingFDNLS := singleSiteFDNLSDefocusing_solves
  focusingFDNLSPower := singleSiteFDNLS_power_exact
  defocusingFDNLSPower := singleSiteFDNLSDefocusing_power_exact
  focusingFDNLSConservation := singleSiteFDNLS_conserved
  miuraPlus := modifiedKdVKink_miura_plus
  miuraMinus := modifiedKdVKink_miura_minus
  schrodingerProfile := solitonA_schrodinger
  bzZeroCurvature := belinskiZakharovNilpotentLax_zeroCurvature
  jacobiToda := belinskiZakharovJacobiToda_deriv
  bzTwoPoleUnimodular := belinskiZakharovTwoPoleDressing_det

end GaloisForLFunctions.HTGeometry.DispersivePDE
