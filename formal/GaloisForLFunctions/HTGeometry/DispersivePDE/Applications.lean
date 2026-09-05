import GaloisForLFunctions.HTGeometry.DispersivePDE.ScalarSolitons
import GaloisForLFunctions.HTGeometry.DispersivePDE.NLSSolitons
import GaloisForLFunctions.HTGeometry.DispersivePDE.FDNLSApplications
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaApplications
import GaloisForLFunctions.HTGeometry.DispersivePDE.MondalElectronAcousticKP
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
  brizardElastica : BrizardElastica.ClosedAtlas
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
  mondalPhysicalLumpTauZero : ∀ q p s : ℝ,
    mondalPhysicalLumpTau q p s 0
      (Real.sqrt (-mondalPhysicalLumpOffset q p s)) 0 = 0
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
    modifiedKdVKinkJet.ux t x + modifiedKdVKink t x ^ 2 = 1
  miuraMinus : ∀ t x : ℝ,
    modifiedKdVKink t x ^ 2 - modifiedKdVKinkJet.ux t x =
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
  mondalLumpHirota := mondalCorrectedLumpTau_solvesHirota
  mondalPrintedRightTimeReverse := mondalPrintedRightOneTau_solvesTimeReversedHirota
  mondalPrintedLeftTimeReverse := mondalPrintedLeftOneTau_solvesTimeReversedHirota
  mondalPhysicalLumpTauZero := mondalPhysicalLumpTau_has_zero
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
