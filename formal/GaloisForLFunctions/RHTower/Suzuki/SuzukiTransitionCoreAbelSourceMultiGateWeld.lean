import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiSelbergOutgoingAbelWeld
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTransitionCoreAlignedGammaXiFission

/-!
# Signed Abel source for the aligned Suzuki transition-core weld

The aligned growing-rank Suzuki carrier was already coefficient-faithful through completed
Gamma alignment, Xi residue selection, analytic multiplicity fission, both reflection
orientations, and the four-orientation non-spectral short.  Its remaining scalar was still
presented as a completed lower-Hardy amplitude.

This module identifies that scalar before divisor selection with the literal finite signed
Selberg square-root Abel action, including its exact polar-lattice, polar, and archimedean
corrections.  The same pre-divisor scalar therefore controls both the completed growing-rank
source energy and every multiplicity-faithful Xi-fibre short.  This is a source-identity weld;
it does not assert the still-open uniform arithmetic bound on that scalar.
-/

open Complex Filter Matrix Set Topology
open scoped BigOperators ComplexOrder

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

noncomputable section

/-- Literal finite signed Abel source after its polar and archimedean corrections. -/
def suzukiTransitionCoreCompletedAbelSource (N : ℕ) : ℝ :=
  (coherentSelbergSquareRootAbelMoment N +
      coherentSquareRootPolarLatticeDefect N) / N -
    unitRieszSuzukiPolarCorrection (Real.log N) +
    unitRieszSuzukiArchCorrection (Real.log N)

/-- The completed lower-Hardy scalar is exactly the corrected signed Abel source before any
divisor is selected. -/
theorem suzukiNaturalApertureCompletedLowerHardyAmplitude_eq_completedAbelSource
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiNaturalApertureCompletedLowerHardyAmplitude N =
      suzukiTransitionCoreCompletedAbelSource N := by
  have hsplit : N - 2 + 2 = N := by omega
  have hgreen :=
    suzukiNaturalApertureCompletedLowerHardyAmplitude_add_two_eq_green (N - 2)
  rw [hsplit] at hgreen
  rw [hgreen, suzukiTransitionCoreCompletedAbelSource,
    unitRieszSuzukiGreen_log_nat_eq_abel_lattice_sub_corrections hN]

/-- Pre-divisor Abel normal form of the aligned growing-rank Suzuki energy.  Prime-pair geometry
stays in the transition-core factor; every completed arithmetic cancellation is carried by the
single coefficient-faithful signed Abel scalar. -/
theorem suzukiTransitionCoreAlignedGammaCompletedEnergy_eq_completedAbelSource
    {N : ℕ} (hN : 2 ≤ N)
    (hcharge : unitRieszCoherentPrimeOutgoingCharge N ≠ 0) :
    suzukiTransitionCoreAlignedGammaCompletedEnergy N =
      suzukiNaturalApertureTransitionCoreCauchyEnergy N *
        (suzukiTransitionCoreCompletedAbelSource N /
          unitRieszCoherentPrimeOutgoingCharge N) ^ (2 : ℕ) := by
  rw [suzukiTransitionCoreAlignedGammaCompletedEnergy, dif_neg hcharge,
    suzukiNaturalApertureCompletedLowerHardyAmplitude_eq_completedAbelSource hN]

/-- Exact cross-route multi-gate descent.  The same pre-divisor signed Abel action survives the
SP-E growing-rank transition carrier, completed Gamma alignment, Xi selection, multiplicity
fission, both reflection orientations, and Route-P/CCM's four-orientation non-spectral short.
No post-selected coefficient or divisor-fitted normalization is introduced. -/
theorem suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy_eq_completedAbelSource
    {N : ℕ} (hN : 2 ≤ N)
    (hcharge : unitRieszCoherentPrimeOutgoingCharge N ≠ 0)
    (rho : XiDivisorSupport) (r : ℝ) :
    suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy N rho r =
      2 * (xiSupportMultiplicity rho : ℝ) *
        suzukiNaturalApertureTransitionCoreCauchyEnergy N *
          (suzukiTransitionCoreCompletedAbelSource N /
            unitRieszCoherentPrimeOutgoingCharge N) ^ (2 : ℕ) *
          Complex.normSq (routePXiBaseConormalResidueFeature (rho : ℂ) r) := by
  rw [suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy_eq,
    suzukiTransitionCoreAlignedGammaCompletedEnergy_eq_completedAbelSource hN hcharge]
  ring

end

end GaloisForLFunctions.RHTower
