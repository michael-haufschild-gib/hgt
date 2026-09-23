import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalPluckerBoundaryTraceCapacity
import GaloisForLFunctions.RHTower.RouteEPCubicSourceNormalizationDebt

/-!
# Boundary capacity is not fourth-depth amplification

P-G100 shows that the canonical continuous-zero boundary transfer escapes P-G99's `1/50`
fixed-node wall: source-normalized packet trace tends to four.  SP-E's independent
coefficient-faithful fourth-depth audit requires something stronger, however.  Its depleted
column has energy `1/64` of its parent, so every nonnegative balancing correction has amplitude
exactly eight.

This module proves that neither channel in the canonical resolvent split can supply that gain.
The transfer `T (eps + T)⁻¹` is a contraction, and the complementary normalized inverse
`eps (eps + T)⁻¹` has norm exactly one.  An amplitude-eight eigenvector of either channel is
therefore zero.  Only the unnormalized inverse can have such gain, and even then its exact norm
forces `eps <= 1/8`.

Thus P-G100's four-unit capacity escape is cofinal rank recovery, not local Radon--Nikodym
amplification.  A viable completed SP-E correction must use the genuinely singular inverse density
or an oriented cross-channel before the boundary limit; the bounded resolvent partition itself
cannot pay the `63/64` trace debt.

No RH premise, Xi-zero computation, numerical estimate, or added axiom enters.
-/

open Set
open scoped InnerProductSpace ContinuousFunctionalCalculus

noncomputable section
namespace RHTower.HedenmalmThetaSource

local instance gammaSewnMobiusApertureStokesPhysicalPluckerBoundaryAmplificationNoGoLocalInst1 : Nontrivial GammaSewnCriticalPhysicalPluckerHilbert := by
  refine ⟨⟨gammaSewnCriticalPhysicalPluckerBasis (0, 0), 0, ?_⟩⟩
  intro h
  have hn := congrArg norm h
  rw [norm_gammaSewnCriticalPhysicalPluckerBasis, norm_zero] at hn
  norm_num at hn

/-- Canonical boundary transfer cannot amplify a nonzero physical vector by the unique SP-E
fourth-depth balancing amplitude. -/
theorem gammaSewnCriticalPhysicalPluckerBoundaryTransfer_no_amplitude_eight
    (eps : ℝ) (heps : 0 < eps)
    {v : GammaSewnCriticalPhysicalPluckerHilbert}
    (hv : boundaryTransfer eps v = (8 : ℂ) • v) :
    v = 0 := by
  exact
    GaloisForLFunctions.RHTower.positiveBoundaryTransfer_eq_smul_imp_eq_zero_of_one_lt_norm
        gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.isSelfAdjoint
        spectrum_real_subset eps heps (by norm_num) hv

/-- The normalized inverse half of the resolvent partition cannot amplify a nonzero physical
vector by eight either. -/
theorem gammaSewnCriticalPhysicalPluckerBoundaryNormalizedInverse_no_amplitude_eight
    (eps : ℝ) (heps : 0 < eps)
    {v : GammaSewnCriticalPhysicalPluckerHilbert}
    (hv : (eps • boundaryInverse eps) v = (8 : ℂ) • v) :
    v = 0 := by
  exact
    GaloisForLFunctions.RHTower.positiveBoundaryNormalizedInverse_eq_smul_imp_eq_zero_of_one_lt_norm
        gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.isSelfAdjoint
        spectrum_real_subset zero_mem_real_spectrum eps heps (by norm_num) hv

/-- If the unnormalized singular inverse realizes amplitude eight on a nonzero vector, the
regularization scale is necessarily at most `1/8`. -/
theorem gammaSewnCriticalPhysicalPluckerBoundaryInverse_amplitude_eight_imp_eps_le
    (eps : ℝ) (heps : 0 < eps)
    {v : GammaSewnCriticalPhysicalPluckerHilbert} (hv0 : v ≠ 0)
    (hv : boundaryInverse eps v = (8 : ℂ) • v) :
    eps ≤ 1 / 8 := by
  have hbound :=
    GaloisForLFunctions.RHTower.norm_le_one_div_of_positiveBoundaryInverse_eq_smul
      gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.isSelfAdjoint
      spectrum_real_subset zero_mem_real_spectrum eps heps hv0 hv
  norm_num at hbound
  have hbound' : (8 : ℝ) ≤ 1 / eps := by simpa [one_div] using hbound
  have hmul : 8 * eps ≤ 1 := (le_div_iff₀ heps).mp hbound'
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr (by
    simpa [mul_comm] using hmul)

/-- **P-G101 amplification no-go.**  Amplitude eight exactly repairs fourth-depth energy, but
neither bounded channel of the canonical boundary resolvent split can realize it on a nonzero
physical vector. -/
theorem gammaSewnCriticalPhysicalPlucker_canonicalBoundarySplit_cannot_rebalance_fourthDepth
    (pe : Nat.Primes × ℕ) (eps : ℝ) (heps : 0 < eps)
    {v : GammaSewnCriticalPhysicalPluckerHilbert} (hv0 : v ≠ 0) :
    let w := routePPrimitiveBaseCauchyCubicWeight pe
    let c : ℝ := 8
    w / 64 * c ^ (2 : ℕ) = w ∧
      boundaryTransfer eps v ≠ (c : ℂ) • v ∧
      (eps • boundaryInverse eps) v ≠ (c : ℂ) • v := by
  dsimp
  constructor
  · ring
  constructor
  · intro h
    exact hv0
      (gammaSewnCriticalPhysicalPluckerBoundaryTransfer_no_amplitude_eight eps heps h)
  · intro h
    exact hv0
      (gammaSewnCriticalPhysicalPluckerBoundaryNormalizedInverse_no_amplitude_eight eps heps h)

end RHTower.HedenmalmThetaSource
