import GaloisForLFunctions.RHTower.XiStokesConductorWallIndex
import GaloisForLFunctions.RHTower.FrankensteinXiGreenStokesQuadraticGhostNormalForm
import GaloisForLFunctions.HTGeometry.ResolvedDefectConservationLaw

/-!
# Resolved Xi Stokes--Ward character

Completion cancels two different Xi-selected defects without annihilating
their constituents.

At first order, the squarefree Stokes current and its polar/Gamma
countercurrent have opposite wall residues.  Their codiagonal is continuous,
but their relative wall charge is `8m`, where `m` is the exact Xi
multiplicity.

At second order, the Laurent quadratic ghost and the physical cyclic
chain-map anomaly form an exact antidiagonal Ward double.  Their codiagonal
vanishes unconditionally, while their relative character vanishes exactly
on the critical line.

Thus completed smoothness and total anomaly cancellation do not erase the
resolved Xi datum.  A critical-line zero retains nonzero conductor charge but
has neutral secondary Ward character.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## First-order resolved wall character -/

/-- Polar/Gamma countercurrent with the same Xi multiplicity marking as the
raw squarefree Stokes current. -/
def xiStokesConductorPolarCountercurrent
    (rho : XiDivisorSupport) (t : ℝ) : ℝ :=
  (xiSupportMultiplicity rho : ℝ) *
    gammaSewnMobiusApertureStokesOrientedPolarCountercurrent t

/-- Multiplicity-marked completed prime--Gamma current. -/
def xiStokesConductorCompletedCurrent
    (rho : XiDivisorSupport) (t : ℝ) : ℝ :=
  (xiSupportMultiplicity rho : ℝ) *
    gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent t

/-- The raw and polar constituents retained before codiagonal completion. -/
def xiStokesConductorResolvedWallCurrent
    (rho : XiDivisorSupport) (t : ℝ) : ℝ × ℝ :=
  (xiStokesConductorWallCurrent rho t,
    xiStokesConductorPolarCountercurrent rho t)

/-- Away from the wall, codiagonalization of the resolved pair is exactly
the completed current. -/
theorem xiStokesConductorResolvedWallCurrent_codiagonal
    (rho : XiDivisorSupport) (t : ℝ) (ht : t ≠ 0) :
    resolvedDefectCodiagonal (R := ℝ)
        (xiStokesConductorResolvedWallCurrent rho t) =
      xiStokesConductorCompletedCurrent rho t := by
  rw [xiStokesConductorResolvedWallCurrent,
    resolvedDefectCodiagonal_apply, xiStokesConductorWallCurrent,
    xiStokesConductorPolarCountercurrent,
    xiStokesConductorCompletedCurrent,
    gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_eq_firstTrace_add_counter
      t ht]
  ring

/-- The multiplicity-marked completed current is continuous at the wall. -/
theorem continuousAt_xiStokesConductorCompletedCurrent_zero
    (rho : XiDivisorSupport) :
    ContinuousAt (xiStokesConductorCompletedCurrent rho) 0 := by
  exact
    continuousAt_gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_zero.const_mul
      (xiSupportMultiplicity rho : ℝ)

/-- The resolved wall pair tends to a nonzero antidiagonal whose coefficient
is four times exact Xi multiplicity. -/
theorem tendsto_xiStokesConductorResolvedWallCurrent_nhdsGT_zero
    (rho : XiDivisorSupport) :
    Tendsto (xiStokesConductorResolvedWallCurrent rho)
      (𝓝[>] (0 : ℝ))
      (𝓝 (((xiSupportMultiplicity rho : ℝ) * 4,
        -((xiSupportMultiplicity rho : ℝ) * 4)))) := by
  have hraw := tendsto_xiStokesConductorWallCurrent_nhdsGT_zero rho
  have hpolar : Tendsto
      (fun t => (xiSupportMultiplicity rho : ℝ) *
        gammaSewnMobiusApertureStokesOrientedPolarCountercurrent t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-((xiSupportMultiplicity rho : ℝ) * 4))) := by
    convert
      tendsto_gammaSewnMobiusApertureStokesOrientedPolarCountercurrent_nhdsGT_zero.const_mul
        (xiSupportMultiplicity rho : ℝ) using 1
    all_goals ring_nf
  change Tendsto
    (fun t => (xiStokesConductorWallCurrent rho t,
      xiStokesConductorPolarCountercurrent rho t))
    (𝓝[>] (0 : ℝ))
    (𝓝 (((xiSupportMultiplicity rho : ℝ) * 4,
      -((xiSupportMultiplicity rho : ℝ) * 4))))
  simpa only [xiStokesConductorPolarCountercurrent, nhds_prod_eq] using
    hraw.prodMk hpolar

/-- Relative, rather than total, wall charge of the resolved pair. -/
def xiStokesConductorResolvedWallRelativeCharge
    (rho : XiDivisorSupport) (t : ℝ) : ℝ :=
  (xiStokesConductorResolvedWallCurrent rho t).1 -
    (xiStokesConductorResolvedWallCurrent rho t).2

/-- The relative wall charge tends to `8m`; codiagonal completion has hidden,
not destroyed, exact multiplicity. -/
theorem tendsto_xiStokesConductorResolvedWallRelativeCharge_nhdsGT_zero
    (rho : XiDivisorSupport) :
    Tendsto (xiStokesConductorResolvedWallRelativeCharge rho)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((xiSupportMultiplicity rho : ℝ) * 8)) := by
  have hraw := tendsto_xiStokesConductorWallCurrent_nhdsGT_zero rho
  have hpolar : Tendsto (xiStokesConductorPolarCountercurrent rho)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-((xiSupportMultiplicity rho : ℝ) * 4))) := by
    change Tendsto
      (fun t => (xiSupportMultiplicity rho : ℝ) *
        gammaSewnMobiusApertureStokesOrientedPolarCountercurrent t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-((xiSupportMultiplicity rho : ℝ) * 4)))
    convert
      tendsto_gammaSewnMobiusApertureStokesOrientedPolarCountercurrent_nhdsGT_zero.const_mul
        (xiSupportMultiplicity rho : ℝ) using 1
    all_goals ring_nf
  change Tendsto
    (fun t => xiStokesConductorWallCurrent rho t -
      xiStokesConductorPolarCountercurrent rho t)
    (𝓝[>] (0 : ℝ))
    (𝓝 ((xiSupportMultiplicity rho : ℝ) * 8))
  convert hraw.sub hpolar using 1
  all_goals ring_nf

/-! ## Second-order resolved Ward character -/

namespace HedenmalmThetaSource

/-- Laurent ghost and physical cyclic anomaly before their Ward
codiagonal is taken. -/
def thetaXiIntegralResolvedWardDouble
    (rho : XiDivisorSupport) (p : Nat.Primes) :=
  (thetaXiIntegralQuadraticGhostVector rho p,
    thetaXiIntegralCyclicBoundaryAnomalyVector rho p)

/-- The complete Ward double is exactly the universal antidiagonal of its
Laurent constituent. -/
theorem thetaXiIntegralResolvedWardDouble_eq_antidiagonal
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralResolvedWardDouble rho p =
      resolvedDefectAntidiagonal (R := ℂ)
        (thetaXiIntegralQuadraticGhostVector rho p) := by
  apply Prod.ext
  · rfl
  · rw [thetaXiIntegralResolvedWardDouble,
      resolvedDefectAntidiagonal_apply,
      thetaXiIntegralCyclicBoundaryAnomalyVector_eq_pairedCurvatureVector,
      thetaXiIntegralPairedCurvatureVector_eq_neg_quadraticGhostVector]

/-- Total Ward anomaly vanishes for every Xi divisor. -/
theorem thetaXiIntegralResolvedWardDouble_codiagonal
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    resolvedDefectCodiagonal (R := ℂ)
        (thetaXiIntegralResolvedWardDouble rho p) = 0 := by
  rw [thetaXiIntegralResolvedWardDouble_eq_antidiagonal]
  simp

/-- Difference coordinate retained before codiagonal anomaly cancellation. -/
def thetaXiIntegralWardRelativeCharacter
    (rho : XiDivisorSupport) (p : Nat.Primes) :=
  (thetaXiIntegralResolvedWardDouble rho p).1 -
    (thetaXiIntegralResolvedWardDouble rho p).2

/-- Relative character is twice the Laurent constituent of the Ward double. -/
theorem thetaXiIntegralWardRelativeCharacter_eq_two_smul_ghost
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralWardRelativeCharacter rho p =
      (2 : ℂ) • thetaXiIntegralQuadraticGhostVector rho p := by
  rw [thetaXiIntegralWardRelativeCharacter,
    thetaXiIntegralResolvedWardDouble,
    thetaXiIntegralCyclicBoundaryAnomalyVector_eq_pairedCurvatureVector,
    thetaXiIntegralPairedCurvatureVector_eq_neg_quadraticGhostVector]
  module

/-- Exact coefficient read by the pinned harmonic reporter.  Multiplicity
and the nonlinear reciprocal-character curvature both survive. -/
theorem pinnedMean_thetaXiIntegralWardRelativeCharacter
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    pinnedMean (thetaXiIntegralWardRelativeCharacter rho p) =
      (((-2 : ℝ) * (xiSupportMultiplicity rho : ℝ) *
        sourceHorizontalGammaSixUnitOppositeBoundaryCurvature
          (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho) : ℝ) : ℂ) := by
  rw [thetaXiIntegralWardRelativeCharacter_eq_two_smul_ghost,
    pinnedMean_smul, thetaXiIntegralQuadraticGhostVector,
    pinnedMean_smul, pinnedMean_pinnedOne, mul_one,
    thetaXiIntegralQuadraticGhostCoefficient_eq_neg_pairedCurvature]
  push_cast
  ring

/-- Secondary relative Ward character, unlike its zero codiagonal, vanishes
exactly at neutral horizontal character. -/
theorem thetaXiIntegralWardRelativeCharacter_eq_zero_iff
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralWardRelativeCharacter rho p = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    have hghost : thetaXiIntegralQuadraticGhostVector rho p = 0 := by
      rw [thetaXiIntegralWardRelativeCharacter_eq_two_smul_ghost] at hzero
      exact (smul_eq_zero.mp hzero).resolve_left (by norm_num)
    exact (thetaXiIntegralQuadraticGhostVector_eq_zero_iff rho p).1 hghost
  · intro hline
    rw [thetaXiIntegralWardRelativeCharacter_eq_two_smul_ghost,
      (thetaXiIntegralQuadraticGhostVector_eq_zero_iff rho p).2 hline,
      smul_zero]

/-- Critical-line neutrality is not zero disappearance: exact conductor
charge remains nonzero while the secondary relative character vanishes. -/
theorem xiStokesPrimaryCharge_ne_zero_and_secondaryNeutral_iff
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    ((xiSupportMultiplicity rho : ℝ) * 8 ≠ 0 ∧
      thetaXiIntegralWardRelativeCharacter rho p = 0) ↔
      (rho : ℂ).re = 1 / 2 := by
  have hcharge : (xiSupportMultiplicity rho : ℝ) * 8 ≠ 0 := by
    have hm : (0 : ℝ) < (xiSupportMultiplicity rho : ℝ) := by
      exact_mod_cast xiSupportMultiplicity_pos rho
    positivity
  rw [and_iff_right hcharge,
    thetaXiIntegralWardRelativeCharacter_eq_zero_iff]

/-- Hostile falsification of unresolved-completion arguments: completed
wall smoothness and total Ward cancellation coexist with a nonzero secondary
relative character exactly off the critical line. -/
theorem completedSmooth_codiagonalZero_but_relativeWardNonzero_iff
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    (ContinuousAt (xiStokesConductorCompletedCurrent rho) 0 ∧
      resolvedDefectCodiagonal (R := ℂ)
          (thetaXiIntegralResolvedWardDouble rho p) = 0 ∧
      thetaXiIntegralWardRelativeCharacter rho p ≠ 0) ↔
      (rho : ℂ).re ≠ 1 / 2 := by
  rw [and_iff_right (continuousAt_xiStokesConductorCompletedCurrent_zero rho),
    and_iff_right (thetaXiIntegralResolvedWardDouble_codiagonal rho p),
    ne_eq, thetaXiIntegralWardRelativeCharacter_eq_zero_iff]

end HedenmalmThetaSource

end

end RHTower
