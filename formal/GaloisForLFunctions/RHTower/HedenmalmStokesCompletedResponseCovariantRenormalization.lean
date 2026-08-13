import GaloisForLFunctions.RHTower.HedenmalmStokesFirstTraceMomentDualityWall
import GaloisForLFunctions.RHTower.HedenmalmThetaMovingHorizonCompletedResponseWeld
import GaloisForLFunctions.RHTower.HedenmalmThetaMovingHorizonCovariantHardyGreenRegularization
import GaloisForLFunctions.RHTower.XiPrimeMarkedUnitDoubleCycleCandidate
import GaloisForLFunctions.RHTower.FrankensteinThetaPrimeTranslationPluckerLanding
import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointBoundaryNuclearObstruction

/-!
# Covariant renormalization of the Stokes first trace

At valuation zero and critical aperture, the positive Stokes moment isolated by P-G140 is exactly
the physical endpoint marginal `log p / p`.  The valuation-corrected completed response has this
same labelled row marginal.  Its packet-dependent diagonal therefore redistributes the divergent
first trace but does not neutralize it: total finite coupling mass is still the sum of the positive
moments.

The theta moving-horizon connection supplies a different, source-native operation.  At centered
depth `d`, every labelled covariant prime-energy term is exactly

`8 d^2 * firstTraceMoment(1 + 2d, (p,0))`.

This family is summable for every `d>0`, extends to zero at the critical wall, and retains the
exact RH radical on actual Xi copies.  Reflection makes this renormalized energy even, while the
underlying completed-response half-density remains odd.  Thus this module constructs the missing
coefficient-faithful before-limit renormalization and isolates its remaining loss: energy
scalarization discards orientation.

No RH premise, Xi-zero computation, numerical estimate, or added axiom enters.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Critical first trace is the physical completed-response marginal -/

/-- The critical valuation-zero positive Stokes moment is the literal physical endpoint weight. -/
theorem gammaSewnMobiusApertureStokesCriticalFirstTracePrimeMoment_eq_physicalEndpointWeight
    (p : Nat.Primes) :
    gammaSewnMobiusApertureStokesFirstTracePositiveMoment 1 (p, 0) =
      physicalPrimeEndpointWeight p := by
  have hnode : xiMobiusContinuousApertureDiskNode 1 p = ((p : ℝ))⁻¹ := by
    rw [xiMobiusContinuousApertureDiskNode]
    norm_num
    have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
    rw [Real.exp_neg, Real.exp_log hp]
  rw [gammaSewnMobiusApertureStokesFirstTracePositiveMoment_primeSlice_eq
    (by norm_num), hnode, physicalPrimeEndpointWeight, div_eq_mul_inv]

/-- The critical prime slice is already nonsummable; higher valuations are not responsible. -/
theorem not_summable_gammaSewnMobiusApertureStokesCriticalFirstTracePrimeMoment :
    ¬ Summable (fun p : Nat.Primes =>
      gammaSewnMobiusApertureStokesFirstTracePositiveMoment 1 (p, 0)) := by
  intro hsum
  apply not_summable_physicalPrimeEndpointWeight
  exact hsum.congr
    gammaSewnMobiusApertureStokesCriticalFirstTracePrimeMoment_eq_physicalEndpointWeight

/-- Packet-dependent diagonal correction forced by the completed off-diagonal response. -/
def gammaSewnMobiusApertureStokesCompletedResponseDiagonalCounterterm
    (P : Finset Nat.Primes) (p : Nat.Primes) : ℝ :=
  -∑ r ∈ P.erase p, xiPhysicalEndpointCompletedPairResponse p r

/-- The balanced diagonal is critical first-trace mass plus the forced labelled counterterm. -/
theorem xiPhysicalEndpointCompletedBalancedCoupling_diagonal_eq_firstTrace_add_counterterm
    (P : Finset Nat.Primes) (p : Nat.Primes) :
    xiPhysicalEndpointCompletedBalancedCoupling P p p =
      gammaSewnMobiusApertureStokesFirstTracePositiveMoment 1 (p, 0) +
        gammaSewnMobiusApertureStokesCompletedResponseDiagonalCounterterm P p := by
  rw [xiPhysicalEndpointCompletedBalancedCoupling, if_pos rfl,
    gammaSewnMobiusApertureStokesCriticalFirstTracePrimeMoment_eq_physicalEndpointWeight,
    gammaSewnMobiusApertureStokesCompletedResponseDiagonalCounterterm]
  ring

/-- Every completed-response row preserves its prime label and has the exact Stokes marginal. -/
theorem sum_xiPhysicalEndpointCompletedBalancedCoupling_eq_criticalFirstTrace
    (P : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∈ P) :
    ∑ r ∈ P, xiPhysicalEndpointCompletedBalancedCoupling P p r =
      gammaSewnMobiusApertureStokesFirstTracePositiveMoment 1 (p, 0) := by
  rw [sum_xiPhysicalEndpointCompletedBalancedCoupling P p hp,
    gammaSewnMobiusApertureStokesCriticalFirstTracePrimeMoment_eq_physicalEndpointWeight]

/-- **Mass-conservation falsifier.** Finite response completion redistributes but does not cancel
the divergent critical positive moment. -/
theorem sum_sum_xiPhysicalEndpointCompletedBalancedCoupling_eq_criticalFirstTrace
    (P : Finset Nat.Primes) :
    ∑ p ∈ P, ∑ r ∈ P, xiPhysicalEndpointCompletedBalancedCoupling P p r =
      ∑ p ∈ P,
        gammaSewnMobiusApertureStokesFirstTracePositiveMoment 1 (p, 0) := by
  apply Finset.sum_congr rfl
  intro p hp
  exact sum_xiPhysicalEndpointCompletedBalancedCoupling_eq_criticalFirstTrace P p hp

/-- Adding a prime transports the old labelled diagonal counterterm by exactly the negative new
off-diagonal source response. -/
theorem gammaSewnMobiusApertureStokesCompletedResponseDiagonalCounterterm_insert_sub
    (P : Finset Nat.Primes) (p r : Nat.Primes)
    (hp : p ∈ P) (hr : r ∉ P) :
    gammaSewnMobiusApertureStokesCompletedResponseDiagonalCounterterm (insert r P) p -
        gammaSewnMobiusApertureStokesCompletedResponseDiagonalCounterterm P p =
      -xiPhysicalEndpointCompletedPairResponse p r := by
  have h := xiPhysicalEndpointCompletedBalancedCoupling_insert_diagonal_sub
    P p r hp hr
  rw [xiPhysicalEndpointCompletedBalancedCoupling_diagonal_eq_firstTrace_add_counterterm,
    xiPhysicalEndpointCompletedBalancedCoupling_diagonal_eq_firstTrace_add_counterterm] at h
  linear_combination h

/-! ## Moving-horizon covariant first-trace renormalization -/

/-- Label-faithful covariant renormalization of the positive Stokes first trace. -/
def gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment
    (d : ℝ) (p : Nat.Primes) : ℝ :=
  8 * d ^ 2 *
    gammaSewnMobiusApertureStokesFirstTracePositiveMoment (1 + 2 * d) (p, 0)

/-- Explicit shifted-prime form of the renormalized moment. -/
theorem gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment_eq
    (d : ℝ) (hd : 0 ≤ d) (p : Nat.Primes) :
    gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment d p =
      8 * Real.log (p : ℝ) * d ^ 2 * (p : ℝ) ^ (-(1 + 2 * d)) := by
  have hs : 0 < 1 + 2 * d := by linarith
  rw [gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment,
    gammaSewnMobiusApertureStokesFirstTracePositiveMoment_primeSlice_eq hs,
    xiMobiusContinuousApertureDiskNode, Real.rpow_def_of_pos]
  · ring
  · exact_mod_cast p.2.pos

/-- Cross-route coefficient identity with the prime-square Euler boundary residue. -/
theorem gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment_eq_primeSquareEuler
    (d : ℝ) (hd : 0 ≤ d) (p : Nat.Primes) :
    gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment d p =
      8 * d ^ 2 * xiMassPrimeSquareEulerWeight d p := by
  rw [gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment_eq d hd p,
    xiMassPrimeSquareEulerWeight_eq]
  ring

/-- For every positive centered depth, covariant first-trace mass is ordinarily summable. -/
theorem summable_gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment
    {d : ℝ} (hd : 0 < d) :
    Summable (gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment d) := by
  have hsum := (summable_xiMassPrimeSquareEulerWeight hd).mul_left (8 * d ^ 2)
  exact hsum.congr (fun p =>
    (gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment_eq_primeSquareEuler
      d hd.le p).symm)

/-- The moving-horizon covariant derivative is exactly the renormalized Stokes moment at every
prime label and every multiplicity-resolved Xi copy. -/
theorem thetaWardMovingHorizonCovariantPrimeTerm_eq_stokesCovariantFirstTrace
    (p : Nat.Primes) (q : XiZeroCopy) :
    8 * Real.log (p : ℝ) *
        HedenmalmThetaSource.thetaMovingHorizonConnection
          (HedenmalmThetaSource.thetaWardContinuousHalfDensityProfile q)
          (Real.log (p : ℝ)) ^ 2 =
      gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment
        |primeDepthBVWoldXiCenteredRate q.1| p := by
  let d := |primeDepthBVWoldXiCenteredRate q.1|
  rw [HedenmalmThetaSource.thetaMovingHorizonConnection_wardContinuousHalfDensityProfile_prime_sq]
  rw [gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment_eq d (abs_nonneg _) p]
  rw [routeNGammaSewnTwistedCriticalChannelAmplitude_sq,
    routeNGammaSewnTwistedCriticalChannelMass]
  dsimp only [d]
  ring

/-- The all-prime renormalized first trace is the existing finite covariant Ward energy. -/
theorem tsum_gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment_eq_thetaWardEnergy
    (q : XiZeroCopy) :
    ∑' p : Nat.Primes,
        gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment
          |primeDepthBVWoldXiCenteredRate q.1| p =
      HedenmalmThetaSource.thetaWardMovingHorizonCovariantPrimeEnergy q := by
  rw [HedenmalmThetaSource.thetaWardMovingHorizonCovariantPrimeEnergy]
  exact tsum_congr (fun p =>
    (thetaWardMovingHorizonCovariantPrimeTerm_eq_stokesCovariantFirstTrace p q).symm)

/-! ## Reflection audit and endpoint -/

/-- Covariant first-trace energy is reflection-even coefficient by coefficient. -/
theorem gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment_lineConj
    (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment
        |primeDepthBVWoldXiCenteredRate (xiZeroCopyLineConjEquiv q).1| p =
      gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment
        |primeDepthBVWoldXiCenteredRate q.1| p := by
  rw [HedenmalmThetaSource.primeDepthBVWoldXiCenteredRate_lineConj, abs_neg]

/-- Exact location of orientation loss: the physical source vector is odd under reflection, but
its covariantly renormalized positive first trace is even. -/
theorem thetaPhysicalEndpoint_sourceOdd_stokesCovariantFirstTraceEven
    (q : XiZeroCopy) (p : Nat.Primes) :
    HedenmalmThetaSource.thetaPhysicalEndpointNormalizedHalfDensity p q +
        HedenmalmThetaSource.thetaPhysicalEndpointNormalizedHalfDensity p
          (xiZeroCopyReflectEquiv q) = 0 ∧
      gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment
          |primeDepthBVWoldXiCenteredRate (xiZeroCopyLineConjEquiv q).1| p =
        gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment
          |primeDepthBVWoldXiCenteredRate q.1| p :=
  ⟨HedenmalmThetaSource.thetaPhysicalEndpointNormalizedHalfDensity_reflection_add_eq_zero p q,
    gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment_lineConj q p⟩

/-- **Renormalized first-trace RH endpoint.** Global vanishing of the source-native, label-faithful
covariant moment is exactly RH.  The missing producer is its unconditional oriented vanishing,
not convergence or carrier construction. -/
theorem all_tsum_gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment_eq_zero_iff_rh :
    (∀ q : XiZeroCopy,
      (∑' p : Nat.Primes,
        gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment
          |primeDepthBVWoldXiCenteredRate q.1| p) = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply HedenmalmThetaSource.all_thetaWardMovingHorizonCovariantPrimeEnergy_eq_zero_iff_riemannHypothesis.mp
    intro q
    rw [← tsum_gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment_eq_thetaWardEnergy]
    exact h q
  · intro hRH q
    rw [tsum_gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment_eq_thetaWardEnergy]
    exact HedenmalmThetaSource.all_thetaWardMovingHorizonCovariantPrimeEnergy_eq_zero_iff_riemannHypothesis.mpr
      hRH q

end

end RHTower
