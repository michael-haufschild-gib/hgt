import GaloisForLFunctions.RHTower.HedenmalmThetaMovingHorizonWardCarrier
import GaloisForLFunctions.RHTower.HedenmalmThetaPhysicalEndpointPrimeHardyGreenScaling

/-!
# Covariant moving-horizon regularization of Route P Hardy--Green energy

The physical moving-horizon half-density connection annihilates the flat universal
`p^(-1/2)` boundary carrier and differentiates the twisted tail.  At centered depth `d`, its
prime sample is therefore `d p^(-1/2-d)`.  With the physical logarithmic prime weight, the
resulting energy is exactly `d²` times the prime-sampled Hardy--Green residual energy.

This converts the exceptional `4/d` pole into a finite positive energy asymptotic to `4d`.  The
energy is summable on every divisor copy and vanishes exactly at neutral grade, hence globally
exactly under RH.  It is a regular source-side detector, not an unconditional proof that the
detector vanishes.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Continuous logarithmic-aperture extension of the physical Ward half-density. -/
def thetaWardContinuousHalfDensityProfile (q : XiZeroCopy) (L : ℝ) : ℝ :=
  thetaWardHorizontalOrientation q *
    (Real.exp (-L / 2) -
      Real.exp (-(1 / 2 + |primeDepthBVWoldXiCenteredRate q.1|) * L))

/-- Prime sampling recovers the literal physical half-density coefficient. -/
theorem thetaWardContinuousHalfDensityProfile_prime
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaWardContinuousHalfDensityProfile q (Real.log (p : ℝ)) =
      thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q := by
  let a : ℝ := primeDepthBVWoldXiCenteredRate q.1
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [thetaWardContinuousHalfDensityProfile,
    thetaMobiusPrimeNormalProfileHalfDensityAmplitude_eq_channelGap,
    thetaWardHorizontalOrientation,
    routeNGammaSewnUniversalCriticalChannelAmplitude,
    routeNGammaSewnTwistedCriticalChannelAmplitude,
    Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hp]
  change (if 0 ≤ a then 1 else -1) *
      (Real.exp (-Real.log (p : ℝ) / 2) -
        Real.exp (-(1 / 2 + |a|) * Real.log (p : ℝ))) =
    if 0 ≤ a then
      Real.exp (Real.log (p : ℝ) * (-(1 / 2))) -
        Real.exp (Real.log (p : ℝ) * (-(1 / 2) - |a|))
    else
      -(Real.exp (Real.log (p : ℝ) * (-(1 / 2))) -
        Real.exp (Real.log (p : ℝ) * (-(1 / 2) - |a|)))
  split <;> ring_nf

theorem hasDerivAt_thetaWardContinuousHalfDensityProfile
    (q : XiZeroCopy) (L : ℝ) :
    HasDerivAt (thetaWardContinuousHalfDensityProfile q)
      (thetaWardHorizontalOrientation q *
        ((-1 / 2) * Real.exp (-L / 2) -
          (-(1 / 2 + |primeDepthBVWoldXiCenteredRate q.1|)) *
            Real.exp (-(1 / 2 + |primeDepthBVWoldXiCenteredRate q.1|) * L))) L := by
  let d : ℝ := |primeDepthBVWoldXiCenteredRate q.1|
  change HasDerivAt
    (fun x : ℝ => thetaWardHorizontalOrientation q *
      (Real.exp (-x / 2) - Real.exp (-(1 / 2 + d) * x))) _ L
  have hUlin : HasDerivAt (fun x : ℝ => -x / 2) (-1 / 2) L := by
    simpa using (hasDerivAt_id L).neg.div_const 2
  have hU : HasDerivAt (fun x : ℝ => Real.exp (-x / 2))
      ((-1 / 2) * Real.exp (-L / 2)) L := by
    simpa only [Function.comp_def, mul_comm] using!
      (Real.hasDerivAt_exp (-L / 2)).comp L hUlin
  have hTlin : HasDerivAt (fun x : ℝ => -(1 / 2 + d) * x)
      (-(1 / 2 + d)) L := by
    simpa using (hasDerivAt_id L).const_mul (-(1 / 2 + d))
  have hT : HasDerivAt (fun x : ℝ => Real.exp (-(1 / 2 + d) * x))
      ((-(1 / 2 + d)) * Real.exp (-(1 / 2 + d) * L)) L := by
    simpa only [Function.comp_def, mul_comm] using!
      (Real.hasDerivAt_exp (-(1 / 2 + d) * L)).comp L hTlin
  have h := (hU.sub hT).const_mul (thetaWardHorizontalOrientation q)
  simpa using h

/-- **Covariant desingularization law.** The half-density connection kills the universal carrier
and leaves centered depth times the twisted tail. -/
theorem thetaMovingHorizonConnection_wardContinuousHalfDensityProfile
    (q : XiZeroCopy) (L : ℝ) :
    thetaMovingHorizonConnection (thetaWardContinuousHalfDensityProfile q) L =
      thetaWardHorizontalOrientation q *
        |primeDepthBVWoldXiCenteredRate q.1| *
          Real.exp (-(1 / 2 + |primeDepthBVWoldXiCenteredRate q.1|) * L) := by
  rw [thetaMovingHorizonConnection,
    (hasDerivAt_thetaWardContinuousHalfDensityProfile q L).deriv,
    thetaWardContinuousHalfDensityProfile]
  ring

theorem thetaMovingHorizonConnection_wardContinuousHalfDensityProfile_prime
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaMovingHorizonConnection (thetaWardContinuousHalfDensityProfile q)
        (Real.log (p : ℝ)) =
      thetaWardHorizontalOrientation q *
        |primeDepthBVWoldXiCenteredRate q.1| *
          routeNGammaSewnTwistedCriticalChannelAmplitude
            (primeDepthBVWoldXiCenteredRate q.1) p := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [thetaMovingHorizonConnection_wardContinuousHalfDensityProfile,
    routeNGammaSewnTwistedCriticalChannelAmplitude,
    Real.rpow_def_of_pos hp]
  congr 2
  ring

theorem thetaMovingHorizonConnection_wardContinuousHalfDensityProfile_prime_sq
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaMovingHorizonConnection (thetaWardContinuousHalfDensityProfile q)
        (Real.log (p : ℝ)) ^ 2 =
      |primeDepthBVWoldXiCenteredRate q.1| ^ 2 *
        routeNGammaSewnTwistedCriticalChannelAmplitude
          (primeDepthBVWoldXiCenteredRate q.1) p ^ 2 := by
  rw [thetaMovingHorizonConnection_wardContinuousHalfDensityProfile_prime]
  have horient : thetaWardHorizontalOrientation q ^ 2 = 1 := by
    rw [thetaWardHorizontalOrientation]
    split <;> norm_num
  rw [mul_pow, mul_pow, horient]
  ring

/-- Logarithmically weighted covariant sample is depth squared times the physical residual sample. -/
theorem eight_mul_log_mul_connection_sq_eq_depth_sq_mul_residual_sample
    (p : Nat.Primes) (q : XiZeroCopy)
    (h : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    8 * Real.log (p : ℝ) *
        thetaMovingHorizonConnection (thetaWardContinuousHalfDensityProfile q)
          (Real.log (p : ℝ)) ^ 2 =
      |primeDepthBVWoldXiCenteredRate q.1| ^ 2 *
        (physicalPrimeEndpointWeight p *
          thetaPhysicalEndpointHardyGreenResidual q (Real.log (p : ℝ)) ^ 2) := by
  rw [thetaMovingHorizonConnection_wardContinuousHalfDensityProfile_prime_sq,
    physicalPrimeEndpointWeight_mul_hardyGreenResidual_sq p q h,
    xiMassPrimeSquareEulerWeight_eq,
    routeNGammaSewnTwistedCriticalChannelAmplitude_sq,
    routeNGammaSewnTwistedCriticalChannelMass]
  have hexp :
      -1 - 2 * |primeDepthBVWoldXiCenteredRate q.1| =
        -(1 + 2 * |primeDepthBVWoldXiCenteredRate q.1|) := by ring
  rw [hexp]
  ring

/-- Prime energy of the covariantly differentiated physical half-density. -/
def thetaWardMovingHorizonCovariantPrimeEnergy (q : XiZeroCopy) : ℝ :=
  ∑' p : Nat.Primes,
    8 * Real.log (p : ℝ) *
      thetaMovingHorizonConnection (thetaWardContinuousHalfDensityProfile q)
        (Real.log (p : ℝ)) ^ 2

/-- Covariant Hardy--Green energy at abstract positive depth. -/
def thetaPhysicalEndpointCovariantHardyGreenEnergy (d : ℝ) : ℝ :=
  d ^ 2 * thetaPhysicalEndpointPrimeHardyGreenEnergy d

/-- Unlike the original Ward half-density, the covariant energy is prime-summable on every fibre. -/
theorem summable_thetaWardMovingHorizonCovariantPrimeEnergyTerm
    (q : XiZeroCopy) :
    Summable (fun p : Nat.Primes =>
      8 * Real.log (p : ℝ) *
        thetaMovingHorizonConnection (thetaWardContinuousHalfDensityProfile q)
          (Real.log (p : ℝ)) ^ 2) := by
  by_cases h : primeDepthBVWoldXiCenteredRate q.1 = 0
  · simp [thetaMovingHorizonConnection_wardContinuousHalfDensityProfile, h]
  · have hsum :=
      (summable_physicalPrimeEndpointWeight_mul_hardyGreenResidual_sq q h).mul_left
        (|primeDepthBVWoldXiCenteredRate q.1| ^ 2)
    exact hsum.congr (fun p =>
      (eight_mul_log_mul_connection_sq_eq_depth_sq_mul_residual_sample p q h).symm)

/-- Actual copy energy is exactly depth squared times P-G30's Hardy--Green energy. -/
theorem thetaWardMovingHorizonCovariantPrimeEnergy_eq
    (q : XiZeroCopy)
    (h : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    thetaWardMovingHorizonCovariantPrimeEnergy q =
      thetaPhysicalEndpointCovariantHardyGreenEnergy
        |primeDepthBVWoldXiCenteredRate q.1| := by
  rw [thetaWardMovingHorizonCovariantPrimeEnergy,
    thetaPhysicalEndpointCovariantHardyGreenEnergy,
    ← thetaPhysicalEndpointSampledHardyGreenResidualEnergy_eq q h,
    thetaPhysicalEndpointSampledHardyGreenResidualEnergy,
    ← tsum_mul_left]
  exact tsum_congr (fun p =>
    eight_mul_log_mul_connection_sq_eq_depth_sq_mul_residual_sample p q h)

/-- Sharp regular wall coefficient: the covariant energy is asymptotic to `4d`. -/
theorem tendsto_thetaPhysicalEndpointCovariantHardyGreenEnergy_div_depth :
    Tendsto (fun d : ℝ => thetaPhysicalEndpointCovariantHardyGreenEnergy d / d)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 4) := by
  refine tendsto_depth_mul_thetaPhysicalEndpointPrimeHardyGreenEnergy.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  change 0 < d at hd
  rw [thetaPhysicalEndpointCovariantHardyGreenEnergy]
  field_simp [hd.ne']

/-- Covariant energy extends continuously to value zero at the critical wall. -/
theorem tendsto_thetaPhysicalEndpointCovariantHardyGreenEnergy :
    Tendsto thetaPhysicalEndpointCovariantHardyGreenEnergy
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hzero : Tendsto (fun d : ℝ => d)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := nhdsWithin_le_nhds
  have h := hzero.mul tendsto_depth_mul_thetaPhysicalEndpointPrimeHardyGreenEnergy
  rw [show thetaPhysicalEndpointCovariantHardyGreenEnergy =
      fun d : ℝ => d * (d * thetaPhysicalEndpointPrimeHardyGreenEnergy d) by
    funext d
    rw [thetaPhysicalEndpointCovariantHardyGreenEnergy]
    ring]
  simpa using h

theorem thetaWardMovingHorizonCovariantPrimeEnergy_nonneg (q : XiZeroCopy) :
    0 ≤ thetaWardMovingHorizonCovariantPrimeEnergy q := by
  rw [thetaWardMovingHorizonCovariantPrimeEnergy]
  exact tsum_nonneg fun p => mul_nonneg
    (mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)))
    (sq_nonneg _)

/-- **P-G34 finite-detector law.** Covariant prime energy vanishes exactly at same-fibre theta
boundary neutrality. -/
theorem thetaWardMovingHorizonCovariantPrimeEnergy_eq_zero_iff
    (q : XiZeroCopy) :
    thetaWardMovingHorizonCovariantPrimeEnergy q = 0 ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  let a : ℝ := primeDepthBVWoldXiCenteredRate q.1
  have hcoefficient :
      -(thetaSource.mass * thetaXiRootEnergy q) ≠ 0 :=
    neg_ne_zero.mpr
      (mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q)).ne'
  have hflux_iff : thetaXiRankTwoBoundaryFlux q = 0 ↔ a = 0 := by
    rw [thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate]
    constructor
    · exact fun hflux => (mul_eq_zero.mp hflux).resolve_left hcoefficient
    · intro ha
      rw [show primeDepthBVWoldXiCenteredRate q.1 = 0 from ha, mul_zero]
  rw [hflux_iff]
  constructor
  · intro henergy
    by_contra ha
    have hd : 0 < |a| := abs_pos.mpr ha
    have hsum : Summable (xiMassPrimeSquareEulerWeight |a|) :=
      summable_xiMassPrimeSquareEulerWeight hd
    have hprime : 0 < ∑' p : Nat.Primes, xiMassPrimeSquareEulerWeight |a| p := by
      refine hsum.tsum_pos (fun p => ?_) (⟨2, Nat.prime_two⟩ : Nat.Primes) ?_
      · rw [xiMassPrimeSquareEulerWeight_eq]
        positivity
      · rw [xiMassPrimeSquareEulerWeight_eq]
        positivity
    have habstract :
        0 < thetaPhysicalEndpointCovariantHardyGreenEnergy |a| := by
      rw [thetaPhysicalEndpointCovariantHardyGreenEnergy,
        thetaPhysicalEndpointPrimeHardyGreenEnergy]
      positivity
    have heq := thetaWardMovingHorizonCovariantPrimeEnergy_eq q ha
    rw [heq] at henergy
    linarith
  · intro ha
    simp [thetaWardMovingHorizonCovariantPrimeEnergy,
      thetaMovingHorizonConnection_wardContinuousHalfDensityProfile,
      show primeDepthBVWoldXiCenteredRate q.1 = 0 from ha]

theorem thetaWardMovingHorizonCovariantPrimeEnergy_pos_iff
    (q : XiZeroCopy) :
    0 < thetaWardMovingHorizonCovariantPrimeEnergy q ↔
      thetaXiRankTwoBoundaryFlux q ≠ 0 := by
  constructor
  · intro hpos hflux
    rw [(thetaWardMovingHorizonCovariantPrimeEnergy_eq_zero_iff q).2 hflux] at hpos
    exact lt_irrefl 0 hpos
  · intro hflux
    exact lt_of_le_of_ne (thetaWardMovingHorizonCovariantPrimeEnergy_nonneg q)
      (fun hzero => hflux
        ((thetaWardMovingHorizonCovariantPrimeEnergy_eq_zero_iff q).1 hzero.symm))

/-- Global vanishing of the finite covariant moving-horizon energy is exactly RH. -/
theorem all_thetaWardMovingHorizonCovariantPrimeEnergy_eq_zero_iff_riemannHypothesis :
    (∀ q : XiZeroCopy, thetaWardMovingHorizonCovariantPrimeEnergy q = 0) ↔
      RiemannHypothesis := by
  rw [← thetaGreenBoundaryNeutral_iff_riemannHypothesis]
  exact forall_congr' thetaWardMovingHorizonCovariantPrimeEnergy_eq_zero_iff

end

end RHTower.HedenmalmThetaSource
