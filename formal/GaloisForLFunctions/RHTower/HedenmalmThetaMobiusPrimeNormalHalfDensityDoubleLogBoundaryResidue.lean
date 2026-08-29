import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPrimeNormalHalfDensityDixmierTraceNoGo
import GaloisForLFunctions.RHTower.MobiusPrimeApertureRetainedMass

/-!
# Möbius prime-normal half-density double-log boundary residue

Ordinary logarithmic Schatten normalization is blind to the prime-sparse physical half-density.
The prime-natural double logarithm retains an exact quantized invariant.  On every nonneutral Xi
copy, ordered physical half-density energy differs from reciprocal-prime mass by an absolutely
summable correction, so its `log log` residue is exactly one.  On every neutral copy it vanishes
identically.

Consequently global zero double-log residue is equivalent to RH.  This constructs the strongest
positive survivor of the Dixmier-trace no-go; the remaining RH-bearing step is to force this
source-built residue to vanish using genuinely non-diagonal Gamma--theta grade/support transport.
-/

open Complex Filter
open scoped BigOperators Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Ordered physical half-density energy through the `N`th prime. -/
def thetaMobiusPrimeNormalHalfDensityEnergyPrefix
    (q : XiZeroCopy) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    thetaMobiusPrimeNormalProfileHalfDensityAmplitude (nthPrimeSubtype n) q ^ 2

/-- Difference between universal reciprocal-prime mass and physical half-density energy. -/
def thetaMobiusPrimeNormalHalfDensityEnergyCorrection
    (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  1 / (p : ℝ) - thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q ^ 2

theorem thetaMobiusPrimeNormalHalfDensityEnergyCorrection_nonneg
    (q : XiZeroCopy) (p : Nat.Primes) :
    0 ≤ thetaMobiusPrimeNormalHalfDensityEnergyCorrection q p := by
  have hamp := abs_thetaMobiusPrimeNormalProfileHalfDensityAmplitude_le_universal p q
  have hu0 : 0 ≤ routeNGammaSewnUniversalCriticalChannelAmplitude p := by
    rw [routeNGammaSewnUniversalCriticalChannelAmplitude]
    exact Real.rpow_nonneg (by exact_mod_cast p.2.pos.le) _
  have huSq : routeNGammaSewnUniversalCriticalChannelAmplitude p ^ 2 = 1 / (p : ℝ) := by
    rw [routeNGammaSewnUniversalCriticalChannelAmplitude_sq,
      routeNGammaSewnUniversalCriticalChannelMass, Real.rpow_neg_one]
    simp
  have hprod : 0 ≤
      (routeNGammaSewnUniversalCriticalChannelAmplitude p -
          |thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q|) *
        (routeNGammaSewnUniversalCriticalChannelAmplitude p +
          |thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q|) :=
    mul_nonneg (sub_nonneg.mpr hamp) (add_nonneg hu0 (abs_nonneg _))
  rw [thetaMobiusPrimeNormalHalfDensityEnergyCorrection, ← huSq]
  nlinarith [sq_abs (thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q)]

/-- The correction is dominated by an absolutely summable prime power off the wall. -/
theorem thetaMobiusPrimeNormalHalfDensityEnergyCorrection_le
    (q : XiZeroCopy) (p : Nat.Primes) :
    thetaMobiusPrimeNormalHalfDensityEnergyCorrection q p ≤
      2 * (p : ℝ) ^ (-(1 + |primeDepthBVWoldXiCenteredRate q.1|)) := by
  let t := primeDepthBVWoldXiCenteredRate q.1
  let u := routeNGammaSewnUniversalCriticalChannelAmplitude p
  let v := routeNGammaSewnTwistedCriticalChannelAmplitude t p
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hv0 : 0 ≤ v := by
    dsimp [v, routeNGammaSewnTwistedCriticalChannelAmplitude]
    exact Real.rpow_nonneg hp0.le _
  have hampSq : thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q ^ 2 =
      (u - v) ^ 2 := by
    rw [thetaMobiusPrimeNormalProfileHalfDensityAmplitude_eq_channelGap]
    change (if 0 ≤ t then u - v else -(u - v)) ^ 2 = (u - v) ^ 2
    split <;> ring
  have huSq : u ^ 2 = 1 / (p : ℝ) := by
    dsimp [u]
    rw [routeNGammaSewnUniversalCriticalChannelAmplitude_sq,
      routeNGammaSewnUniversalCriticalChannelMass, Real.rpow_neg_one]
    simp
  have huv : u * v = (p : ℝ) ^ (-(1 + |t|)) := by
    dsimp [u, v, routeNGammaSewnUniversalCriticalChannelAmplitude,
      routeNGammaSewnTwistedCriticalChannelAmplitude]
    rw [← Real.rpow_add hp0]
    congr 1
    ring
  rw [thetaMobiusPrimeNormalHalfDensityEnergyCorrection, ← huSq, hampSq]
  change u ^ 2 - (u - v) ^ 2 ≤ 2 * (p : ℝ) ^ (-(1 + |t|))
  rw [← huv]
  nlinarith [sq_nonneg v]

/-- Off the wall, the full reciprocal-minus-physical energy correction is summable. -/
theorem summable_thetaMobiusPrimeNormalHalfDensityEnergyCorrection_of_rate_ne_zero
    (q : XiZeroCopy) (hrate : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    Summable (thetaMobiusPrimeNormalHalfDensityEnergyCorrection q) := by
  let sigma := 1 + |primeDepthBVWoldXiCenteredRate q.1|
  have hsigma : 1 < sigma := by
    dsimp [sigma]
    linarith [abs_pos.mpr hrate]
  have hmajor : Summable (fun p : Nat.Primes => 2 * (p : ℝ) ^ (-sigma)) := by
    exact (summable_prime_rpow hsigma).mul_left 2
  apply Summable.of_nonneg_of_le
    (fun p => thetaMobiusPrimeNormalHalfDensityEnergyCorrection_nonneg q p)
    (fun p => by
      simpa [sigma] using thetaMobiusPrimeNormalHalfDensityEnergyCorrection_le q p)
    hmajor

/-- Exact finite-prefix decomposition into universal prime mass minus the summable correction. -/
theorem thetaMobiusPrimeNormalHalfDensityEnergyPrefix_eq_primeDiagonalSum_sub_correction
    (q : XiZeroCopy) (N : ℕ) :
    thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N =
      primeDiagonalSum N -
        ∑ n ∈ Finset.range (N + 1),
          thetaMobiusPrimeNormalHalfDensityEnergyCorrection q (nthPrimeSubtype n) := by
  rw [thetaMobiusPrimeNormalHalfDensityEnergyPrefix, primeDiagonalSum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [thetaMobiusPrimeNormalHalfDensityEnergyCorrection]
  simp [nthPrimeSubtype, one_div]

/-- Every nonneutral Xi copy carries exactly one unit of double-logarithmic physical boundary
energy. -/
theorem tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_one_of_boundaryFlux_ne_zero
    (q : XiZeroCopy) (hflux : thetaXiRankTwoBoundaryFlux q ≠ 0) :
    Tendsto (fun N : ℕ =>
      thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N /
        Real.log (Real.log (N : ℝ))) atTop (𝓝 1) := by
  have hrate : primeDepthBVWoldXiCenteredRate q.1 ≠ 0 := by
    intro hzero
    apply hflux
    rw [thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate, hzero]
    ring
  have hcorrPrime :=
    summable_thetaMobiusPrimeNormalHalfDensityEnergyCorrection_of_rate_ne_zero q hrate
  have hcorrNat : Summable (fun n : ℕ =>
      thetaMobiusPrimeNormalHalfDensityEnergyCorrection q (nthPrimeSubtype n)) := by
    exact nthPrimeEquiv.summable_iff.mpr hcorrPrime
  have hcorrLimit : Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.range (N + 1),
        thetaMobiusPrimeNormalHalfDensityEnergyCorrection q (nthPrimeSubtype n))
      atTop (𝓝 (∑' n : ℕ,
        thetaMobiusPrimeNormalHalfDensityEnergyCorrection q (nthPrimeSubtype n))) := by
    simpa [Function.comp_def] using
      hcorrNat.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglogTop : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlogTop
  have hcorrZero := hcorrLimit.div_atTop hloglogTop
  have hsub := tendsto_primeDiagonalSum_div_logLog.sub hcorrZero
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [] with N
  rw [thetaMobiusPrimeNormalHalfDensityEnergyPrefix_eq_primeDiagonalSum_sub_correction]
  ring

/-- A neutral Xi copy has identically zero double-logarithmic physical boundary energy. -/
theorem tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_zero_of_boundaryFlux_zero
    (q : XiZeroCopy) (hflux : thetaXiRankTwoBoundaryFlux q = 0) :
    Tendsto (fun N : ℕ =>
      thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N /
        Real.log (Real.log (N : ℝ))) atTop (𝓝 0) := by
  rw [show (fun N : ℕ =>
      thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N /
        Real.log (Real.log (N : ℝ))) = fun _ : ℕ => 0 by
    funext N
    rw [thetaMobiusPrimeNormalHalfDensityEnergyPrefix,
      show (fun n : ℕ =>
        thetaMobiusPrimeNormalProfileHalfDensityAmplitude (nthPrimeSubtype n) q ^ 2) =
        fun _ : ℕ => 0 by
      funext n
      rw [thetaMobiusPrimeNormalProfileHalfDensityAmplitude,
        (thetaMobiusPrimeNormalReflectionProfile_eq_zero_iff_boundaryFlux_zero
          (nthPrimeSubtype n) q).2 hflux]
      ring]
    simp]
  exact tendsto_const_nhds

/-- Zero double-logarithmic physical energy is exactly same-copy theta neutrality. -/
theorem tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_zero_iff_boundaryFlux_zero
    (q : XiZeroCopy) :
    Tendsto (fun N : ℕ =>
      thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N /
        Real.log (Real.log (N : ℝ))) atTop (𝓝 0) ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  constructor
  · intro hzero
    by_contra hflux
    have hone :=
      tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_one_of_boundaryFlux_ne_zero
        q hflux
    have : (0 : ℝ) = 1 := tendsto_nhds_unique hzero hone
    norm_num at this
  · exact
      tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_zero_of_boundaryFlux_zero q

/-- Unit double-logarithmic physical energy is exactly same-copy nonneutrality. -/
theorem tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_one_iff_boundaryFlux_ne_zero
    (q : XiZeroCopy) :
    Tendsto (fun N : ℕ =>
      thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N /
        Real.log (Real.log (N : ℝ))) atTop (𝓝 1) ↔
      thetaXiRankTwoBoundaryFlux q ≠ 0 := by
  constructor
  · intro hone hflux
    have hzero :=
      tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_zero_of_boundaryFlux_zero
        q hflux
    have : (1 : ℝ) = 0 := tendsto_nhds_unique hone hzero
    norm_num at this
  · exact
      tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_one_of_boundaryFlux_ne_zero q

/-- Global zero double-logarithmic physical boundary energy is exactly RH. -/
theorem all_tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_zero_iff_riemannHypothesis :
    (∀ q : XiZeroCopy,
      Tendsto (fun N : ℕ =>
        thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N /
          Real.log (Real.log (N : ℝ))) atTop (𝓝 0)) ↔
      RiemannHypothesis := by
  rw [← thetaGreenBoundaryNeutral_iff_riemannHypothesis]
  exact forall_congr'
    tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_zero_iff_boundaryFlux_zero

end

end RHTower.HedenmalmThetaSource
