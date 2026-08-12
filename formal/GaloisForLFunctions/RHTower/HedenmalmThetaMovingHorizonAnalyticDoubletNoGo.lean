import GaloisForLFunctions.RHTower.HedenmalmThetaMovingHorizonCovariantHardyGreenRegularization
import GaloisForLFunctions.RHTower.MobiusLaplaceCriticalDilationNoGo

/-!
# Analytic moving-horizon doublet versus stable covariant channel

P-G34's covariant detector is finite because it retains the decaying channel
`p^(-1/2-|t|)`.  A reflection-equivariant entire source naturally carries both analytic channels
`p^(-1/2-t)` and `p^(-1/2+t)`.  After covariant differentiation their positive doublet energy
splits into a stable term with exponent `-1-2|t|` and an unstable term with exponent
`-1+2|t|`.

The unstable term is beyond the prime harmonic wall for every `t != 0`.  Hence the full analytic
doublet is summable exactly at neutral grade, while the selected stable channel is summable on
every fibre.  Entire reflection completion alone cannot produce P-G34's finite detector: Route P
needs a coefficient-faithful stable/Hardy projection before positive completion.
-/

open scoped BigOperators

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Positive energy of both signed analytic covariant channels. -/
def thetaMovingHorizonAnalyticCovariantDoubletEnergy
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  (t * (p : ℝ) ^ (-(1 / 2 : ℝ) - t)) ^ 2 +
    (t * (p : ℝ) ^ (-(1 / 2 : ℝ) + t)) ^ 2

theorem thetaMovingHorizonAnalyticCovariantDoubletEnergy_eq_signed
    (t : ℝ) (p : Nat.Primes) :
    thetaMovingHorizonAnalyticCovariantDoubletEnergy t p =
      t ^ 2 * (p : ℝ) ^ (-1 - 2 * t) +
        t ^ 2 * (p : ℝ) ^ (-1 + 2 * t) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [thetaMovingHorizonAnalyticCovariantDoubletEnergy,
    mul_pow, mul_pow]
  have hminus : ((p : ℝ) ^ (-(1 / 2 : ℝ) - t)) ^ 2 =
      (p : ℝ) ^ (-1 - 2 * t) := by
    rw [pow_two, ← Real.rpow_add hp]
    congr 1
    ring_nf
  have hplus : ((p : ℝ) ^ (-(1 / 2 : ℝ) + t)) ^ 2 =
      (p : ℝ) ^ (-1 + 2 * t) := by
    rw [pow_two, ← Real.rpow_add hp]
    congr 1
    ring_nf
  rw [hminus, hplus]

/-- The positive analytic doublet is one stable channel plus one unstable channel. -/
theorem thetaMovingHorizonAnalyticCovariantDoubletEnergy_eq_stable_add_unstable
    (t : ℝ) (p : Nat.Primes) :
    thetaMovingHorizonAnalyticCovariantDoubletEnergy t p =
      t ^ 2 * (p : ℝ) ^ (-1 - 2 * |t|) +
        t ^ 2 * (p : ℝ) ^ (-1 + 2 * |t|) := by
  rw [thetaMovingHorizonAnalyticCovariantDoubletEnergy_eq_signed]
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht']
    ring_nf

/-- P-G34's finite connection square is exactly the stable member of the analytic doublet. -/
theorem thetaMovingHorizonConnection_sq_eq_stableAnalyticDoubletChannel
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaMovingHorizonConnection (thetaWardContinuousHalfDensityProfile q)
        (Real.log (p : ℝ)) ^ 2 =
      primeDepthBVWoldXiCenteredRate q.1 ^ 2 *
        (p : ℝ) ^
          (-1 - 2 * |primeDepthBVWoldXiCenteredRate q.1|) := by
  rw [thetaMovingHorizonConnection_wardContinuousHalfDensityProfile_prime_sq,
    routeNGammaSewnTwistedCriticalChannelAmplitude_sq,
    routeNGammaSewnTwistedCriticalChannelMass,
    sq_abs]

/-- Every nonneutral analytic doublet retains a nonsummable prime-harmonic-or-worse channel. -/
theorem not_summable_thetaMovingHorizonAnalyticCovariantDoubletEnergy
    {t : ℝ} (ht : t ≠ 0) :
    ¬ Summable (thetaMovingHorizonAnalyticCovariantDoubletEnergy t) := by
  intro hsum
  let c : ℝ := t ^ 2
  let r : ℝ := -1 + 2 * |t|
  have hc : c ≠ 0 := pow_ne_zero 2 ht
  have hdominant : Summable (fun p : Nat.Primes => c * (p : ℝ) ^ r) := by
    exact Summable.of_nonneg_of_le
      (fun p => by positivity)
      (fun p => by
        rw [thetaMovingHorizonAnalyticCovariantDoubletEnergy_eq_stable_add_unstable]
        dsimp only [c, r]
        exact le_add_of_nonneg_left
          (mul_nonneg (sq_nonneg t) (by positivity)))
      hsum
  have hscaled := hdominant.mul_left c⁻¹
  apply RHTower.not_summable_primeRpow_of_negOne_le (r := r)
    (by dsimp only [r]; linarith [abs_nonneg t])
  refine hscaled.congr (fun p => ?_)
  dsimp only [c, r]
  field_simp [hc]

/-- **P-G35 stable-projection obstruction.** Full analytic doublet is summable only at wall. -/
theorem summable_thetaMovingHorizonAnalyticCovariantDoubletEnergy_iff
    (t : ℝ) :
    Summable (thetaMovingHorizonAnalyticCovariantDoubletEnergy t) ↔ t = 0 := by
  constructor
  · intro hsum
    by_contra ht
    exact not_summable_thetaMovingHorizonAnalyticCovariantDoubletEnergy ht hsum
  · rintro rfl
    rw [show thetaMovingHorizonAnalyticCovariantDoubletEnergy 0 =
        fun _p : Nat.Primes => (0 : ℝ) by
      funext p
      simp [thetaMovingHorizonAnalyticCovariantDoubletEnergy]]
    exact summable_zero

theorem summable_thetaMovingHorizonAnalyticCovariantDoubletEnergy_at_iff_boundaryFlux_zero
    (q : XiZeroCopy) :
    Summable (thetaMovingHorizonAnalyticCovariantDoubletEnergy
      (primeDepthBVWoldXiCenteredRate q.1)) ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  rw [summable_thetaMovingHorizonAnalyticCovariantDoubletEnergy_iff,
    thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate]
  have hcoefficient :
      -(thetaSource.mass * thetaXiRootEnergy q) ≠ 0 :=
    neg_ne_zero.mpr
      (mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q)).ne'
  constructor
  · intro hrate
    rw [hrate, mul_zero]
  · intro hflux
    exact (mul_eq_zero.mp hflux).resolve_left hcoefficient

/-- Global analytic-doublet prime admission is exactly RH, not an unconditional source theorem. -/
theorem all_summable_thetaMovingHorizonAnalyticCovariantDoubletEnergy_iff_riemannHypothesis :
    (∀ q : XiZeroCopy,
      Summable (thetaMovingHorizonAnalyticCovariantDoubletEnergy
        (primeDepthBVWoldXiCenteredRate q.1))) ↔ RiemannHypothesis := by
  rw [← thetaGreenBoundaryNeutral_iff_riemannHypothesis]
  exact forall_congr'
    summable_thetaMovingHorizonAnalyticCovariantDoubletEnergy_at_iff_boundaryFlux_zero

end

end RHTower.HedenmalmThetaSource
