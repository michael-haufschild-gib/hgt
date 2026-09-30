import GaloisForLFunctions.RHTower.LiEvenCrossEulerCurrentBridge
import GaloisForLFunctions.RHTower.XiShiftedReciprocalHankelTailCriterion
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Actual Euler-current mass series

The source negative-binomial transport gives the mass expansion of the actual
Cassini logarithmic-mass current.  Its constant coefficient is zero: the
coefficient indexed by `n` below belongs to mass degree `n + 1`.
-/

open Complex Filter Function Metric Set Topology
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- Source coefficient at mass degree `n + 1`. -/
def liEvenCrossEulerMassCoeff (n : ℕ) : ℝ :=
  2 * (-1 : ℝ) ^ n * ((n + 1 : ℕ) : ℝ) ^ 2 * normalizedPrimeArchMoment n

/-- Canonical Taylor coefficients, including the zero constant term. -/
def liEvenCrossEulerMassTaylorCoeff : ℕ → ℂ
  | 0 => 0
  | n + 1 => (liEvenCrossEulerMassCoeff n : ℂ)

@[simp] theorem liEvenCrossEulerMassTaylorCoeff_zero :
    liEvenCrossEulerMassTaylorCoeff 0 = 0 := rfl

@[simp] theorem liEvenCrossEulerMassTaylorCoeff_succ (n : ℕ) :
    liEvenCrossEulerMassTaylorCoeff (n + 1) = (liEvenCrossEulerMassCoeff n : ℂ) := rfl

/-- The ordinary mass series, without the even interleaving of the central germ. -/
def liEvenCrossEulerMassPowerSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ liEvenCrossEulerMassTaylorCoeff

private theorem hasSum_primeArchSourceNegativeBinomial
    {y : ℝ} (hy : 0 ≤ y) (hymax : y < 41 / 2) (m : ℕ) :
    HasSum (fun r : ℕ =>
      (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (y : ℂ) ^ r *
        (normalizedPrimeArchMoment (r + m) : ℂ))
      (xiShiftedReciprocalMoment y m) := by
  have hdouble := summable_xiShiftedReciprocalSource_double hy hymax m
  have hsum : Summable (fun r : ℕ =>
      (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (y : ℂ) ^ r *
        (normalizedPrimeArchMoment (r + m) : ℂ)) := by
    apply hdouble.prod.congr
    intro r
    rw [ofReal_normalizedPrimeArchMoment_eq_xiCentralReciprocalMoment,
      ← tsum_xiZeroCopyReciprocalSquare_pow, ← tsum_mul_left]
  rw [xiShiftedReciprocalMoment_eq_primeArchSourceNegativeBinomial hy hymax]
  exact hsum.hasSum

private theorem liEvenCrossCassiniLogMassCurrent_eq_shiftedMoments
    {y : ℝ} (hy : 0 < y) :
    liEvenCrossCassiniLogMassCurrent (y : ℂ) =
      2 * (y : ℂ) * xiShiftedReciprocalMoment y 0 -
      6 * (y : ℂ) ^ 2 * xiShiftedReciprocalMoment y 1 +
      4 * (y : ℂ) ^ 3 * xiShiftedReciprocalMoment y 2 := by
  have h0 := neg_two_mul_cassiniLogDeriv_jet_one_sub_eq_xiShiftedMoment hy 0
  have h1 := neg_two_mul_cassiniLogDeriv_jet_one_sub_eq_xiShiftedMoment hy 1
  have h2 := neg_two_mul_cassiniLogDeriv_jet_one_sub_eq_xiShiftedMoment hy 2
  norm_num [iteratedDeriv_succ, iteratedDeriv_one] at h0 h1 h2
  unfold liEvenCrossCassiniLogMassCurrent
  linear_combination 2 * (y : ℂ) * h0 - 6 * (y : ℂ) ^ 2 * h1 +
    2 * (y : ℂ) ^ 3 * h2

/-- Absolute source transport and the first two index shifts assemble the exact mass series. -/
theorem hasSum_liEvenCrossEulerMassSeries_shiftedMoments
    {y : ℝ} (hy : 0 ≤ y) (hy1 : y < 1) :
    HasSum (fun n : ℕ => (liEvenCrossEulerMassCoeff n : ℂ) * (y : ℂ) ^ (n + 1))
      (2 * (y : ℂ) * xiShiftedReciprocalMoment y 0 -
        6 * (y : ℂ) ^ 2 * xiShiftedReciprocalMoment y 1 +
        4 * (y : ℂ) ^ 3 * xiShiftedReciprocalMoment y 2) := by
  have hymax : y < 41 / 2 := by linarith
  have h0 : HasSum (fun n : ℕ =>
      2 * (-1 : ℂ) ^ n * (y : ℂ) ^ (n + 1) *
        (normalizedPrimeArchMoment n : ℂ))
      (2 * (y : ℂ) * xiShiftedReciprocalMoment y 0) := by
    apply ((hasSum_primeArchSourceNegativeBinomial hy hymax 0).mul_left
      (2 * (y : ℂ))).congr_fun
    intro n
    simp only [Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, pow_succ]
    ring
  have h1 : HasSum (fun n : ℕ =>
      6 * (-1 : ℂ) ^ n * (n : ℂ) * (y : ℂ) ^ (n + 1) *
        (normalizedPrimeArchMoment n : ℂ))
      (-6 * (y : ℂ) ^ 2 * xiShiftedReciprocalMoment y 1) := by
    have ht : HasSum (fun n : ℕ =>
        6 * (-1 : ℂ) ^ (n + 1) * ((n + 1 : ℕ) : ℂ) *
          (y : ℂ) ^ (n + 1 + 1) * (normalizedPrimeArchMoment (n + 1) : ℂ))
        (-6 * (y : ℂ) ^ 2 * xiShiftedReciprocalMoment y 1) := by
      apply ((hasSum_primeArchSourceNegativeBinomial hy hymax 1).mul_left
        (-6 * (y : ℂ) ^ 2)).congr_fun
      intro n
      simp only [Nat.choose_one_right, pow_succ]
      ring
    simpa only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_mul, add_zero]
      using (hasSum_nat_add_iff (f := fun n : ℕ =>
        6 * (-1 : ℂ) ^ n * (n : ℂ) * (y : ℂ) ^ (n + 1) *
          (normalizedPrimeArchMoment n : ℂ)) 1).mp ht
  have h2 : HasSum (fun n : ℕ =>
      2 * (-1 : ℂ) ^ n * (n : ℂ) * ((n : ℂ) - 1) * (y : ℂ) ^ (n + 1) *
        (normalizedPrimeArchMoment n : ℂ))
      (4 * (y : ℂ) ^ 3 * xiShiftedReciprocalMoment y 2) := by
    have ht : HasSum (fun n : ℕ =>
        2 * (-1 : ℂ) ^ (n + 2) * ((n + 2 : ℕ) : ℂ) *
          (((n + 2 : ℕ) : ℂ) - 1) * (y : ℂ) ^ (n + 2 + 1) *
          (normalizedPrimeArchMoment (n + 2) : ℂ))
        (4 * (y : ℂ) ^ 3 * xiShiftedReciprocalMoment y 2) := by
      apply ((hasSum_primeArchSourceNegativeBinomial hy hymax 2).mul_left
        (4 * (y : ℂ) ^ 3)).congr_fun
      intro n
      rw [Nat.cast_choose_two]
      simp only [pow_succ]
      ring
    simpa [Finset.sum_range_succ] using (hasSum_nat_add_iff (f := fun n : ℕ =>
      2 * (-1 : ℂ) ^ n * (n : ℂ) * ((n : ℂ) - 1) * (y : ℂ) ^ (n + 1) *
        (normalizedPrimeArchMoment n : ℂ)) 2).mp ht
  have hh := (h0.add h1).add h2
  rw [show 2 * (y : ℂ) * xiShiftedReciprocalMoment y 0 +
      -6 * (y : ℂ) ^ 2 * xiShiftedReciprocalMoment y 1 +
      4 * (y : ℂ) ^ 3 * xiShiftedReciprocalMoment y 2 =
    2 * (y : ℂ) * xiShiftedReciprocalMoment y 0 -
      6 * (y : ℂ) ^ 2 * xiShiftedReciprocalMoment y 1 +
      4 * (y : ℂ) ^ 3 * xiShiftedReciprocalMoment y 2 by ring] at hh
  apply hh.congr_fun
  intro n
  simp only [liEvenCrossEulerMassCoeff]
  push_cast
  ring

/-- Complex absolute summability on the positive real unit mass interval. -/
theorem summable_liEvenCrossEulerMassSeries
    {y : ℝ} (hy : 0 ≤ y) (hy1 : y < 1) :
    Summable (fun n : ℕ => (liEvenCrossEulerMassCoeff n : ℂ) * (y : ℂ) ^ (n + 1)) :=
  (hasSum_liEvenCrossEulerMassSeries_shiftedMoments hy hy1).summable

/-- Absolute coefficient summability, stated over the real source coefficients. -/
theorem summable_norm_liEvenCrossEulerMassCoeff_mul_pow
    {y : ℝ} (hy : 0 ≤ y) (hy1 : y < 1) :
    Summable (fun n : ℕ => ‖liEvenCrossEulerMassCoeff n‖ * y ^ (n + 1)) := by
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hy] using (summable_liEvenCrossEulerMassSeries hy hy1).norm

/-- The actual current has the source-only mass expansion with no extra analytic or RH premise. -/
theorem liEvenCrossCassiniLogMassCurrent_eq_massSeries
    {y : ℝ} (hy : 0 < y) (hy1 : y < 1) :
    liEvenCrossCassiniLogMassCurrent (y : ℂ) =
      ∑' n : ℕ, (liEvenCrossEulerMassCoeff n : ℂ) * (y : ℂ) ^ (n + 1) := by
  rw [liEvenCrossCassiniLogMassCurrent_eq_shiftedMoments hy]
  exact (hasSum_liEvenCrossEulerMassSeries_shiftedMoments hy.le hy1).tsum_eq.symm

/-- The formal series has precisely the shifted source expansion on positive real masses. -/
theorem liEvenCrossEulerMassPowerSeries_sum_eq_massSeries
    {y : ℝ} (hy : 0 ≤ y) (hy1 : y < 1) :
    liEvenCrossEulerMassPowerSeries.sum (y : ℂ) =
      ∑' n : ℕ, (liEvenCrossEulerMassCoeff n : ℂ) * (y : ℂ) ^ (n + 1) := by
  change FormalMultilinearSeries.ofScalarsSum liEvenCrossEulerMassTaylorCoeff (y : ℂ) = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [smul_eq_mul]
  have hs : Summable (fun n : ℕ =>
      liEvenCrossEulerMassTaylorCoeff (n + 1) * (y : ℂ) ^ (n + 1)) := by
    simpa only [liEvenCrossEulerMassTaylorCoeff_succ] using
      summable_liEvenCrossEulerMassSeries hy hy1
  simpa only [liEvenCrossEulerMassTaylorCoeff_zero, liEvenCrossEulerMassTaylorCoeff_succ,
    zero_mul, zero_add] using tsum_eq_zero_add'
      (f := fun n : ℕ => liEvenCrossEulerMassTaylorCoeff n * (y : ℂ) ^ n) hs

/-- Absolute convergence at mass `1/2` gives an unconditional positive radius. -/
theorem one_half_le_liEvenCrossEulerMassPowerSeries_radius :
    ((1 / 2 : ℝ≥0) : ℝ≥0∞) ≤ liEvenCrossEulerMassPowerSeries.radius := by
  apply FormalMultilinearSeries.le_radius_of_summable
  apply (summable_nat_add_iff 1).mp
  simpa only [liEvenCrossEulerMassPowerSeries, FormalMultilinearSeries.ofScalars_norm,
    liEvenCrossEulerMassTaylorCoeff_succ, Complex.norm_real, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_ofNat] using
    summable_norm_liEvenCrossEulerMassCoeff_mul_pow (y := 1 / 2)
      (by norm_num) (by norm_num)

theorem liEvenCrossEulerMassPowerSeries_radius_pos :
    0 < liEvenCrossEulerMassPowerSeries.radius :=
  (by norm_num : (0 : ℝ≥0∞) < ((1 / 2 : ℝ≥0) : ℝ≥0∞)).trans_le
    one_half_le_liEvenCrossEulerMassPowerSeries_radius

/-- Source nonvanishing at the mass origin is centered Xi nonvanishing, `C(1) ≠ 0`. -/
theorem analyticAt_liEvenCrossCassiniLogMassCurrent_zero :
    AnalyticAt ℂ liEvenCrossCassiniLogMassCurrent 0 := by
  apply analyticAt_liEvenCrossCassiniLogMassCurrent_of_source_ne_zero
  have hsource : xiSquaredSeamEntireQuotient 0 = XiC 0 := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      xiSquaredSeamEntireQuotient_sq 0
  simpa only [sub_zero, xiSquaredSeamCassiniSource, sub_self, hsource] using XiC_zero_ne

/-- The canonical mass Taylor series belongs to the actual source current at zero. -/
theorem hasFPowerSeriesAt_liEvenCrossCassiniLogMassCurrent_zero :
    HasFPowerSeriesAt liEvenCrossCassiniLogMassCurrent liEvenCrossEulerMassPowerSeries 0 := by
  have hp : HasFPowerSeriesAt liEvenCrossEulerMassPowerSeries.sum
      liEvenCrossEulerMassPowerSeries 0 :=
    (liEvenCrossEulerMassPowerSeries.hasFPowerSeriesOnBall
      liEvenCrossEulerMassPowerSeries_radius_pos).hasFPowerSeriesAt
  have hreal : Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simp only [mem_compl_iff, mem_singleton_iff]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt hy)
  haveI : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have hsmall : ∀ᶠ y : ℝ in 𝓝[>] 0, y < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have heq : ∀ᶠ y : ℝ in 𝓝[>] 0,
      liEvenCrossEulerMassPowerSeries.sum (y : ℂ) =
        liEvenCrossCassiniLogMassCurrent (y : ℂ) := by
    filter_upwards [hsmall, self_mem_nhdsWithin] with y hy1 hy
    exact (liEvenCrossEulerMassPowerSeries_sum_eq_massSeries hy.le hy1).trans
      (liEvenCrossCassiniLogMassCurrent_eq_massSeries hy hy1).symm
  exact hp.congr ((hp.analyticAt.frequently_eq_iff_eventually_eq
    analyticAt_liEvenCrossCassiniLogMassCurrent_zero).mp (hreal.frequently heq.frequently))

end

end RHTower
