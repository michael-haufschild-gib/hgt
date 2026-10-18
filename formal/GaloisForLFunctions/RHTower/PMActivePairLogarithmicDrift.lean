import GaloisForLFunctions.RHTower.PMAdjacentDivisorSmallDamping
import GaloisForLFunctions.BezoutValuationIncidence.SummationByPartsActivePairAndUncenteredShiftedReduction
import GaloisForLFunctions.BezoutValuationIncidence.ShiftedExponentSmallDampingCovarianceRateAndActiveDrift

/-!
# Arithmetic logarithmic drift of the complete active pair

The same-node and adjacent-node densities determine the active-plus-predecessor drift for every
positive damping. Its small-damping coefficient is positive; the exact complete-energy identity
therefore assigns a larger, explicit cancellation budget to the doubly-inactive interior.
-/

open Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.BiScaleUncertainty

noncomputable section
namespace RHTower

private theorem pm_bounded_div_nat_zero {f : ℕ → ℝ} {C : ℝ} (hf : ∀ n, |f n| ≤ C) :
    Tendsto (fun N : ℕ => f N / N) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun N => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat C)
  rw [norm_div, Real.norm_eq_abs, Real.norm_natCast]
  exact div_le_div_of_nonneg_right (hf N) (Nat.cast_nonneg N)

private theorem pm_sum_shift_sub (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, f (n + 1)) - (∑ n ∈ Icc 1 N, f n) = f (N + 1) - f 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega)]
    linarith

private theorem pm_cesaro_shift {f : ℕ → ℝ} {C L : ℝ}
    (hf : ∀ n, |f n| ≤ C)
    (hmean : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, f n) / (N : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, f (n + 1)) / (N : ℝ)) atTop (𝓝 L) := by
  have hzero := pm_bounded_div_nat_zero (C := 2 * C) (f := fun N => f (N + 1) - f 1)
    (fun N => by linarith [abs_sub (f (N + 1)) (f 1), hf (N + 1), hf 1])
  simpa only [add_zero] using (hmean.add hzero).congr (fun N => by
    rw [← add_div, ← pm_sum_shift_sub f N]
    ring)

private theorem pm_compensated_log_of_mean {f : ℕ → ℝ} {C L : ℝ}
    (hf : ∀ n, |f n| ≤ C)
    (hmean : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, f n) / (N : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 (N - 1),
        f n * (1 / ((n : ℝ) + 1) - 1 / ((N : ℝ) + 1))) / Real.log N)
      atTop (𝓝 L) := by
  have hC : 0 ≤ C := (abs_nonneg (f 0)).trans (hf 0)
  let H : ℕ → ℝ := fun N => ∑ n ∈ Icc 1 N, f n / (n : ℝ)
  let P : ℕ → ℝ := fun N => ∑ n ∈ Icc 1 N,
    f n * (1 / ((n : ℝ) + 1) - 1 / ((N : ℝ) + 1))
  have hid (N : ℕ) : H N - P N =
      (∑ n ∈ Icc 1 N, f n / (pronicSeq n : ℝ)) + (∑ n ∈ Icc 1 N, f n) / ((N : ℝ) + 1) := by
    dsimp only [H, P]
    rw [Finset.sum_div, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (by have := (mem_Icc.mp hn).1; omega : n ≠ 0)
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
    unfold pronicSeq
    push_cast
    field_simp
    ring
  have hpr (N : ℕ) : |∑ n ∈ Icc 1 N, f n / (pronicSeq n : ℝ)| ≤ C := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N, |f n / (pronicSeq n : ℝ)| := abs_sum_le_sum_abs _ _
      _ ≤ C * ∑ n ∈ Icc 1 N, (1 : ℝ) / (pronicSeq n : ℝ) := by
        rw [mul_sum]
        apply sum_le_sum
        intro n _
        rw [abs_div,
          abs_of_nonneg (Nat.cast_nonneg (pronicSeq n) : (0 : ℝ) ≤ (pronicSeq n : ℝ)),
          mul_one_div]
        exact div_le_div_of_nonneg_right (hf n) (Nat.cast_nonneg _)
      _ ≤ C := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (sum_one_div_pronicSeq_le_one N) hC
  have hsum (N : ℕ) : |∑ n ∈ Icc 1 N, f n| ≤ (N : ℝ) * C := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N, |f n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Icc 1 N, C := sum_le_sum fun n _ => hf n
      _ = _ := by simp
  have hgap (N : ℕ) : |H N - P N| ≤ 2 * C := by
    rw [hid]
    apply (abs_add_le _ _).trans
    have hcomp : |(∑ n ∈ Icc 1 N, f n) / ((N : ℝ) + 1)| ≤ C := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      apply (div_le_iff₀ (by positivity)).mpr
      exact (hsum N).trans (by nlinarith)
    linarith [hpr N]
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun N : ℕ => (H N - P N) / Real.log N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := 2 * C)).div_atTop hlog)
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog0 : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlog0]
    exact div_le_div_of_nonneg_right (hgap N) hlog0.le
  have hmain : Tendsto (fun N : ℕ => P N / Real.log N) atTop (𝓝 L) := by
    simpa only [sub_zero] using ((pm_tendsto_harmonic_average_of_mean hmean).sub he).congr
      (fun N => by dsimp only [H, Pi.sub_apply]; ring)
  apply hmain.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hs : Icc 1 N = insert N (Icc 1 (N - 1)) := by
    ext n
    simp only [mem_Icc, mem_insert]
    omega
  have hn : N ∉ Icc 1 (N - 1) := by simp only [mem_Icc]; omega
  simp only [P, hs, sum_insert hn, sub_self, mul_zero, zero_add]

/-- The exact coefficient of logarithmic growth in the active-plus-predecessor sum. -/
def pmActivePairLogDrift (ε : ℝ) : ℝ :=
  (pmShiftedExponentSecondDensity ε - pmPowerDampedSecondDensity ε -
    pmAdjacentDivisorDensity ε (1 + ε) + pmAdjacentDivisorDensity ε ε) / 2

private theorem pm_active_sawtooth_bounds {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    0 ≤ pmActiveSawtoothComponent ε n ∧ pmActiveSawtoothComponent ε n ≤ 1 / 2 := by
  refine ⟨pmActiveSawtoothComponent_nonneg hε.le n, ?_⟩
  unfold pmActiveSawtoothComponent
  linarith [pmPowerDampedDivisorCoeff_nonneg hε.le n,
    pmPowerDampedDivisorCoeff_le_one (by linarith : 0 ≤ 1 + ε) n]

private def pmActivePairSummand (ε : ℝ) (n : ℕ) : ℝ :=
  pmPowerDampedCenteredDivisorCoeff ε (n + 1) * addDiff (pmActiveSawtoothComponent ε) n

private theorem pmActivePairSummand_eq (ε : ℝ) (n : ℕ) :
    pmActivePairSummand ε n =
      (pmPowerDampedDivisorCoeff ε (n + 1) * pmPowerDampedDivisorCoeff (1 + ε) (n + 1) -
        pmPowerDampedDivisorCoeff ε (n + 1) ^ 2 -
        pmPowerDampedDivisorCoeff ε (n + 1) * pmPowerDampedDivisorCoeff (1 + ε) n +
        pmPowerDampedDivisorCoeff ε (n + 1) * pmPowerDampedDivisorCoeff ε n) / 2 -
        (pmPowerDampedDivisorDensity ε).re *
          (pmActiveSawtoothComponent ε (n + 1) - pmActiveSawtoothComponent ε n) := by
  unfold pmActivePairSummand pmPowerDampedCenteredDivisorCoeff addDiff pmActiveSawtoothComponent
  ring

private theorem pmActivePairSummand_bound {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    |pmActivePairSummand ε n| ≤ 1 + |(pmPowerDampedDivisorDensity ε).re| := by
  have hu : |pmPowerDampedDivisorCoeff ε (n + 1)| ≤ 1 := by
    rw [abs_of_nonneg (pmPowerDampedDivisorCoeff_nonneg hε.le _)]
    exact pmPowerDampedDivisorCoeff_le_one hε.le _
  have hS : |pmActiveSawtoothComponent ε (n + 1) - pmActiveSawtoothComponent ε n| ≤ 1 := by
    have h1 := pm_active_sawtooth_bounds hε (n + 1)
    have h0 := pm_active_sawtooth_bounds hε n
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  unfold pmActivePairSummand pmPowerDampedCenteredDivisorCoeff addDiff
  rw [abs_mul]
  have hx : |pmPowerDampedDivisorCoeff ε (n + 1) - (pmPowerDampedDivisorDensity ε).re| ≤
      1 + |(pmPowerDampedDivisorDensity ε).re| := by
    linarith [abs_sub (pmPowerDampedDivisorCoeff ε (n + 1))
      (pmPowerDampedDivisorDensity ε).re]
  calc
    _ ≤ (1 + |(pmPowerDampedDivisorDensity ε).re|) *
        |pmActiveSawtoothComponent ε (n + 1) - pmActiveSawtoothComponent ε n| :=
      mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    _ ≤ (1 + |(pmPowerDampedDivisorDensity ε).re|) * 1 :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := mul_one _

private theorem pmActivePairSummand_mean {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, pmActivePairSummand ε n) / (N : ℝ))
      atTop (𝓝 (pmActivePairLogDrift ε)) := by
  have hA0 : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, pmPowerDampedDivisorCoeff ε n *
        pmPowerDampedDivisorCoeff (1 + ε) n) / (N : ℝ))
      atTop (𝓝 (pmShiftedExponentSecondDensity ε)) := by
    simpa only [Function.comp_def, Nat.floor_natCast] using
      (tendsto_pmPowerDampedDivisorCoeff_mul_add_one_mean hε).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hC0 : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, pmPowerDampedDivisorCoeff ε n ^ 2) / (N : ℝ))
      atTop (𝓝 (pmPowerDampedSecondDensity ε)) := by
    simpa only [Function.comp_def, Nat.floor_natCast] using
      (tendsto_pmPowerDampedDivisorCoeff_sq_mean hε).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hA := pm_cesaro_shift (C := 1) (fun n => by
    have hu0 := pmPowerDampedDivisorCoeff_nonneg hε.le n
    have hv0 := pmPowerDampedDivisorCoeff_nonneg (by linarith : 0 ≤ 1 + ε) n
    rw [abs_of_nonneg (mul_nonneg hu0 hv0)]
    exact (mul_le_mul_of_nonneg_right (pmPowerDampedDivisorCoeff_le_one hε.le n) hv0).trans
      (by simpa using pmPowerDampedDivisorCoeff_le_one (by linarith : 0 ≤ 1 + ε) n)) hA0
  have hC := pm_cesaro_shift (C := 1) (fun n => by
    rw [abs_of_nonneg (sq_nonneg _)]
    have h0 := pmPowerDampedDivisorCoeff_nonneg hε.le n
    have h1 := pmPowerDampedDivisorCoeff_le_one hε.le n
    nlinarith) hC0
  have hS : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N,
        (pmActiveSawtoothComponent ε (n + 1) - pmActiveSawtoothComponent ε n)) / (N : ℝ))
      atTop (𝓝 0) := by
    have hz := pm_bounded_div_nat_zero (C := 1 / 2)
      (f := fun N => pmActiveSawtoothComponent ε (N + 1)) (fun N => by
        rw [abs_of_nonneg (pm_active_sawtooth_bounds hε _).1]
        exact (pm_active_sawtooth_bounds hε _).2)
    apply hz.congr
    intro N
    rw [sum_sub_distrib, pm_sum_shift_sub, pmActiveSawtoothComponent_one, sub_zero]
  have h := ((((hA.sub hC).sub
    (tendsto_pm_adjacent_divisor_mean hε (by linarith : 0 < 1 + ε))).add
    (tendsto_pm_adjacent_divisor_mean hε hε)).div_const (2 : ℝ)).sub
      (hS.const_mul (pmPowerDampedDivisorDensity ε).re)
  have ht : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, pmActivePairSummand ε n) / (N : ℝ))
      atTop (𝓝 ((pmShiftedExponentSecondDensity ε - pmPowerDampedSecondDensity ε -
        pmAdjacentDivisorDensity ε (1 + ε) + pmAdjacentDivisorDensity ε ε) / 2 -
        (pmPowerDampedDivisorDensity ε).re * 0)) := by
    apply h.congr
    intro N
    simp only [pmActivePairSummand_eq, sum_sub_distrib, sum_add_distrib, ← sum_div, ← mul_sum]
    ring
  simpa only [mul_zero, sub_zero, pmActivePairLogDrift] using ht

/-- The complete active-plus-predecessor sum has an unconditional logarithmic rate. -/
theorem tendsto_pmActivePair_div_log {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ =>
      (pmActivePredictableMartingaleSum ε N + pmPredecessorPeakMartingaleSum ε N) /
        Real.log N) atTop (𝓝 (pmActivePairLogDrift ε)) := by
  apply (pm_compensated_log_of_mean (pmActivePairSummand_bound hε)
    (pmActivePairSummand_mean hε)).congr
  intro N
  rw [(pmPredictableMartingaleSum_sub_pmBezoutInteriorMartingaleSum_eq ε N).2]
  rfl

/-- The active-pair logarithmic rate has a strictly positive small-damping coefficient. -/
theorem tendsto_pmActivePairLogDrift_div_parameter :
    Tendsto (fun ε : ℝ => pmActivePairLogDrift ε / ε) (𝓝[>] 0)
      (𝓝 (1 / 4 - pmAdjacentArtinConstant / 2)) := by
  have h := (((tendsto_pmShiftedExponentSecondDensity_div_parameter.sub
    tendsto_pmPowerDampedSecondDensity_div_parameter).sub
      tendsto_pmAdjacentDivisorDensity_shifted_div_parameter).add
        tendsto_pmAdjacentDivisorDensity_self_div_parameter).div_const (2 : ℝ)
  have ht : Tendsto (fun ε : ℝ => pmActivePairLogDrift ε / ε) (𝓝[>] 0)
      (𝓝 ((1 - 1 / 2 - pmAdjacentArtinConstant + 0) / 2)) := by
    apply h.congr
    intro ε
    dsimp only [pmActivePairLogDrift, Pi.add_apply, Pi.sub_apply]
    ring
  have he : (1 - 1 / 2 - pmAdjacentArtinConstant + 0) / 2 =
      1 / 4 - pmAdjacentArtinConstant / 2 := by ring
  simpa only [he] using ht

/-- Two local prime factors already give a strict positive lower bound for the drift slope. -/
theorem pmActivePairLogDrift_slope_pos :
    (1 : ℝ) / 24 ≤ 1 / 4 - pmAdjacentArtinConstant / 2 := by
  linarith [pmAdjacentArtinConstant_pos_le.2]

/-- Every sufficiently small positive damping has positive active-pair logarithmic drift. -/
theorem eventually_pmActivePairLogDrift_gt :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ε / 48 < pmActivePairLogDrift ε := by
  have hlt : (1 : ℝ) / 48 < 1 / 4 - pmAdjacentArtinConstant / 2 := by
    linarith [pmActivePairLogDrift_slope_pos]
  filter_upwards [self_mem_nhdsWithin,
    tendsto_pmActivePairLogDrift_div_parameter.eventually_const_lt hlt] with ε hε h
  have := (lt_div_iff₀ hε).mp h
  linarith

/-- The complete active pair diverges to positive infinity for every sufficiently small damping. -/
theorem eventually_tendsto_pmActivePair_atTop :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      Tendsto (fun N : ℕ =>
        pmActivePredictableMartingaleSum ε N + pmPredecessorPeakMartingaleSum ε N)
        atTop atTop := by
  filter_upwards [self_mem_nhdsWithin, eventually_pmActivePairLogDrift_gt] with ε hε hκ
  have hκ0 : 0 < pmActivePairLogDrift ε := lt_trans (div_pos hε (by norm_num)) hκ
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply ((tendsto_pmActivePair_div_log hε).pos_mul_atTop hκ0 hlog).congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog0 : Real.log N ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hN))
  exact div_mul_cancel₀ _ hlog0

/-- A damping-uniform upper bound fails already for each sufficiently small fixed damping. -/
theorem eventually_not_bounded_pmActivePair :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ¬ ∃ B : ℝ, ∀ N : ℕ,
        pmActivePredictableMartingaleSum ε N + pmPredecessorPeakMartingaleSum ε N ≤ B := by
  filter_upwards [eventually_tendsto_pmActivePair_atTop] with ε h
  rintro ⟨B, hB⟩
  obtain ⟨N, hN⟩ := (h.eventually_gt_atTop B).exists
  exact (not_lt_of_ge (hB N)) hN

/-- The shifted-difference sum in the uncentered active-pair upper bound is itself unbounded.
Thus bounding that reduction uniformly in the horizon cannot close the active-pair estimate. -/
theorem eventually_not_bounded_pmUncenteredShiftedDifference :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ¬ ∃ B : ℝ, ∀ N : ℕ,
        (∑ n ∈ Icc 1 (N - 1),
          (pmPowerDampedDivisorCoeff ε n * pmPowerDampedDivisorCoeff (1 + ε) n -
            pmPowerDampedDivisorCoeff (1 + ε) n * pmPowerDampedDivisorCoeff ε (n + 1)) *
            (1 / ((n : ℝ) + 1) - 1 / ((N : ℝ) + 1))) ≤ B := by
  filter_upwards [self_mem_nhdsWithin, eventually_tendsto_pmActivePair_atTop] with ε hε h
  rintro ⟨B, hB⟩
  obtain ⟨N, hN, hgt⟩ := ((eventually_ge_atTop 1).and
    (h.eventually_gt_atTop (1 / 8 + B / 2))).exists
  have hub := pmActive_add_pmPredecessorPeak_le_eighth_add_half_shifted_diff hε hN
  linarith [hB N]

/-- The precise logarithmic counterterm assigned to the doubly-inactive interior. -/
def pmInteriorLogCounterterm (ε : ℝ) : ℝ :=
  pmPowerDampedDivisorVariance ε / 2 + pmActivePairLogDrift ε

/-- Exact finite-horizon decomposition after subtracting the two known logarithmic drifts. -/
theorem pmPowerDampedDivisorDiscreteEnergy_eq_log_renormalized (ε : ℝ) (N : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy ε N =
      (pmPowerDampedDivisorCovarianceDiagonal ε N -
        pmPowerDampedDivisorVariance ε * Real.log N) +
      2 * (pmActivePredictableMartingaleSum ε N + pmPredecessorPeakMartingaleSum ε N -
        pmActivePairLogDrift ε * Real.log N) +
      2 * (pmBezoutInteriorMartingaleSum ε N + pmInteriorLogCounterterm ε * Real.log N) := by
  have hE := pmPowerDampedDivisorDiscreteEnergy_eq_diagonal_add_two_mul_pmPredictableMartingaleSum
    ε N
  have hP := (pmPredictableMartingaleSum_sub_pmBezoutInteriorMartingaleSum_eq ε N).1
  unfold pmInteriorLogCounterterm
  nlinarith

/-- Unconditionally, the renormalized interior agrees with half the complete energy to `o(log N)`.
This isolates an exact arithmetic cancellation target without assuming an energy bound. -/
theorem tendsto_pmInteriorLogCounterterm_energy_residual {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ =>
      (pmBezoutInteriorMartingaleSum ε N + pmInteriorLogCounterterm ε * Real.log N -
        pmPowerDampedDivisorDiscreteEnergy ε N / 2) / Real.log N)
      atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := pmInteriorLogCounterterm ε)).sub
    (((tendsto_pmPowerDampedDivisorCovarianceDiagonal_div_log hε).div_const (2 : ℝ)).add
      (tendsto_pmActivePair_div_log hε))
  have hz : Tendsto (fun N : ℕ => pmInteriorLogCounterterm ε -
      (pmPowerDampedDivisorCovarianceDiagonal ε N / Real.log N / 2 +
        (pmActivePredictableMartingaleSum ε N + pmPredecessorPeakMartingaleSum ε N) /
          Real.log N)) atTop (𝓝 0) := by
    simpa only [pmInteriorLogCounterterm, sub_self] using h
  apply hz.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog0 : Real.log N ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hN))
  have hE := pmPowerDampedDivisorDiscreteEnergy_eq_diagonal_add_two_mul_pmPredictableMartingaleSum
    ε N
  have hP := (pmPredictableMartingaleSum_sub_pmBezoutInteriorMartingaleSum_eq ε N).1
  field_simp
  nlinarith

/-- The interior cancellation coefficient has an exact arithmetic small-damping slope. -/
theorem tendsto_pmInteriorLogCounterterm_div_parameter :
    Tendsto (fun ε : ℝ => pmInteriorLogCounterterm ε / ε) (𝓝[>] 0)
      (𝓝 ((1 - pmAdjacentArtinConstant) / 2)) := by
  have h := (tendsto_pmPowerDampedDivisorVariance_div_parameter.div_const (2 : ℝ)).add
    tendsto_pmActivePairLogDrift_div_parameter
  have ht : Tendsto (fun ε : ℝ => pmInteriorLogCounterterm ε / ε) (𝓝[>] 0)
      (𝓝 (1 / 2 / 2 + (1 / 4 - pmAdjacentArtinConstant / 2))) := by
    apply h.congr
    intro ε
    dsimp only [pmInteriorLogCounterterm, Pi.add_apply]
    ring
  have he : 1 / 2 / 2 + (1 / 4 - pmAdjacentArtinConstant / 2) =
      (1 - pmAdjacentArtinConstant) / 2 := by ring
  simpa only [he] using ht

/-- The arithmetic interior budget strictly exceeds the diagonal-only coefficient `1/4`. -/
theorem pmInteriorLogCounterterm_slope_bounds :
    (7 : ℝ) / 24 ≤ (1 - pmAdjacentArtinConstant) / 2 ∧
      (1 - pmAdjacentArtinConstant) / 2 < 1 / 2 := by
  constructor <;> linarith [pmAdjacentArtinConstant_pos_le.1, pmAdjacentArtinConstant_pos_le.2]

end RHTower
