import GaloisForLFunctions.RHTower.XiHeatCassiniWoldConvergentLogHolonomy
import GaloisForLFunctions.RHTower.Sieve.MertensSecondExpRate
import GaloisForLFunctions.HTGeometry.LogLinearTailIntegral

/-!
# Exponential square-root-log damping of the Route-T Wold holonomy residual

The finite Euler-depletion correction has a quantitative tail of order `log N / N`, hence is
strictly smaller than the exponential square-root-log Mertens remainder.  Therefore the centered
Wold primitive inherits the Mertens remainder rate.  The result removes the last unquantified
arithmetic sequence from the centered Wold connection and exposes the remaining problem as an
explicit comparison with the timelike half-density profile variation.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The natural Euler-depletion correction is pointwise dominated by `3 log n / n²`. -/
theorem xiHeatCassiniWoldNatTraceCorrection_le_log_div_sq (n : ℕ) :
    xiHeatCassiniWoldNatTraceCorrection n ≤
      3 * (Real.log n / (n : ℝ) ^ (2 : ℕ)) := by
  by_cases hn : n.Prime
  · rw [xiHeatCassiniWoldNatTraceCorrection, dif_pos hn]
    exact xiHeatCassiniWoldEulerTraceCorrection_le ⟨n, hn⟩
  · rw [xiHeatCassiniWoldNatTraceCorrection, dif_neg hn]
    by_cases hn0 : n = 0
    · subst n
      norm_num
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      exact mul_nonneg (by norm_num)
        (div_nonneg (Real.log_nonneg (by exact_mod_cast hn1)) (sq_nonneg _))

/-- Quantitative tail of the positive Euler-depletion correction. -/
theorem xiHeatCassiniWoldNatTraceCorrectionMass_sub_sum_le
    {N : ℕ} (hN : 3 ≤ N) :
    xiHeatCassiniWoldNatTraceCorrectionMass -
        xiHeatCassiniWoldNatTraceCorrectionSum N ≤
      3 * ((Real.log N + 1) / N) := by
  have hsplit :=
    summable_xiHeatCassiniWoldNatTraceCorrection.sum_add_tsum_nat_add (N + 1)
  have htail :
      xiHeatCassiniWoldNatTraceCorrectionMass -
          xiHeatCassiniWoldNatTraceCorrectionSum N =
        ∑' i : ℕ, xiHeatCassiniWoldNatTraceCorrection (i + (N + 1)) := by
    rw [xiHeatCassiniWoldNatTraceCorrectionMass,
      xiHeatCassiniWoldNatTraceCorrectionSum,
      Sieve.Icc_zero_eq_range, ← hsplit]
    ring
  have hcorrectionShift :
      Summable (fun i : ℕ =>
        xiHeatCassiniWoldNatTraceCorrection (i + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).mpr
      summable_xiHeatCassiniWoldNatTraceCorrection
  have hlogShift :
      Summable (fun i : ℕ =>
        Real.log ((N : ℝ) + (i + 1)) /
          ((N : ℝ) + (i + 1)) ^ (2 : ℕ)) := by
    have h := (summable_nat_add_iff (N + 1)).mpr
      GaloisForLFunctions.HTGeometry.summable_logLin_div_sq
    refine h.congr ?_
    intro i
    congr 1 <;> push_cast <;> ring
  have hmajorShift :
      Summable (fun i : ℕ =>
        3 * (Real.log ((N : ℝ) + (i + 1)) /
          ((N : ℝ) + (i + 1)) ^ (2 : ℕ))) :=
    hlogShift.mul_left 3
  have hpoint : ∀ i : ℕ,
      xiHeatCassiniWoldNatTraceCorrection (i + (N + 1)) ≤
        3 * (Real.log ((N : ℝ) + (i + 1)) /
          ((N : ℝ) + (i + 1)) ^ (2 : ℕ)) := by
    intro i
    calc
      xiHeatCassiniWoldNatTraceCorrection (i + (N + 1)) ≤
          3 * (Real.log (((i + (N + 1) : ℕ) : ℝ)) /
            ((i + (N + 1) : ℕ) : ℝ) ^ (2 : ℕ)) :=
        xiHeatCassiniWoldNatTraceCorrection_le_log_div_sq _
      _ = 3 * (Real.log ((N : ℝ) + (i + 1)) /
          ((N : ℝ) + (i + 1)) ^ (2 : ℕ)) := by
        congr 2 <;> push_cast <;> ring
  have hsumMajor :
      (∑' i : ℕ, xiHeatCassiniWoldNatTraceCorrection (i + (N + 1))) ≤
        ∑' i : ℕ, 3 * (Real.log ((N : ℝ) + (i + 1)) /
          ((N : ℝ) + (i + 1)) ^ (2 : ℕ)) :=
    Summable.tsum_le_tsum hpoint hcorrectionShift hmajorShift
  have hExp : Real.exp 1 ≤ (N : ℝ) := by
    have he : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlogTail :=
    GaloisForLFunctions.HTGeometry.tsum_logLin_div_sq_le hExp
  rw [tsum_mul_left] at hsumMajor
  rw [htail]
  exact hsumMajor.trans
    (mul_le_mul_of_nonneg_left hlogTail (by norm_num))

/-- An exponential-rate estimate forces convergence to its displayed center. -/
theorem tendsto_sieve_mertensA_sub_log_of_exp_rate
    {c₁ B c : ℝ} (hc : 0 < c)
    (hrate : ∀ᶠ N : ℕ in atTop,
      |Sieve.mertensA N - Real.log N - c₁| ≤
        B * Real.exp (-c * Real.sqrt (Real.log N))) :
    Tendsto (fun N : ℕ => Sieve.mertensA N - Real.log N) atTop (𝓝 c₁) := by
  have hsqrtLog :
      Tendsto (fun N : ℕ => Real.sqrt (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hscaled :
      Tendsto (fun N : ℕ => c * Real.sqrt (Real.log (N : ℝ))) atTop atTop :=
    hsqrtLog.const_mul_atTop hc
  have hnegative :
      Tendsto (fun N : ℕ => -(c * Real.sqrt (Real.log (N : ℝ)))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hscaled
  have hexp :
      Tendsto (fun N : ℕ =>
        Real.exp (-(c * Real.sqrt (Real.log (N : ℝ))))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hnegative
  have hmajor :
      Tendsto (fun N : ℕ =>
        B * Real.exp (-c * Real.sqrt (Real.log N))) atTop (𝓝 0) := by
    have h := hexp.const_mul B
    rw [mul_zero] at h
    apply h.congr'
    filter_upwards with N
    congr 2
    ring
  have hnorm :
      Tendsto (fun N : ℕ => ‖Sieve.mertensA N - Real.log N - c₁‖)
        atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun N => norm_nonneg _
    · simpa only [Real.norm_eq_abs] using hrate
    · exact hmajor
  have hzero :
      Tendsto (fun N : ℕ => Sieve.mertensA N - Real.log N - c₁)
        atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hsum := (tendsto_const_nhds (x := c₁)).add hzero
  rw [add_zero] at hsum
  apply hsum.congr'
  filter_upwards with N
  ring

/-- The selected Mertens constant inherits the unconditional exponential square-root-log rate. -/
theorem exists_canonical_sieve_mertensA_sub_log_exp_rate :
    ∃ (B c : ℝ), 0 < c ∧ 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      |Sieve.mertensA N - Real.log N - xiHeatCassiniMertensLogConstant| ≤
        B * Real.exp (-c * Real.sqrt (Real.log N)) := by
  obtain ⟨c₁, B, c, hc, hB, hrate⟩ :=
    Sieve.exists_mertensA_sub_log_exp_rate
  have hrateNat : ∀ᶠ N : ℕ in atTop,
      |Sieve.mertensA N - Real.log N - c₁| ≤
        B * Real.exp (-c * Real.sqrt (Real.log N)) := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hrate
    filter_upwards [h] with N hN
    rwa [Nat.floor_natCast] at hN
  have hc₁ : c₁ = xiHeatCassiniMertensLogConstant :=
    tendsto_nhds_unique
      (tendsto_sieve_mertensA_sub_log_of_exp_rate hc hrateNat)
      tendsto_sieve_mertensA_sub_log
  subst c₁
  exact ⟨B, c, hc, hB, hrateNat⟩

/-- The Euler-depletion tail is smaller than every fixed exponential square-root-log shape. -/
theorem eventually_xiHeatCassiniWoldNatTraceCorrection_tail_le_exp
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      xiHeatCassiniWoldNatTraceCorrectionMass -
          xiHeatCassiniWoldNatTraceCorrectionSum N ≤
        6 * Real.exp (-c * Real.sqrt (Real.log N)) := by
  have hshape := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Sieve.sqrt_mul_log_le_shape hc)
  have hone := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Sieve.one_div_le_exp_neg_sqrt_log hc)
  filter_upwards [eventually_ge_atTop 3, hshape, hone] with N hN hshapeN honeN
  have htail := xiHeatCassiniWoldNatTraceCorrectionMass_sub_sum_le hN
  have hNreal : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hNone : (1 : ℝ) ≤ N := by linarith
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNone
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.mpr hNone
  let E : ℝ := Real.exp (-c * Real.sqrt (Real.log N))
  have hlogLe : Real.log (N : ℝ) ≤ (N : ℝ) * E := by
    have haux : 2 * Real.log (N : ℝ) ≤
        2 * Real.sqrt N * Real.log N := by nlinarith
    dsimp only [E]
    linarith
  have hlogDiv : Real.log (N : ℝ) / N ≤ E := by
    rw [div_le_iff₀ hNpos]
    simpa [mul_comm] using hlogLe
  have honeDiv : (1 : ℝ) / N ≤ E := by
    simpa only [E] using honeN
  have hshapeTail : (Real.log (N : ℝ) + 1) / N ≤ 2 * E := by
    calc
      (Real.log (N : ℝ) + 1) / N =
          Real.log (N : ℝ) / N + 1 / N := by field_simp
      _ ≤ E + E := add_le_add hlogDiv honeDiv
      _ = 2 * E := by ring
  calc
    xiHeatCassiniWoldNatTraceCorrectionMass -
          xiHeatCassiniWoldNatTraceCorrectionSum N ≤
        3 * ((Real.log N + 1) / N) := htail
    _ ≤ 3 * (2 * E) := mul_le_mul_of_nonneg_left hshapeTail (by norm_num)
    _ = 6 * Real.exp (-c * Real.sqrt (Real.log N)) := by
      dsimp only [E]
      ring

/-- Centered natural-cutoff Wold primitive. -/
def xiHeatCassiniWoldNatResidualLogDiscrepancy (N : ℕ) : ℝ :=
  xiHeatCassiniWoldNatWeightSum N - Real.log N -
    xiHeatCassiniWoldLogHolonomyConstant

/-- **Quantitative Wold holonomy damping.**  The natural residual inherits the Mertens rate. -/
theorem exists_xiHeatCassiniWoldNatResidualLogDiscrepancy_exp_rate :
    ∃ (B c : ℝ), 0 < c ∧ 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniWoldNatResidualLogDiscrepancy N| ≤
        B * Real.exp (-c * Real.sqrt (Real.log N)) := by
  obtain ⟨B, c, hc, hB, hMertens⟩ :=
    exists_canonical_sieve_mertensA_sub_log_exp_rate
  have htrace := eventually_xiHeatCassiniWoldNatTraceCorrection_tail_le_exp hc
  refine ⟨B + 6, c, hc, by positivity, ?_⟩
  filter_upwards [hMertens, htrace] with N hMertensN htraceN
  have htrace0 : 0 ≤
      xiHeatCassiniWoldNatTraceCorrectionMass -
        xiHeatCassiniWoldNatTraceCorrectionSum N :=
    sub_nonneg.mpr (xiHeatCassiniWoldNatTraceCorrectionSum_le_mass N)
  have hsplit :
      xiHeatCassiniWoldNatResidualLogDiscrepancy N =
        (Sieve.mertensA N - Real.log N - xiHeatCassiniMertensLogConstant) +
        (xiHeatCassiniWoldNatTraceCorrectionMass -
          xiHeatCassiniWoldNatTraceCorrectionSum N) := by
    rw [xiHeatCassiniWoldNatResidualLogDiscrepancy,
      xiHeatCassiniWoldLogHolonomyConstant,
      ← mertensPrimeWeightSum_eq_sieve_mertensA,
      mertensPrimeWeightSum_eq_wold_add_traceCorrection]
    ring
  rw [hsplit]
  calc
    |(Sieve.mertensA N - Real.log N - xiHeatCassiniMertensLogConstant) +
        (xiHeatCassiniWoldNatTraceCorrectionMass -
          xiHeatCassiniWoldNatTraceCorrectionSum N)| ≤
      |Sieve.mertensA N - Real.log N - xiHeatCassiniMertensLogConstant| +
        |xiHeatCassiniWoldNatTraceCorrectionMass -
          xiHeatCassiniWoldNatTraceCorrectionSum N| := abs_add_le _ _
    _ = |Sieve.mertensA N - Real.log N - xiHeatCassiniMertensLogConstant| +
        (xiHeatCassiniWoldNatTraceCorrectionMass -
          xiHeatCassiniWoldNatTraceCorrectionSum N) := by
      rw [abs_of_nonneg htrace0]
    _ ≤ B * Real.exp (-c * Real.sqrt (Real.log N)) +
        6 * Real.exp (-c * Real.sqrt (Real.log N)) :=
      add_le_add hMertensN htraceN
    _ = (B + 6) * Real.exp (-c * Real.sqrt (Real.log N)) := by ring

/-- Ordered-prime Wold residual has the same exponential square-root-log damping. -/
theorem exists_xiHeatCassiniOrderedWoldResidualLogDiscrepancy_exp_rate :
    ∃ (B c : ℝ), 0 < c ∧ 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        B * Real.exp (-c * Real.sqrt (Real.log (nthPrimeSubtype N : ℝ))) := by
  obtain ⟨B, c, hc, hB, hrate⟩ :=
    exists_xiHeatCassiniWoldNatResidualLogDiscrepancy_exp_rate
  refine ⟨B, c, hc, hB, ?_⟩
  have h := nthPrimeSubtype_strictMono.tendsto_atTop.eventually hrate
  filter_upwards [h] with N hN
  simpa only [xiHeatCassiniWoldNatResidualLogDiscrepancy,
    xiHeatCassiniOrderedWoldResidualLogDiscrepancy,
    xiHeatCassiniOrderedWoldLogDiscrepancy,
    xiHeatCassiniOrderedWoldPartialMass_eq_natWeightSum,
    xiMassNthPrimeLogHeight] using hN

/-- Quantitative arithmetic factor in every centered Wold connection atom. -/
theorem exists_norm_xiHeatCassiniOrderedWoldResidualConnectionAtom_exp_rate :
    ∃ (B c : ℝ), 0 < c ∧ 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      ‖xiHeatCassiniOrderedWoldResidualConnectionAtom a τ N‖ ≤
        B * Real.exp (-c * Real.sqrt (Real.log (nthPrimeSubtype N : ℝ))) *
          ‖xiHeatCassiniOrderedPrimeHalfDensityProfile a τ N -
            xiHeatCassiniOrderedPrimeHalfDensityProfile a τ (N + 1)‖ := by
  obtain ⟨B, c, hc, hB, hrate⟩ :=
    exists_xiHeatCassiniOrderedWoldResidualLogDiscrepancy_exp_rate
  refine ⟨B, c, hc, hB, ?_⟩
  filter_upwards [hrate] with N hN
  rw [xiHeatCassiniOrderedWoldResidualConnectionAtom, norm_mul,
    Complex.norm_real]
  exact mul_le_mul_of_nonneg_right hN (norm_nonneg _)

end

end RHTower
