import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualBorelTerminalWidthBound

/-!
# Exact Wold Borel terminal-height spectrum

For every transverse width `0 ≤ alpha < 1/2`, this module proves the exact phase law

`XiZeroHalfPlaneBound alpha ↔ WoldResidualBorelTerminalSpectrum alpha`.

The forward transport is arithmetic and quantitative: generalized von Koch gives the Chebyshev
spectrum, prime-power correction gives theta, Abel summation gives centered weighted-Mertens
decay, Euler trace correction gives the natural Wold rate, and ordered-prime sampling gives every
terminal height strictly below `1/2-alpha`.

The reverse transport uses all strict terminal heights cofinally. Each chosen height gives a
slightly wider Chebyshev spectrum; choosing the height as a function of the requested epsilon
recovers the exact endpoint width. Thus no decay assumption at the boundary itself is used.

All results are unconditional. The specialization `alpha = 0` is an RH classification.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A Chebyshev error spectrum of width `alpha` transfers to the prime-only theta error at every
strictly larger exponent. -/
theorem exists_chebyshevTheta_error_power_bound_of_chebyshevErrorPowerSpectrum
    {alpha delta : ℝ} (halpha : 0 ≤ alpha) (hdelta : 0 < delta)
    (hspectrum : ChebyshevErrorPowerSpectrum alpha) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      |Chebyshev.theta t - t| ≤ C * t ^ (1 / 2 + alpha + delta) := by
  obtain ⟨C, hC, hpsi⟩ := hspectrum (delta / 2) (by linarith)
  refine ⟨C + 4 / delta, by positivity, ?_⟩
  intro t ht
  have ht0 : 0 < t := by linarith
  have hpsi' : |Chebyshev.psi t - t| ≤
      C * t ^ (1 / 2 + alpha + delta / 2) := by
    rw [← chebyshevPsiReal_eq_psi,
      ← criticalMellinError_vonMangoldt_eq_chebyshevPsiReal_sub]
    exact hpsi t ht
  have hprimePower := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log ht
  have hlog := Mertens.log_le_rpow ht0 (show 0 < delta / 2 by linarith)
  have hsqrt0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hcorr :
      2 * Real.sqrt t * Real.log t ≤
        (4 / delta) * t ^ (1 / 2 + delta / 2) := by
    have hfactor : 0 ≤ 2 * Real.sqrt t := mul_nonneg (by norm_num) hsqrt0
    have hmul := mul_le_mul_of_nonneg_left hlog hfactor
    calc
      2 * Real.sqrt t * Real.log t ≤
          2 * Real.sqrt t * ((1 / (delta / 2)) * t ^ (delta / 2)) := hmul
      _ = (4 / delta) * t ^ (1 / 2 + delta / 2) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_add ht0]
        field_simp
        ring
  have htri : |Chebyshev.theta t - t| ≤
      |Chebyshev.psi t - t| + |Chebyshev.psi t - Chebyshev.theta t| := by
    calc
      |Chebyshev.theta t - t| =
          |(Chebyshev.psi t - t) -
            (Chebyshev.psi t - Chebyshev.theta t)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  have hpsiPow : t ^ (1 / 2 + alpha + delta / 2) ≤
      t ^ (1 / 2 + alpha + delta) :=
    Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have hcorrPow : t ^ (1 / 2 + delta / 2) ≤
      t ^ (1 / 2 + alpha + delta) :=
    Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  calc
    |Chebyshev.theta t - t| ≤
        |Chebyshev.psi t - t| + |Chebyshev.psi t - Chebyshev.theta t| := htri
    _ ≤ C * t ^ (1 / 2 + alpha + delta / 2) +
        (4 / delta) * t ^ (1 / 2 + delta / 2) :=
      add_le_add hpsi' (hprimePower.trans hcorr)
    _ ≤ C * t ^ (1 / 2 + alpha + delta) +
        (4 / delta) * t ^ (1 / 2 + alpha + delta) :=
      add_le_add (mul_le_mul_of_nonneg_left hpsiPow hC)
        (mul_le_mul_of_nonneg_left hcorrPow (by positivity))
    _ = (C + 4 / delta) * t ^ (1 / 2 + alpha + delta) := by ring

private theorem integrableOn_thetaErrorDensity_Ioi_two :
    IntegrableOn Sieve.thetaErrorDensity (Ioi (2 : ℝ)) := by
  obtain ⟨c, hc, hbigO⟩ := Sieve.chebyshevTheta_sub_id_isBigO
  rw [Asymptotics.isBigO_iff] at hbigO
  obtain ⟨K, hKev⟩ := hbigO
  rw [eventually_atTop] at hKev
  obtain ⟨T₀, hT₀⟩ := hKev
  let T : ℝ := max T₀ 2
  have hT2 : (2 : ℝ) ≤ T := le_max_right _ _
  have hbd : ∀ t : ℝ, T < t →
      |Chebyshev.theta t - t| ≤
        |K| * t * Real.exp (-c * Real.sqrt (Real.log t)) := by
    intro t ht
    have ht0 : 0 < t := by
      have : (2 : ℝ) < t := lt_of_le_of_lt hT2 ht
      linarith
    have h := hT₀ t (le_trans (le_max_left _ _) ht.le)
    have hshape :
        ‖t * Real.exp (-c * Real.sqrt (Real.log t))‖ =
          t * Real.exp (-c * Real.sqrt (Real.log t)) := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [Pi.sub_apply, id_eq, Real.norm_eq_abs, hshape] at h
    have hE : 0 < Real.exp (-c * Real.sqrt (Real.log t)) := Real.exp_pos _
    nlinarith [le_abs_self K, h, mul_pos ht0 hE]
  exact Sieve.integrableOn_thetaErrorDensity_Ioi hc hT2 hbd

/-- A strict sublinear theta exponent gives the complementary weighted-Mertens power saving. -/
theorem exists_mertensA_sub_log_integralConstant_power_rate_of_theta_bound
    {C eps : ℝ} (hC : 0 < C) (heps0 : 0 < eps) (hepsHalf : eps < 1 / 2)
    (htheta : ∀ t : ℝ, 1 ≤ t →
      |Chebyshev.theta t - t| ≤ C * t ^ (1 / 2 + eps)) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, 2 ≤ x →
      |Sieve.mertensA ⌊x⌋₊ - Real.log x -
        (1 - Real.log 2 +
          ∫ t in Ioi (2 : ℝ), Sieve.thetaErrorDensity t)| ≤
        B * x ^ (-(1 / 2 - eps)) := by
  refine ⟨C + C / (1 / 2 - eps), by positivity, ?_⟩
  intro x hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hInt := integrableOn_thetaErrorDensity_Ioi_two
  have hIoc : IntegrableOn Sieve.thetaErrorDensity (Ioc 2 x) :=
    hInt.mono_set Ioc_subset_Ioi_self
  have hIoi : IntegrableOn Sieve.thetaErrorDensity (Ioi x) :=
    hInt.mono_set (Ioi_subset_Ioi hx)
  have hdisj : Disjoint (Ioc (2 : ℝ) x) (Ioi x) :=
    Set.disjoint_left.mpr fun t ht ht' => absurd ht' (not_lt.mpr ht.2)
  have hsplit : ∫ t in Ioi (2 : ℝ), Sieve.thetaErrorDensity t =
      (∫ t in Ioc 2 x, Sieve.thetaErrorDensity t) +
        ∫ t in Ioi x, Sieve.thetaErrorDensity t := by
    rw [← Ioc_union_Ioi_eq_Ioi hx,
      setIntegral_union hdisj measurableSet_Ioi hIoc hIoi]
  have hid : Sieve.mertensA ⌊x⌋₊ - Real.log x -
        (1 - Real.log 2 +
          ∫ t in Ioi (2 : ℝ), Sieve.thetaErrorDensity t) =
      (Chebyshev.theta x - x) / x -
        ∫ t in Ioi x, Sieve.thetaErrorDensity t := by
    rw [Sieve.mertensA_eq_theta_div_add_setIntegral hx,
      Sieve.setIntegral_theta_div_sq hx, hsplit]
    have hdiv : Chebyshev.theta x / x =
        1 + (Chebyshev.theta x - x) / x := by
      field_simp
      ring
    rw [hdiv]
    ring
  rw [hid]
  have hb1 : |(Chebyshev.theta x - x) / x| ≤
      C * x ^ (-(1 / 2 - eps)) := by
    rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
    calc
      |Chebyshev.theta x - x| ≤ C * x ^ (1 / 2 + eps) := htheta x hx1
      _ = C * x ^ (-(1 / 2 - eps)) * x := by
        symm
        calc
          C * x ^ (-(1 / 2 - eps)) * x =
              C * (x ^ (-(1 / 2 - eps)) * x ^ (1 : ℝ)) := by
            simp only [Real.rpow_one]
            ring
          _ = C * x ^ (-(1 / 2 - eps) + 1) := by rw [Real.rpow_add hx0]
          _ = C * x ^ (1 / 2 + eps) := by congr 2; ring
  have hb2 : |∫ t in Ioi x, Sieve.thetaErrorDensity t| ≤
      C * (x ^ (-(1 / 2 - eps)) / (1 / 2 - eps)) :=
    abs_setIntegral_thetaErrorDensity_Ioi_le_of_power_bound
      heps0 hepsHalf hx1 htheta
  calc
    |(Chebyshev.theta x - x) / x -
        ∫ t in Ioi x, Sieve.thetaErrorDensity t| ≤
      |(Chebyshev.theta x - x) / x| +
        |∫ t in Ioi x, Sieve.thetaErrorDensity t| := abs_sub _ _
    _ ≤ C * x ^ (-(1 / 2 - eps)) +
        C * (x ^ (-(1 / 2 - eps)) / (1 / 2 - eps)) :=
      add_le_add hb1 hb2
    _ = (C + C / (1 / 2 - eps)) * x ^ (-(1 / 2 - eps)) := by
      field_simp

private theorem tendsto_real_rpow_neg_atTop_zero
    {u : ℝ} (hu : 0 < u) :
    Tendsto (fun x : ℝ => x ^ (-u)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun x : ℝ => x ^ u) atTop atTop :=
    tendsto_rpow_atTop hu
  have hinv : Tendsto (fun x : ℝ => (x ^ u)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow
  refine hinv.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_neg hx.le]

/-- Canonical-center form of the weighted-Mertens rate from an arbitrary strict theta exponent. -/
theorem exists_mertensA_sub_log_power_rate_of_theta_bound
    {C eps : ℝ} (hC : 0 < C) (heps0 : 0 < eps) (hepsHalf : eps < 1 / 2)
    (htheta : ∀ t : ℝ, 1 ≤ t →
      |Chebyshev.theta t - t| ≤ C * t ^ (1 / 2 + eps)) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      |Sieve.mertensA N - Real.log N - xiHeatCassiniMertensLogConstant| ≤
        B * (N : ℝ) ^ (-(1 / 2 - eps)) := by
  obtain ⟨B, hB, hreal⟩ :=
    exists_mertensA_sub_log_integralConstant_power_rate_of_theta_bound
      hC heps0 hepsHalf htheta
  let cInt : ℝ := 1 - Real.log 2 +
    ∫ t in Ioi (2 : ℝ), Sieve.thetaErrorDensity t
  have hrateInt : ∀ᶠ N : ℕ in atTop,
      |Sieve.mertensA N - Real.log N - cInt| ≤
        B * (N : ℝ) ^ (-(1 / 2 - eps)) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
    simpa only [cInt, Nat.floor_natCast] using hreal (N : ℝ) hNreal
  have hdecayReal :
      Tendsto (fun x : ℝ => x ^ (-(1 / 2 - eps))) atTop (𝓝 0) :=
    tendsto_real_rpow_neg_atTop_zero (by linarith)
  have hdecayNat :
      Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 2 - eps))) atTop (𝓝 0) :=
    hdecayReal.comp tendsto_natCast_atTop_atTop
  have hmajor :
      Tendsto (fun N : ℕ => B * (N : ℝ) ^ (-(1 / 2 - eps)))
        atTop (𝓝 0) := by
    simpa using hdecayNat.const_mul B
  have hnorm :
      Tendsto (fun N : ℕ => ‖Sieve.mertensA N - Real.log N - cInt‖)
        atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun N => norm_nonneg _
    · simpa only [Real.norm_eq_abs] using hrateInt
    · exact hmajor
  have hzero :
      Tendsto (fun N : ℕ => Sieve.mertensA N - Real.log N - cInt)
        atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hcenter :
      Tendsto (fun N : ℕ => Sieve.mertensA N - Real.log N)
        atTop (𝓝 cInt) := by
    have hsum := (tendsto_const_nhds (x := cInt)).add hzero
    simpa only [add_zero] using hsum.congr' (by
      filter_upwards with N
      ring)
  have hcInt : cInt = xiHeatCassiniMertensLogConstant :=
    tendsto_nhds_unique hcenter tendsto_sieve_mertensA_sub_log
  refine ⟨B, hB, ?_⟩
  simpa only [hcInt] using hrateInt

/-- Every strict exponent above a Chebyshev width gives the complementary canonical Mertens
power saving. -/
theorem exists_mertensA_sub_log_power_rate_of_chebyshevErrorPowerSpectrum
    {alpha delta : ℝ} (halpha : 0 ≤ alpha) (hdelta : 0 < delta)
    (hsubhalf : alpha + delta < 1 / 2)
    (hspectrum : ChebyshevErrorPowerSpectrum alpha) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      |Sieve.mertensA N - Real.log N - xiHeatCassiniMertensLogConstant| ≤
        B * (N : ℝ) ^ (-(1 / 2 - (alpha + delta))) := by
  obtain ⟨C, hC, htheta⟩ :=
    exists_chebyshevTheta_error_power_bound_of_chebyshevErrorPowerSpectrum
      halpha hdelta hspectrum
  apply exists_mertensA_sub_log_power_rate_of_theta_bound
    hC (by linarith) hsubhalf
  simpa only [show (1 : ℝ) / 2 + alpha + delta =
      1 / 2 + (alpha + delta) by ring] using htheta

/-- Chebyshev width gives every natural-cutoff Wold decay rate strictly below its complementary
terminal height. -/
theorem exists_woldNatResidual_power_rate_of_chebyshevErrorPowerSpectrum
    {alpha delta : ℝ} (halpha : 0 ≤ alpha) (hdelta : 0 < delta)
    (hsubhalf : alpha + delta < 1 / 2)
    (hspectrum : ChebyshevErrorPowerSpectrum alpha) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniWoldNatResidualLogDiscrepancy N| ≤
        B * (N : ℝ) ^ (-(1 / 2 - (alpha + delta))) := by
  obtain ⟨B, hB, hMertens⟩ :=
    exists_mertensA_sub_log_power_rate_of_chebyshevErrorPowerSpectrum
      halpha hdelta hsubhalf hspectrum
  let eps : ℝ := alpha + delta
  let D : ℝ := 3 * (1 / (1 / 2 + eps) + 1)
  have heps0 : 0 < eps := by dsimp only [eps]; linarith
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨B + D, by positivity, ?_⟩
  filter_upwards [hMertens,
    eventually_woldNatTraceCorrection_tail_le_power heps0] with N hMN htraceN
  have htrace0 : 0 ≤
      xiHeatCassiniWoldNatTraceCorrectionMass -
        xiHeatCassiniWoldNatTraceCorrectionSum N :=
    sub_nonneg.mpr (xiHeatCassiniWoldNatTraceCorrectionSum_le_mass N)
  have hsplit : xiHeatCassiniWoldNatResidualLogDiscrepancy N =
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
    _ ≤ B * (N : ℝ) ^ (-(1 / 2 - (alpha + delta))) +
        D * (N : ℝ) ^ (-(1 / 2 - (alpha + delta))) := by
      exact add_le_add hMN (by simpa only [D, eps] using htraceN)
    _ = (B + D) * (N : ℝ) ^ (-(1 / 2 - (alpha + delta))) := by ring

/-- Ordered-prime Wold residual inherits every strict complementary rate from a Chebyshev
spectrum. -/
theorem exists_orderedWoldResidual_exp_height_rate_of_chebyshevErrorPowerSpectrum
    {alpha delta : ℝ} (halpha : 0 ≤ alpha) (hdelta : 0 < delta)
    (hsubhalf : alpha + delta < 1 / 2)
    (hspectrum : ChebyshevErrorPowerSpectrum alpha) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        B * Real.exp (-(1 / 2 - (alpha + delta)) *
          xiMassNthPrimeLogHeight N) := by
  obtain ⟨B, hB, hrate⟩ :=
    exists_woldNatResidual_power_rate_of_chebyshevErrorPowerSpectrum
      halpha hdelta hsubhalf hspectrum
  refine ⟨B, hB, ?_⟩
  have h := nthPrimeSubtype_strictMono.tendsto_atTop.eventually hrate
  filter_upwards [h] with N hN
  have hp0 : (0 : ℝ) < nthPrimeSubtype N := nthPrimeSubtype_pos N
  have hres : xiHeatCassiniOrderedWoldResidualLogDiscrepancy N =
      xiHeatCassiniWoldNatResidualLogDiscrepancy (nthPrimeSubtype N) := by
    simp only [xiHeatCassiniWoldNatResidualLogDiscrepancy,
      xiHeatCassiniOrderedWoldResidualLogDiscrepancy,
      xiHeatCassiniOrderedWoldLogDiscrepancy,
      xiHeatCassiniOrderedWoldPartialMass_eq_natWeightSum,
      xiMassNthPrimeLogHeight]
  rw [hres]
  calc
    |xiHeatCassiniWoldNatResidualLogDiscrepancy (nthPrimeSubtype N)| ≤
        B * (nthPrimeSubtype N : ℝ) ^
          (-(1 / 2 - (alpha + delta))) := hN
    _ = B * Real.exp (-(1 / 2 - (alpha + delta)) *
        xiMassNthPrimeLogHeight N) := by
      rw [Real.rpow_def_of_pos hp0]
      unfold xiMassNthPrimeLogHeight
      congr 2
      ring

/-- A Chebyshev width makes the exact Borel terminal vanish at every positive height strictly
below its complementary frontier. -/
theorem tendsto_woldResidualBorelTerminalWeight_zero_of_chebyshevErrorPowerSpectrum
    {alpha y : ℝ} (halpha : 0 ≤ alpha) (hy0 : 0 < y)
    (hyFrontier : y < 1 / 2 - alpha)
    (hspectrum : ChebyshevErrorPowerSpectrum alpha) :
    Tendsto (fun N : ℕ =>
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        Real.exp (y * xiMassNthPrimeLogHeight N)) atTop (𝓝 0) := by
  let delta : ℝ := (1 / 2 - alpha - y) / 2
  let eps : ℝ := alpha + delta
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  have hepsHalf : eps < 1 / 2 := by dsimp only [eps, delta]; linarith
  obtain ⟨B, hB, hrate⟩ :=
    exists_orderedWoldResidual_exp_height_rate_of_chebyshevErrorPowerSpectrum
      halpha hdelta hepsHalf hspectrum
  let d : ℝ := (1 / 2 - eps) - y
  have hd : 0 < d := by dsimp only [d, eps, delta]; linarith
  have hheight := tendsto_xiMassNthPrimeLogHeight_atTop
  have hscaled : Tendsto (fun N : ℕ =>
      d * xiMassNthPrimeLogHeight N) atTop atTop :=
    hheight.const_mul_atTop hd
  have hneg : Tendsto (fun N : ℕ =>
      -(d * xiMassNthPrimeLogHeight N)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hscaled
  have hexp : Tendsto (fun N : ℕ =>
      Real.exp (-(d * xiMassNthPrimeLogHeight N))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hmajor : Tendsto (fun N : ℕ =>
      B * Real.exp (-(d * xiMassNthPrimeLogHeight N))) atTop (𝓝 0) := by
    simpa using hexp.const_mul B
  apply squeeze_zero'
  · exact Eventually.of_forall fun N =>
      mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
  · filter_upwards [hrate] with N hN
    have hexp0 : 0 ≤ Real.exp (y * xiMassNthPrimeLogHeight N) :=
      Real.exp_nonneg _
    calc
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
          Real.exp (y * xiMassNthPrimeLogHeight N) ≤
        (B * Real.exp (-(1 / 2 - (alpha + delta)) *
          xiMassNthPrimeLogHeight N)) *
          Real.exp (y * xiMassNthPrimeLogHeight N) :=
        mul_le_mul_of_nonneg_right hN hexp0
      _ = B * Real.exp (-(d * xiMassNthPrimeLogHeight N)) := by
        calc
          (B * Real.exp (-(1 / 2 - (alpha + delta)) *
              xiMassNthPrimeLogHeight N)) *
              Real.exp (y * xiMassNthPrimeLogHeight N) =
            B * (Real.exp (-(1 / 2 - (alpha + delta)) *
                xiMassNthPrimeLogHeight N) *
              Real.exp (y * xiMassNthPrimeLogHeight N)) := by ring
          _ = B * Real.exp (-(1 / 2 - (alpha + delta)) *
                xiMassNthPrimeLogHeight N +
              y * xiMassNthPrimeLogHeight N) := by rw [Real.exp_add]
          _ = B * Real.exp (-(d * xiMassNthPrimeLogHeight N)) := by
            congr 2
            dsimp only [d, eps]
            ring
  · exact hmajor

/-- Exact positive terminal-height spectrum complementary to a transverse Xi width. -/
def WoldResidualBorelTerminalSpectrum (alpha : ℝ) : Prop :=
  ∀ y : ℝ, 0 < y → y < 1 / 2 - alpha →
    Tendsto (fun N : ℕ =>
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        Real.exp (y * xiMassNthPrimeLogHeight N)) atTop (𝓝 0)

/-- A Chebyshev error spectrum supplies its complete complementary terminal-height spectrum. -/
theorem woldResidualBorelTerminalSpectrum_of_chebyshevErrorPowerSpectrum
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hspectrum : ChebyshevErrorPowerSpectrum alpha) :
    WoldResidualBorelTerminalSpectrum alpha := by
  intro y hy0 hyFrontier
  exact tendsto_woldResidualBorelTerminalWeight_zero_of_chebyshevErrorPowerSpectrum
    halpha hy0 hyFrontier hspectrum

/-- Cofinal decay at every strict complementary terminal height recovers the Chebyshev spectrum
at the exact endpoint width. -/
theorem chebyshevErrorPowerSpectrum_of_woldResidualBorelTerminalSpectrum
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halphaHalf : alpha < 1 / 2)
    (hterminal : WoldResidualBorelTerminalSpectrum alpha) :
    ChebyshevErrorPowerSpectrum alpha := by
  intro epsilon hepsilon
  let eta : ℝ := min (epsilon / 2) ((1 / 2 - alpha) / 2)
  let c : ℝ := 1 / 2 - alpha - eta
  have heta0 : 0 < eta := by
    dsimp only [eta]
    exact lt_min (by linarith) (by linarith)
  have hetaEpsilon : eta ≤ epsilon / 2 := by
    dsimp only [eta]
    exact min_le_left _ _
  have hetaFrontier : eta ≤ (1 / 2 - alpha) / 2 := by
    dsimp only [eta]
    exact min_le_right _ _
  have hc0 : 0 < c := by dsimp only [c]; linarith
  have hcHalf : c < 1 / 2 := by dsimp only [c]; linarith
  have hcFrontier : c < 1 / 2 - alpha := by dsimp only [c]; linarith
  have hterminalC := hterminal c hc0 hcFrontier
  have hspectrumC :=
    chebyshevErrorPowerSpectrum_of_woldResidualBorelTerminalWeight
      hc0 hcHalf hterminalC
  obtain ⟨C, hC, hbound⟩ := hspectrumC (epsilon / 2) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hb := hbound x hx
  have hpow : x ^ (1 / 2 + (1 / 2 - c) + epsilon / 2) ≤
      x ^ (1 / 2 + alpha + epsilon) := by
    apply Real.rpow_le_rpow_of_exponent_le hx
    dsimp only [c]
    linarith
  exact hb.trans (mul_le_mul_of_nonneg_left hpow hC)

/-- Exact all-width law: Xi zeros have transverse width at most `alpha` exactly when the ordered
Wold Borel terminal vanishes at every positive height below `1/2-alpha`. -/
theorem xiZeroHalfPlaneBound_iff_woldResidualBorelTerminalSpectrum
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halphaHalf : alpha < 1 / 2) :
    XiZeroHalfPlaneBound alpha ↔ WoldResidualBorelTerminalSpectrum alpha := by
  constructor
  · intro hXi
    exact woldResidualBorelTerminalSpectrum_of_chebyshevErrorPowerSpectrum halpha
      (chebyshevErrorPowerSpectrum_of_xiZeroHalfPlaneBound halpha hXi)
  · intro hterminal
    exact xiZeroHalfPlaneBound_of_chebyshevErrorPowerSpectrum halpha
      (chebyshevErrorPowerSpectrum_of_woldResidualBorelTerminalSpectrum
        halpha halphaHalf hterminal)

/-- Zero width specializes the all-width law to an unconditional RH classification. -/
theorem riemannHypothesis_iff_woldResidualBorelTerminalSpectrum_zero :
    RiemannHypothesis ↔ WoldResidualBorelTerminalSpectrum 0 := by
  rw [← xiZeroHalfPlaneBound_zero_iff_rh]
  exact xiZeroHalfPlaneBound_iff_woldResidualBorelTerminalSpectrum (by norm_num) (by norm_num)

end
end RHTower

