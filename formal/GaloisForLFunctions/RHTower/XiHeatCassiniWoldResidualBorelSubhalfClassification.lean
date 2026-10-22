import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualBorelStokesCharge
import GaloisForLFunctions.RHTower.Sieve.ChebyshevErrorPowerBound
import GaloisForLFunctions.HTGeometry.PowerTailBochnerBound
import GaloisForLFunctions.RHTower.MertensFirst
import GaloisForLFunctions.RHTower.PrimeVacuumErrorTransfer
import GaloisForLFunctions.RHTower.SourceHorizontalWoldPrimeClockProfile

open Complex Filter Topology Asymptotics MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section


/-- RH transfers from the corpus `psi` estimate to the prime-only `theta` error at every strict
half-power. -/
theorem exists_chebyshevTheta_error_power_bound_of_riemannHypothesis
    (hRH : RiemannHypothesis) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      |Chebyshev.theta t - t| ≤ C * t ^ (1 / 2 + eps) := by
  obtain ⟨C, hC, hpsi⟩ :=
    Sieve.exists_chebyshevPsiReal_error_power_bound hRH (show 0 < eps / 2 by linarith)
  refine ⟨C + 4 / eps, by positivity, ?_⟩
  intro t ht
  have ht0 : 0 < t := by linarith
  have hpsi' : |Chebyshev.psi t - t| ≤ C * t ^ (1 / 2 + eps / 2) := by
    rw [← chebyshevPsiReal_eq_psi]
    exact hpsi t ht
  have hprimePower := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log ht
  have hlog := Mertens.log_le_rpow ht0 (show 0 < eps / 2 by linarith)
  have hsqrt0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hpow0 : 0 ≤ t ^ (eps / 2) := (Real.rpow_pos_of_pos ht0 _).le
  have hcorr :
      2 * Real.sqrt t * Real.log t ≤
        (4 / eps) * t ^ (1 / 2 + eps / 2) := by
    have hfactor : 0 ≤ 2 * Real.sqrt t :=
      mul_nonneg (by norm_num) hsqrt0
    have hmul := mul_le_mul_of_nonneg_left hlog hfactor
    calc
      2 * Real.sqrt t * Real.log t ≤
          2 * Real.sqrt t * ((1 / (eps / 2)) * t ^ (eps / 2)) := hmul
      _ = (4 / eps) * t ^ (1 / 2 + eps / 2) := by
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
  have hsmall : t ^ (1 / 2 + eps / 2) ≤ t ^ (1 / 2 + eps) := by
    exact Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have hsmall0 : 0 ≤ t ^ (1 / 2 + eps / 2) :=
    (Real.rpow_pos_of_pos ht0 _).le
  have hlarge0 : 0 ≤ t ^ (1 / 2 + eps) :=
    (Real.rpow_pos_of_pos ht0 _).le
  calc
    |Chebyshev.theta t - t| ≤
        |Chebyshev.psi t - t| + |Chebyshev.psi t - Chebyshev.theta t| := htri
    _ ≤ C * t ^ (1 / 2 + eps / 2) +
        (4 / eps) * t ^ (1 / 2 + eps / 2) :=
      add_le_add hpsi' (hprimePower.trans hcorr)
    _ = (C + 4 / eps) * t ^ (1 / 2 + eps / 2) := by ring
    _ ≤ (C + 4 / eps) * t ^ (1 / 2 + eps) := by
      exact mul_le_mul_of_nonneg_left hsmall (by positivity)

/-- A strict-half theta error gives the matching power tail for the Mertens error density. -/
theorem abs_setIntegral_thetaErrorDensity_Ioi_le_of_power_bound
    {C eps x : ℝ} (heps0 : 0 < eps) (hepsHalf : eps < 1 / 2)
    (hx : 1 ≤ x)
    (htheta : ∀ t : ℝ, 1 ≤ t →
      |Chebyshev.theta t - t| ≤ C * t ^ (1 / 2 + eps)) :
    |∫ t in Ioi x, Sieve.thetaErrorDensity t| ≤
      C * (x ^ (-(1 / 2 - eps)) / (1 / 2 - eps)) := by
  let q : ℝ := 3 / 2 - eps
  have hq : 1 < q := by dsimp only [q]; linarith
  have hx0 : 0 < x := by linarith
  have htail :=
    GaloisForLFunctions.HTGeometry.norm_integral_Ioi_le_powerTail
      (f := Sieve.thetaErrorDensity) (C := C) (q := q) (x := x)
      hq hx0 ?_
  · rw [Real.norm_eq_abs] at htail
    calc
      |∫ t in Ioi x, Sieve.thetaErrorDensity t| ≤
          C * (x ^ (1 - q) / (q - 1)) := htail
      _ = C * (x ^ (-(1 / 2 - eps)) / (1 / 2 - eps)) := by
        rw [show 1 - q = -(1 / 2 - eps) by dsimp only [q]; ring,
          show q - 1 = 1 / 2 - eps by dsimp only [q]; ring]
  · intro t ht
    have ht1 : 1 ≤ t := hx.trans ht.le
    have ht0 : 0 < t := by linarith
    have hsq : 0 < t ^ 2 := by positivity
    have hb := htheta t ht1
    rw [Real.norm_eq_abs, Sieve.thetaErrorDensity, abs_div, abs_of_pos hsq,
      div_le_iff₀ hsq]
    calc
      |Chebyshev.theta t - t| ≤ C * t ^ (1 / 2 + eps) := hb
      _ = C * |t| ^ (-q) * t ^ 2 := by
        symm
        calc
          C * |t| ^ (-q) * t ^ 2 =
              C * (t ^ (-q) * t ^ (2 : ℝ)) := by
            rw [abs_of_pos ht0, ← Real.rpow_natCast]
            ring
          _ = C * t ^ (-q + 2) := by rw [Real.rpow_add ht0]
          _ = C * t ^ (1 / 2 + eps) := by
            congr 2
            dsimp only [q]
            ring

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

/-- Under RH, Mertens' prime-log discrepancy has every strict half-power rate around the
explicit theta-error integral constant. -/
theorem exists_mertensA_sub_log_integralConstant_power_rate_of_riemannHypothesis
    (hRH : RiemannHypothesis) {eps : ℝ}
    (heps0 : 0 < eps) (hepsHalf : eps < 1 / 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, 2 ≤ x →
      |Sieve.mertensA ⌊x⌋₊ - Real.log x -
        (1 - Real.log 2 +
          ∫ t in Ioi (2 : ℝ), Sieve.thetaErrorDensity t)| ≤
        B * x ^ (-(1 / 2 - eps)) := by
  obtain ⟨C, hC, htheta⟩ :=
    exists_chebyshevTheta_error_power_bound_of_riemannHypothesis hRH heps0
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
          _ = C * x ^ (-(1 / 2 - eps) + 1) := by
            rw [Real.rpow_add hx0]
          _ = C * x ^ (1 / 2 + eps) := by
            congr 2
            ring
  have hb2 : |∫ t in Ioi x, Sieve.thetaErrorDensity t| ≤
      C * (x ^ (-(1 / 2 - eps)) / (1 / 2 - eps)) :=
    abs_setIntegral_thetaErrorDensity_Ioi_le_of_power_bound
      heps0 hepsHalf hx1 htheta
  have htri := abs_sub ((Chebyshev.theta x - x) / x)
    (∫ t in Ioi x, Sieve.thetaErrorDensity t)
  calc
    |(Chebyshev.theta x - x) / x -
        ∫ t in Ioi x, Sieve.thetaErrorDensity t| ≤
      |(Chebyshev.theta x - x) / x| +
        |∫ t in Ioi x, Sieve.thetaErrorDensity t| := htri
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

/-- Canonical Mertens constant form of the strict-half power law. -/
theorem exists_mertensA_sub_log_power_rate_of_riemannHypothesis
    (hRH : RiemannHypothesis) {eps : ℝ}
    (heps0 : 0 < eps) (hepsHalf : eps < 1 / 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      |Sieve.mertensA N - Real.log N - xiHeatCassiniMertensLogConstant| ≤
        B * (N : ℝ) ^ (-(1 / 2 - eps)) := by
  obtain ⟨B, hB, hreal⟩ :=
    exists_mertensA_sub_log_integralConstant_power_rate_of_riemannHypothesis
      hRH heps0 hepsHalf
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
      Tendsto (fun N : ℕ =>
        ‖Sieve.mertensA N - Real.log N - cInt‖) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun N => norm_nonneg _
    · simpa only [Real.norm_eq_abs] using hrateInt
    · exact hmajor
  have hzero :
      Tendsto (fun N : ℕ => Sieve.mertensA N - Real.log N - cInt)
        atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
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

theorem eventually_woldNatTraceCorrection_tail_le_power
    {eps : ℝ} (heps0 : 0 < eps) :
    ∀ᶠ N : ℕ in atTop,
      xiHeatCassiniWoldNatTraceCorrectionMass -
          xiHeatCassiniWoldNatTraceCorrectionSum N ≤
        (3 * (1 / (1 / 2 + eps) + 1)) *
          (N : ℝ) ^ (-(1 / 2 - eps)) := by
  filter_upwards [eventually_ge_atTop 3] with N hN
  have htail := xiHeatCassiniWoldNatTraceCorrectionMass_sub_sum_le hN
  have hNreal : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  let alpha : ℝ := 1 / 2 + eps
  have halpha : 0 < alpha := by dsimp only [alpha]; linarith
  have hlog := Mertens.log_le_rpow hN0 halpha
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ alpha := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 halpha.le
  have hnum : Real.log N + 1 ≤
      (1 / alpha + 1) * (N : ℝ) ^ alpha := by
    nlinarith [hlog, hone]
  have hdiv : (Real.log N + 1) / N ≤
      (1 / alpha + 1) * (N : ℝ) ^ (-(1 / 2 - eps)) := by
    rw [div_le_iff₀ hN0]
    calc
      Real.log N + 1 ≤ (1 / alpha + 1) * (N : ℝ) ^ alpha := hnum
      _ = (1 / alpha + 1) * (N : ℝ) ^ (-(1 / 2 - eps)) * N := by
        symm
        calc
          (1 / alpha + 1) * (N : ℝ) ^ (-(1 / 2 - eps)) * N =
              (1 / alpha + 1) *
                ((N : ℝ) ^ (-(1 / 2 - eps)) * (N : ℝ) ^ (1 : ℝ)) := by
            simp only [Real.rpow_one]
            ring
          _ = (1 / alpha + 1) *
              (N : ℝ) ^ (-(1 / 2 - eps) + 1) := by
            rw [Real.rpow_add hN0]
          _ = (1 / alpha + 1) * (N : ℝ) ^ alpha := by
            congr 2
            dsimp only [alpha]
            ring
  calc
    xiHeatCassiniWoldNatTraceCorrectionMass -
        xiHeatCassiniWoldNatTraceCorrectionSum N ≤
      3 * ((Real.log N + 1) / N) := htail
    _ ≤ 3 * ((1 / alpha + 1) *
        (N : ℝ) ^ (-(1 / 2 - eps))) :=
      mul_le_mul_of_nonneg_left hdiv (by norm_num)
    _ = (3 * (1 / (1 / 2 + eps) + 1)) *
        (N : ℝ) ^ (-(1 / 2 - eps)) := by
      dsimp only [alpha]
      ring

/-- RH gives every strict half-power decay for the centered natural-cutoff Wold primitive. -/
theorem exists_woldNatResidual_power_rate_of_riemannHypothesis
    (hRH : RiemannHypothesis) {eps : ℝ}
    (heps0 : 0 < eps) (hepsHalf : eps < 1 / 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniWoldNatResidualLogDiscrepancy N| ≤
        B * (N : ℝ) ^ (-(1 / 2 - eps)) := by
  obtain ⟨B, hB, hMertens⟩ :=
    exists_mertensA_sub_log_power_rate_of_riemannHypothesis
      hRH heps0 hepsHalf
  let D : ℝ := 3 * (1 / (1 / 2 + eps) + 1)
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
    _ ≤ B * (N : ℝ) ^ (-(1 / 2 - eps)) +
        D * (N : ℝ) ^ (-(1 / 2 - eps)) := by
      exact add_le_add hMN (by simpa only [D] using htraceN)
    _ = (B + D) * (N : ℝ) ^ (-(1 / 2 - eps)) := by ring

/-- Ordered-prime form: RH gives every exponential height rate strictly below one half. -/
theorem exists_orderedWoldResidual_exp_height_rate_of_riemannHypothesis
    (hRH : RiemannHypothesis) {eps : ℝ}
    (heps0 : 0 < eps) (hepsHalf : eps < 1 / 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        B * Real.exp (-(1 / 2 - eps) * xiMassNthPrimeLogHeight N) := by
  obtain ⟨B, hB, hrate⟩ :=
    exists_woldNatResidual_power_rate_of_riemannHypothesis hRH heps0 hepsHalf
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
        B * (nthPrimeSubtype N : ℝ) ^ (-(1 / 2 - eps)) := hN
    _ = B * Real.exp (-(1 / 2 - eps) * xiMassNthPrimeLogHeight N) := by
      rw [Real.rpow_def_of_pos hp0]
      unfold xiMassNthPrimeLogHeight
      congr 2
      ring

/-- RH makes the exact Borel terminal vanish at every strict sub-half height. -/
theorem tendsto_woldResidualBorelTerminalWeight_zero_of_riemannHypothesis
    (hRH : RiemannHypothesis) {y : ℝ} (hy0 : 0 ≤ y) (hyHalf : y < 1 / 2) :
    Tendsto (fun N : ℕ =>
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        Real.exp (y * xiMassNthPrimeLogHeight N)) atTop (𝓝 0) := by
  let eps : ℝ := (1 / 2 - y) / 2
  have heps0 : 0 < eps := by dsimp only [eps]; linarith
  have hepsHalf : eps < 1 / 2 := by dsimp only [eps]; linarith
  obtain ⟨B, hB, hrate⟩ :=
    exists_orderedWoldResidual_exp_height_rate_of_riemannHypothesis
      hRH heps0 hepsHalf
  let d : ℝ := (1 / 2 - eps) - y
  have hd : 0 < d := by dsimp only [d, eps]; linarith
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
        (B * Real.exp (-(1 / 2 - eps) * xiMassNthPrimeLogHeight N)) *
          Real.exp (y * xiMassNthPrimeLogHeight N) :=
        mul_le_mul_of_nonneg_right hN hexp0
      _ = B * Real.exp (-(d * xiMassNthPrimeLogHeight N)) := by
        calc
          (B * Real.exp (-(1 / 2 - eps) * xiMassNthPrimeLogHeight N)) *
              Real.exp (y * xiMassNthPrimeLogHeight N) =
            B * (Real.exp (-(1 / 2 - eps) * xiMassNthPrimeLogHeight N) *
              Real.exp (y * xiMassNthPrimeLogHeight N)) := by ring
          _ = B * Real.exp (-(1 / 2 - eps) * xiMassNthPrimeLogHeight N +
              y * xiMassNthPrimeLogHeight N) := by rw [Real.exp_add]
          _ = B * Real.exp (-(d * xiMassNthPrimeLogHeight N)) := by
            congr 2
            dsimp only [d]
            ring
  · exact hmajor

/-- Under RH, raw and Abel-renormalized finite positive-ray Borel prescriptions have the same
strict-sub-half limit whenever either limit exists. -/
theorem tendsto_woldResidualBorelFiniteRenormalized_sub_raw_zero_of_riemannHypothesis
    (hRH : RiemannHypothesis) (x : ℝ) {y : ℝ}
    (hy0 : 0 ≤ y) (hyHalf : y < 1 / 2) :
    Tendsto (fun N : ℕ =>
      xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent x y N -
        ∫ t : ℝ in Ioi 0,
          ∑ n ∈ Finset.range N,
            xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom x y n t)
      atTop (𝓝 0) := by
  rw [tendsto_xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent_sub_edgeIntegral_zero_iff]
  simpa only [mul_comm] using
    tendsto_woldResidualBorelTerminalWeight_zero_of_riemannHypothesis
      hRH hy0 hyHalf

/-- **Strict-sub-half source classification.** Under critical mesh energy, absolute convergence
of the raw residual edge current at every strict upper height is equivalent to RH. -/
theorem riemannHypothesis_iff_subhalf_residual_absoluteConvergence
    (hcritical : Summable xiHeatCassiniPrimeGapCriticalEnergy) :
    RiemannHypothesis ↔
      ∀ a : ℝ, 0 < a → a < 1 / 2 →
        Summable (fun N : ℕ =>
          ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
            (Complex.I * (a : ℂ)) N‖) := by
  constructor
  · intro hRH a ha0 haHalf
    let eps : ℝ := (1 / 2 - a) / 2
    have heps0 : 0 < eps := by dsimp only [eps]; linarith
    have hepsHalf : eps < 1 / 2 := by dsimp only [eps]; linarith
    obtain ⟨B, hB, hrate⟩ :=
      exists_orderedWoldResidual_exp_height_rate_of_riemannHypothesis
        hRH heps0 hepsHalf
    apply summable_norm_residualAtom_mul_I_of_exp_height_rate
      (c := 1 / 2 - eps) (B := B)
    · exact ha0
    · linarith
    · dsimp only [eps]
      linarith
    · exact hrate
  · intro hconv
    exact riemannHypothesis_of_subhalf_residual_absoluteConvergence_criticalEnergy
      hconv hcritical

end

end RHTower
