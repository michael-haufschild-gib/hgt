import GaloisForLFunctions.RHTower.XiOrderedPositiveZeros
import GaloisForLFunctions.RHTower.PrimeIndexedRVMSchattenInfrastructure

open Complex Set Filter

namespace RHTower

noncomputable section

theorem tendsto_xiOrderedPositiveOrdinate_atTop :
    Tendsto xiOrderedPositiveOrdinate atTop atTop := by
  apply tendsto_atTop.2
  intro T
  filter_upwards [eventually_ge_atTop (xiZeroCount T).toNat] with n hn
  by_contra hnot
  have hle : xiOrderedPositiveOrdinate n ≤ T := le_of_not_ge hnot
  have hcount : ((n + 1 : ℕ) : ℤ) ≤ xiZeroCount T :=
    xiOrderedPositiveOrdinate_le_iff.mp hle
  have hcast : (((xiZeroCount T).toNat : ℕ) : ℤ) = xiZeroCount T :=
    Int.toNat_of_nonneg (xiZeroCount_nonneg T)
  omega

theorem tendsto_routeKRVMQuantile_atTop :
    Tendsto routeKRVMQuantile atTop atTop := by
  apply tendsto_atTop.2
  intro T
  by_cases hT : routeKRVMBase < T
  · filter_upwards [eventually_ge_atTop ⌊(routeKSmoothRVMCount T)⌋₊] with n hn
    by_contra hnot
    have hle : routeKRVMQuantile n ≤ T := le_of_not_ge hnot
    have hlt : n < ⌊routeKSmoothRVMCount T⌋₊ :=
      (routeKRVMQuantile_le_iff_lt_floor_count hT).mp hle
    omega
  · filter_upwards with n
    exact le_trans (le_of_not_gt hT) (routeKRVMBase_lt_quantile n).le

/-- The exact RVM remainder evaluated at multiplicity-ordered actual ordinates. -/
theorem exists_eventually_abs_routeKSmoothRVMCount_ordered_sub_succ_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      |routeKSmoothRVMCount (xiOrderedPositiveOrdinate n) - (n + 1 : ℝ)| ≤
        C * Real.log (xiOrderedPositiveOrdinate n) := by
  obtain ⟨C, hC, T₀, hT₀, hrem⟩ :=
    exists_xiZeroCount_routeKSmoothRVMCount_log_remainder
  refine ⟨C + 2, by linarith, ?_⟩
  have hgammaEventually : ∀ᶠ n : ℕ in atTop,
      max (T₀ + 1) 4 ≤ xiOrderedPositiveOrdinate n :=
    tendsto_xiOrderedPositiveOrdinate_atTop.eventually
      (eventually_ge_atTop (max (T₀ + 1) 4))
  filter_upwards [hgammaEventually] with n hn
  set gamma : ℝ := xiOrderedPositiveOrdinate n with hgamma
  have hgammaT₀ : T₀ ≤ gamma := by
    have : T₀ + 1 ≤ gamma := le_trans (le_max_left _ _) hn
    linarith
  have hgamma4 : (4 : ℝ) ≤ gamma := le_trans (le_max_right _ _) hn
  have hgamma0 : 0 < gamma := by linarith
  have hpredT₀ : T₀ ≤ gamma - 1 := by
    have : T₀ + 1 ≤ gamma := le_trans (le_max_left _ _) hn
    linarith
  have hpred0 : 0 < gamma - 1 := by linarith
  have hlogGammaPos : 0 < Real.log gamma := Real.log_pos (by linarith)
  have hlogPredLe : Real.log (gamma - 1) ≤ Real.log gamma := by
    exact Real.strictMonoOn_log.monotoneOn hpred0 hgamma0 (by linarith)
  have hremGamma := hrem gamma hgammaT₀
  have hremPred := hrem (gamma - 1) hpredT₀
  rw [abs_le] at hremGamma hremPred
  have hcountGammaInt : ((n + 1 : ℕ) : ℤ) ≤ xiZeroCount gamma := by
    have hmem := xiOrderedPositiveOrdinate_mem_upperSet n
    change ((n + 1 : ℕ) : ℤ) ≤
      xiZeroCount (xiOrderedPositiveOrdinate n) at hmem
    simpa [hgamma] using hmem
  have hcountGamma : (n + 1 : ℝ) ≤ (xiZeroCount gamma : ℝ) := by
    exact_mod_cast hcountGammaInt
  have hcountPredInt : xiZeroCount (gamma - 1) ≤ (n : ℤ) := by
    have hnot : ¬ ((n + 1 : ℕ) : ℤ) ≤ xiZeroCount (gamma - 1) := by
      intro hmem
      have hle : gamma ≤ gamma - 1 := by
        rw [hgamma]
        exact xiOrderedPositiveOrdinate_le_iff.mpr hmem
      linarith
    omega
  have hcountPred : (xiZeroCount (gamma - 1) : ℝ) ≤ n := by
    exact_mod_cast hcountPredInt
  have hstep : routeKSmoothRVMCount gamma -
      routeKSmoothRVMCount (gamma - 1) ≤ Real.log gamma := by
    exact routeKSmoothRVMCount_sub_le_log_of_mem_unitBelow hgamma4
      (by linarith) (by linarith)
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- On the large-height chamber, the smooth count gains at least logarithmic slope. -/
theorem routeKSmoothRVMCount_sub_lower_log {a b : ℝ}
    (ha : routeKRVMBase ^ (2 : ℕ) ≤ a) (hab : a ≤ b) :
    (b - a) * Real.log a / (4 * Real.pi) ≤
      routeKSmoothRVMCount b - routeKSmoothRVMCount a := by
  have hbase0 : 0 < routeKRVMBase := routeKRVMBase_pos
  have hbase1 : 1 < routeKRVMBase := one_lt_routeKRVMBase
  have ha0 : 0 < a := lt_of_lt_of_le (sq_pos_of_pos hbase0) ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hd : 0 ≤ b - a := sub_nonneg.mpr hab
  have hlogBase : 0 ≤ Real.log routeKRVMBase :=
    Real.log_nonneg hbase1.le
  have hlogA : 0 ≤ Real.log a := Real.log_nonneg (by
    exact le_trans hbase1.le (le_trans (le_self_pow₀ hbase1.le two_ne_zero) ha))
  have hlogAB : Real.log a ≤ Real.log b :=
    Real.strictMonoOn_log.monotoneOn ha0 hb0 hab
  have htwoLog : 2 * Real.log routeKRVMBase ≤ Real.log a := by
    calc
      2 * Real.log routeKRVMBase = Real.log (routeKRVMBase ^ (2 : ℕ)) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log a := Real.strictMonoOn_log.monotoneOn
        (sq_pos_of_pos hbase0) ha0 ha
  have hmulLog : (b - a) * Real.log a ≤
      b * Real.log b - a * Real.log a := by
    have hnonneg := mul_nonneg hb0.le (sub_nonneg.mpr hlogAB)
    nlinarith
  have hnum : (b - a) * Real.log a / 2 ≤
      (b * Real.log b - a * Real.log a) -
        (b - a) * Real.log routeKRVMBase := by
    have hnonneg := mul_nonneg hd (sub_nonneg.mpr htwoLog)
    nlinarith
  rw [routeKSmoothRVMCount_sub_eq ha0 hb0]
  calc
    (b - a) * Real.log a / (4 * Real.pi) =
        ((b - a) * Real.log a / 2) / (2 * Real.pi) := by ring
    _ ≤ ((b * Real.log b - a * Real.log a) -
        (b - a) * Real.log routeKRVMBase) / (2 * Real.pi) := by
      gcongr

theorem log_sub_ge_log_sub_log_two {x D : ℝ}
    (hx : 2 * D ≤ x) (hx0 : 0 < x) :
    Real.log x - Real.log 2 ≤ Real.log (x - D) := by
  have hhalf0 : 0 < x / 2 := by positivity
  have hsub0 : 0 < x - D := by linarith
  have hhalf : x / 2 ≤ x - D := by linarith
  calc
    Real.log x - Real.log 2 = Real.log (x / 2) := by
      rw [Real.log_div hx0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    _ ≤ Real.log (x - D) :=
      Real.strictMonoOn_log.monotoneOn hhalf0 hsub0 hhalf

/-- The actual multiplicity-ordered ordinates stay within bounded distance of RVM quantiles. -/
theorem exists_eventually_abs_xiOrderedPositiveOrdinate_sub_routeKRVMQuantile_le :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop,
      |xiOrderedPositiveOrdinate n - routeKRVMQuantile n| ≤ D := by
  obtain ⟨C, hC, happrox⟩ :=
    exists_eventually_abs_routeKSmoothRVMCount_ordered_sub_succ_le
  set D : ℝ := 8 * Real.pi * (C + 1) with hDdef
  have hD : 0 < D := by
    rw [hDdef]
    positivity
  refine ⟨D, hD, ?_⟩
  set K : ℝ := max (routeKRVMBase ^ (2 : ℕ) + D)
    (max (2 * D) (Real.exp (2 * Real.log 2 + 1))) with hKdef
  have hlarge : ∀ᶠ n : ℕ in atTop, K ≤ xiOrderedPositiveOrdinate n :=
    tendsto_xiOrderedPositiveOrdinate_atTop.eventually (eventually_ge_atTop K)
  filter_upwards [happrox, hlarge] with n happ hn
  set gamma : ℝ := xiOrderedPositiveOrdinate n with hgamma
  set t : ℝ := routeKRVMQuantile n with ht
  have hgammaK : K ≤ gamma := by simpa [hgamma] using hn
  have hgammaBaseD : routeKRVMBase ^ (2 : ℕ) + D ≤ gamma := by
    exact le_trans (le_max_left _ _) (hKdef ▸ hgammaK)
  have hgammaBase : routeKRVMBase ^ (2 : ℕ) ≤ gamma := by linarith
  have hgammaMinusBase : routeKRVMBase ^ (2 : ℕ) ≤ gamma - D := by linarith
  have hgammaTwoD : 2 * D ≤ gamma := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (hKdef ▸ hgammaK))
  have hgammaExp : Real.exp (2 * Real.log 2 + 1) ≤ gamma := by
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (hKdef ▸ hgammaK))
  have hgamma0 : 0 < gamma := lt_of_lt_of_le
    (sq_pos_of_pos routeKRVMBase_pos) hgammaBase
  have hlogGammaPos : 0 < Real.log gamma := Real.log_pos (by
    exact lt_of_lt_of_le one_lt_routeKRVMBase
      (le_trans (le_self_pow₀ one_lt_routeKRVMBase.le two_ne_zero) hgammaBase))
  have hlogLarge : 2 * Real.log 2 + 1 ≤ Real.log gamma := by
    rw [Real.le_log_iff_exp_le hgamma0]
    exact hgammaExp
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htBase : routeKRVMBase < t := by
    simpa [ht] using routeKRVMBase_lt_quantile n
  have hMt : routeKSmoothRVMCount t = (n + 1 : ℝ) := by
    simpa [ht] using routeKSmoothRVMCount_quantile n
  have happ' : |routeKSmoothRVMCount gamma - (n + 1 : ℝ)| ≤
      C * Real.log gamma := by simpa [hgamma] using happ
  rw [abs_le] at happ'
  rw [abs_le]
  constructor
  · by_contra hnot
    have hfar : gamma + D < t := by linarith
    have hlower := routeKSmoothRVMCount_sub_lower_log hgammaBase
      (by linarith : gamma ≤ t)
    have hdistance : D * Real.log gamma <
        (t - gamma) * Real.log gamma := by
      apply mul_lt_mul_of_pos_right _ hlogGammaPos
      linarith
    have hratio : 2 * (C + 1) * Real.log gamma =
        D * Real.log gamma / (4 * Real.pi) := by
      rw [hDdef]
      field_simp [Real.pi_ne_zero]
      ring
    have hdistanceDiv : D * Real.log gamma / (4 * Real.pi) <
        (t - gamma) * Real.log gamma / (4 * Real.pi) := by
      exact div_lt_div_of_pos_right hdistance (by positivity)
    have hbaseGain : 2 * (C + 1) * Real.log gamma <
        routeKSmoothRVMCount t - routeKSmoothRVMCount gamma := by
      rw [hratio]
      exact hdistanceDiv.trans_le hlower
    nlinarith
  · by_contra hnot
    have hfar : t + D < gamma := by linarith
    have htLe : t ≤ gamma - D := by linarith
    have hbaseSq : routeKRVMBase < routeKRVMBase ^ (2 : ℕ) := by
      nlinarith [routeKRVMBase_pos, one_lt_routeKRVMBase]
    have hminusBase : routeKRVMBase < gamma - D :=
      hbaseSq.trans_le hgammaMinusBase
    have hMle : routeKSmoothRVMCount t ≤
        routeKSmoothRVMCount (gamma - D) :=
      (routeKSmoothRVMCount_strictMonoOn.le_iff_le htBase hminusBase).2 htLe
    have hlower := routeKSmoothRVMCount_sub_lower_log hgammaMinusBase
      (by linarith : gamma - D ≤ gamma)
    have hgain : 2 * (C + 1) * Real.log (gamma - D) ≤
        routeKSmoothRVMCount gamma - routeKSmoothRVMCount t := by
      calc
        2 * (C + 1) * Real.log (gamma - D) =
            (gamma - (gamma - D)) * Real.log (gamma - D) /
              (4 * Real.pi) := by
          rw [hDdef]
          field_simp [Real.pi_ne_zero]
          ring
        _ ≤ routeKSmoothRVMCount gamma -
            routeKSmoothRVMCount (gamma - D) := hlower
        _ ≤ routeKSmoothRVMCount gamma - routeKSmoothRVMCount t := by
          linarith
    have hlogSub := log_sub_ge_log_sub_log_two hgammaTwoD hgamma0
    have hmulLog : 2 * (C + 1) * (Real.log gamma - Real.log 2) ≤
        2 * (C + 1) * Real.log (gamma - D) := by
      exact mul_le_mul_of_nonneg_left hlogSub (by positivity)
    have hprod : 0 ≤ (C + 2) *
        (Real.log gamma - (2 * Real.log 2 + 1)) :=
      mul_nonneg (by linarith) (sub_nonneg.mpr hlogLarge)
    have hsep : C * Real.log gamma <
        2 * (C + 1) * (Real.log gamma - Real.log 2) := by
      nlinarith
    nlinarith

/-- Reciprocal actual/model displacement is absolutely summable. -/
theorem summable_abs_xiOrderedPositiveOrdinate_inv_sub_routeKRVMQuantile_inv :
    Summable (fun n : ℕ =>
      |(xiOrderedPositiveOrdinate n)⁻¹ - (routeKRVMQuantile n)⁻¹|) := by
  obtain ⟨D, hD, hdist⟩ :=
    exists_eventually_abs_xiOrderedPositiveOrdinate_sub_routeKRVMQuantile_le
  have htLarge : ∀ᶠ n : ℕ in atTop, 2 * D ≤ routeKRVMQuantile n :=
    tendsto_routeKRVMQuantile_atTop.eventually (eventually_ge_atTop (2 * D))
  have hmajor : Summable (fun n : ℕ =>
      (2 * D) * (routeKRVMQuantile n)⁻¹ ^ (2 : ℕ)) :=
    summable_routeKRVMQuantile_reciprocal_sq.mul_left (2 * D)
  apply hmajor.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hdist, htLarge] with n hdistN htN
  set gamma : ℝ := xiOrderedPositiveOrdinate n with hgamma
  set t : ℝ := routeKRVMQuantile n with ht
  have hdistN' : |gamma - t| ≤ D := by simpa [hgamma, ht] using hdistN
  have htN' : 2 * D ≤ t := by simpa [ht] using htN
  have ht0 : 0 < t := by
    simpa [ht] using routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile n)
  have hgammaHalf : t / 2 ≤ gamma := by
    rw [abs_le] at hdistN'
    linarith
  have hgamma0 : 0 < gamma := lt_of_lt_of_le (half_pos ht0) hgammaHalf
  have hdenLower : t ^ (2 : ℕ) / 2 ≤ gamma * t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hgammaHalf) ht0.le]
  have hinvSub : gamma⁻¹ - t⁻¹ = (t - gamma) / (gamma * t) := by
    field_simp [hgamma0.ne', ht0.ne']
  have hpoint : |gamma⁻¹ - t⁻¹| ≤ (2 * D) * t⁻¹ ^ (2 : ℕ) := by
    rw [hinvSub, abs_div, abs_mul, abs_of_pos hgamma0, abs_of_pos ht0,
      abs_sub_comm]
    calc
      |gamma - t| / (gamma * t) ≤ D / (gamma * t) := by
        gcongr
      _ ≤ D / (t ^ (2 : ℕ) / 2) := by
        gcongr
      _ = (2 * D) * t⁻¹ ^ (2 : ℕ) := by
        field_simp [ht0.ne']
  simpa only [Real.norm_eq_abs, abs_abs, hgamma, ht] using hpoint

end

end RHTower
