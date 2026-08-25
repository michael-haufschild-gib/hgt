import GaloisForLFunctions.RHTower.Sieve.VonMangoldtSquareDyadicHyperbolaAsymptotic

noncomputable section

open Filter Topology ArithmeticFunction Finset
open scoped ArithmeticFunction BigOperators

namespace RHTower.Sieve

theorem vonMangoldtSquareHyperbolaMass_nonneg (N : ℕ) :
    0 ≤ vonMangoldtSquareHyperbolaMass N := by
  rw [vonMangoldtSquareHyperbolaMass]
  apply Finset.sum_nonneg
  intro d hd
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun m hm => by positivity)

theorem monotone_vonMangoldtSquareHyperbolaMass :
    Monotone vonMangoldtSquareHyperbolaMass := by
  intro M N hMN
  rw [vonMangoldtSquareHyperbolaMass, vonMangoldtSquareHyperbolaMass]
  calc
    ∑ d ∈ Finset.Icc 1 M, (Λ d) ^ 2 / (d : ℝ) *
        ∑ m ∈ Finset.Icc 1 (M / d), (Λ m) ^ 2 / (m : ℝ) ≤
      ∑ d ∈ Finset.Icc 1 M, (Λ d) ^ 2 / (d : ℝ) *
        ∑ m ∈ Finset.Icc 1 (N / d), (Λ m) ^ 2 / (m : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          have hdiv : M / d ≤ N / d := Nat.div_le_div_right hMN
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (by
              intro m hm
              simp only [Finset.mem_Icc] at hm ⊢
              exact ⟨hm.1, hm.2.trans hdiv⟩)
              (fun m hm hnot => by positivity)) (by positivity)
    _ ≤ ∑ d ∈ Finset.Icc 1 N, (Λ d) ^ 2 / (d : ℝ) *
        ∑ m ∈ Finset.Icc 1 (N / d), (Λ m) ^ 2 / (m : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro d hd
            simp only [Finset.mem_Icc] at hd ⊢
            exact ⟨hd.1, hd.2.trans hMN⟩
          · intro d hd hnot
            exact mul_nonneg (by positivity) (Finset.sum_nonneg fun m hm => by positivity)

private theorem tendsto_binaryLog_atTop :
    Tendsto (Nat.log 2) atTop atTop := by
  apply tendsto_atTop.2
  intro K
  filter_upwards [eventually_ge_atTop (2 ^ K)] with N hN
  exact Nat.le_log_of_pow_le (by norm_num) hN

private theorem tendsto_binaryLog_inv_zero :
    Tendsto (fun N : ℕ => (1 : ℝ) / (Nat.log 2 N : ℝ)) atTop (𝓝 0) :=
  Tendsto.div_atTop tendsto_const_nhds
    (tendsto_natCast_atTop_atTop.comp tendsto_binaryLog_atTop)

private theorem tendsto_binaryLog_ratio_succ :
    Tendsto (fun N : ℕ =>
      ((Nat.log 2 N : ℝ) + 1) / (Nat.log 2 N : ℝ)) atTop (𝓝 1) := by
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have h := hone.add tendsto_binaryLog_inv_zero
  have hfinal : Tendsto (fun N : ℕ =>
      1 + 1 / (Nat.log 2 N : ℝ)) atTop (𝓝 ((1 : ℝ) + 0)) := h
  simpa using hfinal.congr' (by
    filter_upwards [tendsto_binaryLog_atTop.eventually (eventually_gt_atTop 0)] with N hlog
    have hne : (Nat.log 2 N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hlog)
    field_simp [hne])

private theorem tendsto_binaryLog_ratio_pred :
    Tendsto (fun N : ℕ =>
      (Nat.log 2 N : ℝ) / ((Nat.log 2 N : ℝ) + 1)) atTop (𝓝 1) := by
  have h := tendsto_binaryLog_ratio_succ.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa [div_eq_mul_inv] using h.congr' (by
    filter_upwards [] with N
    field_simp)

private theorem tendsto_dyadic_lower_envelope :
    Tendsto (fun N : ℕ =>
      vonMangoldtSquareHyperbolaMass (2 ^ Nat.log 2 N) /
        (((Nat.log 2 N : ℝ) + 1) * Real.log 2) ^ 4)
      atTop (𝓝 (1 / 24 : ℝ)) := by
  have hD := tendsto_vonMangoldtSquareHyperbolaMass_pow_two_div_logFourth.comp
    tendsto_binaryLog_atTop
  have hr := tendsto_binaryLog_ratio_pred.pow 4
  have hprod := hD.mul hr
  have hfinal : Tendsto (fun N : ℕ =>
      (vonMangoldtSquareHyperbolaMass (2 ^ Nat.log 2 N) /
        ((Nat.log 2 N : ℝ) * Real.log 2) ^ 4) *
      ((Nat.log 2 N : ℝ) / ((Nat.log 2 N : ℝ) + 1)) ^ 4)
      atTop (𝓝 ((1 / 24 : ℝ) * 1 ^ 4)) := hprod
  simpa only [one_pow, mul_one] using hfinal.congr' (by
    filter_upwards [tendsto_binaryLog_atTop.eventually (eventually_gt_atTop 0)] with N hlog
    have hlogR : (Nat.log 2 N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hlog)
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp [hlogR, hlog2])

private theorem tendsto_dyadic_upper_envelope :
    Tendsto (fun N : ℕ =>
      vonMangoldtSquareHyperbolaMass (2 ^ (Nat.log 2 N + 1)) /
        ((Nat.log 2 N : ℝ) * Real.log 2) ^ 4)
      atTop (𝓝 (1 / 24 : ℝ)) := by
  have hlogSucc : Tendsto (fun N : ℕ => Nat.log 2 N + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro K
    filter_upwards [tendsto_binaryLog_atTop.eventually (eventually_ge_atTop K)] with N hN
    omega
  have hD' : Tendsto (fun N : ℕ =>
      vonMangoldtSquareHyperbolaMass (2 ^ (Nat.log 2 N + 1)) /
        (((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.log 2) ^ 4)
      atTop (nhds (1 / 24 : ℝ)) :=
    tendsto_vonMangoldtSquareHyperbolaMass_pow_two_div_logFourth.comp hlogSucc
  have hD : Tendsto (fun N : ℕ =>
      vonMangoldtSquareHyperbolaMass (2 ^ (Nat.log 2 N + 1)) /
        (((Nat.log 2 N : ℝ) + 1) * Real.log 2) ^ 4)
      atTop (nhds (1 / 24 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hD'
  have hr := tendsto_binaryLog_ratio_succ.pow 4
  have hprod := hD.mul hr
  have hfinal : Tendsto (fun N : ℕ =>
      (vonMangoldtSquareHyperbolaMass (2 ^ (Nat.log 2 N + 1)) /
        (((Nat.log 2 N : ℝ) + 1) * Real.log 2) ^ 4) *
      (((Nat.log 2 N : ℝ) + 1) / (Nat.log 2 N : ℝ)) ^ 4)
      atTop (𝓝 ((1 / 24 : ℝ) * 1 ^ 4)) := hprod
  simpa only [one_pow, mul_one] using hfinal.congr' (by
    filter_upwards [tendsto_binaryLog_atTop.eventually (eventually_gt_atTop 0)] with N hlog
    have hlogR : (Nat.log 2 N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hlog)
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp [hlogR, hlog2])

/-- Sharp all-cutoff asymptotic for square-weight harmonic hyperbola. -/
theorem tendsto_vonMangoldtSquareHyperbolaMass_div_logFourth :
    Tendsto (fun N : ℕ =>
      vonMangoldtSquareHyperbolaMass N / Real.log N ^ 4)
      atTop (𝓝 (1 / 24 : ℝ)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_dyadic_lower_envelope tendsto_dyadic_upper_envelope
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hN0 : N ≠ 0 := by omega
    have hloNat : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN0
    have hhiNat : N < 2 ^ (Nat.log 2 N + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) N
    have hloglo : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
      have hloReal : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hloNat
      have hlog := Real.log_le_log
        (by positivity : (0 : ℝ) < ((2 ^ Nat.log 2 N : ℕ) : ℝ)) hloReal
      rwa [Nat.cast_pow, Real.log_pow] at hlog
    have hloghi : Real.log N ≤ ((Nat.log 2 N : ℝ) + 1) * Real.log 2 := by
      have hNReal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
      have hhiReal : (N : ℝ) < ((2 ^ (Nat.log 2 N + 1) : ℕ) : ℝ) := by
        exact_mod_cast hhiNat
      have hlog := (Real.log_lt_log hNReal hhiReal).le
      rw [Nat.cast_pow, Real.log_pow] at hlog
      push_cast at hlog
      exact hlog
    have hHmono := monotone_vonMangoldtSquareHyperbolaMass hloNat
    have hH0 := vonMangoldtSquareHyperbolaMass_nonneg N
    have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    calc
      vonMangoldtSquareHyperbolaMass (2 ^ Nat.log 2 N) /
          (((Nat.log 2 N : ℝ) + 1) * Real.log 2) ^ 4 ≤
        vonMangoldtSquareHyperbolaMass N /
          (((Nat.log 2 N : ℝ) + 1) * Real.log 2) ^ 4 := by gcongr
      _ ≤ vonMangoldtSquareHyperbolaMass N / Real.log N ^ 4 := by
        gcongr
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hN0 : N ≠ 0 := by omega
    have hloNat : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN0
    have hhiNat : N < 2 ^ (Nat.log 2 N + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) N
    have hloglo : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
      have hloReal : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hloNat
      have hlog := Real.log_le_log
        (by positivity : (0 : ℝ) < ((2 ^ Nat.log 2 N : ℕ) : ℝ)) hloReal
      rwa [Nat.cast_pow, Real.log_pow] at hlog
    have hHmono := monotone_vonMangoldtSquareHyperbolaMass (Nat.le_of_lt hhiNat)
    have hH0 := vonMangoldtSquareHyperbolaMass_nonneg (2 ^ (Nat.log 2 N + 1))
    have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    calc
      vonMangoldtSquareHyperbolaMass N / Real.log N ^ 4 ≤
        vonMangoldtSquareHyperbolaMass (2 ^ (Nat.log 2 N + 1)) /
          Real.log N ^ 4 := by gcongr
      _ ≤ vonMangoldtSquareHyperbolaMass (2 ^ (Nat.log 2 N + 1)) /
          ((Nat.log 2 N : ℝ) * Real.log 2) ^ 4 := by
        have hlogNat : 1 ≤ Nat.log 2 N :=
          Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
        have hlogR : 0 < (Nat.log 2 N : ℝ) := by exact_mod_cast hlogNat
        have hden : 0 < ((Nat.log 2 N : ℝ) * Real.log 2) ^ 4 := by positivity
        gcongr

end RHTower.Sieve
