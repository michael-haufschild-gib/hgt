import GaloisForLFunctions.RHTower.PMPrimeFloorPowerResponse
import GaloisForLFunctions.RHTower.PMAnalyticPowerBoundary
import GaloisForLFunctions.RHTower.SelbergSecondInequality

/-!
# Selberg inequalities do not control the canonical power-model variance

The actual von Mangoldt floor operator has response `Sσ - 1` on the normalized
comparison remainder. The correction at quotient one occupies the full interval
`N / 2 < k ≤ N`. Both existing coarse Selberg inequalities hold, with unchanged
constants, for the explicit `σ = 3 / 4` model whose centered variance diverges.
This is an input-boundary theorem, not a statement about the actual ψ remainder.
-/

open ArithmeticFunction MeasureTheory Finset Filter Topology
noncomputable section
namespace RHTower

/-- Error sequence of the comparison model, not the actual Chebyshev remainder. -/
def pmPowerRemainder (σ : ℝ) (N : ℕ) : ℝ := pmPowerModel σ (N : ℝ) - N

/-- Literal Selberg floor operator, with actual von Mangoldt weights. -/
def pmPowerSelbergResponse (σ : ℝ) (N : ℕ) : ℝ :=
  pmPowerRemainder σ N * Real.log N +
    ∑ k ∈ Icc 1 N, vonMangoldt k * pmPowerRemainder σ (N / k)

theorem pmPowerRemainder_eq {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    pmPowerRemainder σ N = (N : ℝ) ^ σ - 2 * (if N = 1 then 1 else 0) := by
  rcases N with _ | N
  · simp [pmPowerRemainder, pmPowerModel, Real.zero_rpow hσ.ne']
  rcases N with _ | N
  · norm_num [pmPowerRemainder, pmPowerModel]
  have hN : ¬((N + 1 + 1 : ℕ) : ℝ) ≤ 1 := by
    push_cast
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  rw [pmPowerRemainder, pmPowerModel, if_neg hN,
    if_neg (by omega : N + 1 + 1 ≠ 1)]
  ring

theorem abs_pmPowerRemainder_le (σ : ℝ) (N : ℕ) :
    |pmPowerRemainder σ N| ≤ (N : ℝ) ^ σ := by
  rcases N with _ | N
  · simpa [pmPowerRemainder, pmPowerModel] using Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 0) σ
  rcases N with _ | N
  · norm_num [pmPowerRemainder, pmPowerModel]
  have hN : ¬((N + 1 + 1 : ℕ) : ℝ) ≤ 1 := by
    push_cast
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  simp only [pmPowerRemainder, pmPowerModel, if_neg hN, add_sub_cancel_left,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) σ), le_refl]

/-- Altering the value at floor quotient one changes an entire half-interval of prime weights. -/
theorem pm_prime_floor_one_weight (N : ℕ) :
    (∑ k ∈ Icc 1 N, vonMangoldt k * (if N / k = 1 then (1 : ℝ) else 0)) =
      Chebyshev.psi (N : ℝ) - Chebyshev.psi ((N / 2 : ℕ) : ℝ) := by
  have hcut {k : ℕ} (hk : k ∈ Icc 1 N) : N / k = 1 ↔ N / 2 < k := by
    have hk0 : 0 < k := (mem_Icc.mp hk).1
    have hq1 : 1 ≤ N / k := (Nat.le_div_iff_mul_le hk0).mpr (by simpa using (mem_Icc.mp hk).2)
    have h1 : N / k < 2 ↔ N < 2 * k := Nat.div_lt_iff_lt_mul hk0
    have h2 : N / 2 < k ↔ N < k * 2 := Nat.div_lt_iff_lt_mul (by norm_num)
    rw [h2, mul_comm k 2]
    omega
  have hs : (∑ k ∈ Icc 1 N, vonMangoldt k * (if N / k = 1 then (1 : ℝ) else 0)) =
      ∑ k ∈ Ioc (N / 2) N, vonMangoldt k := by
    calc
      _ = ∑ k ∈ Icc 1 N, if N / 2 < k then vonMangoldt k else 0 := by
        apply sum_congr rfl
        intro k hk
        simp only [mul_ite, mul_one, mul_zero, hcut hk]
      _ = _ := by
        rw [← sum_filter]
        congr 1
        ext k
        simp only [mem_filter, mem_Icc, mem_Ioc]
        omega
  rw [hs]
  have hu := Finset.sum_union (f := fun k : ℕ => (vonMangoldt k : ℝ))
    (Finset.Ioc_disjoint_Ioc_of_le (a := 0) (d := N) (le_refl (N / 2)))
  rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (Nat.div_le_self N 2)] at hu
  simp only [Chebyshev.psi, Nat.floor_natCast]
  linarith only [hu]

theorem sum_pmPowerRemainder_floor {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    (∑ k ∈ Icc 1 N, vonMangoldt k * pmPowerRemainder σ (N / k)) =
      pmPrimeFloorPower σ N - 2 * (Chebyshev.psi (N : ℝ) - Chebyshev.psi ((N / 2 : ℕ) : ℝ)) := by
  rw [← pm_prime_floor_one_weight N, pmPrimeFloorPower, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  rw [pmPowerRemainder_eq hσ]
  ring

theorem pmPower_log_le {σ : ℝ} (hσ : σ < 1) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ σ * Real.log N ≤ (N : ℝ) / (1 - σ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hl := Real.log_le_rpow_div hn.le (sub_pos.mpr hσ)
  calc
    _ ≤ (N : ℝ) ^ σ * ((N : ℝ) ^ (1 - σ) / (1 - σ)) :=
      mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg hn.le σ)
    _ = _ := by
      rw [← mul_div_assoc, ← Real.rpow_add hn]
      simp

theorem abs_pmPowerSelbergResponse_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {N : ℕ} (hN : 1 ≤ N) : |pmPowerSelbergResponse σ N| ≤ 8 * N / (1 - σ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have ht := (div_le_iff₀ hn).mp (pmPrimeFloorPower_div_le hσ0 hσ1 N)
  calc
    _ ≤ |pmPowerRemainder σ N * Real.log N| +
        |∑ k ∈ Icc 1 N, vonMangoldt k * pmPowerRemainder σ (N / k)| := abs_add_le _ _
    _ ≤ (N : ℝ) ^ σ * Real.log N + pmPrimeFloorPower σ N := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg hlog]
        exact mul_le_mul_of_nonneg_right (abs_pmPowerRemainder_le σ N) hlog
      · apply le_trans (Finset.abs_sum_le_sum_abs _ _)
        apply sum_le_sum
        intro k _
        rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
        exact mul_le_mul_of_nonneg_left (abs_pmPowerRemainder_le σ (N / k)) vonMangoldt_nonneg
    _ ≤ (N : ℝ) / (1 - σ) + (7 / (1 - σ) * N) :=
      add_le_add (pmPower_log_le hσ1 hN) ht
    _ = _ := by ring

theorem pmPowerRemainder_selberg_recursion (N : ℕ) (hN : 1 ≤ N) :
    |pmPowerSelbergResponse (3 / 4) N| ≤ 400 * N := by
  have h := abs_pmPowerSelbergResponse_le (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num) hN
  norm_num at h
  linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

theorem tendsto_pmPowerRemainder_log_div {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Tendsto (fun N : ℕ => pmPowerRemainder σ N * Real.log N / (N : ℝ)) atTop (𝓝 0) := by
  have ht := (isLittleO_log_rpow_atTop (sub_pos.mpr hσ1)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp : (N : ℝ) ^ σ ≠ 0 := (Real.rpow_pos_of_pos hn σ).ne'
  simp only [Function.comp_apply]
  rw [pmPowerRemainder_eq hσ0, if_neg (by omega : N ≠ 1), mul_zero, sub_zero,
    Real.rpow_sub hn, Real.rpow_one]
  field_simp

theorem tendsto_pmPowerSelbergResponse_div {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Tendsto (fun N : ℕ => pmPowerSelbergResponse σ N / (N : ℝ)) atTop
      (𝓝 (pmPowerResponse σ - 1)) := by
  have h1 : Tendsto (fun N : ℕ => Chebyshev.psi (N : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
    simpa using pm_psi_dilated_limit (by norm_num : 0 < (1 : ℕ))
  have h2 := pm_psi_dilated_limit (by norm_num : 0 < (2 : ℕ))
  have ht := ((tendsto_pmPowerRemainder_log_div hσ0 hσ1).add
    (tendsto_pmPrimeFloorPower_div hσ0 hσ1)).sub ((h1.sub h2).const_mul 2)
  norm_num at ht
  apply ht.congr
  intro N
  rw [pmPowerSelbergResponse, sum_pmPowerRemainder_floor hσ0]
  ring


theorem pmPowerRemainder_log_sq_le {N : ℕ} (hN : 1 ≤ N) :
    |pmPowerRemainder (3 / 4) N| * Real.log N ^ 2 ≤ 64 * N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hl : Real.log (N : ℝ) ≤ 8 * (N : ℝ) ^ (1 / 8 : ℝ) := by
    calc
      _ ≤ (N : ℝ) ^ (1 / 8 : ℝ) / (1 / 8) := Real.log_le_rpow_div hn.le (by norm_num)
      _ = _ := by ring
  have hs : Real.log (N : ℝ) ^ 2 ≤ 64 * (N : ℝ) ^ (1 / 4 : ℝ) := by
    have hp : ((N : ℝ) ^ (1 / 8 : ℝ)) ^ 2 = (N : ℝ) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 8 : ℝ)) 2, ← Real.rpow_mul hn.le]
      norm_num
    calc
      _ ≤ (8 * (N : ℝ) ^ (1 / 8 : ℝ)) ^ 2 := pow_le_pow_left₀ hlog hl 2
      _ = _ := by rw [mul_pow, hp]; norm_num
  calc
    _ ≤ (N : ℝ) ^ (3 / 4 : ℝ) * (64 * (N : ℝ) ^ (1 / 4 : ℝ)) :=
      mul_le_mul (abs_pmPowerRemainder_le (3 / 4) N) hs (sq_nonneg _)
        (Real.rpow_nonneg hn.le _)
    _ = 64 * ((N : ℝ) ^ (3 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hn]; norm_num

theorem pmPowerRemainder_selberg_second (N : ℕ) (hN : 1 ≤ N) :
    |pmPowerRemainder (3 / 4) N| * Real.log N ^ 2 ≤
      (∑ m ∈ Icc 1 N, (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m) *
        |pmPowerRemainder (3 / 4) (N / m)|) + 800 * N * Real.log N + 2900 * N := by
  have hs : 0 ≤ ∑ m ∈ Icc 1 N,
      (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m) *
        |pmPowerRemainder (3 / 4) (N / m)| := by
    apply sum_nonneg
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
    exact mul_nonneg (add_nonneg (mul_nonneg vonMangoldt_nonneg (Real.log_nonneg hm1))
      (vonMangoldt_conv_nonneg m)) (abs_nonneg _)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have ht : 0 ≤ 800 * (N : ℝ) * Real.log N := by positivity
  have hb := pmPowerRemainder_log_sq_le hN
  linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

/-- Both existing coarse Selberg inequalities coexist with divergent canonical
variance for this explicit analytic comparison model. -/
theorem pmPowerModel_selberg_input_counterexample :
    (∀ N : ℕ, 1 ≤ N → |pmPowerSelbergResponse (3 / 4) N| ≤ 400 * N) ∧
    (∀ N : ℕ, 1 ≤ N →
      |pmPowerRemainder (3 / 4) N| * Real.log N ^ 2 ≤
        (∑ m ∈ Icc 1 N, (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m) *
          |pmPowerRemainder (3 / 4) (N / m)|) + 800 * N * Real.log N + 2900 * N) ∧
    (∀ B : ℝ → ℝ, Tendsto (fun R : ℝ =>
      (∫ x in Set.Ioo (0 : ℝ) R, (B R - pmPowerProfile (3 / 4) x) ^ 2) / Real.log R ^ 2)
        atTop atTop) := by
  exact ⟨pmPowerRemainder_selberg_recursion, pmPowerRemainder_selberg_second,
    fun B => tendsto_pmPowerProfile_scalar_error_div_log_sq (by norm_num) (by norm_num) B⟩

end RHTower
