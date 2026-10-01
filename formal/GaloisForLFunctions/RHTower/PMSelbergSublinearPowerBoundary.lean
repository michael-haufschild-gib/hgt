import GaloisForLFunctions.RHTower.PMScaledPowerVariance
import GaloisForLFunctions.RHTower.PMSelbergPowerInputBoundary

/-!
# Sublinear Selberg response can coexist with divergent canonical variance

The exact affine prime-weighted response is `c * Sσ - (1 + c) / 2`.
Its unique positive cancelling amplitude preserves the zero initial interval,
both unchanged-constant Selberg inequalities, and supercritical variance
divergence. The prime weights remain literal; the error sequence is an explicit
comparison model, not the actual Chebyshev remainder.
-/

open ArithmeticFunction MeasureTheory Finset Filter Topology
noncomputable section
namespace RHTower

def pmScaledPowerRemainder (σ c : ℝ) (N : ℕ) : ℝ := pmScaledPowerModel σ c (N : ℝ) - N

def pmScaledPowerSelbergResponse (σ c : ℝ) (N : ℕ) : ℝ :=
  pmScaledPowerRemainder σ c N * Real.log N +
    ∑ k ∈ Icc 1 N, vonMangoldt k * pmScaledPowerRemainder σ c (N / k)

theorem pmScaledPowerRemainder_eq (σ c : ℝ) (N : ℕ) :
    pmScaledPowerRemainder σ c N =
      c * pmPowerRemainder σ N + (c - 1) * (if N = 1 then 1 else 0) := by
  rcases N with _ | N
  · simp [pmScaledPowerRemainder, pmScaledPowerModel_eq, pmPowerRemainder, pmPowerModel]
  rcases N with _ | N
  · norm_num [pmScaledPowerRemainder, pmScaledPowerModel_eq, pmPowerRemainder, pmPowerModel]
    ring
  have hN : ¬((N + 1 + 1 : ℕ) : ℝ) ≤ 1 := by
    push_cast
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  rw [pmScaledPowerRemainder, pmScaledPowerModel_eq, if_neg hN, pmPowerRemainder,
    pmPowerModel, if_neg hN, if_neg (by omega : N + 1 + 1 ≠ 1)]
  ring

theorem abs_pmScaledPowerRemainder_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (σ : ℝ) (N : ℕ) :
    |pmScaledPowerRemainder σ c N| ≤ (N : ℝ) ^ σ :=
  (abs_pmScaledPowerModel_error_le hc0 hc1 (N : ℝ)).trans (abs_pmPowerRemainder_le σ N)

theorem pmScaledPowerSelbergResponse_eq (σ c : ℝ) (N : ℕ) :
    pmScaledPowerSelbergResponse σ c N = c * pmPowerSelbergResponse σ N +
      (c - 1) * (Chebyshev.psi (N : ℝ) - Chebyshev.psi ((N / 2 : ℕ) : ℝ)) := by
  have hlocal : (if N = 1 then (1 : ℝ) else 0) * Real.log N = 0 := by
    by_cases hN : N = 1 <;> simp [hN]
  rw [pmScaledPowerSelbergResponse, pmPowerSelbergResponse, ← pm_prime_floor_one_weight N,
    pmScaledPowerRemainder_eq]
  have hsum : (∑ k ∈ Icc 1 N, vonMangoldt k * pmScaledPowerRemainder σ c (N / k)) =
      c * (∑ k ∈ Icc 1 N, vonMangoldt k * pmPowerRemainder σ (N / k)) +
        (c - 1) * (∑ k ∈ Icc 1 N,
          vonMangoldt k * (if N / k = 1 then (1 : ℝ) else 0)) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    rw [pmScaledPowerRemainder_eq]
    ring
  rw [hsum, add_mul, mul_assoc (c - 1), hlocal, mul_zero, add_zero]
  ring

theorem tendsto_pmScaledPowerSelbergResponse_div {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (c : ℝ) :
    Tendsto (fun N : ℕ => pmScaledPowerSelbergResponse σ c N / (N : ℝ)) atTop
      (𝓝 (c * pmPowerResponse σ - (1 + c) / 2)) := by
  have h1 : Tendsto (fun N : ℕ => Chebyshev.psi (N : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
    simpa using pm_psi_dilated_limit (by norm_num : 0 < (1 : ℕ))
  have h2 := pm_psi_dilated_limit (by norm_num : 0 < (2 : ℕ))
  have ht := ((tendsto_pmPowerSelbergResponse_div hσ0 hσ1).const_mul c).add
    ((h1.sub h2).const_mul (c - 1))
  simp only [Nat.cast_ofNat] at ht
  have he : c * (pmPowerResponse σ - 1) + (c - 1) * (1 - 1 / 2) =
      c * pmPowerResponse σ - (1 + c) / 2 := by ring
  rw [he] at ht
  apply ht.congr
  intro N
  rw [pmScaledPowerSelbergResponse_eq]
  ring

theorem pmScaledPowerSelbergResponse_sublinear_iff {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (c : ℝ) :
    Tendsto (fun N : ℕ => pmScaledPowerSelbergResponse σ c N / (N : ℝ)) atTop (𝓝 0) ↔
      c = pmCancellingPowerAmplitude σ := by
  constructor
  · intro h
    exact (pmPower_affine_response_zero_iff hσ0 hσ1 c).mp
      (tendsto_nhds_unique (tendsto_pmScaledPowerSelbergResponse_div hσ0 hσ1 c) h)
  · intro h
    have he := (pmPower_affine_response_zero_iff hσ0 hσ1 c).mpr h
    simpa only [he] using tendsto_pmScaledPowerSelbergResponse_div hσ0 hσ1 c

theorem abs_pmScaledPowerSelbergResponse_le {σ c : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    |pmScaledPowerSelbergResponse σ c N| ≤ 8 * N / (1 - σ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have ht := (div_le_iff₀ hn).mp (pmPrimeFloorPower_div_le hσ0 hσ1 N)
  calc
    _ ≤ |pmScaledPowerRemainder σ c N * Real.log N| +
        |∑ k ∈ Icc 1 N, vonMangoldt k * pmScaledPowerRemainder σ c (N / k)| := abs_add_le _ _
    _ ≤ (N : ℝ) ^ σ * Real.log N + pmPrimeFloorPower σ N := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg hlog]
        exact mul_le_mul_of_nonneg_right (abs_pmScaledPowerRemainder_le hc0 hc1 σ N) hlog
      · apply le_trans (Finset.abs_sum_le_sum_abs _ _)
        apply sum_le_sum
        intro k _
        rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
        exact mul_le_mul_of_nonneg_left (abs_pmScaledPowerRemainder_le hc0 hc1 σ (N / k))
          vonMangoldt_nonneg
    _ ≤ (N : ℝ) / (1 - σ) + (7 / (1 - σ) * N) := add_le_add (pmPower_log_le hσ1 hN) ht
    _ = _ := by ring

theorem pmCancellingPower_selberg_recursion (N : ℕ) (hN : 1 ≤ N) :
    |pmScaledPowerSelbergResponse (3 / 4) (pmCancellingPowerAmplitude (3 / 4)) N| ≤ 400 * N := by
  have hc := pmCancellingPowerAmplitude_bounds (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num)
  have h := abs_pmScaledPowerSelbergResponse_le (by norm_num : (0 : ℝ) < 3 / 4)
    (by norm_num) hc.1.le hc.2.le hN
  norm_num at h
  linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

theorem pmCancellingPower_selberg_second (N : ℕ) (hN : 1 ≤ N) :
    |pmScaledPowerRemainder (3 / 4) (pmCancellingPowerAmplitude (3 / 4)) N| * Real.log N ^ 2 ≤
      (∑ m ∈ Icc 1 N, (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m) *
        |pmScaledPowerRemainder (3 / 4) (pmCancellingPowerAmplitude (3 / 4)) (N / m)|) +
          800 * N * Real.log N + 2900 * N := by
  have hc := pmCancellingPowerAmplitude_bounds (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num)
  have hb := (mul_le_mul_of_nonneg_right
    (abs_pmScaledPowerModel_error_le hc.1.le hc.2.le (N : ℝ)) (sq_nonneg (Real.log N))).trans
      (pmPowerRemainder_log_sq_le hN)
  change |pmScaledPowerRemainder (3 / 4) (pmCancellingPowerAmplitude (3 / 4)) N| *
    Real.log N ^ 2 ≤ 64 * N at hb
  have hs : 0 ≤ ∑ m ∈ Icc 1 N,
      (vonMangoldt m * Real.log m + (vonMangoldt * vonMangoldt) m) *
        |pmScaledPowerRemainder (3 / 4) (pmCancellingPowerAmplitude (3 / 4)) (N / m)| := by
    apply sum_nonneg
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
    exact mul_nonneg (add_nonneg (mul_nonneg vonMangoldt_nonneg (Real.log_nonneg hm1))
      (vonMangoldt_conv_nonneg m)) (abs_nonneg _)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have ht : 0 ≤ 800 * (N : ℝ) * Real.log N := by positivity
  linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

theorem exists_pm_positive_amplitude_sublinear_response_divergent_variance :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
      Tendsto (fun N : ℕ => pmScaledPowerSelbergResponse (3 / 4) c N / (N : ℝ)) atTop (𝓝 0) ∧
      (∀ B : ℝ → ℝ, Tendsto (fun R : ℝ =>
        (∫ x in Set.Ioo (0 : ℝ) R, (B R - pmScaledPowerProfile (3 / 4) c x) ^ 2) /
          Real.log R ^ 2) atTop atTop) := by
  have hc := pmCancellingPowerAmplitude_bounds (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num)
  refine ⟨pmCancellingPowerAmplitude (3 / 4), hc.1, hc.2, ?_, ?_⟩
  · exact (pmScaledPowerSelbergResponse_sublinear_iff (by norm_num) (by norm_num) _).mpr rfl
  · intro B
    exact tendsto_pmScaledPowerProfile_error_div_log_sq (by norm_num) (by norm_num) hc.1 hc.2.le B

end RHTower
