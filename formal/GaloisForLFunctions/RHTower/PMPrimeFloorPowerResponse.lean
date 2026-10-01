import GaloisForLFunctions.RHTower.PMPowerIncrementSeries
import GaloisForLFunctions.RHTower.DirichletSummatorySwap
import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Exact response of the prime-weighted floor operator to a power

Finite Dirichlet hyperbola interchange retains the actual von Mangoldt weights.
The increment majorant bounds the normalized operator by `7/(1-σ)`. Actual PNT
and dominated convergence identify its limit with the positive response series.
No estimate for the actual Chebyshev remainder is inferred from this comparison.
-/

open ArithmeticFunction MeasureTheory Finset Filter Topology
noncomputable section
namespace RHTower

def pmPowerIncrementAF (σ : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else pmPowerIncrement σ (n - 1), by simp⟩

theorem pmPowerIncrementAF_apply (σ : ℝ) (n : ℕ) :
    pmPowerIncrementAF σ n = if n = 0 then 0 else pmPowerIncrement σ (n - 1) := rfl

theorem pmPowerIncrementAF_succ (σ : ℝ) (n : ℕ) :
    pmPowerIncrementAF σ (n + 1) = pmPowerIncrement σ n := by
  rw [pmPowerIncrementAF_apply]
  simp

def pmPrimeFloorPower (σ : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 N, vonMangoldt k * ((N / k : ℕ) : ℝ) ^ σ

theorem sum_pmPowerIncrementAF {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    (∑ j ∈ Icc 1 N, pmPowerIncrementAF σ j) = (N : ℝ) ^ σ := by
  induction N with
  | zero => simp [Real.zero_rpow hσ.ne']
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    rw [pmPowerIncrementAF_succ, pmPowerIncrement, Nat.cast_add, Nat.cast_one]
    ring

theorem pmPrimeFloorPower_eq_hyperbola {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    pmPrimeFloorPower σ N = ∑ j ∈ Icc 1 N,
      pmPowerIncrement σ (j - 1) * Chebyshev.psi ((N / j : ℕ) : ℝ) := by
  rw [pmPrimeFloorPower]
  simp_rw [← sum_pmPowerIncrementAF hσ]
  rw [← sum_Icc_mul_apply vonMangoldt (pmPowerIncrementAF σ), mul_comm, sum_Icc_mul_apply]
  apply sum_congr rfl
  intro j hj
  have hj0 : j ≠ 0 := by have := (mem_Icc.mp hj).1; omega
  simp only [pmPowerIncrementAF_apply, hj0, if_false, Chebyshev.psi,
    Nat.floor_natCast, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]

theorem pmPowerIncrementKernel_sum_shift (σ : ℝ) (N : ℕ) :
    (∑ j ∈ Icc 1 N, pmPowerIncrement σ (j - 1) / (j : ℝ)) =
      ∑ n ∈ range N, pmPowerIncrementKernel σ n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pmPowerIncrementKernel]

theorem pm_psi_natCast_le_seven (N : ℕ) : Chebyshev.psi (N : ℝ) ≤ 7 * N := by
  have hp := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N)
  have hl : Real.log 4 ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  exact hp.trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg N))

theorem pm_psi_dilated_bound (N d : ℕ) (hd : 0 < d) :
    Chebyshev.psi ((N / d : ℕ) : ℝ) / (N : ℝ) ≤ 7 / (d : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simpa using (div_nonneg (by norm_num : (0 : ℝ) ≤ 7) (Nat.cast_nonneg d))
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hq : ((N / d : ℕ) : ℝ) * (d : ℝ) ≤ N := by exact_mod_cast Nat.div_mul_le_self N d
  calc
    _ ≤ 7 * ((N / d : ℕ) : ℝ) / N :=
      div_le_div_of_nonneg_right (pm_psi_natCast_le_seven _) hNr.le
    _ ≤ _ := by
      apply (div_le_div_iff₀ hNr hdr).mpr
      linarith

theorem pmPrimeFloorPower_nonneg {σ : ℝ} (N : ℕ) : 0 ≤ pmPrimeFloorPower σ N := by
  apply sum_nonneg
  intro k _
  exact mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem pmPrimeFloorPower_div_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (N : ℕ) :
    pmPrimeFloorPower σ N / (N : ℝ) ≤ 7 / (1 - σ) := by
  rw [pmPrimeFloorPower_eq_hyperbola hσ0 N, sum_div]
  calc
    _ ≤ ∑ j ∈ Icc 1 N, 7 * (pmPowerIncrement σ (j - 1) / (j : ℝ)) := by
      apply sum_le_sum
      intro j hj
      have hd : 0 < j := (mem_Icc.mp hj).1
      have h := mul_le_mul_of_nonneg_left (pm_psi_dilated_bound N j hd)
        (pmPowerIncrement_nonneg hσ0.le (j - 1))
      convert h using 1 <;> ring
    _ = 7 * ∑ n ∈ range N, pmPowerIncrementKernel σ n := by
      rw [← mul_sum, pmPowerIncrementKernel_sum_shift]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (sum_pmPowerIncrementKernel_le hσ0 hσ1 N)
        (by norm_num : (0 : ℝ) ≤ 7)
      simpa only [mul_one_div] using h

theorem pm_psi_dilated_limit {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => Chebyshev.psi ((N / d : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 (1 / (d : ℝ))) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hscale : Tendsto (fun N : ℕ => (N : ℝ) / d) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const hdr
  have ht := (tendsto_psi_div_self.comp hscale).div_const (d : ℝ)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have he : Chebyshev.psi ((N / d : ℕ) : ℝ) = Chebyshev.psi ((N : ℝ) / d) := by
    simp only [Chebyshev.psi, Nat.floor_natCast, Nat.floor_div_natCast]
  rw [he]
  simp only [Function.comp_apply]
  field_simp

theorem pmPrimeFloorPower_eq_tsum {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    pmPrimeFloorPower σ N / (N : ℝ) = ∑' n : ℕ,
      pmPowerIncrement σ n * (Chebyshev.psi ((N / (n + 1) : ℕ) : ℝ) / (N : ℝ)) := by
  rw [tsum_eq_sum (s := range N)]
  · rw [pmPrimeFloorPower_eq_hyperbola hσ N, sum_div]
    have hshift : (∑ j ∈ Icc 1 N,
        pmPowerIncrement σ (j - 1) * Chebyshev.psi ((N / j : ℕ) : ℝ) / (N : ℝ)) =
        ∑ n ∈ range N, pmPowerIncrement σ n *
          (Chebyshev.psi ((N / (n + 1) : ℕ) : ℝ) / (N : ℝ)) := by
      have hgen (M : ℕ) : (∑ j ∈ Icc 1 M,
          pmPowerIncrement σ (j - 1) * Chebyshev.psi ((N / j : ℕ) : ℝ) / (N : ℝ)) =
          ∑ n ∈ range M, pmPowerIncrement σ n *
            (Chebyshev.psi ((N / (n + 1) : ℕ) : ℝ) / (N : ℝ)) := by
        induction M with
        | zero => simp
        | succ M ih =>
          rw [sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih, Nat.add_sub_cancel]
          ring
      exact hgen N
    exact hshift
  · intro n hn
    have hdiv : N / (n + 1) = 0 := Nat.div_eq_of_lt (by simp only [Finset.mem_range, not_lt] at hn; omega)
    simp [hdiv]

theorem tendsto_pmPrimeFloorPower_div {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Tendsto (fun N : ℕ => pmPrimeFloorPower σ N / (N : ℝ)) atTop (𝓝 (pmPowerResponse σ)) := by
  have hrow (n : ℕ) : Tendsto (fun N : ℕ => pmPowerIncrement σ n *
      (Chebyshev.psi ((N / (n + 1) : ℕ) : ℝ) / (N : ℝ))) atTop
        (𝓝 (pmPowerIncrementKernel σ n)) := by
    simpa only [pmPowerIncrementKernel, Nat.cast_add, Nat.cast_one, mul_one_div] using
      (pm_psi_dilated_limit (by omega : 0 < n + 1)).const_mul (pmPowerIncrement σ n)
  have hdom : ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      ‖pmPowerIncrement σ n * (Chebyshev.psi ((N / (n + 1) : ℕ) : ℝ) / (N : ℝ))‖ ≤
        7 * pmPowerIncrementKernel σ n := by
    filter_upwards with N n
    have hn := pmPowerIncrement_nonneg hσ0.le n
    have hp := div_nonneg (Chebyshev.psi_nonneg ((N / (n + 1) : ℕ) : ℝ)) (Nat.cast_nonneg N)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hn hp)]
    have h := mul_le_mul_of_nonneg_left (pm_psi_dilated_bound N (n + 1) (by omega)) hn
    calc
      _ ≤ pmPowerIncrement σ n * (7 / ((n : ℝ) + 1)) := by
        simpa only [Nat.cast_add, Nat.cast_one] using h
      _ = _ := by rw [pmPowerIncrementKernel]; ring
  have ht := tendsto_tsum_of_dominated_convergence
    ((summable_pmPowerIncrementKernel hσ0 hσ1).mul_left 7) hrow hdom
  exact ht.congr (fun N => (pmPrimeFloorPower_eq_tsum hσ0 N).symm)

end RHTower
