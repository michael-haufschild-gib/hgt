import GaloisForLFunctions.RHTower.DQPTPartialSumRate
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound

/-!
# DQPT: the partition function of the logarithmic spectrum

**Supplementary Note 2** of arXiv:2511.11199 (published Supplementary Note 2) studies

`Z(β, H₀) = ∑_{n=1}^N n^{−β}`,

the partition function of the Hamiltonian `H₀ = ∑ log(n)|n⟩⟨n|`, and proves

* `β > 1`: `Z → ζ(β)` and `−(1/log₂N) ln Z → 0`;
* `0 < β < 1`: `((N+1)^{1−β} − 1)/(1−β) ≤ Z ≤ 1 + (N^{1−β} − 1)/(1−β)` and
  `−(1/log₂N) ln Z → (β−1) ln 2`.

Main results:
* `dqptPartition_integral_bounds` — **Supplementary Note 2 (2.5)**;
* `dqptPartition_tendsto_zeta` — **Supplementary Note 2 (2.2)**;
* `dqpt_partition_rate_lt_one`, `dqpt_partition_rate_gt_one` — **Supplementary Note 2 (2.7)**.
-/

namespace RHTower.DQPT

open Complex Filter Topology Set

noncomputable section

/-- `Z(β, H₀) = ∑_{n=1}^N n^{−β}`. -/
def dqptPartition (β : ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-β)

theorem dqptPartition_nonneg (β : ℝ) (N : ℕ) : 0 ≤ dqptPartition β N :=
  Finset.sum_nonneg fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _

/-! ## The elementary two-sided bounds -/

/-- `N^{1−β} ≤ Z(β, H₀)`: every one of the `N` terms is at least `N^{−β}`. -/
theorem dqptPartition_rpow_le {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (1 - β) ≤ dqptPartition β N := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hterm : ∀ n ∈ Finset.Icc 1 N, (N : ℝ) ^ (-β) ≤ (n : ℝ) ^ (-β) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
    exact Real.rpow_le_rpow_of_nonpos hn0 hnN (by linarith)
  have hcard : (Finset.Icc 1 N).card = N := by simp
  have hsum : ((N : ℕ) : ℝ) * (N : ℝ) ^ (-β) ≤ dqptPartition β N := by
    rw [dqptPartition]
    calc ((N : ℕ) : ℝ) * (N : ℝ) ^ (-β)
        = ∑ _n ∈ Finset.Icc 1 N, (N : ℝ) ^ (-β) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
      _ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-β) := Finset.sum_le_sum hterm
  have hsplit : (N : ℝ) ^ (1 - β) = (N : ℝ) * (N : ℝ) ^ (-β) := by
    rw [show (1 - β : ℝ) = 1 + (-β) by ring, Real.rpow_add hN0, Real.rpow_one]
  rw [hsplit]
  exact hsum

/-- **Supplementary Note 2 (2.5), lower half.**  `((N+1)^{1−β} − 1)/(1−β) ≤ Z(β, H₀)`. -/
theorem dqptPartition_integral_lower {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (N : ℕ) :
    (((N : ℝ) + 1) ^ (1 - β) - 1) / (1 - β) ≤ dqptPartition β N := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-β)) (Set.Icc ((1 : ℕ) : ℝ) ((N + 1 : ℕ) : ℝ)) :=
    RHTower.Sieve.antitoneOn_rpow_neg (le_of_lt hβ) 1 (N + 1) (le_refl 1)
  have hle : (1 : ℕ) ≤ N + 1 := by omega
  have hcomp := hanti.integral_le_sum_Ico hle
  have hint : (∫ x in ((1 : ℕ) : ℝ)..((N + 1 : ℕ) : ℝ), x ^ (-β))
      = (((N : ℝ) + 1) ^ (1 - β) - 1) / (1 - β) := by
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -β))]
    have hexp : -β + 1 = 1 - β := by ring
    rw [hexp]
    norm_num
  rw [hint] at hcomp
  refine hcomp.trans (le_of_eq ?_)
  rw [dqptPartition, Finset.Ico_add_one_right_eq_Icc]

/-- **Supplementary Note 2 (2.5), upper half.**  `Z(β, H₀) ≤ 1 + (N^{1−β} − 1)/(1−β)`. -/
theorem dqptPartition_integral_upper {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) {N : ℕ} (hN : 1 ≤ N) :
    dqptPartition β N ≤ 1 + ((N : ℝ) ^ (1 - β) - 1) / (1 - β) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-β)) (Set.Icc ((1 : ℕ) : ℝ) ((N : ℕ) : ℝ)) :=
    RHTower.Sieve.antitoneOn_rpow_neg (le_of_lt hβ) 1 N (le_refl 1)
  have hcomp := hanti.sum_le_integral_Ico hN
  have hint : (∫ x in ((1 : ℕ) : ℝ)..((N : ℕ) : ℝ), x ^ (-β))
      = ((N : ℝ) ^ (1 - β) - 1) / (1 - β) := by
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -β))]
    have hexp : -β + 1 = 1 - β := by ring
    rw [hexp]
    norm_num
  rw [hint] at hcomp
  have hreindex : ∑ i ∈ Finset.Ico 1 N, ((i + 1 : ℕ) : ℝ) ^ (-β)
      = ∑ k ∈ Finset.Ico 2 (N + 1), (k : ℝ) ^ (-β) :=
    Finset.sum_Ico_add' (fun k : ℕ => (k : ℝ) ^ (-β)) 1 N 1
  have hsplit : dqptPartition β N
      = (1 : ℝ) ^ (-β) + ∑ k ∈ Finset.Ico 2 (N + 1), (k : ℝ) ^ (-β) := by
    rw [dqptPartition, ← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < N + 1)]
    norm_num
  rw [hsplit, Real.one_rpow, ← hreindex]
  have : ∑ i ∈ Finset.Ico 1 N, ((i + 1 : ℕ) : ℝ) ^ (-β)
      ≤ ((N : ℝ) ^ (1 - β) - 1) / (1 - β) := by
    refine le_trans (le_of_eq ?_) hcomp
    rfl
  linarith

/-! ## The `β > 1` regime -/

theorem dqpt_summable_rpow {β : ℝ} (hβ : 1 < β) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-β)) := by
  have h2 := (summable_nat_add_iff 1).mpr
    (Real.summable_nat_rpow.mpr (show -β < -1 by linarith))
  refine h2.congr (fun n => ?_)
  push_cast; ring_nf

theorem dqptPartition_eq_sum_range (β : ℝ) (N : ℕ) :
    dqptPartition β N = ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-β) := by
  rw [dqptPartition, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  push_cast
  ring_nf

/-- The partition function is at least its first term. -/
theorem one_le_dqptPartition (β : ℝ) {N : ℕ} (hN : 1 ≤ N) : 1 ≤ dqptPartition β N := by
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 N := by
    rw [Finset.mem_Icc]; exact ⟨le_refl 1, hN⟩
  have hle := Finset.single_le_sum
    (f := fun n : ℕ => (n : ℝ) ^ (-β))
    (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) hmem
  rw [dqptPartition]
  simpa using hle

theorem dqptPartition_le_tsum {β : ℝ} (hβ : 1 < β) (N : ℕ) :
    dqptPartition β N ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-β) := by
  rw [dqptPartition_eq_sum_range]
  exact Summable.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (by positivity) _)
    (dqpt_summable_rpow hβ)

theorem dqptPartition_tendsto_tsum {β : ℝ} (hβ : 1 < β) :
    Tendsto (dqptPartition β) atTop (𝓝 (∑' n : ℕ, ((n : ℝ) + 1) ^ (-β))) := by
  refine Tendsto.congr (fun N => (dqptPartition_eq_sum_range β N).symm) ?_
  exact (dqpt_summable_rpow hβ).hasSum.tendsto_sum_nat

/-- **Supplementary Note 2 (2.2).**  For `β > 1` the partition function converges to `ζ(β)`. -/
theorem dqptPartition_tendsto_zeta {β : ℝ} (hβ : 1 < β) :
    Tendsto (fun N : ℕ => ((dqptPartition β N : ℝ) : ℂ)) atTop (𝓝 (riemannZeta (β : ℂ))) := by
  have hre : ((β : ℂ)).re = β := Complex.ofReal_re β
  have hzeta : riemannZeta (β : ℂ) = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (β : ℂ) :=
    zeta_eq_tsum_one_div_nat_add_one_cpow (by rw [hre]; exact hβ)
  have hterm : ∀ n : ℕ, ((((n : ℝ) + 1) ^ (-β) : ℝ) : ℂ) = 1 / ((n : ℂ) + 1) ^ (β : ℂ) := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, ← Complex.ofReal_cpow (le_of_lt hpos)]
    rw [← Complex.ofReal_one, ← Complex.ofReal_div]
    congr 1
    rw [Real.rpow_neg (le_of_lt hpos), one_div]
  have htsum : ((∑' n : ℕ, ((n : ℝ) + 1) ^ (-β) : ℝ) : ℂ) = riemannZeta (β : ℂ) := by
    rw [hzeta, ← tsum_congr hterm]
    exact Complex.ofReal_tsum _
  rw [← htsum]
  exact (Complex.continuous_ofReal.tendsto _).comp (dqptPartition_tendsto_tsum hβ)

/-! ## Supplementary Note 2 (2.7): the logarithmic rate -/

/-- **Case `0 < β < 1`.**  `−(1/log₂N) ln Z(β, H₀) → (β − 1) ln 2`. -/
theorem dqpt_partition_rate_lt_one {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun N : ℕ => -Real.log (dqptPartition β N) / Real.logb 2 (N : ℝ)) atTop
      (𝓝 ((β - 1) * Real.log 2)) := by
  have hc₂ : (0 : ℝ) < 1 + 1 / (1 - β) := by
    have : (0 : ℝ) < 1 - β := by linarith
    positivity
  refine dqpt_tendsto_neg_log_div_logb (a := β - 1) (c₁ := 1) (c₂ := 1 + 1 / (1 - β))
    one_pos hc₂ ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hexp : (-(β - 1) : ℝ) = 1 - β := by ring
    rw [hexp, one_mul]
    exact dqptPartition_rpow_le (le_of_lt hβ) hN
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hexp : (-(β - 1) : ℝ) = 1 - β := by ring
    rw [hexp]
    have hpow : (1 : ℝ) ≤ (N : ℝ) ^ (1 - β) :=
      Real.one_le_rpow hN1 (by linarith)
    have hupper := dqptPartition_integral_upper hβ hβ1 hN
    have hb : (0 : ℝ) < 1 - β := by linarith
    have hkey : 1 + ((N : ℝ) ^ (1 - β) - 1) / (1 - β) ≤ (1 + 1 / (1 - β)) * (N : ℝ) ^ (1 - β) := by
      rw [add_mul, one_mul, one_div, inv_mul_eq_div]
      have hmono : ((N : ℝ) ^ (1 - β) - 1) / (1 - β) ≤ (N : ℝ) ^ (1 - β) / (1 - β) :=
        (div_le_div_iff_of_pos_right hb).mpr (by linarith)
      linarith
    exact hupper.trans hkey

/-- **Case `β > 1`.**  `−(1/log₂N) ln Z(β, H₀) → 0`. -/
theorem dqpt_partition_rate_gt_one {β : ℝ} (hβ : 1 < β) :
    Tendsto (fun N : ℕ => -Real.log (dqptPartition β N) / Real.logb 2 (N : ℝ)) atTop (𝓝 0) := by
  have hpos : (0 : ℝ) < ∑' n : ℕ, ((n : ℝ) + 1) ^ (-β) := by
    refine (dqpt_summable_rpow hβ).tsum_pos (fun n => Real.rpow_nonneg (by positivity) _) 0 ?_
    have : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
    rw [this, Real.one_rpow]
    norm_num
  have hlim := dqpt_tendsto_neg_log_div_logb (u := dqptPartition β) (a := 0) (c₁ := 1)
    (c₂ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-β)) one_pos hpos ?_ ?_
  · simpa using hlim
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hone : (1 : ℝ) * (N : ℝ) ^ (-(0 : ℝ)) = 1 := by
      rw [neg_zero, Real.rpow_zero, mul_one]
    rw [hone]
    exact one_le_dqptPartition β hN
  · filter_upwards with N
    have hone : (N : ℝ) ^ (-(0 : ℝ)) = 1 := by
      rw [neg_zero, Real.rpow_zero]
    rw [hone, mul_one]
    exact dqptPartition_le_tsum hβ N

end

end RHTower.DQPT
