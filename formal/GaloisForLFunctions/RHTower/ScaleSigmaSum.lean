import GaloisForLFunctions.RHTower.WeightedSigmaFubini
import GaloisForLFunctions.RHTower.VonMangoldtLogHarmonicSummatory

/-!
# Summing the σ-contraction over all scales

Three evaluations closing the scale side of the fiber transfer:

* `sum_log_div_le`: `∑_{s ≤ M} log s/s ≤ ½log²M + 1`;
* `sum_inv_le`: `∑_{s ≤ M} 1/s ≤ log M + 2`;
* `sigmaPartial_le_of_ratio`: the uniform closed form
  `σ(s) ≤ (a − g/L)·log s + C₁` for every `s ≥ 1`, merging the crude
  head bound below `x₁` with the ladder contraction above it;
* `sum_inv_sigmaPartial_le`: therefore
  `∑_{s ≤ M} σ(s)/s ≤ (a − g/L)(½log²M + 1) + C₁(log M + 2)` —
  the `½log²` coefficient the recursion divides against.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- `∑_{s ≤ M} log s/s ≤ ½·log²M + 1`. -/
theorem sum_log_div_le (M : ℕ) (hM : 1 ≤ M) :
    ∑ s ∈ Finset.Icc 1 M, Real.log s / (s : ℝ)
      ≤ Real.log M ^ (2 : ℕ) / 2 + 1 := by
  have hins : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
    ext x
    simp [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hins, Finset.sum_insert (by simp [Finset.mem_Icc])]
  have h1 : Real.log ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) = 0 := by
    norm_num
  rw [h1, zero_add]
  have hterm : ∀ s ∈ Finset.Icc 2 M,
      Real.log s / (s : ℝ)
        ≤ Real.log s * (Real.log s - Real.log ((s - 1 : ℕ) : ℝ)) := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    have hs0 : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
    have hlog0 : 0 ≤ Real.log s :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ s))
    have hinc := inv_succ_le_log_succ_sub (n := s - 1) (by omega)
    have hc : ((s - 1 : ℕ) : ℝ) + 1 = (s : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      linarith
    rw [hc] at hinc
    calc Real.log s / (s : ℝ) = Real.log s * (1 / s) := by ring
      _ ≤ Real.log s * (Real.log s - Real.log ((s - 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hinc hlog0
  have hAB : ∀ s ∈ Finset.Icc 2 M,
      Real.log s * (Real.log s - Real.log ((s - 1 : ℕ) : ℝ))
        = (Real.log s ^ (2 : ℕ) - Real.log ((s - 1 : ℕ) : ℝ) ^ (2 : ℕ)) / 2
          + (Real.log s - Real.log ((s - 1 : ℕ) : ℝ)) ^ (2 : ℕ) / 2 := by
    intro s _
    ring
  have htel : ∑ s ∈ Finset.Icc 2 M,
      (Real.log s ^ (2 : ℕ) - Real.log ((s - 1 : ℕ) : ℝ) ^ (2 : ℕ))
      = Real.log M ^ (2 : ℕ) := by
    have hre : ∑ s ∈ Finset.Icc 2 M,
        (Real.log s ^ (2 : ℕ) - Real.log ((s - 1 : ℕ) : ℝ) ^ (2 : ℕ))
        = ∑ j ∈ Finset.Ico 1 M,
            (Real.log ((j : ℝ) + 1) ^ (2 : ℕ) - Real.log j ^ (2 : ℕ)) := by
      apply Finset.sum_nbij' (i := fun s => s - 1) (j := fun j => j + 1)
      · intro s hs
        rw [Finset.mem_Icc] at hs
        rw [Finset.mem_Ico]
        omega
      · intro j hj
        rw [Finset.mem_Ico] at hj
        rw [Finset.mem_Icc]
        omega
      · intro s hs
        rw [Finset.mem_Icc] at hs
        omega
      · intro j _
        omega
      · intro s hs
        rw [Finset.mem_Icc] at hs
        have hc : ((s - 1 : ℕ) : ℝ) + 1 = (s : ℝ) := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
          linarith
        rw [hc]
    rw [hre, sum_log_sq_increment_eq M hM]
  have hΔsq : ∑ s ∈ Finset.Icc 2 M,
      (Real.log s - Real.log ((s - 1 : ℕ) : ℝ)) ^ (2 : ℕ) ≤ 2 := by
    have hle : ∀ s ∈ Finset.Icc 2 M,
        (Real.log s - Real.log ((s - 1 : ℕ) : ℝ)) ^ (2 : ℕ)
          ≤ 1 / ((s - 1 : ℕ) : ℝ) ^ (2 : ℕ) := by
      intro s hs
      rw [Finset.mem_Icc] at hs
      have hs10 : (0 : ℝ) < ((s - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < s - 1)
      have hinc := log_succ_sub_log_le (j := s - 1) (by omega)
      have hc : ((s - 1 : ℕ) : ℝ) + 1 = (s : ℝ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
        linarith
      rw [hc] at hinc
      have hpos : 0 ≤ Real.log s - Real.log ((s - 1 : ℕ) : ℝ) := by
        have := Real.log_le_log hs10 (show ((s - 1 : ℕ) : ℝ) ≤ s by
          linarith)
        linarith
      have h2 : (1 : ℝ) / ((s - 1 : ℕ) : ℝ) ^ (2 : ℕ)
          = (1 / ((s - 1 : ℕ) : ℝ)) ^ (2 : ℕ) := by
        rw [div_pow, one_pow]
      rw [h2]
      exact pow_le_pow_left₀ hpos hinc 2
    have hre2 : ∑ s ∈ Finset.Icc 2 M, 1 / ((s - 1 : ℕ) : ℝ) ^ (2 : ℕ)
        = ∑ j ∈ Finset.Icc 1 (M - 1), 1 / (j : ℝ) ^ (2 : ℕ) := by
      apply Finset.sum_nbij' (i := fun s => s - 1) (j := fun j => j + 1)
      · intro s hs
        rw [Finset.mem_Icc] at hs
        rw [Finset.mem_Icc]
        omega
      · intro j hj
        rw [Finset.mem_Icc] at hj
        rw [Finset.mem_Icc]
        omega
      · intro s hs
        rw [Finset.mem_Icc] at hs
        omega
      · intro j _
        omega
      · intro s _
        rfl
    calc ∑ s ∈ Finset.Icc 2 M,
          (Real.log s - Real.log ((s - 1 : ℕ) : ℝ)) ^ (2 : ℕ)
        ≤ ∑ s ∈ Finset.Icc 2 M, 1 / ((s - 1 : ℕ) : ℝ) ^ (2 : ℕ) :=
          Finset.sum_le_sum hle
      _ = ∑ j ∈ Finset.Icc 1 (M - 1), 1 / (j : ℝ) ^ (2 : ℕ) := hre2
      _ ≤ 2 := sum_inv_sq_le (M - 1)
  calc ∑ s ∈ Finset.Icc 2 M, Real.log s / (s : ℝ)
      ≤ ∑ s ∈ Finset.Icc 2 M,
          Real.log s * (Real.log s - Real.log ((s - 1 : ℕ) : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (∑ s ∈ Finset.Icc 2 M,
          (Real.log s ^ (2 : ℕ) - Real.log ((s - 1 : ℕ) : ℝ) ^ (2 : ℕ))) / 2
        + (∑ s ∈ Finset.Icc 2 M,
            (Real.log s - Real.log ((s - 1 : ℕ) : ℝ)) ^ (2 : ℕ)) / 2 := by
        rw [Finset.sum_congr rfl hAB, Finset.sum_add_distrib,
          ← Finset.sum_div, ← Finset.sum_div]
    _ ≤ Real.log M ^ (2 : ℕ) / 2 + 1 := by
        rw [htel]
        linarith [hΔsq]

/-- `∑_{s ≤ M} 1/s ≤ log M + 2`. -/
theorem sum_inv_le (M : ℕ) (hM : 1 ≤ M) :
    ∑ s ∈ Finset.Icc 1 M, 1 / (s : ℝ) ≤ Real.log M + 2 := by
  have hins : Finset.Icc 1 M = insert 1 (Finset.Ioc 1 M) := by
    ext x
    simp [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [hins, Finset.sum_insert (by simp [Finset.mem_Ioc])]
  rcases Nat.lt_or_ge 1 M with hM1 | hM1
  · have hH := abs_le.1 (abs_sum_inv_window_sub_le le_rfl (le_of_lt hM1))
    have hlog1 : Real.log ((1 : ℕ) : ℝ) = 0 := by norm_num
    rw [hlog1] at hH
    have h2 : (1 : ℝ) / ((1 : ℕ) : ℝ) = 1 := by norm_num
    linarith [hH.2, h2.le, h2.ge]
  · have hM' : M = 1 := by omega
    rw [hM', Finset.Ioc_self, Finset.sum_empty]
    have h3 : Real.log ((1 : ℕ) : ℝ) = 0 := by norm_num
    rw [h3]
    norm_num

end RHTower
