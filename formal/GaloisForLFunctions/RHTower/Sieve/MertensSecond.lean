import GaloisForLFunctions.RHTower.Sieve.MertensFirst
import GaloisForLFunctions.RHTower.Sieve.LogLogTelescope
import Mathlib.Algebra.BigOperators.Module

/-!
# Mertens' second theorem

`∑_{p ≤ N} 1/p = log log N + O(1)`, with both constants explicit.

The proof is discrete summation by parts against `1/log`.  Writing
`A N = ∑_{p ≤ N} (log p)/p = log N + R N` with `|R N|` bounded by Mertens' first theorem,

`∑_{p ≤ N} 1/p = A N / log N + ∑_{2 ≤ i < N} (1/log i - 1/log (i+1)) · A i`.

The `log i` part of `A i` produces exactly the telescoping sum of iterated logarithms, while the
`R i` part is controlled by the total variation `∑ (1/log i - 1/log (i+1)) = 1/log 2 - 1/log N`.
No integral comparison is used anywhere.

The sharp leading constant `1` is essential downstream: a bound `A · log log N + O(1)` with
`A > 1` would be useless for the tail estimates the sieve feeds.
-/

namespace RHTower.Sieve

open Finset Nat

/-- The summand of the weighted prime reciprocal sum, extended by zero off the primes. -/
noncomputable def primeLogWeight (k : ℕ) : ℝ := if k.Prime then Real.log k / (k : ℝ) else 0

/-- Mertens' weighted prime sum. -/
noncomputable def mertensA (N : ℕ) : ℝ := ∑ p ∈ Nat.primesLE N, Real.log p / (p : ℝ)

/-- The prime reciprocal sum. -/
noncomputable def mertensS (N : ℕ) : ℝ := ∑ p ∈ Nat.primesLE N, 1 / (p : ℝ)

theorem sum_range_primeLogWeight (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), primeLogWeight i = mertensA N := by
  rw [mertensA, Nat.primesLE_eq_filter_range, Finset.sum_filter]
  rfl

/-- The explicit constant in Mertens' first theorem. -/
noncomputable def mertensFirstConst : ℝ := max (Real.log 4) (1 + 2 * logSqTailConst)

theorem mertensFirstConst_nonneg : 0 ≤ mertensFirstConst :=
  le_trans (Real.log_nonneg (by norm_num)) (le_max_left _ _)

theorem abs_mertensA_sub_log_le {N : ℕ} (hN : 1 ≤ N) :
    |mertensA N - Real.log N| ≤ mertensFirstConst := by
  have hup := mertensFirst_upper hN
  have hlow := mertensFirst_lower hN
  have h1 : Real.log 4 ≤ mertensFirstConst := le_max_left _ _
  have h2 : 1 + 2 * logSqTailConst ≤ mertensFirstConst := le_max_right _ _
  rw [abs_le]
  constructor <;> [skip; skip] <;> unfold mertensA <;> unfold mertensA at hup hlow <;> linarith

/-- **Summation by parts** for the prime reciprocal sum. -/
theorem mertensS_eq_abel {N : ℕ} (hN : 2 ≤ N) :
    mertensS N = mertensA N / Real.log N
      + ∑ i ∈ Finset.Ico 2 N,
          (1 / Real.log i - 1 / Real.log ((i : ℝ) + 1)) * mertensA i := by
  classical
  have habel := Finset.sum_range_by_parts (fun i : ℕ => 1 / Real.log i) primeLogWeight (N + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at habel
  have hG : ∀ i : ℕ, ∑ j ∈ Finset.range (i + 1), primeLogWeight j = mertensA i :=
    sum_range_primeLogWeight
  rw [hG N] at habel
  have hGi : ∀ i ∈ Finset.range N,
      (1 / Real.log ((i : ℕ) + 1) - 1 / Real.log i) * ∑ j ∈ Finset.range (i + 1), primeLogWeight j
        = (1 / Real.log ((i : ℕ) + 1) - 1 / Real.log i) * mertensA i := by
    intro i _
    rw [hG i]
  rw [Finset.sum_congr rfl hGi] at habel
  have hLHS : ∑ i ∈ Finset.range (N + 1), 1 / Real.log i * primeLogWeight i = mertensS N := by
    rw [mertensS, Nat.primesLE_eq_filter_range, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro i _
    by_cases hp : i.Prime
    · have hi2 : 2 ≤ i := hp.two_le
      have hlog : Real.log i ≠ 0 := ne_of_gt (log_pos_of_two_le hi2)
      simp only [primeLogWeight, if_pos hp]
      field_simp
    · simp [primeLogWeight, hp]
  rw [hLHS] at habel
  have hdrop : ∑ i ∈ Finset.range N,
      (1 / Real.log ((i : ℕ) + 1) - 1 / Real.log i) * mertensA i
        = ∑ i ∈ Finset.Ico 2 N,
            (1 / Real.log ((i : ℕ) + 1) - 1 / Real.log i) * mertensA i := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro i hi
      have := (Finset.mem_Ico.1 hi).2
      exact Finset.mem_range.2 this
    · intro i hi hnot
      have hlt : i < 2 := by
        by_contra hcon
        exact hnot (Finset.mem_Ico.2 ⟨by omega, Finset.mem_range.1 hi⟩)
      interval_cases i
      · simp [mertensA, Nat.primesLE_eq_filter_range]
      · simp [mertensA, Nat.primesLE_eq_filter_range]
  rw [hdrop] at habel
  have hcast : ∀ i : ℕ, ((i : ℕ) + 1 : ℕ) = ((i : ℕ) + 1 : ℕ) := fun _ => rfl
  rw [habel, one_div, ← div_eq_inv_mul, ← Finset.sum_neg_distrib]
  refine congrArg _ ?_
  refine Finset.sum_congr rfl ?_
  intro i _
  have : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  rw [this]
  ring

/-- The total variation of `1/log` over `Ico 2 N`. -/
theorem sum_Ico_inv_log_variation {N : ℕ} (hN : 2 ≤ N) :
    ∑ i ∈ Finset.Ico 2 N, (1 / Real.log i - 1 / Real.log ((i : ℝ) + 1))
      = 1 / Real.log 2 - 1 / Real.log N := by
  have h := sum_Ico_telescope (fun i : ℕ => -(1 / Real.log i)) hN
  have hcong : ∀ i ∈ Finset.Ico 2 N,
      (fun i : ℕ => -(1 / Real.log i)) (i + 1) - (fun i : ℕ => -(1 / Real.log i)) i
        = 1 / Real.log i - 1 / Real.log ((i : ℝ) + 1) := by
    intro i _
    have hc : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    simp only [hc]
    ring
  rw [Finset.sum_congr rfl hcong] at h
  rw [h]
  ring

/-- Each variation term is nonnegative. -/
theorem inv_log_variation_nonneg {i : ℕ} (hi : 2 ≤ i) :
    0 ≤ 1 / Real.log i - 1 / Real.log ((i : ℝ) + 1) := by
  have hlogi : 0 < Real.log i := log_pos_of_two_le hi
  have hiR : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hlog1 : 0 < Real.log ((i : ℝ) + 1) := Real.log_pos (by linarith)
  have hmono : Real.log i ≤ Real.log ((i : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have := one_div_le_one_div_of_le hlogi hmono
  linarith

/-- The `log i` part of the summation-by-parts sum is exactly the telescoping model. -/
theorem sum_Ico_variation_mul_log {N : ℕ} (hN : 2 ≤ N) :
    ∑ i ∈ Finset.Ico 2 N, (1 / Real.log i - 1 / Real.log ((i : ℝ) + 1)) * Real.log i
      = logLogIncrementSum N := by
  rw [logLogIncrementSum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi2 : 2 ≤ i := (Finset.mem_Ico.1 hi).1
  have hlogi : 0 < Real.log i := log_pos_of_two_le hi2
  have hiR : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi2
  have hlog1 : 0 < Real.log ((i : ℝ) + 1) := Real.log_pos (by linarith)
  have hc : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  rw [hc]
  field_simp
  ring

/-- The remainder part of the summation-by-parts sum is uniformly bounded. -/
theorem abs_sum_Ico_variation_mul_remainder_le {N : ℕ} (hN : 2 ≤ N) :
    |∑ i ∈ Finset.Ico 2 N,
        (1 / Real.log i - 1 / Real.log ((i : ℝ) + 1)) * (mertensA i - Real.log i)|
      ≤ mertensFirstConst / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ i ∈ Finset.Ico 2 N,
      |(1 / Real.log i - 1 / Real.log ((i : ℝ) + 1)) * (mertensA i - Real.log i)|
        ≤ (1 / Real.log i - 1 / Real.log ((i : ℝ) + 1)) * mertensFirstConst := by
    intro i hi
    have hi2 : 2 ≤ i := (Finset.mem_Ico.1 hi).1
    have hw := inv_log_variation_nonneg hi2
    rw [abs_mul, abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left (abs_mertensA_sub_log_le (by omega)) hw
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul, sum_Ico_inv_log_variation hN]
  have hlogN : Real.log 2 ≤ Real.log N := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact Real.log_le_log (by norm_num) this
  have hlogNpos : (0 : ℝ) < Real.log N := lt_of_lt_of_le hlog2 hlogN
  have hnn : (0 : ℝ) ≤ 1 / Real.log N := by positivity
  have hC := mertensFirstConst_nonneg
  nlinarith [hnn, hC]

/-- The leading summation-by-parts term is close to `1`. -/
theorem abs_mertensA_div_log_sub_one_le {N : ℕ} (hN : 2 ≤ N) :
    |mertensA N / Real.log N - 1| ≤ mertensFirstConst / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : Real.log 2 ≤ Real.log N := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact Real.log_le_log (by norm_num) this
  have hlogNpos : (0 : ℝ) < Real.log N := lt_of_lt_of_le hlog2 hlogN
  have hrw : mertensA N / Real.log N - 1 = (mertensA N - Real.log N) / Real.log N := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hlogNpos]
  have hnum := abs_mertensA_sub_log_le (by omega : 1 ≤ N)
  have hC := mertensFirstConst_nonneg
  rw [div_le_div_iff₀ hlogNpos hlog2]
  nlinarith [hnum, hC, hlogN]

/-- **Mertens' second theorem, upper bound.** -/
theorem mertensSecond_upper {N : ℕ} (hN : 2 ≤ N) :
    mertensS N
      ≤ Real.log (Real.log N) + (1 + 2 * mertensFirstConst / Real.log 2 - logLog 2) := by
  have hsplit : ∑ i ∈ Finset.Ico 2 N,
      (1 / Real.log i - 1 / Real.log ((i : ℝ) + 1)) * mertensA i
        = logLogIncrementSum N
          + ∑ i ∈ Finset.Ico 2 N,
              (1 / Real.log i - 1 / Real.log ((i : ℝ) + 1)) * (mertensA i - Real.log i) := by
    rw [← sum_Ico_variation_mul_log hN, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have habel := mertensS_eq_abel hN
  rw [hsplit] at habel
  have h1 := (abs_le.1 (abs_mertensA_div_log_sub_one_le hN)).2
  have h2 := (abs_le.1 (abs_sum_Ico_variation_mul_remainder_le hN)).2
  have h3 := logLogIncrementSum_le hN
  rw [habel]
  simp only [logLog] at h3 ⊢
  linarith

/-- **Mertens' second theorem, lower bound.** -/
theorem mertensSecond_lower {N : ℕ} (hN : 2 ≤ N) :
    Real.log (Real.log N) - (2 * mertensFirstConst / Real.log 2 + logLog 3 - 1)
      ≤ mertensS N := by
  have hsplit : ∑ i ∈ Finset.Ico 2 N,
      (1 / Real.log i - 1 / Real.log ((i : ℝ) + 1)) * mertensA i
        = logLogIncrementSum N
          + ∑ i ∈ Finset.Ico 2 N,
              (1 / Real.log i - 1 / Real.log ((i : ℝ) + 1)) * (mertensA i - Real.log i) := by
    rw [← sum_Ico_variation_mul_log hN, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have habel := mertensS_eq_abel hN
  rw [hsplit] at habel
  have h1 := (abs_le.1 (abs_mertensA_div_log_sub_one_le hN)).1
  have h2 := (abs_le.1 (abs_sum_Ico_variation_mul_remainder_le hN)).1
  have h3 := le_logLogIncrementSum hN
  have hmono : logLog N ≤ logLog (N + 1) := by
    have hlogN : 0 < Real.log N := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      exact Real.log_pos (by linarith)
    have hstep : Real.log N ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
      refine Real.log_le_log ?_ ?_
      · have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      · exact_mod_cast Nat.le_succ N
    exact Real.log_le_log hlogN hstep
  rw [habel]
  simp only [logLog] at h3 hmono ⊢
  linarith

end RHTower.Sieve
