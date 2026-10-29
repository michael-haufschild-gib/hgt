import GaloisForLFunctions.HTGeometry.ShiftPartialSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Harmonic mass from a delayed counting lower bound

Nonnegative mass with cumulative lower bound `(N-K)C` dominates a constant
sequence beginning after `K`. Summation by parts transfers this comparison to
the decreasing harmonic weights, with exact loss `H_K`.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

private theorem harmonic_weight_nonneg_of_prefix_nonneg (f : ℕ → ℝ)
    (hf : ∀ N, 0 ≤ ∑ i ∈ range N, f i) (N : ℕ) :
    0 ≤ ∑ i ∈ range N, f i / ((i : ℝ) + 1) := by
  let w : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 1)
  have hstep (j : ℕ) : w (j + 1) - w j ≤ 0 := by
    dsimp [w]
    push_cast
    exact sub_nonpos.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hboundary : 0 ≤ _root_.HTGeometry.partialSum f N * w N :=
    mul_nonneg (hf N) (by dsimp [w]; positivity)
  have hsum : (∑ j ∈ range N, _root_.HTGeometry.partialSum f (j + 1) *
      (w (j + 1) - w j)) ≤ 0 :=
    sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hf (j + 1)) (hstep j)
  have he := _root_.HTGeometry.sum_mul_weight_eq f w N
  have hnonneg : 0 ≤ ∑ i ∈ range N, f i * w i := by
    rw [he]
    linarith only [hboundary, hsum]
  simpa only [w, mul_one_div] using hnonneg

private theorem harmonic_real_eq (N : ℕ) :
    (harmonic N : ℝ) = ∑ i ∈ range N, 1 / ((i : ℝ) + 1) := by
  simp [harmonic, one_div]

/-- An ordinary counting loss of `K` costs only `H_K` under harmonic weighting. -/
theorem harmonic_mass_ge_of_delayed_prefix (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i)
    {C : ℝ} (hC : 0 ≤ C) (K : ℕ)
    (hprefix : ∀ N : ℕ, ((N : ℝ) - K) * C ≤ ∑ i ∈ range N, f i) (N : ℕ) :
    ((harmonic N : ℝ) - (harmonic K : ℝ)) * C ≤
      ∑ i ∈ range N, f i / ((i : ℝ) + 1) := by
  let g : ℕ → ℝ := fun i => if K ≤ i then C else 0
  have hg (L : ℕ) : (∑ i ∈ range L, g i) = ((L - K : ℕ) : ℝ) * C := by
    induction L with
    | zero => simp [g]
    | succ L ih =>
      rw [sum_range_succ, ih]
      by_cases hKL : K ≤ L
      · rw [show g L = C by simp only [g, if_pos hKL], Nat.succ_sub hKL, Nat.cast_succ]
        ring
      · have hLK : L + 1 ≤ K := by omega
        rw [show g L = 0 by simp only [g, if_neg hKL],
          Nat.sub_eq_zero_of_le (by omega : L ≤ K), Nat.sub_eq_zero_of_le hLK]
        simp
  have hcomp (L : ℕ) : (∑ i ∈ range L, g i) ≤ ∑ i ∈ range L, f i := by
    rw [hg L]
    by_cases hKL : K ≤ L
    · rw [Nat.cast_sub hKL]
      exact hprefix L
    · rw [Nat.sub_eq_zero_of_le (by omega : L ≤ K), Nat.cast_zero, zero_mul]
      exact sum_nonneg fun i _ => hf i
  have hdiff : ∀ L, 0 ≤ ∑ i ∈ range L, (f i - g i) := by
    intro L
    rw [sum_sub_distrib]
    exact sub_nonneg.mpr (hcomp L)
  have hweighted := harmonic_weight_nonneg_of_prefix_nonneg (fun i => f i - g i) hdiff N
  simp only [sub_div, sum_sub_distrib] at hweighted
  let H := (range N).filter fun i => i < K
  have hhead : (∑ i ∈ H, C / ((i : ℝ) + 1)) ≤ C * (harmonic K : ℝ) := by
    rw [harmonic_real_eq, mul_sum]
    have hsub : H ⊆ range K := fun i hi => mem_range.mpr (mem_filter.mp hi).2
    have h := sum_le_sum_of_subset_of_nonneg (f := fun i : ℕ => C / ((i : ℝ) + 1)) hsub
      (fun i (_ : i ∈ range K) _ => div_nonneg hC (by positivity))
    simpa only [mul_one_div] using h
  have hsplit : (∑ i ∈ range N, g i / ((i : ℝ) + 1)) +
      (∑ i ∈ H, C / ((i : ℝ) + 1)) = C * (harmonic N : ℝ) := by
    rw [harmonic_real_eq, mul_sum]
    dsimp only [H]
    rw [sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    by_cases hKi : K ≤ i
    · simp only [g, if_pos hKi, if_neg (not_lt_of_ge hKi), add_zero, mul_one_div]
    · simp only [g, if_neg hKi, if_pos (lt_of_not_ge hKi), zero_div, zero_add, mul_one_div]
  nlinarith only [hhead, hsplit, hweighted]

/-- A delayed counting bound gives the logarithm of the ratio of horizons,
with no additional constant loss. -/
theorem logarithmic_mass_ge_of_delayed_prefix (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i)
    {C : ℝ} (hC : 0 ≤ C) (K : ℕ)
    (hprefix : ∀ N : ℕ, ((N : ℝ) - K) * C ≤ ∑ i ∈ range N, f i) (N : ℕ) :
    (Real.log ((N : ℝ) + 1) - Real.log ((K : ℝ) + 1)) * C ≤
      ∑ i ∈ range N, f i / ((i : ℝ) + 1) := by
  by_cases hKN : K ≤ N
  · have hmono := Real.strictMono_eulerMascheroniSeq.monotone hKN
    simp only [Real.eulerMascheroniSeq] at hmono
    exact (mul_le_mul_of_nonneg_right (by linarith only [hmono]) hC).trans
      (harmonic_mass_ge_of_delayed_prefix f hf hC K hprefix N)
  · have hlog : Real.log ((N : ℝ) + 1) ≤ Real.log ((K : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (show N + 1 ≤ K + 1 by omega))
    exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hlog) hC).trans
      (sum_nonneg fun i _ => div_nonneg (hf i) (by positivity))

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.logarithmic_mass_ge_of_delayed_prefix
