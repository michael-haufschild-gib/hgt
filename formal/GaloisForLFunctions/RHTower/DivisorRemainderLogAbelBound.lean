import GaloisForLFunctions.RHTower.SquareSampledDivisorRemainder
import GaloisForLFunctions.RHTower.DivisorHyperbolaPositivePrefix
import GaloisForLFunctions.RHTower.Deninger.DeningerAbelSummation

set_option autoImplicit false
open scoped BigOperators
open Finset

namespace RHTower

/-- Decreasing nonnegative weights preserve a linear bound on signed prefixes. -/
theorem abs_sum_mul_antitone_le_of_linear_prefix
    (a w : ℕ → ℝ) (C : ℝ) (N : ℕ)
    (hw : ∀ n < N, 0 ≤ w n)
    (hanti : ∀ n, n + 1 < N → w (n + 1) ≤ w n)
    (hA : ∀ n ≤ N, |∑ k ∈ range n, a k| ≤ C * n) :
    |∑ n ∈ range N, a n * w n| ≤ C * ∑ n ∈ range N, w n := by
  cases N with
  | zero => simp
  | succ N =>
    have hdiff (n : ℕ) (hn : n ∈ range N) : 0 ≤ w n - w (n + 1) :=
      sub_nonneg.mpr (hanti n (by simpa using mem_range.mp hn))
    have hprefix (n : ℕ) (hn : n ≤ N) :
        |deningerPartialSum a n| ≤ C * (n + 1 : ℕ) :=
      hA (n + 1) (by omega)
    calc
      |∑ n ∈ range (N + 1), a n * w n|
          = |deningerPartialSum a N * w N +
              ∑ n ∈ range N, deningerPartialSum a n * (w n - w (n + 1))| :=
            congrArg abs (deningerAbelSummation a w N)
      _ ≤ |deningerPartialSum a N * w N| +
              ∑ n ∈ range N, |deningerPartialSum a n * (w n - w (n + 1))| :=
        (abs_add_le _ _).trans (add_le_add_right (abs_sum_le_sum_abs _ _) _)
      _ ≤ C * (N + 1 : ℕ) * w N +
              ∑ n ∈ range N, C * (n + 1 : ℕ) * (w n - w (n + 1)) := by
        apply add_le_add
        · rw [abs_mul, abs_of_nonneg (hw N (by omega))]
          exact mul_le_mul_of_nonneg_right (hprefix N le_rfl) (hw N (by omega))
        · apply sum_le_sum
          intro n hn
          rw [abs_mul, abs_of_nonneg (hdiff n hn)]
          exact mul_le_mul_of_nonneg_right (hprefix n (by have := mem_range.mp hn; omega)) (hdiff n hn)
      _ = C * ∑ n ∈ range (N + 1), w n := by
        have hid := deningerAbelSummation (fun _ => (1 : ℝ)) w N
        simp only [one_mul, deningerPartialSum, sum_const, card_range, nsmul_eq_mul,
          mul_one] at hid
        rw [hid, mul_add, mul_sum]
        simp only [mul_assoc]

private theorem divisorRemainder_zero : mobiusSquareDivisorRemainder 0 = 0 := by
  simp [mobiusSquareDivisorRemainder, mobiusSquareDivisorSummatory,
    mobiusSquareDivisorMainTerm]

private theorem log_nat_mono {m n : ℕ} (h : m ≤ n) :
    Real.log (m : ℝ) ≤ Real.log (n : ℝ) := by
  by_cases hm : m = 0
  · subst m
    simpa using Real.log_natCast_nonneg n
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hm) (by exact_mod_cast h)

private theorem sum_divisorRemainder_Icc (N : ℕ) :
    (∑ n ∈ Icc 1 N, mobiusSquareDivisorRemainder n) =
      ∑ n ∈ range (N + 1), mobiusSquareDivisorRemainder n := by
  apply sum_subset
  · intro n hn
    simp only [mem_Icc, mem_range] at *
    omega
  · intro n hn hout
    have hn0 : n = 0 := by
      simp only [mem_Icc, mem_range] at *
      omega
    simpa [hn0] using divisorRemainder_zero

/-- Ordinary signed divisor-error prefixes grow at most linearly times a logarithm. -/
theorem abs_sum_mobiusSquareDivisorRemainder_Icc_le (N : ℕ) :
    |∑ n ∈ Icc 1 N, mobiusSquareDivisorRemainder n| ≤
      (N : ℝ) * (8 + 2 * Real.log ((N : ℝ) + 1)) := by
  have hC := sum_centeredDivisorHyperbola_bounds N
  have hs : (Nat.sqrt N : ℝ) * Nat.sqrt N ≤ (N : ℝ) := by
    exact_mod_cast Nat.sqrt_le N
  have hs' : (Nat.sqrt N : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.sqrt_le_self N
  have hCabs : |∑ n ∈ Icc 1 N, centeredDivisorHyperbola n| ≤ (N : ℝ) / 8 := by
    rw [abs_of_nonpos hC.2]
    nlinarith [hC.1]
  have hE : |∑ n ∈ Icc 1 N,
        (mobiusSquareDivisorRemainder n + 2 * centeredDivisorHyperbola n)| ≤
      (N : ℝ) * (7 + 2 * Real.log ((N : ℝ) + 1)) := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N,
          |mobiusSquareDivisorRemainder n + 2 * centeredDivisorHyperbola n| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Icc 1 N, (7 + 2 * Real.log ((N : ℝ) + 1)) := by
        apply sum_le_sum
        intro n hn
        have hl : Real.log ((n : ℝ) + 1) ≤ Real.log ((N : ℝ) + 1) :=
          Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (mem_Icc.mp hn).2 1)
        exact (abs_mobiusSquareDivisorRemainder_add_centered_le n).trans (by linarith)
      _ = _ := by simp; ring
  have heq : (∑ n ∈ Icc 1 N, mobiusSquareDivisorRemainder n) =
      (∑ n ∈ Icc 1 N, (mobiusSquareDivisorRemainder n + 2 * centeredDivisorHyperbola n)) -
        2 * ∑ n ∈ Icc 1 N, centeredDivisorHyperbola n := by
    rw [sum_add_distrib, mul_sum]
    ring
  rw [heq]
  have ht := abs_add_le
    (∑ n ∈ Icc 1 N, (mobiusSquareDivisorRemainder n + 2 * centeredDivisorHyperbola n))
    (-(2 * ∑ n ∈ Icc 1 N, centeredDivisorHyperbola n))
  rw [← sub_eq_add_neg, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
  nlinarith

private theorem log_increment_eq (n : ℕ) :
    Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) =
      Real.log (1 + 1 / ((n : ℝ) + 1)) := by
  rw [← Real.log_div (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

/-- The inner logarithmic Abel term retains signed divisor-error cancellation. -/
theorem abs_mobiusSquareDivisorRemainder_log_difference_le (X : ℕ) :
    |∑ n ∈ range X, mobiusSquareDivisorRemainder n *
        (Real.log (n : ℝ) - Real.log (n + 1 : ℕ))| ≤
      (8 + 2 * Real.log (X : ℝ)) * Real.log (X : ℝ) := by
  cases X with
  | zero => simp
  | succ M =>
    let a : ℕ → ℝ := fun n => mobiusSquareDivisorRemainder (n + 1)
    let w : ℕ → ℝ := fun n => Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)
    let C : ℝ := 8 + 2 * Real.log (M + 1 : ℕ)
    have hA (n : ℕ) (hn : n ≤ M) : |∑ k ∈ range n, a k| ≤ C * n := by
      have heq : (∑ k ∈ range n, a k) =
          ∑ k ∈ Icc 1 n, mobiusSquareDivisorRemainder k := by
        rw [sum_divisorRemainder_Icc, sum_range_succ']
        simp only [divisorRemainder_zero, add_zero, a]
      rw [heq]
      have hl := log_nat_mono (Nat.add_le_add_right hn 1)
      push_cast at hl
      have hb := abs_sum_mobiusSquareDivisorRemainder_Icc_le n
      dsimp [C]
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hl)]
    have hw (n : ℕ) (_hn : n < M) : 0 ≤ w n := by
      dsimp [w]
      exact sub_nonneg.mpr (Real.log_le_log (by positivity) (by linarith))
    have hanti (n : ℕ) (_hn : n + 1 < M) : w (n + 1) ≤ w n := by
      dsimp [w]
      rw [log_increment_eq, log_increment_eq]
      apply Real.log_le_log (by positivity)
      apply add_le_add_right
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      linarith
    have hab := abs_sum_mul_antitone_le_of_linear_prefix a w C M hw hanti hA
    have hwSum : (∑ n ∈ range M, w n) = Real.log (M + 1 : ℕ) := by
      have htel := sum_range_sub (fun n : ℕ => Real.log ((n : ℝ) + 1)) M
      simpa [w, Nat.cast_add, Nat.cast_one, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using htel
    have hshift : (∑ n ∈ range (M + 1), mobiusSquareDivisorRemainder n *
          (Real.log (n : ℝ) - Real.log (n + 1 : ℕ))) =
        -(∑ n ∈ range M, a n * w n) := by
      rw [sum_range_succ']
      simp only [divisorRemainder_zero, zero_mul, add_zero]
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro n hn
      dsimp [a, w]
      push_cast
      ring_nf
    rw [hshift, abs_neg]
    simpa only [hwSum, C] using hab

end RHTower
