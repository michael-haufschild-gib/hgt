import Mathlib

/-!
# Abel summation against an increasing weight

`Sieve/AbelInequality` carries Dirichlet's test for a *nonincreasing* weight.  The Gram entry of a
Dirichlet polynomial needs the opposite monotonicity: `∑_{n ∼ N} n^{iτ} = ∑_{n ∼ N} n^{1/2}·n^{-1/2+iτ}`
weights the critical-line summand by the *increasing* `n^{1/2}`.  Summation by parts then costs a
factor two and evaluates the weight at the top of the range instead of the bottom.

Stated for a complex summand, since that is what a Dirichlet polynomial supplies.
-/

namespace RHTower.Sieve

open Finset

/-- **Abel's inequality for a nondecreasing nonnegative weight.** -/
theorem norm_sum_mul_le_of_bounded_partial_mono (n : ℕ) (w : ℕ → ℝ) (g : ℕ → ℂ) {B : ℝ}
    (hw0 : 0 ≤ w 0) (hmono : ∀ i, w i ≤ w (i + 1))
    (hB : ∀ k, ‖∑ i ∈ Finset.range k, g i‖ ≤ B) :
    ‖∑ i ∈ Finset.range n, ((w i : ℝ) : ℂ) * g i‖ ≤ 2 * B * w (n - 1) := by
  classical
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hwmono : ∀ i j : ℕ, i ≤ j → w i ≤ w j := by
    intro i j hij
    induction j with
    | zero => simp_all
    | succ m ih =>
      rcases Nat.lt_or_ge i (m + 1) with h | h
      · exact le_trans (ih (by omega)) (hmono m)
      · have : i = m + 1 := by omega
        rw [this]
  have hwn : 0 ≤ w (n - 1) := le_trans hw0 (hwmono 0 (n - 1) (Nat.zero_le _))
  have hkey := Finset.sum_range_by_parts (fun i => ((w i : ℝ) : ℂ)) g n
  simp only [smul_eq_mul] at hkey
  rw [hkey]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 : ‖((w (n - 1) : ℝ) : ℂ) * ∑ i ∈ Finset.range n, g i‖ ≤ w (n - 1) * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwn]
    exact mul_le_mul_of_nonneg_left (hB n) hwn
  have h2 : ‖∑ i ∈ Finset.range (n - 1),
      (((w (i + 1) : ℝ) : ℂ) - ((w i : ℝ) : ℂ)) * ∑ j ∈ Finset.range (i + 1), g j‖
      ≤ w (n - 1) * B - w 0 * B := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i ∈ Finset.range (n - 1),
        ‖(((w (i + 1) : ℝ) : ℂ) - ((w i : ℝ) : ℂ)) * ∑ j ∈ Finset.range (i + 1), g j‖
          ≤ (w (i + 1) - w i) * B := by
      intro i _
      rw [norm_mul]
      have hdiff : ‖((w (i + 1) : ℝ) : ℂ) - ((w i : ℝ) : ℂ)‖ = w (i + 1) - w i := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [hmono i])]
      rw [hdiff]
      exact mul_le_mul_of_nonneg_left (hB (i + 1)) (by linarith [hmono i])
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul]
    have hts : ∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i) = w (n - 1) - w 0 :=
      Finset.sum_range_sub w (n - 1)
    rw [hts, sub_mul]
  have h3 : 0 ≤ w 0 * B := mul_nonneg hw0 hB0
  linarith [h1, h2, h3]

end RHTower.Sieve
