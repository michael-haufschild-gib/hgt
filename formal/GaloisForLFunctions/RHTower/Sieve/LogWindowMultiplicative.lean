import GaloisForLFunctions.RHTower.Sieve.LogWindowKernel

/-!
# The logarithmic window is a multiplicative window

At the position `u = log x` the window `u < log n ≤ u + δ` is exactly the multiplicative window

    x < n ≤ x·e^δ ,

so the mean square of `LogWindowKernel.lean` is a mean square over multiplicative windows of fixed
ratio `e^δ`.  Over a range on which `x` is comparable to `X`, such a window has length comparable to
`X(e^δ − 1)`, which is how a fixed `δ` produces short intervals of a prescribed length.
-/

namespace RHTower.Sieve

open Finset

/-- **The logarithmic window at `log x` is the multiplicative window `(x, x·e^δ]`.** -/
theorem logWindowSum_log (a : ℕ → ℂ) (s : Finset ℕ) (hs : ∀ n ∈ s, 0 < n) (δ : ℝ) {x : ℝ}
    (hx : 0 < x) :
    logWindowSum a s δ (Real.log x)
      = ∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x * Real.exp δ), a n := by
  classical
  rw [logWindowSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : 0 < n := hs n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hxe : (0 : ℝ) < x * Real.exp δ := by positivity
  have hlogxe : Real.log (x * Real.exp δ) = Real.log x + δ := by
    rw [Real.log_mul (ne_of_gt hx) (ne_of_gt (Real.exp_pos δ)), Real.log_exp]
  have hiff : Real.log x ∈ logWindow δ n ↔ (x < (n : ℝ) ∧ (n : ℝ) ≤ x * Real.exp δ) := by
    rw [logWindow, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(Real.log_lt_log_iff hx hnR).1 h2, ?_⟩
      have : Real.log (n : ℝ) ≤ Real.log (x * Real.exp δ) := by
        rw [hlogxe]; linarith
      exact (Real.log_le_log_iff hnR hxe).1 this
    · rintro ⟨h1, h2⟩
      refine ⟨?_, Real.log_lt_log hx h1⟩
      have : Real.log (n : ℝ) ≤ Real.log x + δ := by
        rw [← hlogxe]
        exact Real.log_le_log hnR h2
      linarith
  by_cases hc : x < (n : ℝ) ∧ (n : ℝ) ≤ x * Real.exp δ
  · rw [if_pos hc, Set.indicator_of_mem (hiff.2 hc), one_smul]
  · rw [if_neg hc, Set.indicator_of_notMem (fun h => hc (hiff.1 h)), zero_smul]

/-- **Every linear window is a logarithmic window**, at the ratio `(x+h)/x`. -/
theorem logWindowSum_log_linear (a : ℕ → ℂ) (s : Finset ℕ) (hs : ∀ n ∈ s, 0 < n) {x h : ℝ}
    (hx : 0 < x) (hh : 0 ≤ h) :
    logWindowSum a s (Real.log ((x + h) / x)) (Real.log x)
      = ∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h), a n := by
  classical
  have hpos : (0 : ℝ) < (x + h) / x := by positivity
  have hexp : x * Real.exp (Real.log ((x + h) / x)) = x + h := by
    rw [Real.exp_log hpos]
    field_simp
  rw [logWindowSum_log a s hs _ hx, hexp]

end RHTower.Sieve
