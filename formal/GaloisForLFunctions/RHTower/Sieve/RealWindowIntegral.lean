import GaloisForLFunctions.RHTower.Sieve.RealWindow

/-!
# The window sum is constant on a unit interval

On `[k, k+1)` the floor is `k`, so the real-start window is the integer window at `k` throughout.
The two formulations of a short-interval mean square therefore agree on each unit interval:

`∫_k^{k+1} ‖∑_{x < n ≤ x+L} a_n‖² dx = ‖∑_{k < n ≤ k+L} a_n‖²`.

Only the right endpoint `x = k+1` sees a different window, and a single point is null, so the
integral of the step function is its value on the interior.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- The floor is constant on a unit interval. -/
theorem floor_eq_of_mem_Ico {k : ℕ} {x : ℝ} (h : (k : ℝ) ≤ x) (h2 : x < k + 1) : ⌊x⌋₊ = k := by
  rw [Nat.floor_eq_iff (le_trans (Nat.cast_nonneg k) h)]
  exact ⟨h, by linarith⟩

/-- **The real window is constant on a unit interval.** -/
theorem realWindow_const {k : ℕ} {x : ℝ} (h : (k : ℝ) ≤ x) (h2 : x < k + 1) {L M : ℕ}
    (hM : k + L < M) : realWindow x L M = Finset.Ioc k (k + L) := by
  have hk := floor_eq_of_mem_Ico h h2
  rw [realWindow_eq_Ioc (le_trans (Nat.cast_nonneg k) h) (by rw [hk]; exact hM), hk]

/-- **The unit-interval integral of the window mean square.** -/
theorem integral_unit_window (a : ℕ → ℂ) (k L M : ℕ) (hM : k + L < M) :
    ∫ x in (k : ℝ)..((k : ℝ) + 1), ‖∑ n ∈ realWindow x L M, a n‖ ^ (2 : ℕ)
      = ‖∑ n ∈ Finset.Ioc k (k + L), a n‖ ^ (2 : ℕ) := by
  have hcongr : ∫ x in (k : ℝ)..((k : ℝ) + 1), ‖∑ n ∈ realWindow x L M, a n‖ ^ (2 : ℕ)
      = ∫ _ in (k : ℝ)..((k : ℝ) + 1), ‖∑ n ∈ Finset.Ioc k (k + L), a n‖ ^ (2 : ℕ) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hnull : (volume : Measure ℝ) {(k : ℝ) + 1} = 0 := measure_singleton _
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (fun x hx => ?_) hnull
    simp only [Set.mem_setOf_eq, Classical.not_imp] at hx
    obtain ⟨hmem, hne⟩ := hx
    rw [Set.uIoc_of_le (by linarith), Set.mem_Ioc] at hmem
    rw [Set.mem_singleton_iff]
    by_contra hx1
    exact hne (by rw [realWindow_const (le_of_lt hmem.1) (lt_of_le_of_ne hmem.2 hx1) hM])
  rw [hcongr, intervalIntegral.integral_const]
  simp

end RHTower.Sieve
