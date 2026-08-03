import GaloisForLFunctions.RHTower.Sieve.RealWindowIntegral

/-!
# The mean square over real starts is the discrete variance

Writing the window mean square as `g ∘ ⌊·⌋` for `g k = ‖∑_{k < n ≤ k+L} c_n‖²`, the integrand is
constant on each open unit interval `(k, k+1)`.  Congruence on the *open* interval is enough for both
integrability and the value of the integral, so

`∫_k^{k+1} g ⌊x⌋ dx = g k`,

and adding the unit intervals gives

`∫_Y^{Y+K} g ⌊x⌋ dx = ∑_{k < K} g (Y+k)`.

The continuous mean square of a short-interval sum is therefore *equal* to the discrete variance —
no error term, no approximation.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- The window mean square as a function of the integer start. -/
noncomputable def stepWindow (c : ℕ → ℂ) (L k : ℕ) : ℝ := ‖∑ n ∈ Finset.Ioc k (k + L), c n‖ ^ 2

theorem stepWindow_nonneg (c : ℕ → ℂ) (L k : ℕ) : 0 ≤ stepWindow c L k := by
  rw [stepWindow]; positivity

/-- On the open unit interval the step function is constant. -/
theorem stepWindow_floor_const {k : ℕ} {x : ℝ} (h : (k : ℝ) < x) (h2 : x < k + 1)
    (c : ℕ → ℂ) (L : ℕ) : stepWindow c L ⌊x⌋₊ = stepWindow c L k := by
  rw [floor_eq_of_mem_Ico (le_of_lt h) h2]

/-- The step function is interval integrable on a unit interval. -/
theorem intervalIntegrable_stepWindow (c : ℕ → ℂ) (L k : ℕ) :
    IntervalIntegrable (fun x : ℝ => stepWindow c L ⌊x⌋₊) volume (k : ℝ) ((k : ℝ) + 1) := by
  refine (intervalIntegrable_const (c := stepWindow c L k)).congr_uIoo ?_
  intro x hx
  rw [Set.uIoo_of_le (by linarith), Set.mem_Ioo] at hx
  exact (stepWindow_floor_const hx.1 hx.2 c L).symm

/-- **The unit-interval integral of the step function.** -/
theorem integral_unit_stepWindow (c : ℕ → ℂ) (L k : ℕ) :
    ∫ x in (k : ℝ)..((k : ℝ) + 1), stepWindow c L ⌊x⌋₊ = stepWindow c L k := by
  have hcongr : ∫ x in (k : ℝ)..((k : ℝ) + 1), stepWindow c L ⌊x⌋₊
      = ∫ _ in (k : ℝ)..((k : ℝ) + 1), stepWindow c L k := by
    refine intervalIntegral.integral_congr_uIoo ?_
    intro x hx
    rw [Set.uIoo_of_le (by linarith), Set.mem_Ioo] at hx
    exact stepWindow_floor_const hx.1 hx.2 c L
  rw [hcongr, intervalIntegral.integral_const]
  simp

/-- **The continuous mean square is the discrete variance.** -/
theorem integral_stepWindow_eq_sum (c : ℕ → ℂ) (L Y K : ℕ) :
    ∫ x in (Y : ℝ)..((Y : ℝ) + K), stepWindow c L ⌊x⌋₊
      = ∑ k ∈ Finset.range K, stepWindow c L (Y + k) := by
  have hint : ∀ i < K, IntervalIntegrable (fun x : ℝ => stepWindow c L ⌊x⌋₊) volume
      ((fun i : ℕ => (Y : ℝ) + i) i) ((fun i : ℕ => (Y : ℝ) + i) (i + 1)) := by
    intro i _
    have h := intervalIntegrable_stepWindow c L (Y + i)
    have hc : ((Y + i : ℕ) : ℝ) = (Y : ℝ) + i := by push_cast; ring
    rw [hc] at h
    have hc2 : (Y : ℝ) + ((i : ℝ) + 1) = (Y : ℝ) + i + 1 := by ring
    simpa [hc2] using h
  have key := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (Y : ℝ) + i) (f := fun x : ℝ => stepWindow c L ⌊x⌋₊) (n := K) hint
  simp only [Nat.cast_zero, add_zero] at key
  rw [← key]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : ((Y + i : ℕ) : ℝ) = (Y : ℝ) + i := by push_cast; ring
  have h := integral_unit_stepWindow c L (Y + i)
  rw [hc] at h
  have hc2 : (Y : ℝ) + ((i : ℝ) + 1) = (Y : ℝ) + i + 1 := by ring
  simpa [hc2] using h

end RHTower.Sieve
