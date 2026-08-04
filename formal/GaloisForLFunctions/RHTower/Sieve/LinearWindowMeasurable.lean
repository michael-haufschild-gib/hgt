import GaloisForLFunctions.RHTower.Sieve.LinearVsMultiplicativeWindow

/-!
# The linear window as a function of the logarithmic position

At position `u` the linear window is `e^u < n ≤ e^u + L`, that is `n - L ≤ e^u < n`.  So as a
function of `u` each term is the indicator of the preimage of an interval under `exp`, a measurable
set, and the window sum is a finite combination of such indicators.

It is therefore bounded and measurable, hence integrable on every set of finite measure — which is
what lets the pointwise transfer of `LinearVsMultiplicativeWindow.lean` be integrated over a block of
positions.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

/-- The set of logarithmic positions at which `n` lies in the linear window of length `L`. -/
noncomputable def linWindow (L : ℝ) (n : ℕ) : Set ℝ :=
  (fun u : ℝ => Real.exp u) ⁻¹' (Set.Ico ((n : ℝ) - L) (n : ℝ))

theorem measurableSet_linWindow (L : ℝ) (n : ℕ) : MeasurableSet (linWindow L n) :=
  measurableSet_Ico.preimage Real.measurable_exp

theorem mem_linWindow {L : ℝ} {n : ℕ} {u : ℝ} :
    u ∈ linWindow L n ↔ (Real.exp u < (n : ℝ) ∧ (n : ℝ) ≤ Real.exp u + L) := by
  rw [linWindow, Set.mem_preimage, Set.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, h1⟩

/-- The linear window sum as a function of the logarithmic position. -/
noncomputable def linWindowSum (a : ℕ → ℂ) (s : Finset ℕ) (L u : ℝ) : ℂ :=
  ∑ n ∈ s, (Set.indicator (linWindow L n) (fun _ => (1 : ℝ)) u) • a n

/-- It is the sum over the window. -/
theorem linWindowSum_eq (a : ℕ → ℂ) (s : Finset ℕ) (L u : ℝ) :
    linWindowSum a s L u
      = ∑ n ∈ s.filter (fun n : ℕ =>
          Real.exp u < (n : ℝ) ∧ (n : ℝ) ≤ Real.exp u + L), a n := by
  classical
  rw [linWindowSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hc : Real.exp u < (n : ℝ) ∧ (n : ℝ) ≤ Real.exp u + L
  · rw [if_pos hc, Set.indicator_of_mem (mem_linWindow.2 hc), one_smul]
  · rw [if_neg hc, Set.indicator_of_notMem (fun h => hc (mem_linWindow.1 h)), zero_smul]

theorem measurable_linWindowSum (a : ℕ → ℂ) (s : Finset ℕ) (L : ℝ) :
    Measurable (linWindowSum a s L) := by
  classical
  refine Finset.measurable_sum _ fun n _ => ?_
  exact ((measurable_one.indicator (measurableSet_linWindow L n)).smul_const (a n))

/-- The window sum is bounded by the `ℓ¹` norm of the coefficients. -/
theorem norm_linWindowSum_le (a : ℕ → ℂ) (s : Finset ℕ) (L u : ℝ) :
    ‖linWindowSum a s L u‖ ≤ ∑ n ∈ s, ‖a n‖ := by
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun n _ => ?_
  rw [norm_smul, Real.norm_eq_abs]
  by_cases hc : u ∈ linWindow L n
  · rw [Set.indicator_of_mem hc]
    simp
  · rw [Set.indicator_of_notMem hc]
    simp

/-- **The mean square of a linear window sum is integrable on every set of finite measure.** -/
theorem integrableOn_normSq_linWindowSum (a : ℕ → ℂ) (s : Finset ℕ) (L : ℝ) {E : Set ℝ}
    (hE : volume E ≠ ⊤) :
    IntegrableOn (fun u : ℝ => ‖linWindowSum a s L u‖ ^ 2) E := by
  classical
  set C : ℝ := (∑ n ∈ s, ‖a n‖) ^ 2 with hC
  have hmeas : AEStronglyMeasurable (fun u : ℝ => ‖linWindowSum a s L u‖ ^ 2)
      (volume.restrict E) :=
    (((measurable_linWindowSum a s L).norm.pow_const 2)).aestronglyMeasurable
  refine Integrable.mono' (g := fun _ : ℝ => C) (integrableOn_const hE (by simp)) hmeas ?_
  refine Filter.Eventually.of_forall fun u => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := norm_linWindowSum_le a s L u
  have h0 : (0 : ℝ) ≤ ‖linWindowSum a s L u‖ := norm_nonneg _
  rw [hC]
  nlinarith [h, h0]

end RHTower.Sieve
