import GaloisForLFunctions.RHTower.Sieve.GallagherPointwise

/-!
# Disjoint windows around separated points

For a nonnegative integrand, the integrals over the windows of length `δ` centred at points with
consecutive gaps at least `δ` add up to at most the integral over the enclosing interval:

`∑_{r ≤ R} ∫_{λ_r - δ/2}^{λ_r + δ/2} g ≤ ∫_A^{λ_R + δ/2} g`.

The windows do not overlap — the separation gives `λ_r + δ/2 ≤ λ_{r+1} - δ/2` — so the induction
step splits the enclosing integral into the part already accounted for, a gap of nonnegative
integrand, and the new window.  No measure theory beyond additivity over adjacent intervals is used.

This is the global half of Gallagher's argument: applied to `|S|²` and to `2|S||S'|` it replaces the
local integrals of `GallagherPointwise.lean` by integrals over a single period.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- **Windows around separated points fit inside the enclosing interval.** -/
theorem sum_window_le {g : ℝ → ℝ} (hg : Continuous g) (hgnn : ∀ t, 0 ≤ g t)
    {lam : ℕ → ℝ} {δ A : ℝ} (hδ : 0 < δ) (hgap : ∀ i, lam i + δ ≤ lam (i + 1))
    (hA : A ≤ lam 0 - δ / 2) (R : ℕ) :
    ∑ r ∈ Finset.range (R + 1), (∫ t in (lam r - δ / 2)..(lam r + δ / 2), g t)
      ≤ ∫ t in A..(lam R + δ / 2), g t := by
  induction R with
  | zero =>
      rw [Finset.sum_range_one]
      exact intervalIntegral.integral_mono_interval hA (by linarith) le_rfl
        (Filter.Eventually.of_forall (fun t => hgnn t)) (hg.intervalIntegrable _ _)
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hmid : lam n + δ / 2 ≤ lam (n + 1) - δ / 2 := by
        have := hgap n
        linarith
      have hI1 : IntervalIntegrable g volume A (lam n + δ / 2) := hg.intervalIntegrable _ _
      have hI2 : IntervalIntegrable g volume (lam n + δ / 2) (lam (n + 1) - δ / 2) :=
        hg.intervalIntegrable _ _
      have hI3 : IntervalIntegrable g volume (lam (n + 1) - δ / 2) (lam (n + 1) + δ / 2) :=
        hg.intervalIntegrable _ _
      have hsplit : (∫ t in A..(lam n + δ / 2), g t)
          + (∫ t in (lam n + δ / 2)..(lam (n + 1) - δ / 2), g t)
          + (∫ t in (lam (n + 1) - δ / 2)..(lam (n + 1) + δ / 2), g t)
          = ∫ t in A..(lam (n + 1) + δ / 2), g t := by
        rw [intervalIntegral.integral_add_adjacent_intervals hI1 hI2,
          intervalIntegral.integral_add_adjacent_intervals (hI1.trans hI2) hI3]
      have hmidnn : (0 : ℝ) ≤ ∫ t in (lam n + δ / 2)..(lam (n + 1) - δ / 2), g t :=
        intervalIntegral.integral_nonneg hmid (fun t _ => hgnn t)
      linarith [ih, hsplit, hmidnn]

end RHTower.Sieve
