import GaloisForLFunctions.RHTower.StepFunctionCarrier

/-!
# Exact finite pronic covariance as a step integral

Truncation makes every arithmetic row bounded, irrespective of its growth.
The existing step-pairing theorem then identifies its signed finite pronic
covariance with an exact Lebesgue integral. No asymptotic approximation or
boundedness assumption on the original rows is needed.
-/

noncomputable section
open Finset Set MeasureTheory RHTower
namespace GaloisForLFunctions.BiarithmeticGeometry

private theorem abs_truncatedRow_le (s : ℕ → ℝ) (N n : ℕ) :
    |if n ≤ N then s n else 0| ≤ ∑ k ∈ range (N + 1), |s k| := by
  by_cases hn : n ≤ N
  · rw [if_pos hn]
    exact single_le_sum (fun k _ => abs_nonneg (s k)) (mem_range.mpr (by omega))
  · rw [if_neg hn, abs_zero]
    exact sum_nonneg fun k _ => abs_nonneg (s k)

/-- Every finite signed pronic covariance is exactly the pairing of its truncated step rows. -/
theorem finitePronicPairing_eq_stepGram (s t : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ range N, s (n + 1) * t (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2))) =
      stepGram (fun n => if n ≤ N then s n else 0)
        (fun n => if n ≤ N then t n else 0) := by
  have h := hasSum_stepGram (abs_truncatedRow_le s N) (abs_truncatedRow_le t N)
  rw [← h.tsum_eq, tsum_eq_sum (s := range N)]
  · apply sum_congr rfl
    intro n hn
    simp only [if_pos (by have := mem_range.mp hn; omega : n + 1 ≤ N)]
  · intro n hn
    have hnot : ¬n + 1 ≤ N := by simp only [Finset.mem_range] at hn; omega
    simp only [if_neg hnot, zero_mul, zero_div]

/-- The integral form of the exact finite-horizon covariance, valid for arbitrary rows. -/
theorem finitePronicPairing_eq_integral (s t : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ range N, s (n + 1) * t (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2))) =
      ∫ x in Ioi (1 : ℝ),
        (if ⌊x⌋₊ ≤ N then s ⌊x⌋₊ else 0) *
          (if ⌊x⌋₊ ≤ N then t ⌊x⌋₊ else 0) * (x⁻¹) ^ 2 :=
  finitePronicPairing_eq_stepGram s t N

end GaloisForLFunctions.BiarithmeticGeometry
