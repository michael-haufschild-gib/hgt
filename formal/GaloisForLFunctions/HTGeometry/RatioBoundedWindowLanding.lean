import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith

/-!
# A ratio-bounded sequence lands in every sufficiently wide window

A sequence that starts above a window and whose successive ratios are bounded below by `c` cannot
step over that window: at the first index where it drops below the top, it is still above the
bottom, provided the window is at least as wide as `c⁻¹`.

This is the discrete mechanism behind an order schedule.  The order parameter changes the scale by a
bounded factor at each step, so a target window wider than that factor is always hit by some
admissible order — no optimisation and no balancing are involved.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Window landing.**  If `u` starts at or above `L`, satisfies `c * u (m-1) ≤ u m` above the
starting index, reaches `U` or below at some index `k₀`, and the window is at least as wide as `c⁻¹`
in the sense `L ≤ c * U`, then some index no larger than `k₀` lands inside `[L, U]`. -/
theorem exists_mem_window_of_ratio_lower_bound {u : ℕ → ℝ} {c L U : ℝ} {start k₀ : ℕ}
    (hc : 0 ≤ c) (hratio : ∀ m, start < m → c * u (m - 1) ≤ u m)
    (hstart : L ≤ u start) (hwidth : L ≤ c * U)
    (hk₀ : start ≤ k₀) (hu₀ : u k₀ ≤ U) :
    ∃ k, start ≤ k ∧ k ≤ k₀ ∧ L ≤ u k ∧ u k ≤ U := by
  classical
  have hPex : ∃ k, start ≤ k ∧ u k ≤ U := ⟨k₀, hk₀, hu₀⟩
  obtain ⟨hks, hkU⟩ := Nat.find_spec hPex
  refine ⟨Nat.find hPex, hks, Nat.find_le ⟨hk₀, hu₀⟩, ?_, hkU⟩
  rcases eq_or_lt_of_le hks with heq | hlt
  · rw [← heq]; exact hstart
  · have hprev : ¬ (start ≤ Nat.find hPex - 1 ∧ u (Nat.find hPex - 1) ≤ U) :=
      Nat.find_min hPex (by omega)
    have hprevle : start ≤ Nat.find hPex - 1 := by omega
    have hprevgt : U < u (Nat.find hPex - 1) := by
      by_contra hcon
      exact hprev ⟨hprevle, le_of_not_gt hcon⟩
    have hstep := hratio (Nat.find hPex) hlt
    have hmul : c * U ≤ c * u (Nat.find hPex - 1) :=
      mul_le_mul_of_nonneg_left hprevgt.le hc
    linarith

end GaloisForLFunctions.HTGeometry
