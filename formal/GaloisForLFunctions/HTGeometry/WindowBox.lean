import GaloisForLFunctions.HTGeometry.SourceBox

/-!
# Replacing a degree window inside the coefficient box

Zeroing a degree window of a point of the coefficient box, and then writing a bounded window into it,
stays inside the box and changes no coefficient outside the window.  The coefficient sequence of the
result is the zeroed sequence plus the window sequence, which is what turns free window jets into
free increments of the jets of the source.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The zero point of a ball of the coefficient box. -/
theorem zero_mem_boxBall (k : ℕ) : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) ((k.factorial : ℝ))⁻¹ := by
  rw [Metric.mem_closedBall, dist_self]
  positivity

/-- A point of the box with a degree window zeroed. -/
def zeroWindowBox (c : sourceBox) (N W : ℕ) : sourceBox :=
  fun k => if N ≤ k ∧ k - N < W then ⟨0, zero_mem_boxBall k⟩ else c k

theorem boxSeq_zeroWindowBox_of_outside (c : sourceBox) (N W : ℕ) {k : ℕ}
    (hk : ¬ (N ≤ k ∧ k - N < W)) : boxSeq (zeroWindowBox c N W) k = boxSeq c k := by
  rw [boxSeq, zeroWindowBox, if_neg hk]
  rfl

theorem boxSeq_zeroWindowBox_of_inside (c : sourceBox) (N W : ℕ) {k : ℕ}
    (hk : N ≤ k ∧ k - N < W) : boxSeq (zeroWindowBox c N W) k = 0 := by
  rw [boxSeq, zeroWindowBox, if_pos hk]

theorem zeroWindowBox_eq_of_lt (c : sourceBox) (N W : ℕ) {k : ℕ} (hk : k < N) :
    zeroWindowBox c N W k = c k := by
  rw [zeroWindowBox, if_neg (by omega)]

/-- A point of the box with a bounded window written into a zeroed range. -/
def setWindowBox (c : sourceBox) (N W : ℕ) (w : Fin W → ℂ)
    (hw : ∀ i : Fin W, ‖w i‖ ≤ (((N + (i : ℕ)).factorial : ℝ))⁻¹) : sourceBox :=
  fun k => if h : N ≤ k ∧ k - N < W then
      ⟨w ⟨k - N, h.2⟩, by
        rw [Metric.mem_closedBall, dist_zero_right]
        have hb := hw ⟨k - N, h.2⟩
        simpa [show N + (k - N) = k by omega] using hb⟩
    else c k

theorem setWindowBox_eq_of_lt (c : sourceBox) (N W : ℕ) (w : Fin W → ℂ)
    (hw : ∀ i : Fin W, ‖w i‖ ≤ (((N + (i : ℕ)).factorial : ℝ))⁻¹) {k : ℕ} (hk : k < N) :
    setWindowBox c N W w hw k = c k := by
  rw [setWindowBox, dif_neg (by omega)]

/-- **The coefficient sequence of a written window is the base plus the window sequence.** -/
theorem boxSeq_setWindowBox (c : sourceBox) (N W : ℕ) (w : Fin W → ℂ)
    (hw : ∀ i : Fin W, ‖w i‖ ≤ (((N + (i : ℕ)).factorial : ℝ))⁻¹)
    (hc : ∀ k : ℕ, N ≤ k → k - N < W → boxSeq c k = 0) :
    boxSeq (setWindowBox c N W w hw) = fun k => boxSeq c k + windowSeq N W w k := by
  funext k
  by_cases h : N ≤ k ∧ k - N < W
  · rw [boxSeq, setWindowBox, dif_pos h, hc k h.1 h.2, zero_add, windowSeq, dif_pos h]
  · rw [boxSeq, setWindowBox, dif_neg h, windowSeq, dif_neg h, add_zero]
    rfl

end

end GaloisForLFunctions.HTGeometry
