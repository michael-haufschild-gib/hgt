import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A smooth cutoff for a compact interval avoiding the origin

For a bounded interval `[a,b]` not containing the origin there is a smooth compactly supported
function equal to one on a neighbourhood of `[a,b]` and vanishing on a neighbourhood of the origin.
Multiplying by it turns a function that is smooth only away from the origin into a globally smooth
function of temperate growth agreeing with the original one near `[a,b]`.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- **A smooth cutoff equal to one near a compact interval avoiding the origin.** -/
theorem exists_interval_cutoff {a b : ℝ} (hab : a < b) (h0 : (0 : ℝ) ∉ Icc a b) :
    ∃ (χ : ℝ → ℝ) (δ : ℝ), 0 < δ ∧
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      (∀ x ∈ Ioo (a - δ) (b + δ), χ x = 1) ∧ (∀ x, |x| ≤ 2 * δ → χ x = 0) := by
  have hsign : 0 < a ∨ b < 0 := by
    by_contra hcon
    push Not at hcon
    exact h0 ⟨hcon.1, hcon.2⟩
  set M : ℝ := min |a| |b| with hM
  have hMpos : 0 < M := by
    rcases hsign with h | h
    · have hb : 0 < b := lt_trans h hab
      rw [hM, abs_of_pos h, abs_of_pos hb]
      exact lt_min h hb
    · have hbneg : |b| = -b := abs_of_neg h
      have haneg : |a| = -a := abs_of_neg (lt_trans hab h)
      rw [hM, haneg, hbneg]
      refine lt_min (by linarith) (by linarith)
  set c : ℝ := (a + b) / 2 with hc
  set δ : ℝ := M / 4 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hcabs : |c| = (b - a) / 2 + M := by
    rcases hsign with h | h
    · have hb : 0 < b := lt_trans h hab
      have hcpos : 0 < c := by rw [hc]; linarith
      have hMa : M = a := by
        rw [hM, abs_of_pos h, abs_of_pos hb]
        exact min_eq_left hab.le
      rw [abs_of_pos hcpos, hMa, hc]
      ring
    · have ha : a < 0 := lt_trans hab h
      have hcneg : c < 0 := by rw [hc]; linarith
      have hMb : M = -b := by
        rw [hM, abs_of_neg ha, abs_of_neg h]
        exact min_eq_right (by linarith)
      rw [abs_of_neg hcneg, hMb, hc]
      ring
  have hrin : 0 < (b - a) / 2 + δ := by linarith
  have hlt : (b - a) / 2 + δ < (b - a) / 2 + 2 * δ := by linarith
  set f : ContDiffBump c := ⟨(b - a) / 2 + δ, (b - a) / 2 + 2 * δ, hrin, hlt⟩ with hf
  have hrIn : f.rIn = (b - a) / 2 + δ := rfl
  have hrOut : f.rOut = (b - a) / 2 + 2 * δ := rfl
  refine ⟨fun x => f x, δ, hδpos, f.contDiff, f.hasCompactSupport, ?_, ?_⟩
  · intro x hx
    refine f.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq, hrIn, abs_le]
    obtain ⟨h1, h2⟩ := hx
    constructor <;> · rw [hc]; linarith
  · intro x hx
    refine f.zero_of_le_dist ?_
    rw [Real.dist_eq, hrOut]
    have hge : |c| - |x| ≤ |x - c| := by
      have := abs_sub_abs_le_abs_sub c x
      have habs : |c - x| = |x - c| := abs_sub_comm c x
      linarith [this, habs.le, habs.ge]
    have hMδ : M = 4 * δ := by rw [hδ]; ring
    rw [hcabs, hMδ] at hge
    linarith

end GaloisForLFunctions.HTGeometry
