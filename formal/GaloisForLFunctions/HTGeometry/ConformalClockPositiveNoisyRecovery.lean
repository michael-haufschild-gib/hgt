import GaloisForLFunctions.HTGeometry.ConformalClockNoisyMatrixRecovery
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Strict-positive noisy conformal scale recovery

For an exponential reference scale, noisy recovery of a prescribed Lipschitz error
anchor is equivalent to the existing weighted-noise inequalities and one exact
pointwise positivity guard. No uniform positive lower bound on the reference scale
is required. The signed distance tent realizes every feasible anchor.

The second theorem uses the actual projective matrix reporters, with independent
common scalar defects. The third supplies an exponential competing scale through
half its logarithm. The Lipschitz budget belongs to the physical scale difference;
no continuity, Lipschitz bound, or differentiability of its logarithm is asserted.
-/

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [PseudoMetricSpace X]

/-- Exact weighted-error feasibility with a strictly positive exponential reference scale. -/
theorem positiveClockGap_feasible_iff (sigma : X → ℝ) (L epsilon : NNReal)
    (g : X → NNReal) (p : X) (a : ℝ) :
    (∃ u : X → ℝ, LipschitzWith L u ∧ u p = a ∧
      (∀ x, (g x : ℝ) * |u x| ≤ epsilon) ∧
      ∀ x, 0 < Real.exp (2 * sigma x) + u x) ↔
    (∀ x, (g x : ℝ) * |a| ≤ (epsilon : ℝ) + (g x : ℝ) * L * dist x p) ∧
      ∀ x, 0 < Real.exp (2 * sigma x) + min 0 (a + (L : ℝ) * dist x p) := by
  constructor
  · rintro ⟨u, hu, ha, hnoise, hpositive⟩
    refine ⟨(weightedClockGap_feasible_iff_affine L epsilon g p a).mp
      ⟨u, hu, ha, hnoise⟩, ?_⟩
    intro x
    by_cases hx : 0 ≤ a + (L : ℝ) * dist x p
    · rw [min_eq_left hx, add_zero]
      exact Real.exp_pos _
    · rw [min_eq_right (le_of_not_ge hx)]
      have hb := hu.le_add_mul x p
      rw [ha] at hb
      linarith [hpositive x]
  · rintro ⟨hnoise, hguard⟩
    have henv := (weightedClockGap_feasible_iff L epsilon g p a).mp
      ((weightedClockGap_feasible_iff_affine L epsilon g p a).mpr hnoise)
    refine ⟨clockGapExtremizer L p a, clockGapExtremizer_lipschitz L p a,
      clockGapExtremizer_anchor L p a, ?_, ?_⟩
    · intro x
      rw [clockGapExtremizer_abs]
      exact henv x
    · intro x
      by_cases ha : 0 ≤ a
      · have hu : 0 ≤ clockGapExtremizer L p a x := by
          rw [clockGapExtremizer, if_pos ha, clockGapEnvelope]
          exact le_max_left _ _
        linarith [Real.exp_pos (2 * sigma x)]
      · have heq : clockGapExtremizer L p a x = min 0 (a + (L : ℝ) * dist x p) := by
          rw [clockGapExtremizer, if_neg ha, clockGapEnvelope, abs_of_neg (lt_of_not_ge ha)]
          by_cases hx : 0 ≤ a + (L : ℝ) * dist x p
          · rw [min_eq_left hx, max_eq_left (by linarith)]
            simp
          · rw [min_eq_right (le_of_not_ge hx), max_eq_right (by linarith)]
            ring
        rw [heq]
        exact hguard x

/-- Strict positivity adds exactly the stated guard to observed matrix-noise feasibility. -/
theorem positiveNoisyProjectiveClock_feasible_iff {n : ℕ}
    (M : X → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (sigma : X → ℝ)
    (d₁ d₂ : X → ℂ) (L epsilon : NNReal) (p : X) (a : ℝ) :
    (∃ other : X → ℝ,
      LipschitzWith L (fun x => other x - Real.exp (2 * sigma x)) ∧
      other p - Real.exp (2 * sigma p) = a ∧
      (∀ x, ‖projectiveDelayPanel ((other x : ℂ) • M x + d₁ x • 1) -
        projectiveDelayPanel ((Real.exp (2 * sigma x) : ℂ) • M x + d₂ x • 1)‖ ≤ epsilon) ∧
      ∀ x, 0 < other x) ↔
    (∀ x, ‖projectiveDelayPanel (M x)‖ * |a| ≤
      (epsilon : ℝ) + ‖projectiveDelayPanel (M x)‖ * L * dist x p) ∧
      ∀ x, 0 < Real.exp (2 * sigma x) + min 0 (a + (L : ℝ) * dist x p) := by
  let g : X → NNReal := fun x => ⟨‖projectiveDelayPanel (M x)‖, norm_nonneg _⟩
  have hg (x : X) : (g x : ℝ) = ‖projectiveDelayPanel (M x)‖ := rfl
  change _ ↔ (∀ x, (g x : ℝ) * |a| ≤ (epsilon : ℝ) + (g x : ℝ) * L * dist x p) ∧ _
  rw [← positiveClockGap_feasible_iff sigma L epsilon g p a]
  constructor
  · rintro ⟨other, hu, ha, hnoise, hpositive⟩
    refine ⟨fun x => other x - Real.exp (2 * sigma x), hu, ha, ?_, ?_⟩
    · intro x
      have hb := hnoise x
      rw [projectiveMixedClock_noise_exact] at hb
      rw [hg x]
      simpa only [mul_comm] using hb
    · intro x
      convert hpositive x using 1
      ring
  · rintro ⟨u, hu, ha, hnoise, hpositive⟩
    refine ⟨fun x => Real.exp (2 * sigma x) + u x, ?_, ?_, ?_, hpositive⟩
    · simpa only [add_sub_cancel_left] using hu
    · simpa only [add_sub_cancel_left] using ha
    · intro x
      rw [projectiveMixedClock_noise_exact]
      have hb := hnoise x
      rw [hg x] at hb
      simpa only [add_sub_cancel_left, mul_comm] using hb

/-- The complete positive-scale classification expressed through an exponential competitor. -/
theorem conformalLogScale_noisy_feasible_iff {n : ℕ}
    (M : X → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (sigma : X → ℝ)
    (d₁ d₂ : X → ℂ) (L epsilon : NNReal) (p : X) (a : ℝ) :
    (∃ tau : X → ℝ,
      LipschitzWith L (fun x => Real.exp (2 * tau x) - Real.exp (2 * sigma x)) ∧
      Real.exp (2 * tau p) - Real.exp (2 * sigma p) = a ∧
      ∀ x, ‖projectiveDelayPanel ((Real.exp (2 * tau x) : ℂ) • M x + d₁ x • 1) -
        projectiveDelayPanel ((Real.exp (2 * sigma x) : ℂ) • M x + d₂ x • 1)‖ ≤ epsilon) ↔
    (∀ x, ‖projectiveDelayPanel (M x)‖ * |a| ≤
      (epsilon : ℝ) + ‖projectiveDelayPanel (M x)‖ * L * dist x p) ∧
      ∀ x, 0 < Real.exp (2 * sigma x) + min 0 (a + (L : ℝ) * dist x p) := by
  rw [← positiveNoisyProjectiveClock_feasible_iff M sigma d₁ d₂ L epsilon p a]
  constructor
  · rintro ⟨tau, hu, ha, hnoise⟩
    exact ⟨fun x => Real.exp (2 * tau x), hu, ha, hnoise, fun x => Real.exp_pos _⟩
  · rintro ⟨other, hu, ha, hnoise, hpositive⟩
    let tau : X → ℝ := fun x => Real.log (other x) / 2
    have he (x : X) : Real.exp (2 * tau x) = other x := by
      dsimp [tau]
      rw [show 2 * (Real.log (other x) / 2) = Real.log (other x) by ring,
        Real.exp_log (hpositive x)]
    refine ⟨tau, ?_, ?_, ?_⟩
    · simpa only [he] using hu
    · simpa only [he] using ha
    · simpa only [he] using hnoise

end GaloisForLFunctions.HTGeometry
