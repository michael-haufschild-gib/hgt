import GaloisForLFunctions.WindowTowerOfSpecZ.TheFirstFoldPaysANegativeFrozenDirection

/-!
# The first stage rejects the frozen and the flipped divisor

On a window of length `21/20 ∈ (log 2, log 3)` the prime `2` is the only prime that acts, and Weil's
form with prime-two weight `w` is the first-stage form
`W_w(H) = Q₁(H) − 2w∫H(u)H(u + log 2)du`, with `Q₁` the frozen form (WTZ `stageForm 1`). The weight
of `ζ` is `w₂ = log 2/√2` (`firstStageForm_zeta`).

* **The admissible weights form an interval** (`convex_firstStageWeights`).
* **The frozen divisor fails** (`zero_notMem_firstStageWeights`): WTZ's first-stage test has
  `Q₁(H) < 0`.
* **The flipped divisor fails** (`neg_notMem_firstStageWeights`): on the same test
  `W_{−w₂}(H) = 2Q₁(H) − W(H) < 0`, since `W(H) > 0`.
* **The sign of `Λ(2)` is forced** (`pos_of_mem_firstStageWeights`): if the first stage of `ζ` is
  nonnegative, every admissible prime-two weight is positive, since a convex set containing `w₂`
  and a weight `≤ 0` contains `0`.

So the first prime stage is a calibration of the prime-two weight: it rejects the frozen and the
flipped divisors, and it reads `Λ(2)` only through an interval of positive weights.
-/

open MeasureTheory Set Filter Topology Zeta23

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open GaloisForLFunctions.WindowTowerOfSpecZ GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
open SpacingScaleHarmonicAnalysis _root_.RHTower.WeilMarkovPole

/-- Weil's form of the first stage with prime-two weight `w`. -/
def firstStageForm (w : ℝ) (H : ℝ → ℝ) : ℝ :=
  stageForm 1 H - 2 * w * ∫ u, H u * H (u + Real.log 2)

theorem windowLevel_first_stage : windowLevel (21 / 20) = 2 := by
  unfold windowLevel
  apply (Nat.floor_eq_iff (Real.exp_pos (21 / 20 : ℝ)).le).mpr
  constructor
  · have h : Real.log 2 ≤ (21 / 20 : ℝ) := by linarith only [Real.log_two_lt_d9]
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2), Nat.cast_ofNat] using
      Real.exp_le_exp.mpr h
  · have h : (21 / 20 : ℝ) < Real.log 3 := by linarith only [Real.log_three_gt_d9]
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 3), Nat.cast_ofNat,
      show (2 : ℝ) + 1 = 3 by norm_num] using Real.exp_lt_exp.mpr h

/-- At the weight of `ζ` the first-stage form is Weil's form. -/
theorem firstStageForm_zeta {H : ℝ → ℝ} (hH : IsWindowTest (21 / 20) H) :
    firstStageForm (primeJumpWeight 2) H = weilQuad H := by
  have hlocal := weilQuad_eq_markovForm_windowLevel hH
  rw [windowLevel_first_stage] at hlocal
  have hstep := markovForm_succ hH.continuous hH.hasCompactSupport (N := 1) (by norm_num)
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hstep
  unfold firstStageForm stageForm
  linarith only [hstep, hlocal]

/-- The prime-two weights for which the first stage is nonnegative. -/
def firstStageWeights : Set ℝ :=
  {w | ∀ H : ℝ → ℝ, IsWindowTest (21 / 20) H → 0 ≤ firstStageForm w H}

theorem first_stage_nonneg_iff :
    (∀ H : ℝ → ℝ, IsWindowTest (21 / 20) H → 0 ≤ weilQuad H) ↔
      primeJumpWeight 2 ∈ firstStageWeights := by
  constructor
  · intro h H hH; rw [firstStageForm_zeta hH]; exact h H hH
  · intro h H hH; rw [← firstStageForm_zeta hH]; exact h H hH

/-- **The admissible weights form an interval.** -/
theorem convex_firstStageWeights : Convex ℝ firstStageWeights := by
  intro w₁ h₁ w₂ h₂ s t hs ht hst H hH
  have e₁ := h₁ H hH
  have e₂ := h₂ H hH
  have e : firstStageForm (s • w₁ + t • w₂) H =
      s * firstStageForm w₁ H + t * firstStageForm w₂ H := by
    unfold firstStageForm
    simp only [smul_eq_mul]
    have : stageForm 1 H = (s + t) * stageForm 1 H := by rw [hst, one_mul]
    linear_combination this
  rw [e]
  exact add_nonneg (mul_nonneg hs e₁) (mul_nonneg ht e₂)

/-- **The frozen divisor fails at the first stage.** -/
theorem zero_notMem_firstStageWeights : (0 : ℝ) ∉ firstStageWeights := by
  intro h
  obtain ⟨H, hH, hneg, _⟩ := exists_first_stage_negative_frozen_positive_complete
  have := h H hH
  unfold firstStageForm at this
  linarith

/-- **The flipped divisor fails at the first stage.** -/
theorem neg_notMem_firstStageWeights : -primeJumpWeight 2 ∉ firstStageWeights := by
  intro h
  obtain ⟨H, hH, hneg, hpos⟩ := exists_first_stage_negative_frozen_positive_complete
  have hf := h H hH
  have hz := firstStageForm_zeta hH
  unfold firstStageForm at hf hz
  linarith

theorem primeJumpWeight_two_pos : 0 < primeJumpWeight 2 := by
  unfold primeJumpWeight
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  push_cast
  exact div_pos (Real.log_pos (by norm_num)) (by positivity)

/-- **The sign of `Λ(2)` is forced.** If the first stage of `ζ` is nonnegative, every admissible
prime-two weight is positive. -/
theorem pos_of_mem_firstStageWeights
    (hζ : ∀ H : ℝ → ℝ, IsWindowTest (21 / 20) H → 0 ≤ weilQuad H) {w : ℝ}
    (hw : w ∈ firstStageWeights) : 0 < w := by
  by_contra hle
  push Not at hle
  have h₂ := first_stage_nonneg_iff.mp hζ
  have hp := primeJumpWeight_two_pos
  set w₂ := primeJumpWeight 2
  have hd : 0 < w₂ - w := by linarith
  -- `0 = s w + t w₂` with `s = w₂/(w₂ − w)`, `t = −w/(w₂ − w)`
  have hmem := convex_firstStageWeights hw h₂ (a := w₂ / (w₂ - w)) (b := -w / (w₂ - w))
    (div_nonneg hp.le hd.le) (div_nonneg (by linarith) hd.le) (by field_simp; ring)
  have h0 : (w₂ / (w₂ - w)) • w + (-w / (w₂ - w)) • w₂ = 0 := by
    simp only [smul_eq_mul]; field_simp; ring
  rw [h0] at hmem
  exact zero_notMem_firstStageWeights hmem

end GaloisForLFunctions.SignedWindowCriticality

end
