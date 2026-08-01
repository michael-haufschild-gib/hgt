import GaloisForLFunctions.RHTower.SoninShellTailWeightedSum

/-!
# The channel on a vector with a power tail is bounded uniformly in the height

Combining the split at a shell index with the geometric bound on the outer shells gives a bound on
the step multiplier that does not mention the tower's height: below the cut it is the largest layer
logarithm, above the cut a single geometric term in the cut index.

Only the vector's mass outside a ball enters, so the hypothesis is stated that way — a power decay
of the mass above every radius past the cut.  A tall tower therefore buys nothing against such a
vector: the contribution it can supply is the logarithm at the cut, and no more.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap GaloisForLFunctions.HTGeometry
open scoped InnerProduct InnerProductSpace

/-- **Height-uniform bound from a power decay of the shell masses.** -/
theorem norm_evenLogShellChannel_apply_le_of_powerTail {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    {p : ℕ} (hp : p ≠ 0) (n K : ℕ) (u : evenSubspace) {M C : ℝ}
    (hM : ∀ k, k < K → |Real.log (logShellRadius a r k)| ≤ M)
    (hC : 0 ≤ C) (hone : 1 ≤ logShellRadius a r K)
    (hdecay : ∀ k, K ≤ k → ‖evenIndicatorLayer (logShellRadius a r k)
        (logShellRadius a r (k + 1)) u‖ ^ 2 ≤ C / logShellRadius a r k ^ (p + 1)) :
    ‖evenLogShellChannel a r n u‖ ≤
      Real.sqrt (M ^ 2 * ‖u‖ ^ 2 + 4 * C / a ^ p * ((r ^ p)⁻¹ ^ K * (1 - (r ^ p)⁻¹)⁻¹)) :=
  norm_evenLogShellChannel_apply_le_of_tail a r ha hr n K u M _ hM
    (sum_Ico_logShellRadius_weight_le ha hr hp K n u hC hone hdecay)

/-- The shell masses inherit a power decay from the mass outside a ball. -/
theorem norm_sq_evenIndicatorLayer_le_of_highTail {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    (K : ℕ) (u : evenSubspace) {C : ℝ} {p : ℕ}
    (htail : ∀ t : ℝ, logShellRadius a r K ≤ t → ‖u - evenIndicatorCutoff t u‖ ^ 2 ≤
      C / t ^ (p + 1)) :
    ∀ k, K ≤ k → ‖evenIndicatorLayer (logShellRadius a r k)
        (logShellRadius a r (k + 1)) u‖ ^ 2 ≤ C / logShellRadius a r k ^ (p + 1) := by
  intro k hKk
  have hshell := norm_evenIndicatorLayer_apply_le_high
    (logShellRadius_mono ha hr (Nat.le_succ k)) u
  have hsq : ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 ≤
      ‖u - evenIndicatorCutoff (logShellRadius a r k) u‖ ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self (norm_nonneg _) hshell
  exact le_trans hsq (htail _ (logShellRadius_mono ha hr hKk))

/-- **Height-uniform bound from a power decay of the mass outside a ball.** -/
theorem norm_evenLogShellChannel_apply_le_of_highTail {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    {p : ℕ} (hp : p ≠ 0) (n K : ℕ) (u : evenSubspace) {M C : ℝ}
    (hM : ∀ k, k < K → |Real.log (logShellRadius a r k)| ≤ M)
    (hC : 0 ≤ C) (hone : 1 ≤ logShellRadius a r K)
    (htail : ∀ t : ℝ, logShellRadius a r K ≤ t → ‖u - evenIndicatorCutoff t u‖ ^ 2 ≤
      C / t ^ (p + 1)) :
    ‖evenLogShellChannel a r n u‖ ≤
      Real.sqrt (M ^ 2 * ‖u‖ ^ 2 + 4 * C / a ^ p * ((r ^ p)⁻¹ ^ K * (1 - (r ^ p)⁻¹)⁻¹)) :=
  norm_evenLogShellChannel_apply_le_of_powerTail ha hr hp n K u hM hC hone
    (norm_sq_evenIndicatorLayer_le_of_highTail ha hr K u htail)

/-- **Height-uniform bound in the frequency variable.**  Only the vector's spectral mass outside a
ball enters. -/
theorem norm_evenFourierLogShellChannel_apply_le_of_highTail {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    {p : ℕ} (hp : p ≠ 0) (n K : ℕ) (w : evenSubspace) {M C : ℝ}
    (hM : ∀ k, k < K → |Real.log (logShellRadius a r k)| ≤ M)
    (hC : 0 ≤ C) (hone : 1 ≤ logShellRadius a r K)
    (htail : ∀ t : ℝ, logShellRadius a r K ≤ t →
      ‖evenFourierTransform w - evenIndicatorCutoff t (evenFourierTransform w)‖ ^ 2 ≤
        C / t ^ (p + 1)) :
    ‖evenFourierLogShellChannel a r n w‖ ≤
      Real.sqrt (M ^ 2 * ‖w‖ ^ 2 + 4 * C / a ^ p * ((r ^ p)⁻¹ ^ K * (1 - (r ^ p)⁻¹)⁻¹)) := by
  rw [norm_evenFourierLogShellChannel_apply]
  have h := norm_evenLogShellChannel_apply_le_of_highTail ha hr hp n K (evenFourierTransform w)
    hM hC hone htail
  rwa [evenFourierTransform_isometry] at h

/-- **The contribution a tall frequency-side tower can supply.**  The pairing of a vector with the
channel's image is at most its norm times the height-uniform bound. -/
theorem re_inner_evenFourierLogShellChannel_le {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    {p : ℕ} (hp : p ≠ 0) (n K : ℕ) (w : evenSubspace) {M C : ℝ}
    (hM : ∀ k, k < K → |Real.log (logShellRadius a r k)| ≤ M)
    (hC : 0 ≤ C) (hone : 1 ≤ logShellRadius a r K)
    (htail : ∀ t : ℝ, logShellRadius a r K ≤ t →
      ‖evenFourierTransform w - evenIndicatorCutoff t (evenFourierTransform w)‖ ^ 2 ≤
        C / t ^ (p + 1)) :
    (⟪w, evenFourierLogShellChannel a r n w⟫_ℂ).re ≤
      ‖w‖ * Real.sqrt (M ^ 2 * ‖w‖ ^ 2 + 4 * C / a ^ p * ((r ^ p)⁻¹ ^ K * (1 - (r ^ p)⁻¹)⁻¹)) := by
  have h1 : (⟪w, evenFourierLogShellChannel a r n w⟫_ℂ).re ≤ ‖(⟪w,
      evenFourierLogShellChannel a r n w⟫_ℂ)‖ := Complex.re_le_norm _
  have h2 : ‖(⟪w, evenFourierLogShellChannel a r n w⟫_ℂ)‖ ≤
      ‖w‖ * ‖evenFourierLogShellChannel a r n w‖ := norm_inner_le_norm _ _
  have h3 := norm_evenFourierLogShellChannel_apply_le_of_highTail ha hr hp n K w hM hC hone htail
  exact le_trans (le_trans h1 h2) (mul_le_mul_of_nonneg_left h3 (norm_nonneg w))

end RHTower

