import GaloisForLFunctions.RHTower.CCM.CCMCoherentExteriorMomentGammaRate

/-!
# The shrinking frequency window of exact moment cancellation

The corrected symbols converge uniformly back to the original symbols. Their
cancelled first moment is visible on the shrinking scale `ξ = y / βₙ`, where
the exact limiting profile is `M * (y - sin y)`. Thus a small Gamma correction
does not provide a uniform Taylor estimate on a fixed frequency window.
-/

noncomputable section
open Filter Topology

namespace RHTower

theorem abs_ccmActualHeadMomentCancelledSineAt_sub_original_le
    (a : SuzukiPositiveAperture) (N : ℕ) (r : ℝ) (n : ℕ) (ξ : ℝ) :
    |ccmActualHeadMomentCancelledSineAt a N r n ξ -
      ccmActualHeadMidpointSineSymbol (2*a.1) N r ξ| ≤
      |ccmActualHeadMidpointSignedMoment (2*a.1) N r| / ccmMidpointExteriorFrequencyAt a r n := by
  unfold ccmActualHeadMomentCancelledSineAt
  rw [sub_sub_cancel_left, abs_neg, abs_mul, abs_div,
    abs_of_pos (ccmMidpointExteriorFrequencyAt_pos a r n)]
  exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
    (div_nonneg (abs_nonneg _) (ccmMidpointExteriorFrequencyAt_pos a r n).le)).trans_eq (mul_one _)

theorem abs_ccmActualHeadMomentCancelledCurrentAt_sub_original_le
    (a : SuzukiPositiveAperture) (N : ℕ) (r : ℝ) (n : ℕ) (ξ : ℝ) :
    |ccmActualHeadMomentCancelledCurrentAt a N r n ξ -
      ccmActualHeadMidpointCurrentSymbol (2*a.1) N r ξ| ≤
      2 * (|ccmActualHeadMidpointSignedMoment (2*a.1) N r| /
        ccmMidpointExteriorFrequencyAt a r n) := by
  unfold ccmActualHeadMomentCancelledCurrentAt ccmActualHeadMidpointCurrentSymbol
  rw [← mul_sub, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hs := abs_ccmActualHeadMomentCancelledSineAt_sub_original_le a N r n ξ
  exact mul_le_mul ((mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)).trans_eq
    (mul_one _)) hs (abs_nonneg _) (by positivity)

/-- A global error bound for the exact rescaled cancellation profile. -/
theorem abs_ccmActualHeadMomentCancelledSineAt_boundary_error_le
    (a : SuzukiPositiveAperture) (N : ℕ) (r y : ℝ) (n : ℕ) :
    |ccmMidpointExteriorFrequencyAt a r n *
        ccmActualHeadMomentCancelledSineAt a N r n (y/ccmMidpointExteriorFrequencyAt a r n) -
      ccmActualHeadMidpointSignedMoment (2*a.1) N r*(y-Real.sin y)| ≤
      (|y|^3/6*ccmActualHeadMidpointCubicMoment (2*a.1) N r) /
        (ccmMidpointExteriorFrequencyAt a r n)^2 := by
  let β := ccmMidpointExteriorFrequencyAt a r n
  have hβ : 0 < β := ccmMidpointExteriorFrequencyAt_pos a r n
  have he : β * ccmActualHeadMomentCancelledSineAt a N r n (y/β) -
      ccmActualHeadMidpointSignedMoment (2*a.1) N r*(y-Real.sin y) =
      β*(ccmActualHeadMidpointSineSymbol (2*a.1) N r (y/β) -
        (y/β)*ccmActualHeadMidpointSignedMoment (2*a.1) N r) := by
    unfold ccmActualHeadMomentCancelledSineAt
    change β * (_ - (_/β)*Real.sin (β*(y/β))) - _ = _
    rw [mul_div_cancel₀ _ (ne_of_gt hβ)]
    field_simp [ne_of_gt hβ]
    ring
  change |β * ccmActualHeadMomentCancelledSineAt a N r n (y/β) - _| ≤ _
  rw [he, abs_mul, abs_of_pos hβ]
  calc
    _ ≤ β * (|y/β|^3/6*ccmActualHeadMidpointCubicMoment (2*a.1) N r) :=
      mul_le_mul_of_nonneg_left
        (abs_ccmActualHeadMidpointSineSymbol_sub_moment_le (2*a.1) N r (y/β)) hβ.le
    _ = _ := by
      rw [abs_div, abs_of_pos hβ]
      change β * ((|y|/β)^3/6*_) = _/β^2
      field_simp [ne_of_gt hβ]

private theorem tendsto_of_inverse_square_error (a : SuzukiPositiveAperture) (r : ℝ)
    (u : ℕ → ℝ) (L C : ℝ)
    (hu : ∀ n, |u n-L| ≤ C/(ccmMidpointExteriorFrequencyAt a r n)^2) :
    Tendsto u atTop (𝓝 L) := by
  have hi : Tendsto (fun n => 1/ccmMidpointExteriorFrequencyAt a r n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_ccmMidpointExteriorFrequencyAt a r)
  have hb : Tendsto (fun n => C/(ccmMidpointExteriorFrequencyAt a r n)^2) atTop (𝓝 0) := by
    simpa only [div_pow, one_pow, mul_one_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      (hi.pow 2).const_mul C
  have hz : Tendsto (fun n => u n-L) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using hu n) hb
  simpa only [sub_add_cancel, zero_add] using hz.add_const L

/-- The first moment survives as a non-polynomial profile in a shrinking window. -/
theorem tendsto_ccmActualHeadMomentCancelledSineAt_boundary
    (a : SuzukiPositiveAperture) (N : ℕ) (r y : ℝ) :
    Tendsto (fun n => ccmMidpointExteriorFrequencyAt a r n *
      ccmActualHeadMomentCancelledSineAt a N r n (y/ccmMidpointExteriorFrequencyAt a r n)) atTop
      (𝓝 (ccmActualHeadMidpointSignedMoment (2*a.1) N r*(y-Real.sin y))) :=
  tendsto_of_inverse_square_error a r _ _ _
    (fun n => abs_ccmActualHeadMomentCancelledSineAt_boundary_error_le a N r y n)

private theorem tendsto_scaled_sin (a : SuzukiPositiveAperture) (r y : ℝ) :
    Tendsto (fun n => ccmMidpointExteriorFrequencyAt a r n *
      Real.sin (y/ccmMidpointExteriorFrequencyAt a r n)) atTop (𝓝 y) := by
  apply tendsto_of_inverse_square_error a r _ y (|y|^3/6)
  intro n
  let β := ccmMidpointExteriorFrequencyAt a r n
  have hβ : 0 < β := ccmMidpointExteriorFrequencyAt_pos a r n
  have he : β*Real.sin (y/β)-y = β*(Real.sin (y/β)-y/β) := by
    field_simp [ne_of_gt hβ]
  change |β*Real.sin (y/β)-y| ≤ (|y|^3/6)/β^2
  rw [he, abs_mul, abs_of_pos hβ]
  calc
    _ ≤ β*(|y/β|^3/6) := mul_le_mul_of_nonneg_left
      (by simpa only [abs_sub_comm] using Real.abs_sub_sin_le (y/β)) hβ.le
    _ = _ := by
      rw [abs_div, abs_of_pos hβ]
      field_simp [ne_of_gt hβ]

/-- The signed current has an exact rescaled profile, retaining its arithmetic sign. -/
theorem tendsto_ccmActualHeadMomentCancelledCurrentAt_boundary
    (a : SuzukiPositiveAperture) (N : ℕ) (r y : ℝ) :
    Tendsto (fun n => (ccmMidpointExteriorFrequencyAt a r n)^2 *
      ccmActualHeadMomentCancelledCurrentAt a N r n (y/ccmMidpointExteriorFrequencyAt a r n)) atTop
      (𝓝 (-2*(Real.pi*r*y)*
        (ccmActualHeadMidpointSignedMoment (2*a.1) N r*(y-Real.sin y)))) := by
  have h := ((tendsto_scaled_sin a r (Real.pi*r*y)).const_mul (-2)).mul
    (tendsto_ccmActualHeadMomentCancelledSineAt_boundary a N r y)
  convert h using 1
  funext n
  unfold ccmActualHeadMomentCancelledCurrentAt
  rw [mul_div_assoc]
  ring

end RHTower
