import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Sampling.GuardScales

/-! # Weak seams at reciprocal dates on a single disorder draw -/

open MeasureTheory Filter Finset Set Real
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open FixedHorizon BlockDilations.AdaptiveCuts
noncomputable section

/-- Every bracketing strip out to the largest tested prefix contains a
weak bond, eventually at every reciprocal date on the same draw. -/
theorem gaussian_moving_seams :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ j : ℕ in atTop,
      ∀ n : ℕ, n+1≤4*(2*j)^256 →
        missedBonds n (j^80) ((1/(j:ℝ))^8) ω=∅ := by
  let c := (2*gaussianDensityFloor)^9
  have hc : 0<c := pow_pos (mul_pos zero_lt_two gaussianDensityFloor_pos) _
  apply gaussian_covered_strips _ _ hc
  filter_upwards [eventually_gt_atTop (0:ℕ)] with j hj
  have hJ : (0:ℝ)<j := Nat.cast_pos.mpr hj
  have hj₁ : 1≤(j:ℝ) := by exact_mod_cast hj
  refine ⟨pow_pos (one_div_pos.mpr hJ) _,pow_le_one₀ (one_div_pos.mpr hJ).le ((div_le_one hJ).mpr hj₁),?_⟩
  calc
    c*j ≤ c*(j:ℝ)^8 := mul_le_mul_of_nonneg_left
      (by simpa only [pow_one] using pow_le_pow_right₀ hj₁ (by decide : 1≤8)) hc.le
    _ = _ := by dsimp only [c]; rw [Nat.cast_pow]; field_simp [hJ.ne']

#print axioms gaussian_moving_seams
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
