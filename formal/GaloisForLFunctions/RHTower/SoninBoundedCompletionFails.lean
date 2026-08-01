import GaloisForLFunctions.RHTower.SoninCompletionMustGrowLinearly

/-!
# A bounded contribution is a sublinear one

A contribution bounded in absolute value divides by the scale to zero, so the sublinear failure
covers it.  In particular a completion built from a uniformly bounded operator family contributes at
most the bound times the squared packet norm, and therefore fails.

This places the bounded case inside the sublinear one on the schedule's own scales, rather than
leaving it to a separate argument.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology InnerProduct InnerProductSpace

/-- A bounded function divides by the argument to zero. -/
theorem tendsto_div_atTop_nhds_zero_of_bounded {g : ℝ → ℝ} {Bnd : ℝ}
    (hg : ∀ r : ℝ, |g r| ≤ Bnd) : Tendsto (fun r : ℝ => g r / r) atTop (𝓝 0) := by
  have hBnd : 0 ≤ Bnd := le_trans (abs_nonneg (g 0)) (hg 0)
  have hupper : Tendsto (fun r : ℝ => Bnd / r) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop tendsto_id Bnd
  have hlower : Tendsto (fun r : ℝ => -(Bnd / r)) atTop (𝓝 0) := by
    simpa using hupper.neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have h := (abs_le.mp (hg r)).1
    have hstep : -Bnd / r ≤ g r / r := by gcongr
    rwa [neg_div] at hstep
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have h := (abs_le.mp (hg r)).2
    gcongr

/-- **The pairing of a vector with a bounded operator's image.** -/
theorem re_inner_self_le_opNorm_mul_sq {C : evenSubspace →L[ℂ] evenSubspace} {B W : ℝ}
    (hC : ‖C‖ ≤ B) {w : evenSubspace} (hw : ‖w‖ ≤ W) (hBnn : 0 ≤ B) :
    (⟪w, C w⟫_ℂ).re ≤ B * W ^ 2 := by
  have h1 : (⟪w, C w⟫_ℂ).re ≤ ‖(⟪w, C w⟫_ℂ)‖ := Complex.re_le_norm _
  have h2 : ‖(⟪w, C w⟫_ℂ)‖ ≤ ‖w‖ * ‖C w‖ := norm_inner_le_norm _ _
  have h3 : ‖C w‖ ≤ ‖C‖ * ‖w‖ := C.le_opNorm w
  have hwnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hCnn : (0 : ℝ) ≤ ‖C‖ := norm_nonneg C
  calc (⟪w, C w⟫_ℂ).re ≤ ‖w‖ * ‖C w‖ := le_trans h1 h2
    _ ≤ ‖w‖ * (‖C‖ * ‖w‖) := mul_le_mul_of_nonneg_left h3 hwnn
    _ = ‖C‖ * ‖w‖ ^ 2 := by ring
    _ ≤ B * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg _)
    _ ≤ B * W ^ 2 := by
        have hsq : ‖w‖ ^ 2 ≤ W ^ 2 := by
          rw [pow_two, pow_two]
          exact mul_self_le_mul_self hwnn hw
        exact mul_le_mul_of_nonneg_left hsq hBnn

/-- **No bounded completion restores the floor.** -/
theorem not_bddBelow_soninCompletedPacketValueVar_of_bounded (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) (f : ℝ → ℝ) {Bnd : ℝ} (hf : ∀ r : ℝ, |f r| ≤ Bnd) :
    ∃ (κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ soninCompletedPacketValueVar s a b c
          (fun i => soninShellCutScale b c (Nstart + i) κ) hp
          (fun i => f (soninShellCutScale b c (Nstart + i) κ)) :=
  not_bddBelow_soninCompletedPacketValueVar_of_sublinear N₀ hN₀ a b c q hbc ha hab hb haq hqb f
    (tendsto_div_atTop_nhds_zero_of_bounded hf)

end RHTower
