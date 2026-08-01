import GaloisForLFunctions.RHTower.SoninShellCutScheduledSlack

/-!
# Choosing the prescribed product

Both slack terms that survive the scale substitution vanish as the prescribed product grows: the
middle one because it is a majorant weighted by the root of its own argument, the high-side one
because its exponent is negative.  So for any target there is a product beyond which their sum is
below it.

This fixes the first of the schedule's two constants, and fixes it independently of the cut.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open Filter
open scoped Topology

/-- The middle slack constant vanishes as the product grows. -/
theorem tendsto_middleSlackConst_atTop (a q A : ℝ) (hA : 0 ≤ A) (haq : a < q) :
    Tendsto (fun κ : ℝ => Real.sqrt (A * (κ * (q - a))) * soninRefTailSup (κ * (q - a)))
      atTop (𝓝 0) := by
  have hgap : (0 : ℝ) < q - a := by linarith
  have hinner : Tendsto (fun κ : ℝ => κ * (q - a)) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hgap tendsto_id
  exact (tendsto_sqrt_const_mul_soninRefTailSup_atTop hA).comp hinner

/-- The high-side slack constant vanishes as the product grows. -/
theorem tendsto_highSlackConst_atTop (b C : ℝ) (hb : 0 < b) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) :
    Tendsto (fun κ : ℝ => Real.sqrt (C * (κ * b) ^ (1 - (2 * N₀ : ℝ)))) atTop (𝓝 0) := by
  have hinner : Tendsto (fun κ : ℝ => κ * b) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hb tendsto_id
  exact (tendsto_sqrt_const_mul_rpow_atTop C hN₀).comp hinner

/-- **The product can be chosen.**  Beyond some product both surviving slack terms, together, are
below any positive target. -/
theorem exists_kappa_slack_le (a q b A C : ℝ) (hA : 0 ≤ A) (haq : a < q) (hb : 0 < b)
    {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (D : ℝ) {target : ℝ} (htarget : 0 < target) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ ≤ κ →
      D * (Real.sqrt (A * (κ * (q - a))) * soninRefTailSup (κ * (q - a))) +
        Real.sqrt (C * (κ * b) ^ (1 - (2 * N₀ : ℝ))) ≤ target := by
  have hmid := (tendsto_middleSlackConst_atTop a q A hA haq).const_mul D
  rw [mul_zero] at hmid
  have hhigh := tendsto_highSlackConst_atTop b C hb hN₀
  have hsum := hmid.add hhigh
  rw [add_zero] at hsum
  rw [Metric.tendsto_atTop] at hsum
  obtain ⟨U, hU⟩ := hsum target htarget
  refine ⟨max U 1, lt_of_lt_of_le zero_lt_one (le_max_right U 1), fun κ hκ => ?_⟩
  have hUκ : U ≤ κ := le_trans (le_max_left U 1) hκ
  have h := hU κ hUκ
  rw [Real.dist_eq, sub_zero] at h
  exact le_trans (le_abs_self _) h.le

end RHTower
