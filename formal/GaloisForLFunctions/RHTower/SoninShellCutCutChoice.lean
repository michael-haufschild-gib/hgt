import GaloisForLFunctions.RHTower.SoninShellCutKappaChoice

/-!
# Choosing the cut

The outer slack term is the only one still moving with the cut.  Its majorant factor is bounded by
the global majorant, whatever the carrier, so the whole term is below a fixed multiple of the root
of half-width against the outer radius — and that root vanishes as the cut refines.

So for any target the cut can be taken fine enough, with the prescribed product already fixed.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open Filter
open scoped Topology

/-- The majorant at any nonnegative radius is below the global one. -/
theorem soninRefTailSup_le_global {u : ℝ} (hu : 0 ≤ u) :
    soninRefTailSup u ≤ soninRefTailSup 0 := soninRefTailSup_antitone hu

/-- **The outer term against the global majorant.**  Past the outer radius the carrier plays no
role in the bound. -/
theorem outerSlack_le_global (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) (w D : ℝ)
    (hD : 0 ≤ D) (hw : b ≤ w) :
    D * (soninRefTailSup (soninShellCutWidth b c N * (w - b)) *
        Real.sqrt (soninShellCutWidth b c N * b / ∫ y : ℝ, soninUnitBumpSq y)) ≤
      D * (soninRefTailSup 0 *
        Real.sqrt (soninShellCutWidth b c N * b / ∫ y : ℝ, soninUnitBumpSq y)) := by
  have hδ := soninShellCutWidth_pos b c hbc hN
  have harg : (0 : ℝ) ≤ soninShellCutWidth b c N * (w - b) := by
    have : (0 : ℝ) ≤ w - b := by linarith
    positivity
  have hsqrt : (0 : ℝ) ≤
      Real.sqrt (soninShellCutWidth b c N * b / ∫ y : ℝ, soninUnitBumpSq y) := Real.sqrt_nonneg _
  have hmono := soninRefTailSup_le_global harg
  have := mul_le_mul_of_nonneg_right hmono hsqrt
  exact mul_le_mul_of_nonneg_left this hD

/-- **The cut can be chosen.**  Once the cut is fine enough the outer term is below any positive
target. -/
theorem eventually_outerSlack_le (b c D : ℝ) {target : ℝ} (htarget : 0 < target) :
    ∀ᶠ N : ℕ in atTop,
      D * (soninRefTailSup 0 *
        Real.sqrt (soninShellCutWidth b c N * b / ∫ y : ℝ, soninUnitBumpSq y)) < target := by
  have hbase := tendsto_sqrt_soninShellCutWidth_mul_atTop b c b
  have hscaled := hbase.const_mul (D * soninRefTailSup 0)
  rw [mul_zero] at hscaled
  have hcongr : Tendsto (fun N : ℕ =>
      D * (soninRefTailSup 0 *
        Real.sqrt (soninShellCutWidth b c N * b / ∫ y : ℝ, soninUnitBumpSq y)))
      atTop (𝓝 0) := by
    refine hscaled.congr fun N => ?_
    ring
  exact hcongr.eventually (gt_mem_nhds htarget)

end RHTower
