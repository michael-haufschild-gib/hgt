import GaloisForLFunctions.RHTower.SoninShellCutCutChoice

/-!
# The coupling's largeness conditions hold once the cut is fine

Under the scale tied to the cut every condition the coupling imposes on the scale is a statement
that a linearly growing quantity has passed a fixed threshold: the scale itself above one, the
carrier past the outer radius, the inner aperture reached after dilation.

All of them therefore hold from some cut onwards, together with the cut being nonempty.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open Filter
open scoped Topology

/-- **Every largeness condition is eventual in the cut.** -/
theorem eventually_soninShellCutScale_conditions
    (a b c q κ : ℝ) (hbc : b < c) (ha : 0 < a) (hq : 0 < q) (hκ : 0 < κ) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ 1 < soninShellCutScale b c N κ ∧
      b < soninShellCutScale b c N κ * q ∧ c ≤ soninShellCutScale b c N κ * a := by
  have hs := tendsto_soninShellCutScale_atTop b c hbc hκ
  have h0 : ∀ᶠ N : ℕ in atTop, 0 < N := eventually_gt_atTop 0
  have h1 := hs.eventually_gt_atTop 1
  have h2 := (Filter.Tendsto.atTop_mul_const hq hs).eventually_gt_atTop b
  have h3 := (Filter.Tendsto.atTop_mul_const ha hs).eventually_ge_atTop c
  filter_upwards [h0, h1, h2, h3] with N k0 k1 k2 k3
  exact ⟨k0, k1, k2, k3⟩

/-- **The tail conditions are eventual too.**  Both are conditions on the prescribed product, which
the tied scale holds fixed, so they are conditions on the product alone. -/
theorem soninShellCut_tail_conditions_of_product
    (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) {κ : ℝ} (hκ : 0 < κ) (q : ℝ) (hq : 0 < q)
    (hmean : 2 * soninRefTailSup (κ * q) ≤ ∫ y : ℝ, soninUnitBumpData y)
    (hSq : soninRefSqTailSup (κ * q) ≤ (∫ y : ℝ, soninUnitBumpSq y) / 20) :
    2 * soninRefTailSup (soninShellCutWidth b c N *
        |soninShellCutScale b c N κ * q|) ≤ ∫ y : ℝ, soninUnitBumpData y ∧
      soninRefSqTailSup (soninShellCutWidth b c N *
        |soninShellCutScale b c N κ * q|) ≤ (∫ y : ℝ, soninUnitBumpSq y) / 20 := by
  have hr : 0 < soninShellCutScale b c N κ := soninShellCutScale_pos b c hbc hN hκ
  have habs : |soninShellCutScale b c N κ * q| = soninShellCutScale b c N κ * q :=
    abs_of_pos (by positivity)
  have hprod : soninShellCutWidth b c N * (soninShellCutScale b c N κ * q) = κ * q := by
    have h := soninShellCutWidth_mul_scale b c hbc hN κ
    calc soninShellCutWidth b c N * (soninShellCutScale b c N κ * q)
        = soninShellCutWidth b c N * soninShellCutScale b c N κ * q := by ring
      _ = κ * q := by rw [h]
  rw [habs, hprod]
  exact ⟨hmean, hSq⟩

end RHTower
