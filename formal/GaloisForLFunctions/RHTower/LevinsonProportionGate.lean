import GaloisForLFunctions.RHTower.LevinsonOddFiberDensity
import GaloisForLFunctions.RHTower.OddFiberSimpleCharging

/-!
# The two card gates, from the Levinson mean-square gate

Composing the density passage with the odd-fibre/simple-critical charging turns the mollified
mean-square gate into exactly the two statements the folder's cards consume:

* a positive lower density of **simple** critical zeros — the gate of
  `bounded-support-weil-critical-tail-uniqueness`;
* a positive lower density of **singleton horizontal fibres** — the non-vacuity of
  `horizontal-singleton-zero-fibers`.
-/

open Filter Topology

noncomputable section

namespace RHTower

theorem eventually_pos_xiPosZeroCount : ∀ᶠ T in atTop, 0 < (xiPosZeroCount T : ℝ) := by
  filter_upwards [eventually_inv_four_pi_mul_le_xiPosZeroCount, eventually_ge_atTop (3 : ℝ)]
    with T hT hT3
  have hlog : (0 : ℝ) < Real.log T := Real.log_pos (by linarith)
  have hpos : (0 : ℝ) < 1 / (4 * Real.pi) * (T * Real.log T) := by
    have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  linarith

/-- **A positive lower density of simple critical zeros.** -/
theorem le_liminf_xiSimpleCriticalRatio_of_gate {R c δ : ℝ}
    (hR : 0 < R) (hc : 1 ≤ c) (hδ : 0 < δ)
    (hmargin : 1 / 3 + 2 * δ < 1 - Real.log c / R)
    (hgate : LevinsonMeanSquareGate R c) :
    δ ≤ liminf xiSimpleCriticalRatio atTop := by
  have hcob : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop xiSimpleCriticalRatio :=
    (isBoundedUnder_of ⟨1, fun T => xiSimpleCriticalRatio_le_one T⟩).isCoboundedUnder_ge
  refine le_liminf_of_le hcob ?_
  filter_upwards [eventually_oddFiber_ge_of_gate hR hc hδ hmargin hgate,
    eventually_pos_xiPosZeroCount] with U hU hUpos
  have hcharge : (3 : ℝ) * (xiOddFiberCount U : ℝ)
      ≤ 3 * (xiSimpleCriticalZeroCount U : ℝ) + (xiPosZeroCount U : ℝ) := by
    exact_mod_cast three_mul_xiOddFiberCount_le_simple U
  have hkey : δ * (xiPosZeroCount U : ℝ) ≤ (xiSimpleCriticalZeroCount U : ℝ) := by
    nlinarith [hU, hcharge]
  rw [xiSimpleCriticalRatio, le_div_iff₀ hUpos]
  linarith

/-- **A positive lower density of singleton horizontal fibres.** -/
theorem le_liminf_xiSingletonFiberRatio_of_gate {R c δ : ℝ}
    (hR : 0 < R) (hc : 1 ≤ c) (hδ : 0 < δ)
    (hmargin : 1 / 3 + 2 * δ < 1 - Real.log c / R)
    (hgate : LevinsonMeanSquareGate R c) :
    (3 / 2 : ℝ) * δ ≤ liminf xiSingletonFiberRatio atTop := by
  have hcob : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop xiSingletonFiberRatio :=
    (isBoundedUnder_of ⟨1, fun T => xiSingletonFiberRatio_le_one T⟩).isCoboundedUnder_ge
  refine le_liminf_of_le hcob ?_
  filter_upwards [eventually_oddFiber_ge_of_gate hR hc hδ hmargin hgate,
    eventually_pos_xiPosZeroCount] with U hU hUpos
  have hratio : (1 / 3 + δ : ℝ) ≤ xiOddFiberRatio U := by
    rw [xiOddFiberRatio, le_div_iff₀ hUpos]
    linarith
  have hcharge := xiOddFiberRatio_charge U
  linarith

end RHTower

end
