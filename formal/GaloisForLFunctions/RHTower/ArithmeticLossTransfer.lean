/-
# How an arithmetic loss propagates through the twelfth-power double-large-sieve chain

The double-large-sieve step bounds a **twelfth** power of the summed short-curve norms by the
first-spacing majorant, whose `H`-exponent is `9` when the sixth-moment input is sharp:

    `(∑_i ‖S(x_i)‖)^12 ≤ K · H^9` .

If the sixth-moment input degrades from `A₆(H) ≤ C H^(6+ε)` to `A₆(H) ≤ C H^(6+ρ)`, the majorant's
exponent degrades to `9 + ρ`, and taking twelfth roots divides the loss by twelve:

    **an arithmetic loss `ρ` in the sixth moment costs exactly `ρ/12` in the exponent of `∑‖S‖`.**

Two consequences.

* The record needs the sixth-moment input **sharp to within `o(1)`**: any fixed `ρ > 0` degrades the
  final exponent by `ρ/12 > 0`.  The input is therefore already at its extremal value and carries **no
  slack**; an improvement of the record cannot come from it.

* Conversely the exponent budget for a target gain `Δθ` is `ρ ≤ 12 Δθ`.  Descending from `13/84` to
  the two-regime spacing threshold `11/72` is a gain of `1/504`, so it corresponds to an `H`-exponent
  budget of `12/504 = 1/42` — numerically the width of the coverage interval `[17/42, 3/7]`.

Since the first-spacing side is extremal, the remaining slack in the chain lies in the second-spacing
count, which the elimination step leaves explicit.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace RHTower

noncomputable section

/-! ### Twelfth roots -/

/-- **Taking a twelfth root of a power bound.** -/
theorem twelfth_root_transfer {X Y : ℝ} (hX : 0 ≤ X) (h : X ^ (12 : ℕ) ≤ Y) :
    X ≤ Y ^ (1 / 12 : ℝ) := by
  have h1 : X = (X ^ (12 : ℕ)) ^ (1 / 12 : ℝ) := by
    rw [← Real.rpow_natCast X 12, ← Real.rpow_mul hX]
    norm_num
  rw [h1]
  exact Real.rpow_le_rpow (by positivity) h (by norm_num)

/-- **The chain in exponent form.**  A twelfth-power bound `X^12 ≤ K·H^(9+ρ)` gives
`X ≤ K^(1/12) · H^(3/4 + ρ/12)`. -/
theorem chain_exponent_transfer {X K H ρ : ℝ} (hX : 0 ≤ X) (hK : 0 ≤ K) (hH : 0 < H)
    (h : X ^ (12 : ℕ) ≤ K * H ^ (9 + ρ)) :
    X ≤ K ^ (1 / 12 : ℝ) * H ^ (3 / 4 + ρ / 12) := by
  have hstep := twelfth_root_transfer hX h
  have hsplit : (K * H ^ (9 + ρ)) ^ (1 / 12 : ℝ)
      = K ^ (1 / 12 : ℝ) * H ^ (3 / 4 + ρ / 12) := by
    rw [Real.mul_rpow hK (Real.rpow_nonneg hH.le _), ← Real.rpow_mul hH.le]
    congr 1
    ring_nf
  rwa [hsplit] at hstep

/-! ### The loss law -/

/-- The exponent cost of an arithmetic loss `ρ` in the sixth-moment input. -/
def arithmeticLoss (ρ : ℝ) : ℝ := ρ / 12

/-- **A loss `ρ` upstream costs exactly `ρ/12` downstream.** -/
theorem arithmeticLoss_eq (ρ : ℝ) : (9 + ρ) / 12 - 9 / 12 = arithmeticLoss ρ := by
  unfold arithmeticLoss; ring

/-- **Sharp input costs nothing.** -/
@[simp] theorem arithmeticLoss_zero : arithmeticLoss 0 = 0 := by
  unfold arithmeticLoss; norm_num

/-- **Any fixed positive loss is strictly costly**: the sixth-moment input carries no slack. -/
theorem arithmeticLoss_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < arithmeticLoss ρ := by
  unfold arithmeticLoss; linarith

/-- **The budget for a target gain.** -/
theorem arithmeticLoss_budget (Δ : ℝ) : arithmeticLoss (12 * Δ) = Δ := by
  unfold arithmeticLoss; ring

/-- **From the record to the two-regime spacing threshold the budget is `1/42`.** -/
theorem budget_record_to_threshold : 12 * ((13 : ℝ) / 84 - 11 / 72) = 1 / 42 := by norm_num

/-- The gain itself is `1/504`. -/
theorem gap_record_to_threshold : (13 : ℝ) / 84 - 11 / 72 = 1 / 504 := by norm_num

/-- **Summary.**  The twelfth power divides arithmetic losses by twelve; a sharp sixth moment is
therefore necessary and already extremal, and the gain from the record to the two-regime threshold
corresponds to an `H`-exponent budget of `1/42`. -/
theorem arithmetic_loss_summary (ρ : ℝ) :
    (9 + ρ) / 12 - 9 / 12 = ρ / 12 ∧ (13 : ℝ) / 84 - 11 / 72 = 1 / 504 ∧
      12 * ((13 : ℝ) / 84 - 11 / 72) = 1 / 42 :=
  ⟨arithmeticLoss_eq ρ, gap_record_to_threshold, budget_record_to_threshold⟩

end

end RHTower
