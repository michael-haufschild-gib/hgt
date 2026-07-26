/-
# Two recurrence types, and which of them can reach the Lindelöf exponent

Bourgain's argument passes through two structurally different recurrences.

* An **additive-in-value contraction** `b(n) ≤ q·b(n/2) + C·n^ε` with `q < 1` contracts the *constant*;
  the constants form a geometric series with sum `C/(1-q)`, and the conclusion is `b(n) ≤ D·n^ε` with
  `D = max(B, C/(1-q))`.  Its exponent floor is **`ε` — Lindelöf quality**, for every `q < 1`.

* A **multiplicative-in-scale contraction** `b(N) ≤ C·N^δ·b(N^α)` with `α < 1` contracts the *scale*;
  the losses form a geometric series in the *exponent* with sum `δ/(1-α)`.  Its floor is
  **`δ/(1-α) > 0` whenever `δ > 0`**.

So the two differ in what the geometric series sums: a constant in the first case, an exponent in the
second.  All of Bourgain's exponent loss sits in the second.  Consequently:

* the **per-step budget** for a target `β` is exactly `perStepBudget α β = (1-α)·β`; at `α = 2/3` and
  `β = 13/84` it is `13/252`, Bourgain's per-step loss;
* the multiplicative recurrence reaches the Lindelöf exponent **iff its per-step loss is sub-power**,
  i.e. iff for every `ε > 0` the recurrence holds with `δ = (1-α)ε` — in which case it is, in exponent
  terms, an additive contraction.
-/
import GaloisForLFunctions.RHTower.BourgainRecurrenceFloor
import GaloisForLFunctions.RHTower.BourgainScaleContraction

namespace RHTower

noncomputable section

/-! ### The per-step budget -/

/-- The largest per-step loss compatible with a total exponent `β`. -/
def perStepBudget (α β : ℝ) : ℝ := (1 - α) * β

/-- **It is exactly the loss whose floor is the target.** -/
theorem powerScaleFloor_perStepBudget {α : ℝ} (hα : α < 1) (β : ℝ) :
    powerScaleFloor (perStepBudget α β) α = β := by
  have h : (1 : ℝ) - α ≠ 0 := sub_ne_zero.mpr (ne_of_gt hα)
  unfold powerScaleFloor perStepBudget
  field_simp

/-- **A per-step loss is admissible for the target exactly when it is within budget.** -/
theorem within_budget_iff {α δ β : ℝ} (hα : α < 1) :
    powerScaleFloor δ α ≤ β ↔ δ ≤ perStepBudget α β := by
  have h : (0 : ℝ) < 1 - α := by linarith
  unfold powerScaleFloor perStepBudget
  rw [div_le_iff₀ h]
  constructor <;> intro hh <;> nlinarith

/-- **Bourgain's per-step loss is exactly the budget for `13/84` at contraction `2/3`.** -/
theorem perStepBudget_bourgain : perStepBudget (2 / 3) bourgainZetaExponent = 13 / 252 := by
  unfold perStepBudget bourgainZetaExponent; norm_num

/-! ### The multiplicative floor is positive unless the loss vanishes -/

/-- **A positive per-step loss forces a positive floor.** -/
theorem powerScaleFloor_pos {α δ : ℝ} (hα : α < 1) (hδ : 0 < δ) : 0 < powerScaleFloor δ α := by
  have h : (0 : ℝ) < 1 - α := by linarith
  exact div_pos hδ h

/-- **Sub-power per-step loss gives sub-power total loss.**  For every target `ε > 0` there is a
positive admissible per-step loss, namely `(1-α)ε`. -/
theorem subpower_perStep_suffices {α : ℝ} (hα : α < 1) {ε : ℝ} (hε : 0 < ε) :
    0 < perStepBudget α ε ∧ powerScaleFloor (perStepBudget α ε) α = ε := by
  have h : (0 : ℝ) < 1 - α := by linarith
  exact ⟨mul_pos h hε, powerScaleFloor_perStepBudget hα ε⟩

/-! ### The additive contraction reaches Lindelöf quality for every ratio -/

/-- **The additive-in-value contraction has exponent floor `ε` for every ratio `q < 1`.**  This is the
corpus contraction theorem, restated as the statement that its floor does not depend on `q`. -/
theorem additive_floor_is_epsilon
    (b : ℕ → ℝ) {q C B ε : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hbase : b 1 ≤ B)
    (hrec : ∀ n : ℕ, 2 ≤ n → b n ≤ q * b (n / 2) + C * (n : ℝ) ^ ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 0 < n → b n ≤ D * (n : ℝ) ^ ε :=
  subpower_bound_of_dyadic_contraction b hq0 hq1 hB hε hbase hrec

/-! ### The dichotomy -/

/-- **The dichotomy.**  With the same contraction strength, the additive-in-value recurrence has
exponent floor `ε` while the multiplicative-in-scale recurrence has floor `δ/(1-α)`, positive whenever
`δ > 0`; the two agree exactly when the per-step loss is sub-power. -/
theorem recurrence_dichotomy {α δ : ℝ} (hα : α < 1) (hδ : 0 < δ) :
    0 < powerScaleFloor δ α ∧
      (powerScaleFloor δ α = 0 ↔ δ = 0) ∧
        ∀ e : ℝ, 0 < e → powerScaleFloor (perStepBudget α e) α = e :=
  ⟨powerScaleFloor_pos hα hδ, powerScaleFloor_eq_zero_iff hα,
    fun _ he => (subpower_perStep_suffices hα he).2⟩

/-- **Bourgain's instance.**  The multiplicative floor at his parameters is `13/84`, strictly positive,
whereas an additive contraction at any ratio would give `ε`. -/
theorem bourgain_instance :
    powerScaleFloor (13 / 252) (2 / 3) = bourgainZetaExponent ∧
      perStepBudget (2 / 3) bourgainZetaExponent = 13 / 252 ∧
        0 < powerScaleFloor (13 / 252 : ℝ) (2 / 3) := by
  refine ⟨powerScaleFloor_bourgain, perStepBudget_bourgain, ?_⟩
  exact powerScaleFloor_pos (by norm_num) (by norm_num)

end

end RHTower
