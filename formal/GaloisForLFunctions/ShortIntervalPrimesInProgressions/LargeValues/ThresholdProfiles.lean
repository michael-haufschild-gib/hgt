import Mathlib.Data.ENNReal.BigOperators

/-!
# One-variable threshold costs for products

A joint level forces each factor to pay its marginal threshold cost. Independent
choices make the joint infimum exactly the sum of marginal infima, including empty
level sets. These are the order-theoretic mechanisms of Lemma 3.1 and §3 of
arXiv:2610.09567. Extended nonnegative reals retain the value infinity for an empty level.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions

/-- Least cost of reaching a specified level; an unattainable level costs infinity. -/
def thresholdCost {α L : Type*} [Preorder L]
    (H : α → L) (cost : α → ℝ≥0∞) (t : L) : ℝ≥0∞ :=
  ⨅ x : {x // t ≤ H x}, cost x

/-- Every configuration pays at least the threshold cost of its own level. -/
theorem thresholdCost_at_value_le {α : Type*} (H : α → ℝ) (cost : α → ℝ≥0∞) (x : α) :
    thresholdCost H cost (H x) ≤ cost x :=
  iInf_le_of_le ⟨x, le_rfl⟩ le_rfl

/-- Independent threshold constraints separate exactly, even if any factor has no witnesses. -/
theorem trilinear_thresholdCost_eq_iInf {α β γ : Type*}
    (H₁ : α → ℝ) (H₂ : β → ℝ) (H₃ : γ → ℝ)
    (c₁ : α → ℝ≥0∞) (c₂ : β → ℝ≥0∞) (c₃ : γ → ℝ≥0∞) (t : ℝ) :
    thresholdCost H₁ c₁ t + thresholdCost H₂ c₂ t + thresholdCost H₃ c₃ t =
      ⨅ x : {x // t ≤ H₁ x}, ⨅ y : {y // t ≤ H₂ y}, ⨅ z : {z // t ≤ H₃ z},
        c₁ x + c₂ y + c₃ z := by
  unfold thresholdCost
  rw [ENNReal.iInf_add, ENNReal.iInf_add]
  apply iInf_congr
  intro x
  rw [ENNReal.add_iInf (a := c₁ x) (f := fun y : {y // t ≤ H₂ y} => c₂ y),
    ENNReal.iInf_add]
  apply iInf_congr
  intro y
  exact ENNReal.add_iInf

/-- The minimum of three observed levels turns the one-variable cost into a joint lower bound. -/
theorem trilinear_thresholdCost_le {α β γ : Type*}
    (H₁ : α → ℝ) (H₂ : β → ℝ) (H₃ : γ → ℝ)
    (c₁ : α → ℝ≥0∞) (c₂ : β → ℝ≥0∞) (c₃ : γ → ℝ≥0∞)
    (x : α) (y : β) (z : γ) :
    let t := min (H₁ x) (min (H₂ y) (H₃ z))
    thresholdCost H₁ c₁ t + thresholdCost H₂ c₂ t + thresholdCost H₃ c₃ t ≤
      c₁ x + c₂ y + c₃ z := by
  dsimp only
  rw [trilinear_thresholdCost_eq_iInf]
  exact iInf_le_of_le ⟨x, min_le_left _ _⟩
    (iInf_le_of_le ⟨y, (min_le_right _ _).trans (min_le_left _ _)⟩
      (iInf_le_of_le ⟨z, (min_le_right _ _).trans (min_le_right _ _)⟩ le_rfl))

/-- The same mechanism works for every finite family, without assuming the index set nonempty. -/
theorem finite_thresholdCost_le {ι α : Type*} [Fintype ι]
    (H : ι → α → ℝ≥0∞) (cost : ι → α → ℝ≥0∞) (x : ι → α) :
    ∑ i, thresholdCost (H i) (cost i) (⨅ j, H j (x j)) ≤
      ∑ i, cost i (x i) := by
  exact Finset.sum_le_sum fun i _ => iInf_le_of_le ⟨x i, iInf_le _ i⟩ le_rfl

#print axioms trilinear_thresholdCost_eq_iInf
#print axioms trilinear_thresholdCost_le
#print axioms finite_thresholdCost_le

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
