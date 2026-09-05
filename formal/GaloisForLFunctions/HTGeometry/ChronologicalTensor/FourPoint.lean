import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Chronological capacity on four ordered endpoints

Affine probes `(1,x)` contract an alternating pair to an endpoint difference. In gap
coordinates the separated and enclosing pairings are `u*w` and `v*(u+v+w)`.
Their span has the exact total-variation capacity `max (|a|/4) |b|`.
The upper bound and a unit-cost maximizer are both provided for every coefficient pair.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

noncomputable section

def fourCost (u v w : ℝ) : ℝ := |u| + |v| + |w|

def separated (u _v w : ℝ) : ℝ := u * w

def enclosing (u v w : ℝ) : ℝ := v * (u + v + w)

def crossing (u v w : ℝ) : ℝ := (u + v) * (v + w)

def fourResponse (a b u v w : ℝ) : ℝ :=
  a * separated u v w + b * enclosing u v w

def fourCapacity (a b : ℝ) : ℝ := max (|a| / 4) |b|

theorem plucker (u v w : ℝ) :
    crossing u v w = separated u v w + enclosing u v w := by
  unfold crossing separated enclosing
  ring

theorem four_budget (u v w : ℝ) :
    4 * |separated u v w| + |enclosing u v w| ≤ fourCost u v w ^ 2 := by
  have ht : |u + v + w| ≤ |u| + |v| + |w| :=
    (abs_add_le (u + v) w).trans (add_le_add (abs_add_le u v) le_rfl)
  have hb := mul_le_mul_of_nonneg_left ht (abs_nonneg v)
  have hcross : 0 ≤ |v| * (|u| + |w|) :=
    mul_nonneg (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  simp only [separated, enclosing, abs_mul, fourCost]
  nlinarith [sq_nonneg (|u| - |w|)]

theorem four_sharp_bound (a b u v w : ℝ) :
    |fourResponse a b u v w| ≤ fourCapacity a b * fourCost u v w ^ 2 := by
  have ha : |a| ≤ 4 * fourCapacity a b := by
    have := le_max_left (|a| / 4) |b|
    unfold fourCapacity
    linarith
  have hb : |b| ≤ fourCapacity a b := le_max_right _ _
  have hc : 0 ≤ fourCapacity a b := (abs_nonneg b).trans hb
  calc
    |fourResponse a b u v w| ≤
        |a| * |separated u v w| + |b| * |enclosing u v w| := by
      simpa only [fourResponse, abs_mul] using
        abs_add_le (a * separated u v w) (b * enclosing u v w)
    _ ≤ (4 * fourCapacity a b) * |separated u v w| +
        fourCapacity a b * |enclosing u v w| :=
      add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hb (abs_nonneg _))
    _ = fourCapacity a b * (4 * |separated u v w| + |enclosing u v w|) := by ring
    _ ≤ fourCapacity a b * fourCost u v w ^ 2 :=
      mul_le_mul_of_nonneg_left (four_budget u v w) hc

theorem four_attained (a b : ℝ) :
    ∃ u v w : ℝ, fourCost u v w = 1 ∧
      |fourResponse a b u v w| = fourCapacity a b := by
  by_cases h : |b| ≤ |a| / 4
  · refine ⟨1/2, 0, 1/2, ?_, ?_⟩
    · simp [fourCost]
      ring
    · simp only [fourResponse, separated, enclosing, fourCapacity, max_eq_left h]
      have he : a * ((1/2 : ℝ) * (1/2)) + b * (0 * (1/2 + 0 + 1/2)) = a / 4 := by ring
      rw [he, abs_div]
      simp
  · refine ⟨0, 1, 0, ?_, ?_⟩
    · simp [fourCost]
    · simp [fourResponse, separated, enclosing, fourCapacity, max_eq_right (le_of_not_ge h)]

theorem four_classification (a b : ℝ) :
    (∀ u v w : ℝ, |fourResponse a b u v w| ≤
      fourCapacity a b * fourCost u v w ^ 2) ∧
    (∃ u v w : ℝ, fourCost u v w = 1 ∧
      |fourResponse a b u v w| = fourCapacity a b) :=
  ⟨four_sharp_bound a b, four_attained a b⟩

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
