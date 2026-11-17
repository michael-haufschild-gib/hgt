import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith

/-!
# Bellman certificates with finite branching

The stopped-chain argument of arXiv:2611.16663 extends to finite decision
trees. Branching replaces addition of downstream errors by their maximum.
The resulting certificate controls the true minimum over all routes, even
with signed edge costs. Iteration stabilizes after depth plus one sweeps;
the extra sweep resets arbitrary leaf data.
-/

namespace GaloisForLFunctions.ExclusionOfTheCriticalState.DecisionBellman

/-- A finite optimization problem with signed edge costs and labelled terminal states. -/
inductive Tree (α : Type*) where
  | leaf : α → Tree α
  | branch : ℝ → Tree α → ℝ → Tree α → Tree α

noncomputable section
variable {α : Type*}

/-- Exact minimum cost, including the terminal payoff. -/
def value (g : α → ℝ) : Tree α → ℝ
  | .leaf a => g a
  | .branch a l b r => min (a + value g l) (b + value g r)

/-- One Bellman sweep resets terminal values and optimizes over both successors. -/
def step (g : α → ℝ) (W : Tree α → ℝ) : Tree α → ℝ
  | .leaf a => g a
  | .branch a l b r => min (a + W l) (b + W r)

def depth : Tree α → ℕ
  | .leaf _ => 0
  | .branch _ l _ r => max (depth l) (depth r) + 1

/-- All costs of complete routes; no intermediate node is a terminal option. -/
def outcomes (g : α → ℝ) : Tree α → Set ℝ
  | .leaf a => {g a}
  | .branch a l b r => (fun x => a + x) '' outcomes g l ∪
      (fun x => b + x) '' outcomes g r

/-- Bellman's value is attained and is the minimum of the literal route costs. -/
theorem value_isLeast (g : α → ℝ) (t : Tree α) :
    IsLeast (outcomes g t) (value g t) := by
  induction t with
  | leaf a =>
    refine ⟨rfl, ?_⟩
    intro q hq
    exact le_of_eq hq.symm
  | branch a l b r ihl ihr =>
    constructor
    · by_cases h : a + value g l ≤ b + value g r
      · change min (a + value g l) (b + value g r) ∈ _
        rw [min_eq_left h]
        exact Or.inl ⟨value g l, ihl.1, rfl⟩
      · change min (a + value g l) (b + value g r) ∈ _
        rw [min_eq_right (le_of_not_ge h)]
        exact Or.inr ⟨value g r, ihr.1, rfl⟩
    · rintro q (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
      · exact (min_le_left _ _).trans (add_le_add le_rfl (ihl.2 hv))
      · exact (min_le_right _ _).trans (add_le_add le_rfl (ihr.2 hv))

/-- Local defects are accumulated along the most adverse continuation. -/
def certificate (g : α → ℝ) (W : Tree α → ℝ) : Tree α → ℝ
  | .leaf a => |W (.leaf a) - g a|
  | .branch a l b r => |W (.branch a l b r) - step g W (.branch a l b r)| +
      max (certificate g W l) (certificate g W r)

/-- Branch minima are nonexpansive, so accumulated defects control the exact optimal value. -/
theorem abs_error_le_certificate (g : α → ℝ) (W : Tree α → ℝ) (t : Tree α) :
    |W t - value g t| ≤ certificate g W t := by
  induction t with
  | leaf a => exact le_rfl
  | branch a l b r ihl ihr =>
    have hmin := abs_min_sub_min_le_max
      (a + W l) (b + W r) (a + value g l) (b + value g r)
    simp only [add_sub_add_left_eq_sub] at hmin
    calc
      |W (.branch a l b r) - value g (.branch a l b r)| ≤
          |W (.branch a l b r) - step g W (.branch a l b r)| +
          |step g W (.branch a l b r) - value g (.branch a l b r)| :=
        abs_sub_le _ _ _
      _ ≤ certificate g W (.branch a l b r) :=
        add_le_add le_rfl (hmin.trans (max_le_max ihl ihr))

theorem value_mem_certificate_interval (g : α → ℝ) (W : Tree α → ℝ) (t : Tree α) :
    W t - certificate g W t ≤ value g t ∧ value g t ≤ W t + certificate g W t := by
  have h := abs_le.mp (abs_error_le_certificate g W t)
  constructor <;> linarith only [h.1, h.2]

private theorem certificate_value (g : α → ℝ) (t : Tree α) :
    certificate g (value g) t = 0 := by
  induction t with
  | leaf a => simp only [certificate, value, sub_self, abs_zero]
  | branch a l b r ihl ihr =>
    simp only [certificate, step, value, sub_self, abs_zero, ihl, ihr, max_self, add_zero]

/-- The stopped branching operator still has a unique fixed point for arbitrary signed costs. -/
theorem fixed_iff (g : α → ℝ) (W : Tree α → ℝ) : step g W = W ↔ W = value g := by
  constructor
  · intro h
    funext t
    induction t with
    | leaf a => exact (congrFun h (.leaf a)).symm
    | branch a l b r ihl ihr =>
      have ht := congrFun h (.branch a l b r)
      change min (a + W l) (b + W r) = W (.branch a l b r) at ht
      rw [ihl, ihr] at ht
      exact ht.symm
  · rintro rfl
    funext t
    cases t <;> rfl

/-- Every initial candidate is forgotten after one more sweep than the tree depth. -/
theorem iterate_exact (g : α → ℝ) (W : Tree α → ℝ) (t : Tree α) :
    (step g)^[depth t + 1] W t = value g t := by
  have h (k : ℕ) : ∀ s : Tree α, depth s < k → (step g)^[k] W s = value g s := by
    induction k with
    | zero => intro s hs; exact False.elim (Nat.not_lt_zero _ hs)
    | succ k ih =>
      intro s hs
      rw [Function.iterate_succ_apply']
      cases s with
      | leaf a => rfl
      | branch a l b r =>
        have hm : max (depth l) (depth r) < k := Nat.succ_lt_succ_iff.mp hs
        change min (a + (step g)^[k] W l) (b + (step g)^[k] W r) = _
        rw [ih l ((le_max_left _ _).trans_lt hm), ih r ((le_max_right _ _).trans_lt hm)]
        rfl
  exact h _ t (Nat.lt_succ_self _)

/-- Negativity of the optimal value is equivalent to a negative complete route. -/
theorem negative_outcome_iff (g : α → ℝ) (t : Tree α) :
    (∃ q ∈ outcomes g t, q < 0) ↔ value g t < 0 := by
  constructor
  · rintro ⟨q, hq, hn⟩
    exact ((value_isLeast g t).2 hq).trans_lt hn
  · intro h
    exact ⟨value g t, (value_isLeast g t).1, h⟩

/-- Residual certificates characterize the existence of a negative complete route. -/
theorem negative_certificate_iff (g : α → ℝ) (t : Tree α) :
    (∃ W : Tree α → ℝ, W t + certificate g W t < 0) ↔
      ∃ q ∈ outcomes g t, q < 0 := by
  rw [negative_outcome_iff]
  constructor
  · rintro ⟨W, hW⟩
    exact (value_mem_certificate_interval g W t).2.trans_lt hW
  · intro h
    exact ⟨value g, by simpa only [certificate_value, add_zero] using h⟩

#print axioms value_isLeast
#print axioms abs_error_le_certificate
#print axioms fixed_iff
#print axioms iterate_exact
#print axioms negative_certificate_iff

end
end GaloisForLFunctions.ExclusionOfTheCriticalState.DecisionBellman
