import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

/-!
# Bounded first-moment discrepancy from two opposite literal orientations

The two-jet Route L extraction uses one family of positive displacements and one of negative
displacements. Each family has the same cardinality, and every displacement has magnitude at most
the physical block length. Select all of the family with smaller total magnitude and a prefix of
the other: the overshoot is at most one block length. This module formalizes that finite selection
without fractional coefficients or a probabilistic balancing hypothesis.
-/

namespace RHTower

private theorem list_sum_nonneg_of (xs : List ℝ) (hx : ∀ x ∈ xs, 0 ≤ x) :
    0 ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx0 : 0 ≤ x := hx x (by simp)
      have hxs : ∀ y ∈ xs, 0 ≤ y := by
        intro y hy
        exact hx y (by simp [hy])
      simpa using add_nonneg hx0 (ih hxs)

/-- A bounded nonnegative list has a prefix whose sum first crosses a prescribed target, with
overshoot no larger than one entry bound. -/
theorem exists_prefix_sum_between (L : ℝ) (hL : 0 ≤ L) :
    ∀ (xs : List ℝ) (target : ℝ),
      (∀ x ∈ xs, 0 ≤ x ∧ x ≤ L) → 0 ≤ target → target ≤ xs.sum →
      ∃ ys zs : List ℝ, xs = ys ++ zs ∧ target ≤ ys.sum ∧ ys.sum ≤ target + L := by
  intro xs
  induction xs with
  | nil =>
      intro target _ ht hsum
      refine ⟨[], [], by simp, ?_, ?_⟩ <;> simp at hsum ⊢ <;> linarith
  | cons x xs ih =>
      intro target hb ht hsum
      have hx : 0 ≤ x ∧ x ≤ L := hb x (by simp)
      have hxs : ∀ y ∈ xs, 0 ≤ y ∧ y ≤ L := by
        intro y hy
        exact hb y (by simp [hy])
      by_cases htx : target ≤ x
      · refine ⟨[x], xs, by simp, ?_, ?_⟩ <;> simp <;> linarith
      · have ht' : 0 ≤ target - x := by linarith
        have hsum' : target - x ≤ xs.sum := by simp at hsum; linarith
        obtain ⟨ys, zs, hsplit, hlow, hhigh⟩ := ih (target - x) hxs ht' hsum'
        refine ⟨x :: ys, zs, ?_, ?_, ?_⟩
        · simp [hsplit]
        · simp; linarith
        · simp; linarith

/-- Two finite displacement families admit a signed selection with one family taken completely
and net displacement at most `L`. The selected entries retain unit coefficients. -/
theorem exists_balanced_two_orientations (L : ℝ) (hL : 0 ≤ L)
    (u v : List ℝ)
    (hu : ∀ x ∈ u, 0 ≤ x ∧ x ≤ L)
    (hv : ∀ x ∈ v, 0 ≤ x ∧ x ≤ L) :
    ∃ us vs ut vt : List ℝ,
      u = us ++ ut ∧ v = vs ++ vt ∧
      (ut = [] ∨ vt = []) ∧ |us.sum - vs.sum| ≤ L := by
  have hus : 0 ≤ u.sum := list_sum_nonneg_of u (fun x hx => (hu x hx).1)
  have hvs : 0 ≤ v.sum := list_sum_nonneg_of v (fun x hx => (hv x hx).1)
  rcases le_total u.sum v.sum with hle | hle
  · obtain ⟨vs, vt, hsplit, hlow, hhigh⟩ :=
      exists_prefix_sum_between L hL v u.sum hv hus hle
    refine ⟨u, vs, [], vt, by simp, hsplit, Or.inl rfl, ?_⟩
    rw [abs_le]
    constructor <;> linarith
  · obtain ⟨us, ut, hsplit, hlow, hhigh⟩ :=
      exists_prefix_sum_between L hL u v.sum hu hvs hle
    refine ⟨us, v, ut, [], hsplit, by simp, Or.inr rfl, ?_⟩
    rw [abs_le]
    constructor <;> linarith

end RHTower
