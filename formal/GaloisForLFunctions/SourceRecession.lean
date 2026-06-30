import Mathlib.Tactic

/-!
# Source-normalization recession gates

This file formalizes the finite-dimensional algebraic core of
`finite-source-normalizations-leave-budget-recession.md`.

It proves the recession-direction step used by the source-selector ledger: if a
fixed budget inequality holds along an entire one-sided affine ray, the ray
direction is nonnegative on every test vector; if it holds along the whole
two-sided affine line, the direction is zero on every test vector.

What is **not** formalized here: the Euler/Gamma/functional-equation source
construction, the completed boundary-Weyl object, any Stieltjes/Markov
positivity theorem, or RH.
-/

namespace GaloisForLFunctions

noncomputable section

/-- **One-sided source-budget recession gate.** If a budget inequality
`0 <= B[v] + R[v] + t * D[v]` holds for every `t >= 0`, then the recession
direction `D` is nonnegative on every test vector.

This is the formal core of the ledger rule: a one-sided source-normalization
ray can preserve a fixed Loewner budget only when its remaining recession
direction is already nonnegative. -/
@[aesop safe]
theorem source_budget_one_sided_recession_nonnegative {V : Type*} (B R D : V -> ℝ)
    (h : ∀ t : ℝ, 0 ≤ t -> ∀ v : V, 0 ≤ B v + R v + t * D v) :
    ∀ v : V, 0 ≤ D v := by
  intro v
  by_contra hDnon
  rw [not_le] at hDnon
  set A : ℝ := B v + R v with hA
  set t : ℝ := (|A| + 1) / (-D v) with htdef
  have hden_pos : 0 < -D v := by linarith
  have ht_nonneg : 0 ≤ t := by
    rw [htdef]
    exact div_nonneg (by positivity) hden_pos.le
  have hbudget := h t ht_nonneg v
  have hvalue : B v + R v + t * D v = A - (|A| + 1) := by
    rw [hA, htdef]
    field_simp [hDnon.ne]
    ring
  have hneg : A - (|A| + 1) < 0 := by
    have hle : A ≤ |A| := le_abs_self A
    linarith
  linarith

/-- **Two-sided source-budget recession gate.** If a budget inequality
`0 <= B[v] + R[v] + t * D[v]` holds for every real `t`, then the recession
direction `D` vanishes on every test vector.

This is the formal core of the two-sided finite-normalization audit: if both
`D` and `-D` remain admissible, a fixed budget can hold on the whole affine
line only when the direction has no quadratic effect. -/
@[aesop safe]
theorem source_budget_two_sided_recession_zero {V : Type*} (B R D : V -> ℝ)
    (h : ∀ t : ℝ, ∀ v : V, 0 ≤ B v + R v + t * D v) :
    ∀ v : V, D v = 0 := by
  intro v
  have hpos : 0 ≤ D v :=
    source_budget_one_sided_recession_nonnegative B R D (fun t _ht w => h t w) v
  have hneg : 0 ≤ -D v :=
    source_budget_one_sided_recession_nonnegative B R (fun w => -D w)
      (fun t _ht w => by
        have hw := h (-t) w
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hw) v
  linarith

end

end GaloisForLFunctions
