import Mathlib.GroupTheory.Perm.Support
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Equiv
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.HurwitzFactorization

variable {α : Type*} [DecidableEq α]

/-- Count factor occurrences that move a specified sheet. Repeated factors count separately. -/
def occurrences (l : List (Perm α)) (x : α) : ℕ :=
  (l.map fun g => if g x ≠ x then 1 else 0).sum

@[simp] theorem occurrences_nil (x : α) : occurrences ([] : List (Perm α)) x = 0 := rfl

@[simp] theorem occurrences_cons (g : Perm α) (l : List (Perm α)) (x : α) :
    occurrences (g :: l) x = (if g x ≠ x then 1 else 0) + occurrences l x := by
  simp [occurrences]

theorem prod_fixed_of_occurrences_eq_zero (l : List (Perm α)) (x : α)
    (h : occurrences l x = 0) : l.prod x = x := by
  revert h
  induction l with
  | nil => intro _; rfl
  | cons g l ih =>
      intro h
      rw [occurrences_cons] at h
      have hg : g x = x := by
        by_contra hne
        simp [hne] at h
      have hl : occurrences l x = 0 := by simpa [hg] using h
      rw [List.prod_cons, Perm.mul_apply, ih hl, hg]

theorem sum_occurrences [Fintype α] (l : List (Perm α))
    (hl : ∀ g ∈ l, g.IsSwap) : ∑ x, occurrences l x = 2 * l.length := by
  induction l with
  | nil => simp
  | cons g l ih =>
      have hg : g.IsSwap := hl g (by simp)
      have htail : ∀ t ∈ l, t.IsSwap := fun t ht => hl t (List.mem_cons_of_mem g ht)
      simp only [occurrences_cons, Finset.sum_add_distrib]
      rw [Finset.sum_boole]
      change g.support.card + ∑ x, occurrences l x = 2 * (g :: l).length
      rw [Perm.card_support_eq_two.mpr hg, ih htail, List.length_cons]
      omega

/-- Any length-(d−1) transposition word with fixed-point-free product contains a sheet
moved by exactly one factor. Transitivity of the product is unnecessary for this leaf law. -/
theorem exists_occurrences_eq_one [Fintype α] (l : List (Perm α))
    (hl : ∀ g ∈ l, g.IsSwap) (hlen : l.length + 1 = Fintype.card α)
    (hfree : ∀ x, l.prod x ≠ x) : ∃ x, occurrences l x = 1 := by
  by_contra h
  push Not at h
  have hge (x : α) : 2 ≤ occurrences l x := by
    have hz : occurrences l x ≠ 0 := fun hx =>
      hfree x (prod_fixed_of_occurrences_eq_zero l x hx)
    have hne := h x
    omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hge x)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  rw [sum_occurrences l hl] at hs
  simp only [Nat.cast_id] at hs
  omega

end GaloisForLFunctions.HTGeometry.HurwitzFactorization
