import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Sums over the positions of a list, with the chosen position deleted

Wick-type expansions are indexed by *choices of positions* in a word: one picks an entry of a list
and continues with the list obtained by deleting that entry.  This file packages that pattern as

```text
positionSum l f = ∑ k : Fin l.length, f l[k] (l.eraseIdx k)
```

and proves the four facts needed to run an induction over such expansions:

* `positionSum_cons` — the head/tail recursion;
* `positionSum_add`, `positionSum_smul` — linearity in the summand;
* `positionSum_swap` — **the exchange law**: iterating the construction twice produces a sum that is
  symmetric under exchanging the two chosen entries.

The exchange law is the combinatorial heart of Wick's theorem.  Choosing a position, deleting it and
choosing a second position enumerates the ordered pairs of distinct positions of the original list,
and deleting both entries gives the same residual list for either order of the two choices.  The
proof below never mentions ordered pairs: the head/tail recursion turns the exchange into an
induction in which the two "first" terms of the two sides are each other's second terms.
-/

universe u v w

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {α : Type u} {A : Type v}

section AddCommMonoid

variable [AddCommMonoid A]

/-- The sum over all positions of `l` of a quantity depending on the entry at that position and on
the list obtained from `l` by deleting that position. -/
def positionSum (l : List α) (f : α → List α → A) : A :=
  ∑ k : Fin l.length, f l[(k : ℕ)] (l.eraseIdx (k : ℕ))

@[simp] theorem positionSum_nil (f : α → List α → A) : positionSum ([] : List α) f = 0 := by
  simp [positionSum]

/-- **Head/tail recursion for a position sum.**  Either the chosen position is the head, or it is a
position of the tail — in which case the head survives the deletion. -/
theorem positionSum_cons (w : α) (m : List α) (f : α → List α → A) :
    positionSum (w :: m) f = f w m + positionSum m (fun a s => f a (w :: s)) := by
  simp only [positionSum, List.length_cons]
  rw [Fin.sum_univ_succ]
  simp

@[simp] theorem positionSum_zero (l : List α) :
    positionSum l (fun _ _ => (0 : A)) = 0 := by
  simp [positionSum]

theorem positionSum_add (l : List α) (f g : α → List α → A) :
    positionSum l (fun a s => f a s + g a s) = positionSum l f + positionSum l g := by
  simp [positionSum, Finset.sum_add_distrib]

theorem positionSum_congr {l : List α} {f g : α → List α → A} (h : ∀ a s, f a s = g a s) :
    positionSum l f = positionSum l g := by
  simp only [positionSum]
  exact Finset.sum_congr rfl fun k _ => h _ _

/-- **The exchange law.**  Choosing a position, deleting it, and choosing a second position gives a
double sum which is symmetric in the two chosen entries. -/
theorem positionSum_swap :
    ∀ (l : List α) (F : α → α → List α → A),
      positionSum l (fun a s => positionSum s (fun b t => F a b t))
        = positionSum l (fun a s => positionSum s (fun b t => F b a t)) := by
  intro l
  induction l with
  | nil => intro F; simp
  | cons w m ih =>
      intro F
      rw [positionSum_cons, positionSum_cons]
      -- expand the inner position sums over the surviving head `w`
      have hL : positionSum m (fun a s => positionSum (w :: s) (fun b t => F a b t))
          = positionSum m (fun a s => F a w s)
            + positionSum m (fun a s => positionSum s (fun b t => F a b (w :: t))) := by
        rw [← positionSum_add]
        exact positionSum_congr fun a s => positionSum_cons _ _ _
      have hR : positionSum m (fun a s => positionSum (w :: s) (fun b t => F b a t))
          = positionSum m (fun a s => F w a s)
            + positionSum m (fun a s => positionSum s (fun b t => F b a (w :: t))) := by
        rw [← positionSum_add]
        exact positionSum_congr fun a s => positionSum_cons _ _ _
      rw [hL, hR, ih (fun a b t => F a b (w :: t)), add_left_comm]

end AddCommMonoid

section SMul

variable [AddCommMonoid A] {K : Type w} [Monoid K] [DistribMulAction K A]

theorem positionSum_smul (l : List α) (c : K) (f : α → List α → A) :
    positionSum l (fun a s => c • f a s) = c • positionSum l f := by
  simp [positionSum, Finset.smul_sum]

end SMul

section Mul

variable [NonUnitalNonAssocSemiring A]

theorem mul_positionSum (x : A) (l : List α) (f : α → List α → A) :
    x * positionSum l f = positionSum l (fun a s => x * f a s) := by
  simp [positionSum, Finset.mul_sum]

theorem positionSum_mul (x : A) (l : List α) (f : α → List α → A) :
    positionSum l f * x = positionSum l (fun a s => f a s * x) := by
  simp [positionSum, Finset.sum_mul]

end Mul

section Congr

variable [AddCommMonoid A]

/-- Congruence for a position sum, only along the entries and residual lists that actually occur. -/
theorem positionSum_congr' {l : List α} {f g : α → List α → A}
    (h : ∀ k : Fin l.length,
      f l[(k : ℕ)] (l.eraseIdx (k : ℕ)) = g l[(k : ℕ)] (l.eraseIdx (k : ℕ))) :
    positionSum l f = positionSum l g :=
  Finset.sum_congr rfl fun k _ => h k

/-- An additive map passes through a position sum. -/
theorem map_positionSum {B : Type*} [AddCommMonoid B] {F : Type*} [FunLike F A B]
    [AddMonoidHomClass F A B] (g : F) (l : List α) (f : α → List α → A) :
    g (positionSum l f) = positionSum l (fun a s => g (f a s)) := by
  simp [positionSum, map_sum]

/-- Every residual list occurring in a position sum is shorter than the list itself. -/
theorem length_eraseIdx_lt {l : List α} (k : Fin l.length) :
    (l.eraseIdx (k : ℕ)).length < l.length := by
  have h := k.isLt
  rw [List.length_eraseIdx_of_lt h]
  omega

end Congr

end GaloisForLFunctions.HTGeometry
