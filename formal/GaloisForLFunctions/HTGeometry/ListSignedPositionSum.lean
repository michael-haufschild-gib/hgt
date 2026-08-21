import GaloisForLFunctions.HTGeometry.ListPositionSum
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Tactic.Abel

/-!
# Signed sums over the positions of a list

The fermionic analogue of `positionSum`: the term at position `k` carries the crossing sign
`(-1) ^ k`,

```text
signedPositionSum K l f = ∑ k : Fin l.length, (-1) ^ k • f l[k] (l.eraseIdx k) .
```

The head/tail recursion acquires a minus sign,

```text
signedPositionSum K (w :: m) f = f w m - signedPositionSum K m (fun a s => f a (w :: s)) ,
```

and consequently the exchange law becomes an *anti*symmetry: choosing a position, deleting it and
choosing a second position gives a double sum that changes sign when the two chosen entries are
exchanged (`signedPositionSum_swap`).  This single sign is the whole difference between Wick's
theorem for bosons and for fermions; it is what turns the complete-pairing sum into a Pfaffian.
-/

universe u v w

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {α : Type u} {M : Type w}

/-- The sum over the positions of `l`, the term at position `k` weighted by the crossing sign
`(-1) ^ k`. -/
def signedPositionSum (K : Type v) [CommRing K] [AddCommGroup M] [Module K M]
    (l : List α) (f : α → List α → M) : M :=
  ∑ k : Fin l.length, (-1 : K) ^ (k : ℕ) • f l[(k : ℕ)] (l.eraseIdx (k : ℕ))

variable {K : Type v} [CommRing K] [AddCommGroup M] [Module K M]

@[simp] theorem signedPositionSum_nil (f : α → List α → M) :
    signedPositionSum K ([] : List α) f = 0 := by
  simp [signedPositionSum]

/-- **Head/tail recursion.**  Moving past the head costs one crossing, hence one sign. -/
theorem signedPositionSum_cons (w : α) (m : List α) (f : α → List α → M) :
    signedPositionSum K (w :: m) f
      = f w m - signedPositionSum K m (fun a s => f a (w :: s)) := by
  simp only [signedPositionSum, List.length_cons]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, List.getElem_cons_zero, List.eraseIdx_cons_zero,
    Fin.val_succ, List.getElem_cons_succ, List.eraseIdx_cons_succ]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_succ, mul_comm ((-1 : K) ^ (k : ℕ)) (-1 : K), neg_one_mul, neg_smul]

theorem signedPositionSum_congr' {l : List α} {f g : α → List α → M}
    (h : ∀ k : Fin l.length,
      f l[(k : ℕ)] (l.eraseIdx (k : ℕ)) = g l[(k : ℕ)] (l.eraseIdx (k : ℕ))) :
    signedPositionSum K l f = signedPositionSum K l g :=
  Finset.sum_congr rfl fun k _ => by rw [h k]

theorem signedPositionSum_congr {l : List α} {f g : α → List α → M} (h : ∀ a s, f a s = g a s) :
    signedPositionSum K l f = signedPositionSum K l g :=
  signedPositionSum_congr' fun _ => h _ _

@[simp] theorem signedPositionSum_zero (l : List α) :
    signedPositionSum K l (fun _ _ => (0 : M)) = 0 := by
  simp [signedPositionSum]

theorem signedPositionSum_add (l : List α) (f g : α → List α → M) :
    signedPositionSum K l (fun a s => f a s + g a s)
      = signedPositionSum K l f + signedPositionSum K l g := by
  simp [signedPositionSum, smul_add, Finset.sum_add_distrib]

theorem signedPositionSum_sub (l : List α) (f g : α → List α → M) :
    signedPositionSum K l (fun a s => f a s - g a s)
      = signedPositionSum K l f - signedPositionSum K l g := by
  simp [signedPositionSum, smul_sub, Finset.sum_sub_distrib]

theorem signedPositionSum_neg (l : List α) (f : α → List α → M) :
    signedPositionSum K l (fun a s => -f a s) = -signedPositionSum K l f := by
  simp [signedPositionSum, Finset.sum_neg_distrib]

theorem signedPositionSum_smul (l : List α) (b : K) (f : α → List α → M) :
    signedPositionSum K l (fun a s => b • f a s) = b • signedPositionSum K l f := by
  simp only [signedPositionSum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

/-- **The exchange law is an antisymmetry.**  Choosing a position, deleting it and choosing a
second position produces a double sum that changes sign under exchanging the two chosen entries. -/
theorem signedPositionSum_swap :
    ∀ (l : List α) (F : α → α → List α → M),
      signedPositionSum K l (fun a s => signedPositionSum K s (fun b t => F a b t))
        = -signedPositionSum K l (fun a s => signedPositionSum K s (fun b t => F b a t)) := by
  intro l
  induction l with
  | nil => intro F; simp
  | cons w m ih =>
      intro F
      rw [signedPositionSum_cons, signedPositionSum_cons]
      have hL : signedPositionSum K m
            (fun a s => signedPositionSum K (w :: s) (fun b t => F a b t))
          = signedPositionSum K m (fun a s => F a w s)
            - signedPositionSum K m
                (fun a s => signedPositionSum K s (fun b t => F a b (w :: t))) := by
        rw [← signedPositionSum_sub]
        exact signedPositionSum_congr fun a s => signedPositionSum_cons _ _ _
      have hR : signedPositionSum K m
            (fun a s => signedPositionSum K (w :: s) (fun b t => F b a t))
          = signedPositionSum K m (fun a s => F w a s)
            - signedPositionSum K m
                (fun a s => signedPositionSum K s (fun b t => F b a (w :: t))) := by
        rw [← signedPositionSum_sub]
        exact signedPositionSum_congr fun a s => signedPositionSum_cons _ _ _
      rw [hL, hR, ih (fun a b t => F a b (w :: t))]
      abel

section Mul

variable {A : Type w} [Ring A] [Algebra K A]

theorem mul_signedPositionSum (x : A) (l : List α) (f : α → List α → A) :
    x * signedPositionSum K l f = signedPositionSum K l (fun a s => x * f a s) := by
  simp only [signedPositionSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Algebra.mul_smul_comm _ _ _

theorem signedPositionSum_mul (x : A) (l : List α) (f : α → List α → A) :
    signedPositionSum K l f * x = signedPositionSum K l (fun a s => f a s * x) := by
  simp only [signedPositionSum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => smul_mul_assoc _ _ _

end Mul

/-- An additive map passes through a signed position sum. -/
theorem map_signedPositionSum {N : Type*} [AddCommGroup N] [Module K N] (g : M →ₗ[K] N)
    (l : List α) (f : α → List α → M) :
    g (signedPositionSum K l f) = signedPositionSum K l (fun a s => g (f a s)) := by
  simp [signedPositionSum, map_sum]

end GaloisForLFunctions.HTGeometry
