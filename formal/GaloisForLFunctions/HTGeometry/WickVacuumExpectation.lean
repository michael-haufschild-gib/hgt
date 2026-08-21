import GaloisForLFunctions.HTGeometry.WickTheorem
import GaloisForLFunctions.HTGeometry.CompletePairing

/-!
# Vacuum expectation values: only the complete pairings survive

A *vacuum* for a creation/annihilation system is a normalised linear functional that is killed by a
creation operator standing on the left and by an annihilation operator standing on the right:

```text
ω 1 = 1,   ω (cre i * x) = 0,   ω (x * ann i) = 0 .
```

These two conditions annihilate every nonempty normal-ordered product, because the leading letter of
such a product is either a creation operator on the far left or — after commuting the annihilation
letters, which is legitimate since they commute — an annihilation operator on the far right.
Applying `ω` to Wick's theorem therefore kills every partial pairing that leaves a letter
uncontracted, and

```text
ω (op l₀ * op l₁ * ⋯) = ∑ over perfect matchings of the word ∏ contractions .
```

This is Wick's theorem in its correlation-function form: a vacuum expectation of a product of free
fields is the sum over the ways of pairing the fields, and it vanishes for words of odd length.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {K : Type u} {A : Type v} {ι : Type w}
variable [CommSemiring K] [Semiring A] [Algebra K A]

/-- **A vacuum for a creation/annihilation system**: a normalised linear functional annihilated by
creation operators on the left and by annihilation operators on the right. -/
structure WickVacuum (W : WickSystem K A ι) where
  /-- The expectation functional. -/
  ω : A →ₗ[K] K
  /-- Normalisation. -/
  ω_one : ω 1 = 1
  /-- A creation operator on the left annihilates the vacuum functional. -/
  ω_cre : ∀ (i : ι) (x : A), ω (W.cre i * x) = 0
  /-- An annihilation operator on the right annihilates the vacuum functional. -/
  ω_ann : ∀ (i : ι) (x : A), ω (x * W.ann i) = 0

namespace WickVacuum

variable {W : WickSystem K A ι} (V : WickVacuum W)

/-- The vacuum kills every nonempty normal-ordered product. -/
theorem ω_nord (u : WickMode ι) (t : List (WickMode ι)) : V.ω (W.nord (u :: t)) = 0 := by
  cases u with
  | cre j =>
      rw [W.nord_cons_cre]
      exact V.ω_cre j _
  | ann j =>
      rw [W.nord_cons_ann']
      exact V.ω_ann j _

private theorem apply_wickExpand_eq_zero_aux :
    ∀ (n : ℕ) (l : List (WickMode ι)), l.length ≤ n → ∀ φ : List (WickMode ι) → A,
      (∀ s, V.ω (φ s) = 0) → V.ω (W.wickExpand φ l) = 0 := by
  intro n
  induction n with
  | zero =>
      intro l hl φ hφ
      match l with
      | [] => simpa using hφ []
      | (_ :: _) => simp at hl
  | succ n ih =>
      intro l hl φ hφ
      match l with
      | [] => simpa using hφ []
      | (u :: t) =>
        have ht : t.length ≤ n := by simpa using hl
        rw [W.wickExpand_cons, map_add, ih t ht (fun s => φ (u :: s)) (fun s => hφ _),
          map_positionSum, zero_add]
        refine Finset.sum_eq_zero fun k _ => ?_
        show V.ω (W.contract u t[(k : ℕ)] • W.wickExpand φ (t.eraseIdx (k : ℕ))) = 0
        rw [map_smul, ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht) φ hφ, smul_zero]

/-- A Wick expansion whose leftover functional is killed by the vacuum has zero expectation. -/
theorem apply_wickExpand_eq_zero (φ : List (WickMode ι) → A) (hφ : ∀ s, V.ω (φ s) = 0)
    (l : List (WickMode ι)) : V.ω (W.wickExpand φ l) = 0 :=
  apply_wickExpand_eq_zero_aux V l.length l le_rfl φ hφ

private theorem ω_wickExpand_nord_aux :
    ∀ (n : ℕ) (l : List (WickMode ι)), l.length ≤ n →
      V.ω (W.wickExpand W.nord l) = completePairing W.contract l := by
  intro n
  induction n with
  | zero =>
      intro l hl
      match l with
      | [] => simpa using V.ω_one
      | (_ :: _) => simp at hl
  | succ n ih =>
      intro l hl
      match l with
      | [] => simpa using V.ω_one
      | (u :: t) =>
        have ht : t.length ≤ n := by simpa using hl
        rw [W.wickExpand_cons, map_add,
          apply_wickExpand_eq_zero V (fun s => W.nord (u :: s)) (fun s => V.ω_nord u s) t,
          map_positionSum, zero_add, completePairing_cons]
        refine positionSum_congr' fun k => ?_
        show V.ω (W.contract u t[(k : ℕ)] • W.wickExpand W.nord (t.eraseIdx (k : ℕ)))
            = W.contract u t[(k : ℕ)] * completePairing W.contract (t.eraseIdx (k : ℕ))
        rw [map_smul, smul_eq_mul, ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht)]

/-- **Wick's theorem for vacuum expectation values.**  The expectation of an ordered product of
creation and annihilation operators is the sum over all perfect matchings of the word of the product
of the contractions of the matched letters.  In particular it vanishes for words of odd length. -/
theorem vacuum_prod_op (l : List (WickMode ι)) :
    V.ω ((l.map W.op).prod) = completePairing W.contract l := by
  rw [W.prod_op_eq_wickExpand_nord l]
  exact ω_wickExpand_nord_aux V l.length l le_rfl

end WickVacuum

end GaloisForLFunctions.HTGeometry
