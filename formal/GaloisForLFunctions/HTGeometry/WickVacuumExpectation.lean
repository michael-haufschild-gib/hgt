import GaloisForLFunctions.HTGeometry.WickTheorem

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

/-- **Wick's theorem for vacuum expectation values.**  The expectation of an ordered product of
creation and annihilation operators is the sum over all perfect matchings of the word of the product
of the contractions of the matched letters.  In particular it vanishes for words of odd length. -/
theorem vacuum_prod_op (l : List (WickMode ι)) :
    V.ω ((l.map W.op).prod) = completePairing W.contract l := by
  rw [W.prod_op_eq_pairingExpand_nord l, map_pairingExpand]
  refine pairingExpand_eq_completePairing _ _ ?_ ?_ l
  · simpa using V.ω_one
  · intro u t
    exact V.ω_nord u t

end WickVacuum

end GaloisForLFunctions.HTGeometry
