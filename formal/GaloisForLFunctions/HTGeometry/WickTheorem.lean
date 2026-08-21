import GaloisForLFunctions.HTGeometry.WickNormalOrdering
import GaloisForLFunctions.HTGeometry.PairingExpansion

/-!
# Wick's theorem

For a creation/annihilation system `W : WickSystem K A ι` and a word `l : List (WickMode ι)`,
Wick's theorem expands the ordered operator product `op l₀ * op l₁ * ⋯` as the normal-ordered
product plus the sum of all *partial contractions*: for every choice of disjoint pairs of letters
one multiplies the corresponding contraction scalars and normally orders the letters that are left.

```text
(l.map op).prod = pairingExpand contract nord l
                = nord l + ∑ (single contractions) + ∑ (double contractions) + ⋯
```

The right-hand side is `pairingExpand`, whose recursion visits each partial pairing of the word
exactly once: the first letter is either left uncontracted — and prepended to the residual word
produced by the rest of the recursion — or contracted against one of the later letters, which is
then deleted along with it.

## Proof

The induction is the one in the physics literature.  Multiplying the expansion of `t` on the left by
one further operator `op u` is handled by `WickSystem.op_mul_nord`: `op u` either enters the
normal-ordered word or is contracted against one of its letters.  The contraction terms so produced
are indexed by *a partial pairing of `t` together with an uncontracted letter of it*, whereas the
recursion for the expansion of `u :: t` indexes them by *a letter of `t` together with a partial
pairing of the rest*.  That these two enumerations agree is the exchange law
`pairingExpand_positionSum`.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

namespace WickSystem

variable {K : Type u} {A : Type v} {ι : Type w}
variable [CommSemiring K] [Semiring A] [Algebra K A] (W : WickSystem K A ι)

/-- **Wick's theorem.**  The ordered product of the operators of a word equals the sum, over all
choices of disjoint pairs of letters, of the product of the contractions of the paired letters times
the normal-ordered product of the unpaired letters. -/
theorem prod_op_eq_pairingExpand_nord (l : List (WickMode ι)) :
    (l.map W.op).prod = pairingExpand W.contract W.nord l := by
  induction l with
  | nil => simp
  | cons u t ih =>
      rw [List.map_cons, List.prod_cons, ih, mul_pairingExpand]
      have hfun : (fun s => W.op u * W.nord s)
          = fun s => W.nord (u :: s)
              + positionSum s (fun a s' => W.contract u a • W.nord s') := by
        funext s
        exact W.op_mul_nord u s
      rw [hfun, pairingExpand_add, pairingExpand_cons]
      congr 1
      rw [pairingExpand_positionSum W.contract (fun a s' => W.contract u a • W.nord s')]
      exact positionSum_congr fun a s =>
        pairingExpand_smul W.contract (W.contract u a) W.nord s

/-- The one-letter case: a single operator is already normally ordered. -/
theorem prod_op_singleton (u : WickMode ι) : W.op u = W.nord [u] := by
  have h := W.prod_op_eq_pairingExpand_nord [u]
  rw [pairingExpand_cons] at h
  simpa using h

/-- The two-letter case, in the classical form `A B = :A B: + ⟨A B⟩`. -/
theorem prod_op_pair (u v : WickMode ι) :
    W.op u * W.op v = W.nord [u, v] + W.contract u v • (1 : A) :=
  W.mul_eq_nord_add_contract u v

end WickSystem

end GaloisForLFunctions.HTGeometry
