import GaloisForLFunctions.HTGeometry.WickVacuumExpectation

/-!
# Wick's theorem for fields

A free field is the sum of its creation and annihilation parts,

```text
φ x = cre x + ann x ,
```

and the physical form of Wick's theorem expands a product of fields — not of pure creation and
annihilation operators — into a normal-ordered product plus contractions:

```text
φ x₀ * φ x₁ * ⋯ = :φ x₀ φ x₁ ⋯: + ∑ (single contractions) + ∑ (double contractions) + ⋯
```

Normal ordering a word of fields means expanding every field into its two parts and, in each of the
resulting terms, moving the creation parts to the left of the annihilation parts.  Because
annihilation operators commute with one another, that operation obeys the two-term recursion

```text
nordField []       = 1
nordField (x :: l) = cre x * nordField l + nordField l * ann x ,
```

which is how it is defined here: the new field either contributes its creation part on the far left
or its annihilation part on the far right.

The contraction of two fields is the scalar `κ x y`, and — by
`WickVacuum.ω_field_mul_field` — it is exactly the two-point function `ω (φ x * φ y)`.  Applying a
vacuum to the expansion therefore gives the correlation-function form of Wick's theorem:

```text
ω (φ x₀ * φ x₁ * ⋯) = ∑ over the perfect matchings of the word ∏ ω (φ xᵢ φ xⱼ) .
```
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

namespace WickSystem

variable {K : Type u} {A : Type v} {ι : Type w}
variable [CommSemiring K] [Semiring A] [Algebra K A] (W : WickSystem K A ι)

/-- **The field of a label**: the sum of its creation and annihilation parts. -/
def field (x : ι) : A := W.cre x + W.ann x

theorem field_def (x : ι) : W.field x = W.cre x + W.ann x := rfl

/-- **The normal-ordered product of a word of fields.**  Each new field contributes its creation
part on the far left and its annihilation part on the far right. -/
def nordField (V : WickSystem K A ι) : List ι → A
  | [] => 1
  | (x :: l) => V.cre x * nordField V l + nordField V l * V.ann x

@[simp] theorem nordField_nil : W.nordField ([] : List ι) = 1 := by
  rw [nordField]

theorem nordField_cons (x : ι) (l : List ι) :
    W.nordField (x :: l) = W.cre x * W.nordField l + W.nordField l * W.ann x := by
  rw [nordField]

/-- **Commuting an annihilation operator through a normal-ordered word of fields.**  It passes to
the right, leaving one contraction term for every field it crosses. -/
theorem ann_mul_nordField (x : ι) (l : List ι) :
    W.ann x * W.nordField l
      = W.nordField l * W.ann x + positionSum l (fun a s => W.κ x a • W.nordField s) := by
  induction l with
  | nil => simp
  | cons y m ih =>
      have h1 : W.ann x * (W.cre y * W.nordField m)
          = W.cre y * W.nordField m * W.ann x
            + (W.cre y * positionSum m (fun a s => W.κ x a • W.nordField s)
              + W.κ x y • W.nordField m) := by
        rw [← mul_assoc, W.ann_mul_cre x y, add_mul, mul_assoc, smul_mul_assoc, one_mul, ih,
          mul_add, ← mul_assoc]
        abel
      have h2 : W.ann x * (W.nordField m * W.ann y)
          = W.nordField m * W.ann y * W.ann x
            + positionSum m (fun a s => W.κ x a • W.nordField s) * W.ann y := by
        rw [← mul_assoc, ih, add_mul, mul_assoc, W.ann_mul_ann x y, ← mul_assoc]
      have hL : W.cre y * positionSum m (fun a s => W.κ x a • W.nordField s)
          = positionSum m (fun a s => W.κ x a • (W.cre y * W.nordField s)) := by
        rw [mul_positionSum]
        exact positionSum_congr fun a s => Algebra.mul_smul_comm _ _ _
      have hR : positionSum m (fun a s => W.κ x a • W.nordField s) * W.ann y
          = positionSum m (fun a s => W.κ x a • (W.nordField s * W.ann y)) := by
        rw [positionSum_mul]
        exact positionSum_congr fun a s => smul_mul_assoc _ _ _
      have h3 : positionSum (y :: m) (fun a s => W.κ x a • W.nordField s)
          = W.κ x y • W.nordField m
            + (positionSum m (fun a s => W.κ x a • (W.cre y * W.nordField s))
              + positionSum m (fun a s => W.κ x a • (W.nordField s * W.ann y))) := by
        rw [positionSum_cons, ← positionSum_add]
        congr 1
        exact positionSum_congr fun a s => by rw [nordField_cons, smul_add]
      rw [nordField_cons, mul_add, h1, h2, h3, add_mul, hL, hR]
      abel

/-- **Pushing one field into a normal-ordered word of fields.** -/
theorem field_mul_nordField (x : ι) (l : List ι) :
    W.field x * W.nordField l
      = W.nordField (x :: l) + positionSum l (fun a s => W.κ x a • W.nordField s) := by
  rw [field_def, add_mul, ann_mul_nordField, nordField_cons]
  abel

/-- **Wick's theorem for fields.**  An ordered product of free fields is the sum, over all choices
of disjoint pairs of fields, of the product of their contractions times the normal-ordered product
of the fields left over. -/
theorem prod_field_eq_pairingExpand_nordField (l : List ι) :
    (l.map W.field).prod = pairingExpand W.κ W.nordField l := by
  induction l with
  | nil => simp
  | cons u t ih =>
      rw [List.map_cons, List.prod_cons, ih, mul_pairingExpand]
      have hfun : (fun s => W.field u * W.nordField s)
          = fun s => W.nordField (u :: s)
              + positionSum s (fun a s' => W.κ u a • W.nordField s') := by
        funext s
        exact W.field_mul_nordField u s
      rw [hfun, pairingExpand_add, pairingExpand_cons]
      congr 1
      rw [pairingExpand_positionSum W.κ (fun a s' => W.κ u a • W.nordField s')]
      exact positionSum_congr fun a s => pairingExpand_smul W.κ (W.κ u a) W.nordField s

/-- Two fields: the classical `φ x φ y = :φ x φ y: + ⟨φ x φ y⟩`. -/
theorem field_mul_field (x y : ι) :
    W.field x * W.field y = W.nordField [x, y] + W.κ x y • (1 : A) := by
  have h := W.prod_field_eq_pairingExpand_nordField [x, y]
  rw [pairingExpand_cons, pairingExpand_cons] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    positionSum_cons, positionSum_nil, pairingExpand_nil, add_zero] at h
  rw [h, nordField_nil]

end WickSystem

namespace WickVacuum

variable {K : Type u} {A : Type v} {ι : Type w}
variable [CommSemiring K] [Semiring A] [Algebra K A]
variable {W : WickSystem K A ι} (V : WickVacuum W)

/-- The vacuum kills every nonempty normal-ordered word of fields. -/
theorem ω_nordField (x : ι) (l : List ι) : V.ω (W.nordField (x :: l)) = 0 := by
  rw [W.nordField_cons, map_add, V.ω_cre, V.ω_ann, add_zero]

/-- **The contraction is the two-point function.** -/
theorem ω_field_mul_field (x y : ι) : V.ω (W.field x * W.field y) = W.κ x y := by
  rw [W.field_mul_field, map_add, map_smul, V.ω_nordField x [y], smul_eq_mul, V.ω_one, mul_one, zero_add]

/-- **Wick's theorem for correlation functions.**  The vacuum expectation of an ordered product of
free fields is the sum over all perfect matchings of the word of the products of the two-point
functions of the matched fields; in particular it vanishes for an odd number of fields. -/
theorem vacuum_prod_field (l : List ι) :
    V.ω ((l.map W.field).prod) = completePairing W.κ l := by
  rw [W.prod_field_eq_pairingExpand_nordField l, map_pairingExpand]
  refine pairingExpand_eq_completePairing _ _ ?_ ?_ l
  · simpa using V.ω_one
  · intro u t
    exact V.ω_nordField u t

end WickVacuum

end GaloisForLFunctions.HTGeometry
