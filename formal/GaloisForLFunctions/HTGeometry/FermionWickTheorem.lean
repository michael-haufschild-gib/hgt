import GaloisForLFunctions.HTGeometry.SignedPairingExpansion
import Mathlib.Algebra.Algebra.Defs

/-!
# Wick's theorem for fermions

A fermionic creation/annihilation system obeys the canonical *anti*commutation relations

```text
cre i * cre j = -(cre j * cre i),   ann i * ann j = -(ann j * ann i),
ann i * cre j = -(cre j * ann i) + κ i j • 1 .
```

Wick's theorem has the same shape as in the bosonic case, with every contraction weighted by the
sign of the crossing it makes:

```text
(l.map field).prod = signedPairingExpand κ nordField l ,
```

and a vacuum expectation keeps only the complete pairings, so that a fermionic correlation function
is the **Pfaffian** of the matrix of two-point functions.

## Normal ordering without sign bookkeeping

Every term of the normal-ordered product of a word of `n` fields is a product of exactly `n`
operators, so moving an annihilation operator from the far left to the far right across it costs the
sign `(-1) ^ n`.  Rather than carry that power, this file defines the normal-ordered product
together with its sign-reversed companion by the mutual recursion

```text
nordField    []       = 1                nordFieldAlt []       = 1
nordField    (x :: l) = cre x * nordField l + nordFieldAlt l * ann x
nordFieldAlt (x :: l) = -(cre x * nordFieldAlt l) - nordField l * ann x
```

(so `nordFieldAlt l = (-1) ^ l.length • nordField l`), and the commutation law becomes the pair

```text
ann x * nordField    l = nordFieldAlt l * ann x + ∑ signed contractions of nordField
ann x * nordFieldAlt l = nordField    l * ann x - ∑ signed contractions of nordFieldAlt ,
```

proved by a single mutual induction.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

/-- **A fermionic creation/annihilation system**: the canonical anticommutation relations. -/
structure FermionSystem (K : Type u) (A : Type v) (ι : Type w)
    [CommRing K] [Ring A] [Algebra K A] where
  /-- The creation operators. -/
  cre : ι → A
  /-- The annihilation operators. -/
  ann : ι → A
  /-- The elementary contraction. -/
  κ : ι → ι → K
  /-- Creation operators anticommute. -/
  cre_mul_cre : ∀ i j, cre i * cre j = -(cre j * cre i)
  /-- Annihilation operators anticommute. -/
  ann_mul_ann : ∀ i j, ann i * ann j = -(ann j * ann i)
  /-- The canonical anticommutation relation. -/
  ann_mul_cre : ∀ i j, ann i * cre j = -(cre j * ann i) + κ i j • (1 : A)

namespace FermionSystem

variable {K : Type u} {A : Type v} {ι : Type w}
variable [CommRing K] [Ring A] [Algebra K A]

/-- The field of a label: creation plus annihilation. -/
def field (V : FermionSystem K A ι) (x : ι) : A := V.cre x + V.ann x

theorem field_def (V : FermionSystem K A ι) (x : ι) : V.field x = V.cre x + V.ann x := rfl

/-- The normal-ordered product of a word of fields together with its sign-reversed companion. -/
def nordPair (V : FermionSystem K A ι) : List ι → A × A
  | [] => (1, 1)
  | (x :: l) =>
      (V.cre x * (nordPair V l).1 + (nordPair V l).2 * V.ann x,
        -(V.cre x * (nordPair V l).2) - (nordPair V l).1 * V.ann x)

/-- **The normal-ordered product of a word of fields.** -/
def nordField (V : FermionSystem K A ι) (l : List ι) : A := (V.nordPair l).1

/-- The sign-reversed normal-ordered product, `(-1) ^ l.length` times `nordField`. -/
def nordFieldAlt (V : FermionSystem K A ι) (l : List ι) : A := (V.nordPair l).2

variable (V : FermionSystem K A ι)

@[simp] theorem nordField_nil : V.nordField ([] : List ι) = 1 := rfl
@[simp] theorem nordFieldAlt_nil : V.nordFieldAlt ([] : List ι) = 1 := rfl

theorem nordField_cons (x : ι) (l : List ι) :
    V.nordField (x :: l) = V.cre x * V.nordField l + V.nordFieldAlt l * V.ann x := rfl

theorem nordFieldAlt_cons (x : ι) (l : List ι) :
    V.nordFieldAlt (x :: l) = -(V.cre x * V.nordFieldAlt l) - V.nordField l * V.ann x := rfl

/-- **The two commutation laws**, proved by one mutual induction: an annihilation operator passes
from the left of a normal-ordered word of fields to its right, leaving one signed contraction term
for every field it crosses. -/
theorem ann_mul_nordField_and_alt (x : ι) : ∀ l : List ι,
    V.ann x * V.nordField l
        = V.nordFieldAlt l * V.ann x
          + signedPositionSum K l (fun a s => V.κ x a • V.nordField s)
      ∧ V.ann x * V.nordFieldAlt l
        = V.nordField l * V.ann x
          - signedPositionSum K l (fun a s => V.κ x a • V.nordFieldAlt s) := by
  intro l
  induction l with
  | nil => constructor <;> simp
  | cons y m ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hsplit : signedPositionSum K m (fun a s => V.κ x a • V.nordField (y :: s))
          = V.cre y * signedPositionSum K m (fun a s => V.κ x a • V.nordField s)
            + signedPositionSum K m (fun a s => V.κ x a • V.nordFieldAlt s) * V.ann y := by
        rw [mul_signedPositionSum, signedPositionSum_mul, ← signedPositionSum_add]
        refine signedPositionSum_congr fun a s => ?_
        rw [nordField_cons, smul_add, ← Algebra.mul_smul_comm, ← smul_mul_assoc]
      have hsplit' : signedPositionSum K m (fun a s => V.κ x a • V.nordFieldAlt (y :: s))
          = -(V.cre y * signedPositionSum K m (fun a s => V.κ x a • V.nordFieldAlt s))
            - signedPositionSum K m (fun a s => V.κ x a • V.nordField s) * V.ann y := by
        rw [mul_signedPositionSum, signedPositionSum_mul, ← signedPositionSum_neg,
          ← signedPositionSum_sub]
        refine signedPositionSum_congr fun a s => ?_
        rw [nordFieldAlt_cons, smul_sub, smul_neg, ← Algebra.mul_smul_comm, ← smul_mul_assoc]
      have hA : V.ann x * (V.cre y * V.nordField m)
          = -(V.cre y * V.nordFieldAlt m * V.ann x)
            - V.cre y * signedPositionSum K m (fun a s => V.κ x a • V.nordField s)
            + V.κ x y • V.nordField m := by
        rw [← mul_assoc, V.ann_mul_cre x y, add_mul, neg_mul, mul_assoc, ih1, mul_add,
          smul_mul_assoc, one_mul, ← mul_assoc]
        abel
      have hB : V.ann x * (V.nordFieldAlt m * V.ann y)
          = -(V.nordField m * V.ann y * V.ann x)
            - signedPositionSum K m (fun a s => V.κ x a • V.nordFieldAlt s) * V.ann y := by
        rw [← mul_assoc, ih2, sub_mul, mul_assoc, V.ann_mul_ann x y, mul_neg, ← mul_assoc]
      have hC : V.ann x * (V.cre y * V.nordFieldAlt m)
          = -(V.cre y * V.nordField m * V.ann x)
            + V.cre y * signedPositionSum K m (fun a s => V.κ x a • V.nordFieldAlt s)
            + V.κ x y • V.nordFieldAlt m := by
        rw [← mul_assoc, V.ann_mul_cre x y, add_mul, neg_mul, mul_assoc, ih2, mul_sub,
          smul_mul_assoc, one_mul, ← mul_assoc]
        abel
      have hD : V.ann x * (V.nordField m * V.ann y)
          = -(V.nordFieldAlt m * V.ann y * V.ann x)
            + signedPositionSum K m (fun a s => V.κ x a • V.nordField s) * V.ann y := by
        rw [← mul_assoc, ih1, add_mul, mul_assoc, V.ann_mul_ann x y, mul_neg, ← mul_assoc]
      constructor
      · rw [nordField_cons, nordFieldAlt_cons, signedPositionSum_cons, mul_add, hA, hB, hsplit,
          sub_mul, neg_mul]
        abel
      · rw [nordFieldAlt_cons, nordField_cons, signedPositionSum_cons, mul_sub, mul_neg, hC, hD,
          hsplit', add_mul]
        abel

/-- An annihilation operator passes through a normal-ordered word of fields. -/
theorem ann_mul_nordField (x : ι) (l : List ι) :
    V.ann x * V.nordField l
      = V.nordFieldAlt l * V.ann x
        + signedPositionSum K l (fun a s => V.κ x a • V.nordField s) :=
  (V.ann_mul_nordField_and_alt x l).1

/-- **Pushing one field into a normal-ordered word of fields.** -/
theorem field_mul_nordField (x : ι) (l : List ι) :
    V.field x * V.nordField l
      = V.nordField (x :: l) + signedPositionSum K l (fun a s => V.κ x a • V.nordField s) := by
  rw [field_def, add_mul, ann_mul_nordField, nordField_cons]
  abel

/-- **Wick's theorem for fermionic fields.**  An ordered product of free fermionic fields is the
signed sum, over all choices of disjoint pairs of fields, of the product of their contractions times
the normal-ordered product of the fields left over. -/
theorem prod_field_eq_signedPairingExpand (l : List ι) :
    (l.map V.field).prod = signedPairingExpand K V.κ V.nordField l := by
  induction l with
  | nil => simp
  | cons u t ih =>
      rw [List.map_cons, List.prod_cons, ih, mul_signedPairingExpand]
      have hfun : (fun s => V.field u * V.nordField s)
          = fun s => V.nordField (u :: s)
              + signedPositionSum K s (fun a s' => V.κ u a • V.nordField s') := by
        funext s
        exact V.field_mul_nordField u s
      rw [hfun, signedPairingExpand_add, signedPairingExpand_cons]
      congr 1
      rw [signedPairingExpand_signedPositionSum V.κ (fun a s' => V.κ u a • V.nordField s')]
      exact signedPositionSum_congr fun a s =>
        signedPairingExpand_smul V.κ (V.κ u a) V.nordField s

end FermionSystem

/-- **A vacuum for a fermionic system.** -/
structure FermionVacuum {K : Type u} {A : Type v} {ι : Type w}
    [CommRing K] [Ring A] [Algebra K A] (V : FermionSystem K A ι) where
  /-- The expectation functional. -/
  ω : A →ₗ[K] K
  /-- Normalisation. -/
  ω_one : ω 1 = 1
  /-- A creation operator on the left annihilates the vacuum functional. -/
  ω_cre : ∀ (i : ι) (x : A), ω (V.cre i * x) = 0
  /-- An annihilation operator on the right annihilates the vacuum functional. -/
  ω_ann : ∀ (i : ι) (x : A), ω (x * V.ann i) = 0

namespace FermionVacuum

variable {K : Type u} {A : Type v} {ι : Type w}
variable [CommRing K] [Ring A] [Algebra K A]
variable {V : FermionSystem K A ι} (Ω : FermionVacuum V)

/-- The vacuum kills every nonempty normal-ordered word of fields. -/
theorem ω_nordField (x : ι) (l : List ι) : Ω.ω (V.nordField (x :: l)) = 0 := by
  rw [V.nordField_cons, map_add, Ω.ω_cre, Ω.ω_ann, add_zero]

/-- **Wick's theorem for fermionic correlation functions.**  The vacuum expectation of an ordered
product of free fermionic fields is the Pfaffian of the matrix of two-point functions; in
particular it vanishes for an odd number of fields. -/
theorem vacuum_prod_field (l : List ι) :
    Ω.ω ((l.map V.field).prod) = pfaffianPairing K V.κ l := by
  rw [V.prod_field_eq_signedPairingExpand l, map_signedPairingExpand]
  refine signedPairingExpand_eq_pfaffianPairing _ _ ?_ ?_ l
  · simpa using Ω.ω_one
  · intro u t
    exact Ω.ω_nordField u t

/-- **The contraction is the two-point function.** -/
theorem ω_field_mul_field (x y : ι) : Ω.ω (V.field x * V.field y) = V.κ x y := by
  have h := Ω.vacuum_prod_field [x, y]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [h, pfaffianPairing_cons]
  simp [signedPositionSum]

end FermionVacuum

end GaloisForLFunctions.HTGeometry
