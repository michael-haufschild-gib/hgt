import GaloisForLFunctions.HTGeometry.ListPositionSum
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel

/-!
# Creation/annihilation systems, normal ordering, and the one-step contraction law

This file sets up the algebraic frame in which Wick's theorem is stated and proves the single
commutation step on which its induction rests.

## The frame

A `WickSystem K A ι` is a unital `K`-algebra `A` together with two families of elements of `A`
indexed by `ι`,

```text
cre i   (creation operators)      ann i   (annihilation operators)
```

subject to the canonical commutation relations of a free bosonic field:

```text
cre i * cre j = cre j * cre i,   ann i * ann j = ann j * ann i,
ann i * cre j = cre j * ann i + κ i j • 1 .
```

The scalar `κ i j` is the elementary contraction; in field theory it is the propagator.

## Normal ordering

A *mode* is a single creation or annihilation label, `WickMode ι`.  For a word `l : List (WickMode ι)`
the normal-ordered product `W.nord l` is obtained by moving every creation operator to the left of
every annihilation operator, keeping the relative order inside each of the two groups.  Because
creations commute among themselves and annihilations commute among themselves this is unambiguous;
we define it directly as `creProd l * annProd l`.

The contraction of two modes,

```text
W.contract (ann i) (cre j) = κ i j,   W.contract _ _ = 0 otherwise,
```

is precisely the defect `u * v - :u v:` of the normal ordering on a two-letter word
(`WickSystem.mul_eq_nord_add_contract`).

## Main result

`WickSystem.op_mul_nord`:

```text
op u * nord l = nord (u :: l) + ∑ (positions k of l) contract u l[k] • nord (l.eraseIdx k)
```

Pushing one operator into a normal-ordered word produces the longer normal-ordered word plus one
contraction term for every letter the operator had to cross.  This is the inductive step of Wick's
theorem, and everything else in the theorem is bookkeeping over these contractions.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

/-- A single letter of a Wick word: either a creation label or an annihilation label. -/
inductive WickMode (ι : Type w) where
  | cre (i : ι) : WickMode ι
  | ann (i : ι) : WickMode ι
  deriving DecidableEq

namespace WickMode

variable {ι : Type w}

/-- Whether a mode is a creation mode. -/
def isCre : WickMode ι → Bool
  | .cre _ => true
  | .ann _ => false

@[simp] theorem isCre_cre (i : ι) : (WickMode.cre i).isCre = true := rfl
@[simp] theorem isCre_ann (i : ι) : (WickMode.ann i).isCre = false := rfl

end WickMode

/-- **A creation/annihilation system.**  A unital `K`-algebra together with two families of elements
satisfying the canonical commutation relations, with elementary contraction `κ`. -/
structure WickSystem (K : Type u) (A : Type v) (ι : Type w)
    [CommSemiring K] [Semiring A] [Algebra K A] where
  /-- The creation operators. -/
  cre : ι → A
  /-- The annihilation operators. -/
  ann : ι → A
  /-- The elementary contraction `⟨ann i, cre j⟩`. -/
  κ : ι → ι → K
  /-- Creation operators commute. -/
  cre_mul_cre : ∀ i j, cre i * cre j = cre j * cre i
  /-- Annihilation operators commute. -/
  ann_mul_ann : ∀ i j, ann i * ann j = ann j * ann i
  /-- The canonical commutation relation. -/
  ann_mul_cre : ∀ i j, ann i * cre j = cre j * ann i + κ i j • (1 : A)

namespace WickSystem

variable {K : Type u} {A : Type v} {ι : Type w}
variable [CommSemiring K] [Semiring A] [Algebra K A] (W : WickSystem K A ι)

/-- The operator attached to a mode. -/
def op : WickMode ι → A
  | .cre i => W.cre i
  | .ann i => W.ann i

@[simp] theorem op_cre (i : ι) : W.op (.cre i) = W.cre i := rfl
@[simp] theorem op_ann (i : ι) : W.op (.ann i) = W.ann i := rfl

/-- The contraction of two modes: nonzero only for an annihilation operator standing to the left of
a creation operator. -/
def contract : WickMode ι → WickMode ι → K
  | .ann i, .cre j => W.κ i j
  | _, _ => 0

@[simp] theorem contract_ann_cre (i j : ι) : W.contract (.ann i) (.cre j) = W.κ i j := rfl
@[simp] theorem contract_ann_ann (i j : ι) : W.contract (.ann i) (.ann j) = 0 := rfl
@[simp] theorem contract_cre (i : ι) (v : WickMode ι) : W.contract (.cre i) v = 0 := by
  cases v <;> rfl

/-! ## Normal ordering -/

/-- The product of the creation operators of a word, in order. -/
def creProd (l : List (WickMode ι)) : A :=
  ((l.filter WickMode.isCre).map W.op).prod

/-- The product of the annihilation operators of a word, in order. -/
def annProd (l : List (WickMode ι)) : A :=
  ((l.filter (fun v => !v.isCre)).map W.op).prod

/-- **The normal-ordered product** of a word: every creation operator moved to the left of every
annihilation operator, relative orders preserved. -/
def nord (l : List (WickMode ι)) : A := W.creProd l * W.annProd l

@[simp] theorem creProd_nil : W.creProd ([] : List (WickMode ι)) = 1 := rfl
@[simp] theorem annProd_nil : W.annProd ([] : List (WickMode ι)) = 1 := rfl
@[simp] theorem nord_nil : W.nord ([] : List (WickMode ι)) = 1 := by simp [nord]

@[simp] theorem creProd_cons_cre (i : ι) (l : List (WickMode ι)) :
    W.creProd (.cre i :: l) = W.cre i * W.creProd l := by
  simp [creProd]

@[simp] theorem creProd_cons_ann (i : ι) (l : List (WickMode ι)) :
    W.creProd (.ann i :: l) = W.creProd l := by
  simp [creProd]

@[simp] theorem annProd_cons_cre (i : ι) (l : List (WickMode ι)) :
    W.annProd (.cre i :: l) = W.annProd l := by
  simp [annProd]

@[simp] theorem annProd_cons_ann (i : ι) (l : List (WickMode ι)) :
    W.annProd (.ann i :: l) = W.ann i * W.annProd l := by
  simp [annProd]

@[simp] theorem nord_cons_cre (i : ι) (l : List (WickMode ι)) :
    W.nord (.cre i :: l) = W.cre i * W.nord l := by
  simp [nord, mul_assoc]

theorem nord_cons_ann (i : ι) (l : List (WickMode ι)) :
    W.nord (.ann i :: l) = W.creProd l * (W.ann i * W.annProd l) := by
  simp [nord]

/-- Annihilation operators commute with the annihilation part of any word. -/
theorem ann_mul_annProd (j : ι) (l : List (WickMode ι)) :
    W.ann j * W.annProd l = W.annProd l * W.ann j := by
  induction l with
  | nil => simp
  | cons v m ih =>
      cases v with
      | cre i => simpa using ih
      | ann i =>
          rw [annProd_cons_ann, ← mul_assoc, W.ann_mul_ann j i, mul_assoc, ih, mul_assoc]

/-- Prefixing an annihilation letter appends its operator on the right of the normal-ordered
product. -/
theorem nord_cons_ann' (i : ι) (l : List (WickMode ι)) :
    W.nord (.ann i :: l) = W.nord l * W.ann i := by
  rw [nord_cons_ann, nord, mul_assoc, ← W.ann_mul_annProd i l]

/-- The contraction of two modes is exactly the defect of normal ordering on a two-letter word. -/
theorem mul_eq_nord_add_contract (u v : WickMode ι) :
    W.op u * W.op v = W.nord [u, v] + W.contract u v • (1 : A) := by
  cases u with
  | cre i =>
      cases v with
      | cre j => simp [nord, creProd, annProd]
      | ann j => simp [nord, creProd, annProd]
  | ann i =>
      cases v with
      | cre j => simp [nord, creProd, annProd, W.ann_mul_cre i j]
      | ann j => simp [nord, creProd, annProd]

/-! ## The one-step contraction law -/

/-- **Pushing one operator into a normal-ordered word.**  The operator either joins the word, or is
contracted against one of its letters. -/
theorem op_mul_nord (u : WickMode ι) (l : List (WickMode ι)) :
    W.op u * W.nord l
      = W.nord (u :: l) + positionSum l (fun a s => W.contract u a • W.nord s) := by
  cases u with
  | cre i =>
      have h : positionSum l (fun a s => W.contract (WickMode.cre i) a • W.nord s)
          = (0 : A) := by
        rw [show (fun (a : WickMode ι) (s : List (WickMode ι)) =>
            W.contract (WickMode.cre i) a • W.nord s) = fun _ _ => (0 : A) from by
          funext a s; simp]
        simp
      rw [h, nord_cons_cre, add_zero, op_cre]
  | ann i =>
      induction l with
      | nil => simp [nord_cons_ann]
      | cons v m ih =>
          cases v with
          | cre j =>
              rw [nord_cons_cre, ← mul_assoc, op_ann, W.ann_mul_cre i j, add_mul, mul_assoc,
                smul_mul_assoc, one_mul, ← op_ann, ih, mul_add]
              rw [positionSum_cons]
              have hcre : W.nord (WickMode.ann i :: WickMode.cre j :: m)
                  = W.cre j * W.nord (WickMode.ann i :: m) := by
                rw [nord_cons_ann, nord_cons_ann, creProd_cons_cre, annProd_cons_cre, mul_assoc]
              have hsum : W.cre j * positionSum m
                    (fun a s => W.contract (WickMode.ann i) a • W.nord s)
                  = positionSum m (fun a s =>
                      W.contract (WickMode.ann i) a • W.nord (WickMode.cre j :: s)) := by
                simp only [positionSum, Finset.mul_sum]
                exact Finset.sum_congr rfl fun k _ => by
                  rw [Algebra.mul_smul_comm, nord_cons_cre]
              rw [hcre, hsum, contract_ann_cre]
              abel
          | ann j =>
              have hcomm : W.nord (WickMode.ann j :: m) = W.nord m * W.ann j := by
                rw [nord_cons_ann, nord, mul_assoc, ← W.ann_mul_annProd j m]
              rw [hcomm, ← mul_assoc, op_ann, ← op_ann, ih, add_mul]
              rw [positionSum_cons, contract_ann_ann, zero_smul, zero_add]
              have hn : W.nord (WickMode.ann i :: m) * W.ann j
                  = W.nord (WickMode.ann i :: WickMode.ann j :: m) := by
                rw [nord_cons_ann, nord_cons_ann, creProd_cons_ann, annProd_cons_ann,
                  mul_assoc (W.creProd m) (W.ann i * W.annProd m) (W.ann j),
                  mul_assoc (W.ann i) (W.annProd m) (W.ann j), ← W.ann_mul_annProd j m]
              have hsum : positionSum m (fun a s => W.contract (WickMode.ann i) a • W.nord s)
                    * W.ann j
                  = positionSum m (fun a s =>
                      W.contract (WickMode.ann i) a • W.nord (WickMode.ann j :: s)) := by
                simp only [positionSum, Finset.sum_mul]
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [smul_mul_assoc]
                congr 1
                rw [nord_cons_ann, nord, mul_assoc, ← W.ann_mul_annProd j]
              rw [hn, hsum]

end WickSystem

end GaloisForLFunctions.HTGeometry
