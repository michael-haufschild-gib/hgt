/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.BorelWeil.RegularFunctions
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The standard Borel subgroup of `SL(n,k)` and its diagonal characters

For a linearly ordered finite index type `n`, the **standard Borel subgroup** `borel n k` of
`SL(n,k)` consists of the upper-triangular special linear matrices.  Its characters used by the
Borel–Weil construction are the products of powers of the diagonal entries,
`borelChar μ b = ∏ i, (b i i) ^ μ i`.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.borel` — the upper-triangular subgroup.
* `GaloisForLFunctions.HTGeometry.BorelWeil.borelChar` — the diagonal character attached to a
  weight `μ : n → ℕ`.

## Main results

* `diag_mul_of_blockTriangular` — the diagonal of a product of upper-triangular matrices is the
  product of the diagonals.
* `borelChar_mul`, `borelChar_one` — `borelChar μ` is multiplicative on the Borel subgroup.
-/

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] {k : Type*} [CommRing k]

omit [DecidableEq n] in
/-- The diagonal entries of a product of two upper-triangular matrices multiply. -/
theorem diag_mul_of_blockTriangular {A B : Matrix n n k}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro r _ hr
    rcases lt_or_gt_of_ne hr with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

variable (n k) in
/-- The **standard Borel subgroup** of `SL(n,k)`: the upper-triangular special linear matrices. -/
def borel : Subgroup (SpecialLinearGroup n k) where
  carrier := {b | (b : Matrix n n k).BlockTriangular id}
  mul_mem' hA hB := by
    simpa [SpecialLinearGroup.coe_mul] using Matrix.BlockTriangular.mul hA hB
  one_mem' := by
    simpa [SpecialLinearGroup.coe_one] using
      (Matrix.blockTriangular_one : (1 : Matrix n n k).BlockTriangular id)
  inv_mem' := by
    intro b hb
    have hdet : ((b : Matrix n n k)).det = 1 := b.2
    have hinv : ((b⁻¹ : SpecialLinearGroup n k) : Matrix n n k) = (b : Matrix n n k)⁻¹ := by
      rw [SpecialLinearGroup.coe_inv, Matrix.inv_def, hdet]
      simp
    haveI : Invertible ((b : Matrix n n k)).det := by rw [hdet]; exact invertibleOne
    haveI : Invertible (b : Matrix n n k) := Matrix.invertibleOfDetInvertible _
    rw [Set.mem_setOf_eq, hinv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb

@[simp] theorem mem_borel_iff {b : SpecialLinearGroup n k} :
    b ∈ borel n k ↔ (b : Matrix n n k).BlockTriangular id := Iff.rfl

/-- The diagonal character of the Borel subgroup attached to a weight `μ : n → ℕ`. -/
def borelChar (μ : n → ℕ) (b : SpecialLinearGroup n k) : k :=
  ∏ i, ((b : Matrix n n k) i i) ^ (μ i)

omit [LinearOrder n] in
@[simp] theorem borelChar_one (μ : n → ℕ) : borelChar μ (1 : SpecialLinearGroup n k) = 1 := by
  simp [borelChar, SpecialLinearGroup.coe_one, Matrix.one_apply_eq]

theorem borelChar_mul (μ : n → ℕ) {A B : SpecialLinearGroup n k}
    (hA : A ∈ borel n k) (hB : B ∈ borel n k) :
    borelChar μ (A * B) = borelChar μ A * borelChar μ B := by
  simp only [borelChar, SpecialLinearGroup.coe_mul]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [diag_mul_of_blockTriangular hA hB i, mul_pow]

end GaloisForLFunctions.HTGeometry.BorelWeil
