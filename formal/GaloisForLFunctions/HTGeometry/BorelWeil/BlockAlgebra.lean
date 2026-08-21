/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The `2 × 2` block subalgebra attached to a pair of indices

Every matrix used in the rank-one (root `SL₂`) analysis of the Borel–Weil sections is of the form
`1 + a E_{ii} + b E_{ij} + c E_{ji} + d E_{jj}` for a fixed pair `i ≠ j`.  These matrices are
closed under multiplication, and the multiplication rule is exactly `2 × 2` matrix multiplication
on `!![1 + a, b; c, 1 + d]`.  Recording this once turns every root-`SL₂` identity in `SL(n,k)` into
scalar algebra.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.blkAux`
* `GaloisForLFunctions.HTGeometry.BorelWeil.blk`

## Main results

* `blk_mul` — the multiplication rule.
* `blk_diag_self`, `blk_diag_other` — the diagonal entries.
* `blk_blockTriangular` — upper triangularity when the lower entry vanishes and `i < j`.
-/

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [CommRing k]

omit [Fintype n] in
theorem single_mul_single' [Fintype n] (p q r s : n) (x y : k) :
    (Matrix.single p q x : Matrix n n k) * Matrix.single r s y
      = if q = r then Matrix.single p s (x * y) else 0 := by
  by_cases h : q = r
  · subst h; simp
  · simp [h]

/-- The `2 × 2` block perturbation `a E_{ii} + b E_{ij} + c E_{ji} + d E_{jj}`. -/
def blkAux (i j : n) (a b c d : k) : Matrix n n k :=
  Matrix.single i i a + Matrix.single i j b + Matrix.single j i c + Matrix.single j j d

omit [Fintype n] in
theorem blkAux_congr {i j : n} {a b c d a' b' c' d' : k}
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') :
    blkAux i j a b c d = blkAux i j a' b' c' d' := by rw [ha, hb, hc, hd]

omit [Fintype n] in
theorem blkAux_add (i j : n) (a b c d a' b' c' d' : k) :
    blkAux i j a b c d + blkAux i j a' b' c' d'
      = blkAux i j (a + a') (b + b') (c + c') (d + d') := by
  simp only [blkAux, Matrix.single_add]
  abel

theorem blkAux_mul {i j : n} (hij : i ≠ j) (a b c d a' b' c' d' : k) :
    blkAux i j a b c d * blkAux i j a' b' c' d'
      = blkAux i j (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blkAux, add_mul, mul_add, single_mul_single', if_neg hij, if_neg (Ne.symm hij),
    add_zero, zero_add, Matrix.single_add]
  ac_rfl

/-- The matrix `1 + a E_{ii} + b E_{ij} + c E_{ji} + d E_{jj}`, i.e. the block `!![1+a, b; c, 1+d]`
placed at the index pair `(i, j)` inside the identity matrix. -/
def blk (i j : n) (a b c d : k) : Matrix n n k := 1 + blkAux i j a b c d

omit [Fintype n] in
@[simp] theorem blk_zero (i j : n) : blk i j (0 : k) 0 0 0 = 1 := by
  simp [blk, blkAux]

/-- **The block multiplication rule.** -/
theorem blk_mul {i j : n} (hij : i ≠ j) (a b c d a' b' c' d' : k) :
    blk i j a b c d * blk i j a' b' c' d'
      = blk i j (a + a' + (a * a' + b * c')) (b + b' + (a * b' + b * d'))
          (c + c' + (c * a' + d * c')) (d + d' + (c * b' + d * d')) := by
  have key : blk i j a b c d * blk i j a' b' c' d'
      = 1 + (blkAux i j a b c d + (blkAux i j a' b' c' d'
          + blkAux i j (a * a' + b * c') (a * b' + b * d') (c * a' + d * c')
              (c * b' + d * d'))) := by
    simp only [blk, add_mul, mul_add, one_mul, mul_one, blkAux_mul hij]
    ac_rfl
  rw [key, blkAux_add, blkAux_add, blk]
  exact congrArg (HAdd.hAdd 1) (blkAux_congr (by ring) (by ring) (by ring) (by ring))

omit [Fintype n] in
theorem transvection_eq_blk (i j : n) (c : k) :
    Matrix.transvection i j c = blk i j 0 c 0 0 := by
  simp [Matrix.transvection, blk, blkAux]

omit [Fintype n] in
theorem blkAux_apply (i j : n) (a b c d : k) (r s : n) :
    blkAux i j a b c d r s =
      (if i = r ∧ i = s then a else 0) + (if i = r ∧ j = s then b else 0)
        + (if j = r ∧ i = s then c else 0) + (if j = r ∧ j = s then d else 0) := by
  simp [blkAux, Matrix.single, Matrix.of_apply]

omit [Fintype n] in
theorem blk_diag_left {i j : n} (hij : i ≠ j) (a b c d : k) :
    blk i j a b c d i i = 1 + a := by
  simp [blk, blkAux_apply, Ne.symm hij]

omit [Fintype n] in
theorem blk_diag_right {i j : n} (hij : i ≠ j) (a b c d : k) :
    blk i j a b c d j j = 1 + d := by
  simp [blk, blkAux_apply, hij]

omit [Fintype n] in
theorem blk_diag_other {i j : n} (a b c d : k) {r : n} (hri : r ≠ i) (hrj : r ≠ j) :
    blk i j a b c d r r = 1 := by
  simp [blk, blkAux_apply, Ne.symm hri, Ne.symm hrj]

omit [Fintype n] in
/-- A block matrix with vanishing lower entry, at an increasing index pair, is upper
triangular. -/
theorem blk_blockTriangular [LinearOrder n] {i j : n} (hij : i < j) (a b d : k) :
    (blk i j a b 0 d).BlockTriangular id := by
  intro r s hrs
  have hne : r ≠ s := by
    rintro rfl
    exact absurd hrs (lt_irrefl _)
  have h1 : ¬ (i = r ∧ i = s) := fun h => hne (h.1.symm.trans h.2)
  have h2 : ¬ (i = r ∧ j = s) := by
    rintro ⟨rfl, rfl⟩
    exact absurd hrs (not_lt.mpr hij.le)
  have h3 : ¬ (j = r ∧ j = s) := fun h => hne (h.1.symm.trans h.2)
  simp only [blk, Matrix.add_apply, blkAux_apply, Matrix.one_apply_ne hne, if_neg h1, if_neg h2,
    if_neg h3, ite_self, add_zero]

end GaloisForLFunctions.HTGeometry.BorelWeil
