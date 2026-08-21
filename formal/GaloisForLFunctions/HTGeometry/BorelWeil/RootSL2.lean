/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.BorelWeil.BlockAlgebra
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The root `SL₂` inside `SL(n,k)` and its Bruhat identity

Fix a pair of indices `i ≠ j`.  The transvections `rootU c = 1 + c E_{ij}` and
`rootL c = 1 + c E_{ji}` generate a copy of `SL₂` inside `SL(n,k)`.  This file records the
elements needed for the rank-one analysis of the Borel–Weil sections and the single Bruhat
identity they satisfy:

`rootU (-t) * rootWinv * rootBeta t = rootL (-t⁻¹)`  for `t ≠ 0`,

where `rootBeta t` is upper triangular with diagonal `(t⁻¹, t)` in the `(i,j)` block.  Written in
the block `SL₂`, this is the Bruhat decomposition
`[[1,0],[-t⁻¹,1]] = [[1,-t],[0,1]] · [[0,1],[-1,0]] · [[t⁻¹,-1],[0,t]]`.

## Main definitions

* `slTrans`, `rootU`, `rootL`, `rootWinv`, `rootH`, `rootBeta`.

## Main results

* `rootBruhat` — the Bruhat identity above.
* `coe_rootBeta` — the explicit block form of `rootBeta`.
-/

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]

omit [Fintype n] in
theorem blk_congr {i j : n} {a b c d a' b' c' d' : k}
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') :
    blk i j a b c d = blk i j a' b' c' d' := by rw [ha, hb, hc, hd]

/-- The elementary transvection `1 + c E_{ij}` as an element of `SL(n,k)`. -/
def slTrans (i j : n) (hij : i ≠ j) (c : k) : SpecialLinearGroup n k :=
  ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j hij c⟩

@[simp] theorem coe_slTrans (i j : n) (hij : i ≠ j) (c : k) :
    (slTrans i j hij c : Matrix n n k) = Matrix.transvection i j c := rfl

variable (i j : n) (hij : i ≠ j)

/-- The upper root element `1 + c E_{ij}`. -/
def rootU (c : k) : SpecialLinearGroup n k := slTrans i j hij c

/-- The lower root element `1 + c E_{ji}`. -/
def rootL (c : k) : SpecialLinearGroup n k := slTrans j i (Ne.symm hij) c

theorem coe_rootU (c : k) : (rootU i j hij c : Matrix n n k) = blk i j 0 c 0 0 := by
  simp [rootU, Matrix.transvection, blk, blkAux]

theorem coe_rootL (c : k) : (rootL i j hij c : Matrix n n k) = blk i j 0 0 c 0 := by
  simp [rootL, Matrix.transvection, blk, blkAux]

@[simp] theorem rootL_zero : rootL i j hij (0 : k) = 1 := by
  apply Subtype.ext
  simp [rootL, Matrix.transvection]

/-- The inverse Weyl element of the root `SL₂`, written as a product of transvections. -/
def rootWinv : SpecialLinearGroup n k :=
  rootL i j hij (-1) * rootU i j hij 1 * rootL i j hij (-1)

theorem coe_rootWinv :
    ((rootWinv i j hij : SpecialLinearGroup n k) : Matrix n n k)
      = blk i j (-1) 1 (-1) (-1) := by
  rw [rootWinv]
  simp only [SpecialLinearGroup.coe_mul, coe_rootU, coe_rootL]
  rw [blk_mul hij, blk_mul hij]
  exact blk_congr (by ring) (by ring) (by ring) (by ring)

/-- The torus element of the root `SL₂` with diagonal `(a, a⁻¹)`, written as a product of
transvections. -/
def rootH (a : k) : SpecialLinearGroup n k :=
  rootU i j hij (-a) * rootL i j hij a⁻¹ * rootU i j hij (-a) * rootWinv i j hij

theorem coe_rootH {a : k} (ha : a ≠ 0) :
    (rootH i j hij a : Matrix n n k) = blk i j (a - 1) 0 0 (a⁻¹ - 1) := by
  rw [rootH]
  simp only [SpecialLinearGroup.coe_mul, coe_rootU, coe_rootL, coe_rootWinv]
  rw [blk_mul hij, blk_mul hij, blk_mul hij]
  refine blk_congr ?_ ?_ ?_ ?_ <;> field_simp <;> ring

/-- The upper-triangular Bruhat factor with diagonal `(t⁻¹, t)`. -/
def rootBeta (t : k) : SpecialLinearGroup n k :=
  rootH i j hij t⁻¹ * rootU i j hij (-t)

theorem coe_rootBeta {t : k} (ht : t ≠ 0) :
    (rootBeta i j hij t : Matrix n n k) = blk i j (t⁻¹ - 1) (-1) 0 (t - 1) := by
  rw [rootBeta]
  simp only [SpecialLinearGroup.coe_mul, coe_rootU, coe_rootH i j hij (inv_ne_zero ht)]
  rw [blk_mul hij]
  refine blk_congr ?_ ?_ ?_ ?_ <;> field_simp <;> ring

/-- **The Bruhat identity of the root `SL₂`.** -/
theorem rootBruhat {t : k} (ht : t ≠ 0) :
    rootU i j hij (-t) * rootWinv i j hij * rootBeta i j hij t = rootL i j hij (-t⁻¹) := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, coe_rootU, coe_rootWinv, coe_rootBeta i j hij ht,
    coe_rootL]
  rw [blk_mul hij, blk_mul hij]
  refine blk_congr ?_ ?_ ?_ ?_ <;> field_simp <;> ring

end GaloisForLFunctions.HTGeometry.BorelWeil
