import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-!
# Characteristic polynomial of a block-diagonal family of `2 × 2` symmetric blocks

The two-local family with a single transverse coupling `u` at site `i` is block-diagonal in the
hypercube pairs `{x, x ⊕ eᵢ}`, each block being the symmetric matrix `!![α, u; u, β]`.  Its
characteristic polynomial is therefore the product over pairs of

  `X² − (α + β) X + (αβ − u²)`,   discriminant `(α − β)² + 4u²`.

This file supplies exactly that: the block-diagonal product rule (which mathlib has for `det` but
not for `charpoly`) and the two-by-two computation.

## Main results

* `charpoly_blockDiagonal` — the characteristic polynomial of a block-diagonal matrix is the
  product of the blocks' characteristic polynomials.
* `charpoly_symmTwo`, `discrim_symmTwo` — the quadratic and its discriminant.
-/

open Polynomial Matrix

namespace GaloisForLFunctions.HTGeometry

/-- **The characteristic polynomial of a block-diagonal matrix is the product over blocks.** -/
theorem charpoly_blockDiagonal {o n R : Type*} [Fintype o] [DecidableEq o] [Fintype n]
    [DecidableEq n] [CommRing R] (M : o → Matrix n n R) :
    (Matrix.blockDiagonal M).charpoly = ∏ k, (M k).charpoly := by
  classical
  have hcm : Matrix.charmatrix (Matrix.blockDiagonal M)
      = Matrix.blockDiagonal fun k => Matrix.charmatrix (M k) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    by_cases hkl : k = l
    · subst hkl
      simp [Matrix.charmatrix, Matrix.blockDiagonal_apply, Matrix.diagonal]
    · simp [Matrix.charmatrix, Matrix.blockDiagonal_apply, hkl, Matrix.diagonal]
  rw [Matrix.charpoly, hcm, Matrix.det_blockDiagonal]
  rfl

/-- The symmetric two-by-two block `!![α, u; u, β]`. -/
def symmTwo {R : Type*} [CommRing R] (α β u : R) : Matrix (Fin 2) (Fin 2) R :=
  !![α, u; u, β]

@[simp] theorem trace_symmTwo {R : Type*} [CommRing R] (α β u : R) :
    (symmTwo α β u).trace = α + β := by
  simp [symmTwo, Matrix.trace_fin_two]

@[simp] theorem det_symmTwo {R : Type*} [CommRing R] (α β u : R) :
    (symmTwo α β u).det = α * β - u * u := by
  simp [symmTwo, Matrix.det_fin_two]

/-- **The block's characteristic polynomial.** -/
theorem charpoly_symmTwo {R : Type*} [CommRing R] [Nontrivial R] (α β u : R) :
    (symmTwo α β u).charpoly = X ^ 2 - C (α + β) * X + C (α * β - u * u) := by
  rw [Matrix.charpoly_fin_two, trace_symmTwo, det_symmTwo]

/-- **The block's discriminant** is `(α − β)² + 4u²`, which for a real symmetric block is a sum of
squares and for a complexified one can vanish. -/
theorem discrim_symmTwo {R : Type*} [CommRing R] (α β u : R) :
    (α + β) * (α + β) - 4 * (α * β - u * u) = (α - β) * (α - β) + 4 * (u * u) := by
  ring

end GaloisForLFunctions.HTGeometry
