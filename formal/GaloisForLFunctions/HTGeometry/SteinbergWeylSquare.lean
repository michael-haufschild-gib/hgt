import GaloisForLFunctions.HTGeometry.SteinbergSymbolCocycle
import Mathlib.Tactic.LinearCombination

/-!
# The square of the Weyl element, modulo `K₂`

In the two-index block the Weyl matrix is `[[0,u],[−u⁻¹,0]]`, whose square is `−1`.  So

```text
weylMatrix i j u * weylMatrix i j u = diagMatrix i j (−1) ,
```

with no dependence on `u` at all: the unit cancels between the two off-diagonal entries.  Lifting to
the Steinberg group, `w_ij(u)² h_ij(−1)⁻¹` maps to the identity, hence lies in `K₂`, and its word
uses only the two indices `i` and `j`, hence it is central.

This is the `K₂`-level form of the classical relation `w(u)² = h(−1)`.  The relation itself is a
consequence of the presentation; what follows from the matrix map alone is that the two sides agree
up to a central element of `K₂`, and that is already enough wherever the argument works modulo the
centre.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- **The Weyl matrix squares to the diagonal matrix at `−1`**, independently of the unit. -/
theorem weylMatrix_sq {i j : n} (hij : i ≠ j) (u : Rˣ) :
    weylMatrix i j u * weylMatrix i j u = diagMatrix i j (-1 : Rˣ) := by
  have hji : j ≠ i := Ne.symm hij
  set X : Matrix n n R := Matrix.single i j 1 with hXdef
  set Y : Matrix n n R := Matrix.single j i 1 with hYdef
  set Z : Matrix n n R := Matrix.single i i 1 with hZdef
  set W : Matrix n n R := Matrix.single j j 1 with hWdef
  have hXX : X * X = 0 := by rw [hXdef]; simp [hji]
  have hXY : X * Y = Z := by rw [hXdef, hYdef, hZdef]; simp
  have hXZ : X * Z = 0 := by rw [hXdef, hZdef]; simp [hji]
  have hXW : X * W = X := by rw [hXdef, hWdef]; simp
  have hYX : Y * X = W := by rw [hXdef, hYdef, hWdef]; simp
  have hYY : Y * Y = 0 := by rw [hYdef]; simp [hij]
  have hYZ : Y * Z = Y := by rw [hYdef, hZdef]; simp
  have hYW : Y * W = 0 := by rw [hYdef, hWdef]; simp [hij]
  have hZX : Z * X = X := by rw [hXdef, hZdef]; simp
  have hZY : Z * Y = 0 := by rw [hYdef, hZdef]; simp [hij]
  have hZZ : Z * Z = Z := by rw [hZdef]; simp
  have hZW : Z * W = 0 := by rw [hZdef, hWdef]; simp [hij]
  have hWX : W * X = 0 := by rw [hXdef, hWdef]; simp [hji]
  have hWY : W * Y = Y := by rw [hYdef, hWdef]; simp
  have hWZ : W * Z = 0 := by rw [hZdef, hWdef]; simp [hji]
  have hWW : W * W = W := by rw [hWdef]; simp
  rw [weylMatrix, diagMatrix]
  rw [single_eq_smul i j (u : R), single_eq_smul j i (-((u⁻¹ : Rˣ) : R)),
    single_eq_smul i i (-1 : R), single_eq_smul j j (-1 : R),
    single_eq_smul i i (((-1 : Rˣ) : R) - 1), single_eq_smul j j ((((-1 : Rˣ)⁻¹ : Rˣ) : R) - 1)]
  rw [← hXdef, ← hYdef, ← hZdef, ← hWdef]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, hXX, hXY, hXZ, hXW, hYX, hYY, hYZ, hYW,
    hZX, hZY, hZZ, hZW, hWX, hWY, hWZ, hWW, smul_zero]
  have hu : (u : R) * (((u⁻¹ : Rˣ)) : R) = 1 := u.mul_inv
  have hinv : (((-1 : Rˣ)⁻¹ : Rˣ) : R) = -1 := by norm_num
  have hneg : (((-1 : Rˣ)) : R) = -1 := by norm_num
  rw [hinv, hneg]
  match_scalars
  · ring
  · ring
  · ring
  · linear_combination -hu
  · linear_combination -hu

/-- **The image of the squared Weyl element is the diagonal unit at `−1`.** -/
theorem steinbergToGL_weyl_sq {i j : n} (hij : i ≠ j) (u : Rˣ) :
    steinbergToGL (steinbergWeyl hij u * steinbergWeyl hij u) = diagUnit hij (-1 : Rˣ) := by
  refine Units.ext ?_
  rw [map_mul, Units.val_mul, steinbergToGL_weyl]
  exact weylMatrix_sq hij u

/-- **The failure of `w(u)² = h(−1)` lies in `K₂`.** -/
theorem steinbergWeyl_sq_mul_torus_inv_mem_KTwo {i j : n} (hij : i ≠ j) (u : Rˣ) :
    steinbergWeyl hij u * steinbergWeyl hij u * (steinbergTorus hij (-1 : Rˣ))⁻¹
      ∈ KTwo R n := by
  rw [mem_KTwo_iff, map_mul, map_inv, steinbergToGL_weyl_sq, steinbergToGL_torus,
    mul_inv_cancel]

omit [Fintype n] in
/-- The word uses only the two indices. -/
theorem steinbergWeyl_sq_mul_torus_inv_mem_indexClosure {i j : n} (hij : i ≠ j) (u : Rˣ) :
    steinbergWeyl hij u * steinbergWeyl hij u * (steinbergTorus hij (-1 : Rˣ))⁻¹
      ∈ Subgroup.closure (indexGens (R := R) (n := n) {i, j}) :=
  Subgroup.mul_mem _
    (Subgroup.mul_mem _ (steinbergWeyl_mem_indexClosure hij u)
      (steinbergWeyl_mem_indexClosure hij u))
    (Subgroup.inv_mem _ (steinbergTorus_mem_indexClosure hij (-1 : Rˣ)))

/-- **`w(u)²` and `h(−1)` agree up to a central element of `K₂`**, as soon as a third index is
available. -/
theorem steinbergWeyl_sq_mul_torus_inv_mem_center {i j : n} (hij : i ≠ j) (u : Rˣ)
    {h : n} (hhi : h ≠ i) (hhj : h ≠ j) :
    steinbergWeyl hij u * steinbergWeyl hij u * (steinbergTorus hij (-1 : Rˣ))⁻¹
      ∈ Subgroup.center (SteinbergGroup R n) := by
  refine KTwo_mem_center (h := h) (steinbergWeyl_sq_mul_torus_inv_mem_KTwo hij u)
    (steinbergWeyl_sq_mul_torus_inv_mem_indexClosure hij u) ?_
  simp [hhi, hhj]

/-- The square of the Weyl element does not depend on the unit, modulo `K₂`. -/
theorem steinbergWeyl_sq_mul_sq_inv_mem_KTwo {i j : n} (hij : i ≠ j) (u v : Rˣ) :
    steinbergWeyl hij u * steinbergWeyl hij u
        * (steinbergWeyl hij v * steinbergWeyl hij v)⁻¹ ∈ KTwo R n := by
  rw [mem_KTwo_iff, map_mul, map_inv, steinbergToGL_weyl_sq, steinbergToGL_weyl_sq,
    mul_inv_cancel]

end GaloisForLFunctions.HTGeometry

end
