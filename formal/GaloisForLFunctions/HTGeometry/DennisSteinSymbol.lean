import GaloisForLFunctions.HTGeometry.SteinbergSymbolCocycle
import Mathlib.Tactic.LinearCombination

/-!
# The Dennis–Stein symbol

For `a b : R` with `1 + ab` a unit, the element

```text
⟨a,b⟩ = x_ji(−b(1+ab)⁻¹) · x_ij(a) · x_ji(b) · x_ij(−(1+ab)⁻¹a) · h_ij(1+ab)⁻¹
```

of the Steinberg group lies in `K₂`.  The four elementary factors multiply, in the two-index block,
to the diagonal matrix `diag(1+ab, (1+ab)⁻¹)`:

```text
⎡ 1      0 ⎤ ⎡ 1  a ⎤ ⎡ 1  0 ⎤ ⎡ 1  −a/w ⎤     ⎡ w  0   ⎤
⎣ −b/w   1 ⎦ ⎣ 0  1 ⎦ ⎣ b  1 ⎦ ⎣ 0   1   ⎦  =  ⎣ 0  1/w ⎦ ,    w = 1 + ab,
```

which is exactly the image of `h_ij(w)`, so the whole product maps to the identity.  Unlike the
Steinberg symbol `{u,v}`, which is built only from units, the Dennis–Stein symbol has an argument in
`R` itself, and its defining relations mix the additive and multiplicative structure of the ring.
That is what makes it — and not the Weyl or torus conjugation calculus — the route to the Steinberg
relation `{u, 1−u} = 1`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- **The four elementary factors of the Dennis–Stein symbol multiply to the diagonal matrix.** -/
theorem transvection_dennisStein {i j : n} (hij : i ≠ j) (a b : R) (w : Rˣ)
    (hw : (w : R) = 1 + a * b) :
    Matrix.transvection j i (-(b * (((w⁻¹ : Rˣ)) : R))) * Matrix.transvection i j a
        * Matrix.transvection j i b
        * Matrix.transvection i j (-((((w⁻¹ : Rˣ)) : R) * a))
      = diagMatrix i j w := by
  have hji : j ≠ i := Ne.symm hij
  have hcw : (((w⁻¹ : Rˣ)) : R) * (1 + a * b) = 1 := by
    rw [← hw]; exact w.inv_mul
  have hXX : (Matrix.single i j (1 : R) : Matrix n n R) * Matrix.single i j 1 = 0 := by simp [hji]
  have hXY : (Matrix.single i j (1 : R) : Matrix n n R) * Matrix.single j i 1
      = Matrix.single i i 1 := by simp
  have hYX : (Matrix.single j i (1 : R) : Matrix n n R) * Matrix.single i j 1
      = Matrix.single j j 1 := by simp
  have hYY : (Matrix.single j i (1 : R) : Matrix n n R) * Matrix.single j i 1 = 0 := by simp [hij]
  have hZX : (Matrix.single i i (1 : R) : Matrix n n R) * Matrix.single i j 1
      = Matrix.single i j 1 := by simp
  have hWX : (Matrix.single j j (1 : R) : Matrix n n R) * Matrix.single i j 1 = 0 := by simp [hji]
  have hWY : (Matrix.single j j (1 : R) : Matrix n n R) * Matrix.single j i 1
      = Matrix.single j i 1 := by simp
  rw [diagMatrix]
  simp only [Matrix.transvection]
  rw [single_eq_smul j i (-(b * (((w⁻¹ : Rˣ)) : R))), single_eq_smul i j a,
    single_eq_smul j i b, single_eq_smul i j (-((((w⁻¹ : Rˣ)) : R) * a)),
    single_eq_smul i i ((w : R) - 1), single_eq_smul j j ((((w⁻¹ : Rˣ)) : R) - 1)]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, hXX, hXY, hYX, hYY, hZX, hWX, hWY,
    smul_zero, add_zero]
  match_scalars
  · ring
  · linear_combination (-b) * hcw
  · linear_combination (-a) * hcw
  · linear_combination (a * b * (((w⁻¹ : Rˣ)) : R) - 1) * hcw
  · linear_combination (-1 : R) * hw

/-- **The Dennis–Stein symbol.**  Defined for `a b : R` and a unit `w` with `w = 1 + ab`. -/
def dennisStein {i j : n} (hij : i ≠ j) (a b : R) (w : Rˣ) : SteinbergGroup R n :=
  steinbergX (Ne.symm hij) (-(b * (((w⁻¹ : Rˣ)) : R)))
    * steinbergX hij a
    * steinbergX (Ne.symm hij) b
    * steinbergX hij (-((((w⁻¹ : Rˣ)) : R) * a))
    * (steinbergTorus hij w)⁻¹

/-- **The Dennis–Stein symbol lies in `K₂`.** -/
theorem dennisStein_mem_KTwo {i j : n} (hij : i ≠ j) (a b : R) (w : Rˣ)
    (hw : (w : R) = 1 + a * b) : dennisStein hij a b w ∈ KTwo R n := by
  have hmat : (steinbergToGL (steinbergX (Ne.symm hij) (-(b * (((w⁻¹ : Rˣ)) : R))))
      * steinbergToGL (steinbergX hij a) * steinbergToGL (steinbergX (Ne.symm hij) b)
      * steinbergToGL (steinbergX hij (-((((w⁻¹ : Rˣ)) : R) * a))) : (Matrix n n R)ˣ)
      = diagUnit hij w := by
    rw [steinbergToGL_x, steinbergToGL_x, steinbergToGL_x, steinbergToGL_x]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, Units.val_mul, elemUnit_val, elemUnit_val,
      elemUnit_val, elemUnit_val]
    exact transvection_dennisStein hij a b w hw
  rw [mem_KTwo_iff, dennisStein, map_mul, map_mul, map_mul, map_mul, map_inv,
    steinbergToGL_torus, hmat, mul_inv_cancel]

omit [Fintype n] in
/-- The Dennis–Stein symbol is a word in the two indices `i` and `j`. -/
theorem dennisStein_mem_indexClosure {i j : n} (hij : i ≠ j) (a b : R) (w : Rˣ) :
    dennisStein hij a b w ∈ Subgroup.closure (indexGens (R := R) (n := n) {i, j}) := by
  rw [dennisStein]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_)
    ?_) (Subgroup.inv_mem _ (steinbergTorus_mem_indexClosure hij w))
  · exact Subgroup.subset_closure ⟨j, i, Ne.symm hij, by simp, by simp, _, rfl⟩
  · exact Subgroup.subset_closure ⟨i, j, hij, by simp, by simp, _, rfl⟩
  · exact Subgroup.subset_closure ⟨j, i, Ne.symm hij, by simp, by simp, _, rfl⟩
  · exact Subgroup.subset_closure ⟨i, j, hij, by simp, by simp, _, rfl⟩

/-- **The Dennis–Stein symbol is central**, as soon as a third index is available. -/
theorem dennisStein_mem_center {i j : n} (hij : i ≠ j) (a b : R) (w : Rˣ)
    (hw : (w : R) = 1 + a * b) {h : n} (hhi : h ≠ i) (hhj : h ≠ j) :
    dennisStein hij a b w ∈ Subgroup.center (SteinbergGroup R n) := by
  refine KTwo_mem_center (h := h) (dennisStein_mem_KTwo hij a b w hw)
    (dennisStein_mem_indexClosure hij a b w) ?_
  simp [hhi, hhj]

omit [DecidableEq n] [Fintype n] in
/-- With `b = 0` the symbol degenerates: `⟨a,0⟩ = 1`. -/
theorem dennisStein_right_zero {i j : n} (hij : i ≠ j) (a : R) :
    dennisStein hij a 0 (1 : Rˣ) = 1 := by
  rw [dennisStein, steinbergTorus_one]
  simp only [inv_one, Units.val_one, mul_one, one_mul, neg_zero, steinbergX_zero]
  rw [steinbergX_mul, add_neg_cancel, steinbergX_zero]

omit [DecidableEq n] [Fintype n] in
/-- With `a = 0` the symbol degenerates: `⟨0,b⟩ = 1`. -/
theorem dennisStein_left_zero {i j : n} (hij : i ≠ j) (b : R) :
    dennisStein hij 0 b (1 : Rˣ) = 1 := by
  rw [dennisStein, steinbergTorus_one]
  simp only [inv_one, Units.val_one, mul_one, mul_zero, neg_zero, steinbergX_zero]
  rw [steinbergX_mul, neg_add_cancel, steinbergX_zero]

end GaloisForLFunctions.HTGeometry

end
