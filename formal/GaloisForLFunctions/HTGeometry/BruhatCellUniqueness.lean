import GaloisForLFunctions.HTGeometry.DennisSteinBruhat

/-!
# The Bruhat cell parameters are unique

In the two-index block the Bruhat product is

```text
⎡ 1  0 ⎤ ⎡ w  0   ⎤ ⎡ 1  α ⎤     ⎡ w      α w        ⎤
⎣ β  1 ⎦ ⎣ 0  w⁻¹ ⎦ ⎣ 0  1 ⎦  =  ⎣ β w    w⁻¹ + αβw  ⎦ ,
```

so the three parameters are read off the matrix directly: `w` from the `(i,i)` entry, then `α` and
`β` from the two off-diagonal ones.  Distinct parameters therefore give distinct matrices.

Combined with the Bruhat decomposition of the Steinberg group, this pins the Dennis–Stein symbol:
two ways of writing the same element in Bruhat form must agree in all three parameters, so their
central corrections agree as well.  That is the mechanism by which word identities in `St(R)` become
identities between symbols.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- **The Bruhat product in closed form.** -/
theorem bruhatMatrix_eq {i j : n} (hij : i ≠ j) (α β : R) (w : Rˣ) :
    (Matrix.transvection j i β * diagMatrix i j w * Matrix.transvection i j α)
      = 1 + Matrix.single i i ((w : R) - 1)
        + Matrix.single j j ((((w⁻¹ : Rˣ)) : R) - 1 + α * β * (w : R))
        + Matrix.single i j (α * (w : R)) + Matrix.single j i (β * (w : R)) := by
  have hji : j ≠ i := Ne.symm hij
  have hXY : (Matrix.single i j (1 : R) : Matrix n n R) * Matrix.single j i 1
      = Matrix.single i i 1 := by simp
  have hYX : (Matrix.single j i (1 : R) : Matrix n n R) * Matrix.single i j 1
      = Matrix.single j j 1 := by simp
  have hYZ : (Matrix.single j i (1 : R) : Matrix n n R) * Matrix.single i i 1
      = Matrix.single j i 1 := by simp
  have hYW : (Matrix.single j i (1 : R) : Matrix n n R) * Matrix.single j j 1 = 0 := by
    simp [hij]
  have hZX : (Matrix.single i i (1 : R) : Matrix n n R) * Matrix.single i j 1
      = Matrix.single i j 1 := by simp
  have hWX : (Matrix.single j j (1 : R) : Matrix n n R) * Matrix.single i j 1 = 0 := by
    simp [hji]
  have hZZ : (Matrix.single i i (1 : R) : Matrix n n R) * Matrix.single i i 1
      = Matrix.single i i 1 := by simp
  have hWW : (Matrix.single j j (1 : R) : Matrix n n R) * Matrix.single j j 1
      = Matrix.single j j 1 := by simp
  have hXW : (Matrix.single i j (1 : R) : Matrix n n R) * Matrix.single j j 1
      = Matrix.single i j 1 := by simp
  have hWY : (Matrix.single j j (1 : R) : Matrix n n R) * Matrix.single j i 1
      = Matrix.single j i 1 := by simp
  simp only [Matrix.transvection, diagMatrix]
  rw [single_eq_smul j i β, single_eq_smul i j α,
    single_eq_smul i i ((w : R) - 1), single_eq_smul j j ((((w⁻¹ : Rˣ)) : R) - 1),
    single_eq_smul j j ((((w⁻¹ : Rˣ)) : R) - 1 + α * β * (w : R)),
    single_eq_smul i j (α * (w : R)), single_eq_smul j i (β * (w : R))]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, hYX, hYZ, hYW, hZX, hWX, smul_zero, add_zero]
  match_scalars <;> ring

/-- **The Bruhat parameters are determined by the matrix.** -/
theorem bruhat_params_unique {i j : n} (hij : i ≠ j) {α β α' β' : R} {w w' : Rˣ}
    (h : (Matrix.transvection j i β * diagMatrix i j w * Matrix.transvection i j α)
      = Matrix.transvection j i β' * diagMatrix i j w' * Matrix.transvection i j α') :
    (w : R) = (w' : R) ∧ α * (w : R) = α' * (w' : R) ∧ β * (w : R) = β' * (w' : R) := by
  have hji : j ≠ i := Ne.symm hij
  rw [bruhatMatrix_eq hij, bruhatMatrix_eq hij] at h
  refine ⟨?_, ?_, ?_⟩
  · have hii := congrFun (congrFun h i) i
    simpa [Matrix.single_apply, Matrix.one_apply, hij, hji] using hii
  · have hij' := congrFun (congrFun h i) j
    simpa [Matrix.single_apply, Matrix.one_apply, hij, hji] using hij'
  · have hji' := congrFun (congrFun h j) i
    simpa [Matrix.single_apply, Matrix.one_apply, hij, hji] using hji'

end GaloisForLFunctions.HTGeometry

end
