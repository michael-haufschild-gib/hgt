import GaloisForLFunctions.HTGeometry.BruhatCellUniqueness

/-!
# Uniqueness of the Bruhat form in the Steinberg group

An element of `St(R)` written in Bruhat form

```text
x_ji(β) · Z · h_ij(w) · x_ij(α)        with `Z ∈ K₂`
```

determines `w`, `αw` and `βw`, because `Z` maps to the identity and the matrix Bruhat parameters are
unique.  Once the parameters are known to agree, the central factors can be cancelled outright.

This converts a word identity in `St(R)` into an identity between central corrections: whenever a
single element is written in Bruhat form in two ways, the two central parts are equal.  It is the
step that turns the Bruhat decomposition into relations among Dennis–Stein symbols.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- The matrix image of a Bruhat word with a central correction. -/
theorem steinbergToGL_bruhat {i j : n} (hij : i ≠ j) (α β : R) (w : Rˣ)
    {Z : SteinbergGroup R n} (hZ : Z ∈ KTwo R n) :
    ((steinbergToGL (steinbergX (Ne.symm hij) β * Z * steinbergTorus hij w
        * steinbergX hij α) : (Matrix n n R)ˣ) : Matrix n n R)
      = Matrix.transvection j i β * diagMatrix i j w * Matrix.transvection i j α := by
  have hZ1 : steinbergToGL Z = 1 := (mem_KTwo_iff _).1 hZ
  rw [map_mul, map_mul, map_mul, hZ1, steinbergToGL_x, steinbergToGL_x, steinbergToGL_torus,
    mul_one]
  rw [Units.val_mul, Units.val_mul, elemUnit_val, elemUnit_val]
  rfl

/-- **The Bruhat parameters of a Steinberg-group element are unique.** -/
theorem bruhat_group_params_unique {i j : n} (hij : i ≠ j) {α β α' β' : R} {w w' : Rˣ}
    {Z Z' : SteinbergGroup R n} (hZ : Z ∈ KTwo R n) (hZ' : Z' ∈ KTwo R n)
    (h : steinbergX (Ne.symm hij) β * Z * steinbergTorus hij w * steinbergX hij α
      = steinbergX (Ne.symm hij) β' * Z' * steinbergTorus hij w' * steinbergX hij α') :
    (w : R) = (w' : R) ∧ α * (w : R) = α' * (w' : R) ∧ β * (w : R) = β' * (w' : R) := by
  have hmat := congrArg (fun g : SteinbergGroup R n =>
    ((steinbergToGL g : (Matrix n n R)ˣ) : Matrix n n R)) h
  rw [steinbergToGL_bruhat hij α β w hZ, steinbergToGL_bruhat hij α' β' w' hZ'] at hmat
  exact bruhat_params_unique hij hmat

omit [DecidableEq n] [Fintype n] in
/-- **Equal Bruhat words with equal parameters have equal central parts.** -/
theorem bruhat_center_unique {i j : n} (hij : i ≠ j) {α β : R} {w : Rˣ}
    {Z Z' : SteinbergGroup R n}
    (h : steinbergX (Ne.symm hij) β * Z * steinbergTorus hij w * steinbergX hij α
      = steinbergX (Ne.symm hij) β * Z' * steinbergTorus hij w * steinbergX hij α) :
    Z = Z' := by
  have h1 := mul_right_cancel h
  have h2 := mul_right_cancel h1
  exact mul_left_cancel h2

end GaloisForLFunctions.HTGeometry

end
