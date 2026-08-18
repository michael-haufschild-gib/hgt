import GaloisForLFunctions.HTGeometry.SteinbergWeylConjugation

/-!
# Rank-three factorisation of Weyl elements

The Weyl element for the root `(i,j)` has an exact factorisation through any third
index `k`:

```text
w_ij(u) = w_ik(u) w_kj(1) w_ik(-u).
```

This is an equality in the presented Steinberg group, not only after applying the
elementary-matrix map.  It is the rank-three word relation needed to reduce
two-index Weyl calculations, including the Steinberg relation, to the defining
root relations.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

omit [DecidableEq n] [Fintype n] in
/-- **Exact rank-three factorisation with arbitrary unit parameters.** -/
theorem steinbergWeyl_triangle_mul {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u v : Rˣ) :
    steinbergWeyl hik u * steinbergWeyl (Ne.symm hjk) v * steinbergWeyl hik (-u)
      = steinbergWeyl hij (u * v) := by
  have hrow := steinbergWeyl_conj_row hik hij (Ne.symm hjk) u ((v : Rˣ) : R)
  have hsecond := steinbergWeyl_conj_second hik hij (Ne.symm hjk) u
    (-(((v⁻¹ : Rˣ)) : R))
  have hWv : steinbergWeyl (Ne.symm hjk) v
      = steinbergX (Ne.symm hjk) ((v : Rˣ) : R)
        * steinbergX hjk (-(((v⁻¹ : Rˣ)) : R))
        * steinbergX (Ne.symm hjk) ((v : Rˣ) : R) := by
    rw [steinbergWeyl]
  rw [steinbergWeyl_neg hik u]
  calc steinbergWeyl hik u * steinbergWeyl (Ne.symm hjk) v * (steinbergWeyl hik u)⁻¹
      = (steinbergWeyl hik u * steinbergX (Ne.symm hjk) ((v : Rˣ) : R)
          * (steinbergWeyl hik u)⁻¹)
        * (steinbergWeyl hik u * steinbergX hjk (-(((v⁻¹ : Rˣ)) : R))
          * (steinbergWeyl hik u)⁻¹)
        * (steinbergWeyl hik u * steinbergX (Ne.symm hjk) ((v : Rˣ) : R)
          * (steinbergWeyl hik u)⁻¹) := by
        rw [hWv]
        group
    _ = steinbergX hij (((u : Rˣ) : R) * ((v : Rˣ) : R))
        * steinbergX (Ne.symm hij) (-(((v⁻¹ : Rˣ)) : R) * (((u⁻¹ : Rˣ)) : R))
        * steinbergX hij (((u : Rˣ) : R) * ((v : Rˣ) : R)) := by
        rw [hrow, hsecond]
    _ = steinbergWeyl hij (u * v) := by
        simp [steinbergWeyl]

omit [DecidableEq n] [Fintype n] in
/-- **Exact rank-three factorisation of a Weyl element.** -/
theorem steinbergWeyl_triangle {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) :
    steinbergWeyl hik u * steinbergWeyl (Ne.symm hjk) 1 * steinbergWeyl hik (-u)
      = steinbergWeyl hij u := by
  simpa using steinbergWeyl_triangle_mul hij hik hjk u (1 : Rˣ)

omit [DecidableEq n] [Fintype n] in
/-- **Exchange form of the rank-three Weyl factorisation.** -/
theorem steinbergWeyl_triangle_exchange {i j k : n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (u : Rˣ) :
    steinbergWeyl hij u * steinbergWeyl hik u
      = steinbergWeyl hik u * steinbergWeyl (Ne.symm hjk) 1 := by
  rw [← steinbergWeyl_triangle hij hik hjk u, steinbergWeyl_neg hik u]
  group

end GaloisForLFunctions.HTGeometry

end
