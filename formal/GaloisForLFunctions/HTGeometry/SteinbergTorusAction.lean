import GaloisForLFunctions.HTGeometry.SteinbergWeylConjugation

/-!
# The torus acts by the diagonal character

The torus element `h(u) = w(u) w(−1)` conjugates the generators the way the diagonal matrix
`diag(u, u⁻¹)` does:

```text
h(u) x_ij(a) h(u)⁻¹ = x_ij(u a u) ,
h(u) x_ik(a) h(u)⁻¹ = x_ik(u a) ,
h(u) x_ki(d) h(u)⁻¹ = x_ki(d u⁻¹) .
```

Each is the composition of two Weyl moves.  The inner one is at the unit `−1`, where the formulas
degenerate — `(−1)⁻¹ = −1`, so the two signs cancel and `w(−1)` acts by a bare transposition of the
indices — and the outer one at `u` reinstates the unit.  Everything comes from the three Steinberg
relations, with no appeal to matrices.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n]

omit [DecidableEq n] in
/-- The Weyl element at `−1` is a bare transposition on the diagonal generators. -/
theorem steinbergWeyl_neg_one_conj_self {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a : R) :
    steinbergWeyl hij (-1 : Rˣ) * steinbergX hij a * (steinbergWeyl hij (-1 : Rˣ))⁻¹
      = steinbergX (Ne.symm hij) (-a) := by
  have h := steinbergWeyl_conj_self hij hik hjk (-1 : Rˣ) a
  have hval : -((((-1 : Rˣ)⁻¹ : Rˣ)) : R) * a * ((((-1 : Rˣ)⁻¹ : Rˣ)) : R) = -a := by
    simp
  rwa [hval] at h

omit [DecidableEq n] in
/-- The Weyl element at `−1` transposes a row generator without a unit. -/
theorem steinbergWeyl_neg_one_conj_first {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a : R) :
    steinbergWeyl hij (-1 : Rˣ) * steinbergX hik a * (steinbergWeyl hij (-1 : Rˣ))⁻¹
      = steinbergX hjk a := by
  have h := steinbergWeyl_conj_first hij hik hjk (-1 : Rˣ) a
  have hval : -((((-1 : Rˣ)⁻¹ : Rˣ)) : R) * a = a := by simp
  rwa [hval] at h

omit [DecidableEq n] in
/-- The Weyl element at `−1` transposes a column generator without a unit. -/
theorem steinbergWeyl_neg_one_conj_col {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (d : R) :
    steinbergWeyl hij (-1 : Rˣ) * steinbergX (Ne.symm hik) d * (steinbergWeyl hij (-1 : Rˣ))⁻¹
      = steinbergX (Ne.symm hjk) d := by
  have h := steinbergWeyl_conj_col hij hik hjk (-1 : Rˣ) d
  have hval : -(d * (((-1 : Rˣ)) : R)) = d := by simp
  rwa [hval] at h

/-! ## The torus action -/

omit [DecidableEq n] in
/-- **The torus scales a diagonal generator on both sides.** -/
theorem steinbergTorus_conj_self {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) (a : R) :
    steinbergTorus hij u * steinbergX hij a * (steinbergTorus hij u)⁻¹
      = steinbergX hij (((u : Rˣ) : R) * a * (((u : Rˣ)) : R)) := by
  have hinner := steinbergWeyl_neg_one_conj_self hij hik hjk a
  have houter := steinbergWeyl_conj_transpose hij hik hjk u (-a)
  have hval : -(((u : Rˣ) : R) * -a * (((u : Rˣ)) : R))
      = ((u : Rˣ) : R) * a * (((u : Rˣ)) : R) := by ring
  rw [hval] at houter
  rw [steinbergTorus]
  calc steinbergWeyl hij u * steinbergWeyl hij (-1 : Rˣ) * steinbergX hij a
        * (steinbergWeyl hij u * steinbergWeyl hij (-1 : Rˣ))⁻¹
      = steinbergWeyl hij u * (steinbergWeyl hij (-1 : Rˣ) * steinbergX hij a
          * (steinbergWeyl hij (-1 : Rˣ))⁻¹) * (steinbergWeyl hij u)⁻¹ := by group
    _ = steinbergWeyl hij u * steinbergX (Ne.symm hij) (-a) * (steinbergWeyl hij u)⁻¹ := by
        rw [hinner]
    _ = steinbergX hij (((u : Rˣ) : R) * a * (((u : Rˣ)) : R)) := houter

omit [DecidableEq n] in
/-- **The torus scales a row generator on the left.** -/
theorem steinbergTorus_conj_first {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) (a : R) :
    steinbergTorus hij u * steinbergX hik a * (steinbergTorus hij u)⁻¹
      = steinbergX hik (((u : Rˣ) : R) * a) := by
  have hinner := steinbergWeyl_neg_one_conj_first hij hik hjk a
  have houter := steinbergWeyl_conj_row hij hik hjk u a
  rw [steinbergTorus]
  calc steinbergWeyl hij u * steinbergWeyl hij (-1 : Rˣ) * steinbergX hik a
        * (steinbergWeyl hij u * steinbergWeyl hij (-1 : Rˣ))⁻¹
      = steinbergWeyl hij u * (steinbergWeyl hij (-1 : Rˣ) * steinbergX hik a
          * (steinbergWeyl hij (-1 : Rˣ))⁻¹) * (steinbergWeyl hij u)⁻¹ := by group
    _ = steinbergWeyl hij u * steinbergX hjk a * (steinbergWeyl hij u)⁻¹ := by rw [hinner]
    _ = steinbergX hik (((u : Rˣ) : R) * a) := houter

omit [DecidableEq n] in
/-- **The torus scales a column generator on the right, by the inverse.** -/
theorem steinbergTorus_conj_col {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) (d : R) :
    steinbergTorus hij u * steinbergX (Ne.symm hik) d * (steinbergTorus hij u)⁻¹
      = steinbergX (Ne.symm hik) (d * (((u⁻¹ : Rˣ)) : R)) := by
  have hinner := steinbergWeyl_neg_one_conj_col hij hik hjk d
  have houter := steinbergWeyl_conj_second hij hik hjk u d
  rw [steinbergTorus]
  calc steinbergWeyl hij u * steinbergWeyl hij (-1 : Rˣ) * steinbergX (Ne.symm hik) d
        * (steinbergWeyl hij u * steinbergWeyl hij (-1 : Rˣ))⁻¹
      = steinbergWeyl hij u * (steinbergWeyl hij (-1 : Rˣ) * steinbergX (Ne.symm hik) d
          * (steinbergWeyl hij (-1 : Rˣ))⁻¹) * (steinbergWeyl hij u)⁻¹ := by group
    _ = steinbergWeyl hij u * steinbergX (Ne.symm hjk) d * (steinbergWeyl hij u)⁻¹ := by
        rw [hinner]
    _ = steinbergX (Ne.symm hik) (d * (((u⁻¹ : Rˣ)) : R)) := houter

/-! ## The remaining three weights -/

omit [DecidableEq n] in
/-- **The torus scales a `j`-row generator by the inverse on the left.** -/
theorem steinbergTorus_conj_row {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) (c : R) :
    steinbergTorus hij u * steinbergX hjk c * (steinbergTorus hij u)⁻¹
      = steinbergX hjk ((((u⁻¹ : Rˣ)) : R) * c) := by
  have hinner : steinbergWeyl hij (-1 : Rˣ) * steinbergX hjk c
      * (steinbergWeyl hij (-1 : Rˣ))⁻¹ = steinbergX hik (-c) := by
    have h := steinbergWeyl_conj_row hij hik hjk (-1 : Rˣ) c
    have hval : (((-1 : Rˣ)) : R) * c = -c := by simp
    rwa [hval] at h
  have houter : steinbergWeyl hij u * steinbergX hik (-c) * (steinbergWeyl hij u)⁻¹
      = steinbergX hjk ((((u⁻¹ : Rˣ)) : R) * c) := by
    have h := steinbergWeyl_conj_first hij hik hjk u (-c)
    have hval : -((((u⁻¹ : Rˣ)) : R)) * -c = (((u⁻¹ : Rˣ)) : R) * c := by ring
    rwa [hval] at h
  rw [steinbergTorus]
  calc steinbergWeyl hij u * steinbergWeyl hij (-1 : Rˣ) * steinbergX hjk c
        * (steinbergWeyl hij u * steinbergWeyl hij (-1 : Rˣ))⁻¹
      = steinbergWeyl hij u * (steinbergWeyl hij (-1 : Rˣ) * steinbergX hjk c
          * (steinbergWeyl hij (-1 : Rˣ))⁻¹) * (steinbergWeyl hij u)⁻¹ := by group
    _ = steinbergWeyl hij u * steinbergX hik (-c) * (steinbergWeyl hij u)⁻¹ := by rw [hinner]
    _ = steinbergX hjk ((((u⁻¹ : Rˣ)) : R) * c) := houter

omit [DecidableEq n] in
/-- **The torus scales a `j`-column generator on the right.** -/
theorem steinbergTorus_conj_second {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) (b : R) :
    steinbergTorus hij u * steinbergX (Ne.symm hjk) b * (steinbergTorus hij u)⁻¹
      = steinbergX (Ne.symm hjk) (b * (((u : Rˣ)) : R)) := by
  have hinner : steinbergWeyl hij (-1 : Rˣ) * steinbergX (Ne.symm hjk) b
      * (steinbergWeyl hij (-1 : Rˣ))⁻¹ = steinbergX (Ne.symm hik) (-b) := by
    have h := steinbergWeyl_conj_second hij hik hjk (-1 : Rˣ) b
    have hval : b * ((((-1 : Rˣ)⁻¹ : Rˣ)) : R) = -b := by simp
    rwa [hval] at h
  have houter : steinbergWeyl hij u * steinbergX (Ne.symm hik) (-b)
      * (steinbergWeyl hij u)⁻¹ = steinbergX (Ne.symm hjk) (b * (((u : Rˣ)) : R)) := by
    have h := steinbergWeyl_conj_col hij hik hjk u (-b)
    have hval : -(-b * (((u : Rˣ)) : R)) = b * (((u : Rˣ)) : R) := by ring
    rwa [hval] at h
  rw [steinbergTorus]
  calc steinbergWeyl hij u * steinbergWeyl hij (-1 : Rˣ) * steinbergX (Ne.symm hjk) b
        * (steinbergWeyl hij u * steinbergWeyl hij (-1 : Rˣ))⁻¹
      = steinbergWeyl hij u * (steinbergWeyl hij (-1 : Rˣ) * steinbergX (Ne.symm hjk) b
          * (steinbergWeyl hij (-1 : Rˣ))⁻¹) * (steinbergWeyl hij u)⁻¹ := by group
    _ = steinbergWeyl hij u * steinbergX (Ne.symm hik) (-b) * (steinbergWeyl hij u)⁻¹ := by
        rw [hinner]
    _ = steinbergX (Ne.symm hjk) (b * (((u : Rˣ)) : R)) := houter

omit [DecidableEq n] in
/-- **The torus scales the transposed diagonal generator by the inverse on both sides.** -/
theorem steinbergTorus_conj_transpose {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) (b : R) :
    steinbergTorus hij u * steinbergX (Ne.symm hij) b * (steinbergTorus hij u)⁻¹
      = steinbergX (Ne.symm hij) ((((u⁻¹ : Rˣ)) : R) * b * (((u⁻¹ : Rˣ)) : R)) := by
  have hinner : steinbergWeyl hij (-1 : Rˣ) * steinbergX (Ne.symm hij) b
      * (steinbergWeyl hij (-1 : Rˣ))⁻¹ = steinbergX hij (-b) := by
    have h := steinbergWeyl_conj_transpose hij hik hjk (-1 : Rˣ) b
    have hval : -((((-1 : Rˣ)) : R) * b * (((-1 : Rˣ)) : R)) = -b := by simp
    rwa [hval] at h
  have houter : steinbergWeyl hij u * steinbergX hij (-b) * (steinbergWeyl hij u)⁻¹
      = steinbergX (Ne.symm hij) ((((u⁻¹ : Rˣ)) : R) * b * (((u⁻¹ : Rˣ)) : R)) := by
    have h := steinbergWeyl_conj_self hij hik hjk u (-b)
    have hval : -((((u⁻¹ : Rˣ)) : R)) * -b * (((u⁻¹ : Rˣ)) : R)
        = (((u⁻¹ : Rˣ)) : R) * b * (((u⁻¹ : Rˣ)) : R) := by ring
    rwa [hval] at h
  rw [steinbergTorus]
  calc steinbergWeyl hij u * steinbergWeyl hij (-1 : Rˣ) * steinbergX (Ne.symm hij) b
        * (steinbergWeyl hij u * steinbergWeyl hij (-1 : Rˣ))⁻¹
      = steinbergWeyl hij u * (steinbergWeyl hij (-1 : Rˣ) * steinbergX (Ne.symm hij) b
          * (steinbergWeyl hij (-1 : Rˣ))⁻¹) * (steinbergWeyl hij u)⁻¹ := by group
    _ = steinbergWeyl hij u * steinbergX hij (-b) * (steinbergWeyl hij u)⁻¹ := by rw [hinner]
    _ = steinbergX (Ne.symm hij) ((((u⁻¹ : Rˣ)) : R) * b * (((u⁻¹ : Rˣ)) : R)) := houter

end GaloisForLFunctions.HTGeometry

end
