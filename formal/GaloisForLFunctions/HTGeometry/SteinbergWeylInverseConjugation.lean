import GaloisForLFunctions.HTGeometry.SteinbergTorusAction

/-!
# Conjugation by the inverse Weyl element

Since `w_ij(−u) = w_ij(u)⁻¹`, the action of the inverse Weyl element is obtained by feeding `−u`
into the six conjugation formulas.  Two of them are unchanged — the ones with a unit on each side,
where the two signs cancel — and the other four flip sign:

```text
w(u)⁻¹ x_ik(a) w(u) = x_jk(u⁻¹ a)        w(u)⁻¹ x_jk(c) w(u) = x_ik(−u c)
w(u)⁻¹ x_kj(b) w(u) = x_ki(−b u⁻¹)       w(u)⁻¹ x_ki(d) w(u) = x_kj(d u)
w(u)⁻¹ x_ij(a) w(u) = x_ji(−u⁻¹ a u⁻¹)   w(u)⁻¹ x_ji(b) w(u) = x_ij(−u b u)
```

These are what one uses to move a Weyl element leftwards through a word, and together with the
forward formulas they say that conjugation by `w(u)` is an automorphism of the set of generators
up to the indicated rescalings.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n]

omit [DecidableEq n] in
private theorem steinbergUnit_neg_val (u : Rˣ) : (((-u : Rˣ)) : R) = -(((u : Rˣ)) : R) := by
  simp

omit [DecidableEq n] in
private theorem steinbergUnit_neg_inv_val (u : Rˣ) :
    (((((-u : Rˣ))⁻¹ : Rˣ)) : R) = -(((u⁻¹ : Rˣ)) : R) := by
  simp

omit [DecidableEq n] in
/-- The inverse Weyl element moves a first-index row generator to the second index. -/
theorem steinbergWeyl_inv_conj_first {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) (a : R) :
    (steinbergWeyl hij u)⁻¹ * steinbergX hik a * steinbergWeyl hij u
      = steinbergX hjk ((((u⁻¹ : Rˣ)) : R) * a) := by
  have h := steinbergWeyl_conj_first hij hik hjk (-u) a
  rw [steinbergWeyl_neg, inv_inv, steinbergUnit_neg_inv_val] at h
  have hval : -(-(((u⁻¹ : Rˣ)) : R)) * a = (((u⁻¹ : Rˣ)) : R) * a := by ring
  rwa [hval] at h

omit [DecidableEq n] in
/-- The inverse Weyl element moves a second-index column generator to the first index. -/
theorem steinbergWeyl_inv_conj_second {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) (b : R) :
    (steinbergWeyl hij u)⁻¹ * steinbergX (Ne.symm hjk) b * steinbergWeyl hij u
      = steinbergX (Ne.symm hik) (-(b * (((u⁻¹ : Rˣ)) : R))) := by
  have h := steinbergWeyl_conj_second hij hik hjk (-u) b
  rw [steinbergWeyl_neg, inv_inv, steinbergUnit_neg_inv_val] at h
  have hval : b * -(((u⁻¹ : Rˣ)) : R) = -(b * (((u⁻¹ : Rˣ)) : R)) := by ring
  rwa [hval] at h

omit [DecidableEq n] in
/-- Conjugating a diagonal generator by the inverse Weyl element gives the same answer as
conjugating by the Weyl element itself: the two signs cancel. -/
theorem steinbergWeyl_inv_conj_self {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) (a : R) :
    (steinbergWeyl hij u)⁻¹ * steinbergX hij a * steinbergWeyl hij u
      = steinbergX (Ne.symm hij) (-(((u⁻¹ : Rˣ)) : R) * a * (((u⁻¹ : Rˣ)) : R)) := by
  have h := steinbergWeyl_conj_self hij hik hjk (-u) a
  rw [steinbergWeyl_neg, inv_inv, steinbergUnit_neg_inv_val] at h
  have hval : -(-(((u⁻¹ : Rˣ)) : R)) * a * -(((u⁻¹ : Rˣ)) : R)
      = -(((u⁻¹ : Rˣ)) : R) * a * (((u⁻¹ : Rˣ)) : R) := by ring
  rwa [hval] at h

omit [DecidableEq n] in
/-- The inverse Weyl element moves a second-index row generator to the first index. -/
theorem steinbergWeyl_inv_conj_row {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) (c : R) :
    (steinbergWeyl hij u)⁻¹ * steinbergX hjk c * steinbergWeyl hij u
      = steinbergX hik (-((((u : Rˣ)) : R) * c)) := by
  have h := steinbergWeyl_conj_row hij hik hjk (-u) c
  rw [steinbergWeyl_neg, inv_inv, steinbergUnit_neg_val] at h
  have hval : -(((u : Rˣ)) : R) * c = -((((u : Rˣ)) : R) * c) := by ring
  rwa [hval] at h

omit [DecidableEq n] in
/-- The inverse Weyl element moves a first-index column generator to the second index. -/
theorem steinbergWeyl_inv_conj_col {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) (d : R) :
    (steinbergWeyl hij u)⁻¹ * steinbergX (Ne.symm hik) d * steinbergWeyl hij u
      = steinbergX (Ne.symm hjk) (d * (((u : Rˣ)) : R)) := by
  have h := steinbergWeyl_conj_col hij hik hjk (-u) d
  rw [steinbergWeyl_neg, inv_inv, steinbergUnit_neg_val] at h
  have hval : -(d * -(((u : Rˣ)) : R)) = d * (((u : Rˣ)) : R) := by ring
  rwa [hval] at h

omit [DecidableEq n] in
/-- Conjugating the transposed diagonal generator by the inverse Weyl element again agrees with
the forward formula. -/
theorem steinbergWeyl_inv_conj_transpose {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) (b : R) :
    (steinbergWeyl hij u)⁻¹ * steinbergX (Ne.symm hij) b * steinbergWeyl hij u
      = steinbergX hij (-((((u : Rˣ)) : R) * b * (((u : Rˣ)) : R))) := by
  have h := steinbergWeyl_conj_transpose hij hik hjk (-u) b
  rw [steinbergWeyl_neg, inv_inv, steinbergUnit_neg_val] at h
  have hval : -(-(((u : Rˣ)) : R) * b * -(((u : Rˣ)) : R))
      = -((((u : Rˣ)) : R) * b * (((u : Rˣ)) : R)) := by ring
  rwa [hval] at h

end GaloisForLFunctions.HTGeometry

end
