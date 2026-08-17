import GaloisForLFunctions.HTGeometry.DennisSteinIndexIndependent

/-!
# The Dennis–Stein symbol does not depend on the first index either

Conjugation by `w_ik(-1)` exchanges the first index of the pair, again with no sign and no torus
correction:

```text
w_ik(-1) x_ij(s) w_ik(-1)⁻¹ = x_kj(s) ,   w_ik(-1) x_ji(s) w_ik(-1)⁻¹ = x_jk(s) ,
w_ik(-1) w_ij(t) w_ik(-1)⁻¹ = w_kj(t) ,   w_ik(-1) h_ij(v) w_ik(-1)⁻¹ = h_kj(v) .
```

Together with the second-index statement this makes the symbol independent of the index pair
altogether: any two ordered pairs of a triple are joined by these two moves.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

omit [DecidableEq n] [Fintype n] in
/-- `w_ik(-1)` sends an `i`-row generator to a `k`-row generator, with no sign. -/
theorem steinbergWeyl_ik_neg_conj_row {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (s : R) :
    steinbergWeyl hik (-1) * steinbergX hij s * (steinbergWeyl hik (-1))⁻¹
      = steinbergX (Ne.symm hjk) s := by
  have h := steinbergWeyl_conj_first hik hij (Ne.symm hjk) (-1 : Rˣ) s
  simpa using h

omit [DecidableEq n] [Fintype n] in
/-- `w_ik(-1)` sends an `i`-column generator to a `k`-column generator, with no sign. -/
theorem steinbergWeyl_ik_neg_conj_col {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (s : R) :
    steinbergWeyl hik (-1) * steinbergX (Ne.symm hij) s * (steinbergWeyl hik (-1))⁻¹
      = steinbergX hjk s := by
  have h := steinbergWeyl_conj_col hik hij (Ne.symm hjk) (-1 : Rˣ) s
  simpa using h

omit [DecidableEq n] [Fintype n] in
/-- `w_ik(-1)` carries the Weyl elements of `(i,j)` to those of `(k,j)` exactly. -/
theorem steinbergWeyl_ik_neg_conj_weyl {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (t : Rˣ) :
    steinbergWeyl hik (-1) * steinbergWeyl hij t * (steinbergWeyl hik (-1))⁻¹
      = steinbergWeyl (Ne.symm hjk) t := by
  calc steinbergWeyl hik (-1) * steinbergWeyl hij t * (steinbergWeyl hik (-1))⁻¹
      = steinbergWeyl hik (-1) * (steinbergX hij ((t : Rˣ) : R)
          * steinbergX (Ne.symm hij) (-((((t⁻¹ : Rˣ)) : R)))
          * steinbergX hij ((t : Rˣ) : R)) * (steinbergWeyl hik (-1))⁻¹ := by rfl
    _ = (steinbergWeyl hik (-1) * steinbergX hij ((t : Rˣ) : R) * (steinbergWeyl hik (-1))⁻¹)
        * (steinbergWeyl hik (-1) * steinbergX (Ne.symm hij) (-((((t⁻¹ : Rˣ)) : R)))
            * (steinbergWeyl hik (-1))⁻¹)
        * (steinbergWeyl hik (-1) * steinbergX hij ((t : Rˣ) : R)
            * (steinbergWeyl hik (-1))⁻¹) := by group
    _ = steinbergX (Ne.symm hjk) ((t : Rˣ) : R)
        * steinbergX hjk (-((((t⁻¹ : Rˣ)) : R)))
        * steinbergX (Ne.symm hjk) ((t : Rˣ) : R) := by
        rw [steinbergWeyl_ik_neg_conj_row hij hik hjk,
          steinbergWeyl_ik_neg_conj_col hij hik hjk]
    _ = steinbergWeyl (Ne.symm hjk) t := by rfl

omit [DecidableEq n] [Fintype n] in
/-- **`w_ik(-1)` carries the torus of `(i,j)` to that of `(k,j)` exactly.** -/
theorem steinbergTorus_ik_neg_conj {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (v : Rˣ) :
    steinbergWeyl hik (-1) * steinbergTorus hij v * (steinbergWeyl hik (-1))⁻¹
      = steinbergTorus (Ne.symm hjk) v := by
  calc steinbergWeyl hik (-1) * steinbergTorus hij v * (steinbergWeyl hik (-1))⁻¹
      = (steinbergWeyl hik (-1) * steinbergWeyl hij v * (steinbergWeyl hik (-1))⁻¹)
        * (steinbergWeyl hik (-1) * steinbergWeyl hij (-1 : Rˣ)
            * (steinbergWeyl hik (-1))⁻¹) := by
        rw [steinbergTorus]
        group
    _ = steinbergWeyl (Ne.symm hjk) v * steinbergWeyl (Ne.symm hjk) (-1 : Rˣ) := by
        rw [steinbergWeyl_ik_neg_conj_weyl hij hik hjk v,
          steinbergWeyl_ik_neg_conj_weyl hij hik hjk]
    _ = steinbergTorus (Ne.symm hjk) v := by rw [steinbergTorus]

/-- **The Dennis–Stein symbol is independent of the first index.** -/
theorem dennisStein_first_index_independent {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b : R) (v : Rˣ) (hv : (v : R) = 1 + a * b) :
    dennisStein hij a b v = dennisStein (Ne.symm hjk) a b v := by
  have hDc := Subgroup.mem_center_iff.1 (dennisStein_mem_center hij a b v hv
    (Ne.symm hik) (Ne.symm hjk))
  have hconjD : steinbergWeyl hik (-1) * dennisStein hij a b v * (steinbergWeyl hik (-1))⁻¹
      = dennisStein hij a b v := by
    rw [hDc (steinbergWeyl hik (-1))]
    group
  rw [← hconjD]
  calc steinbergWeyl hik (-1) * dennisStein hij a b v * (steinbergWeyl hik (-1))⁻¹
      = (steinbergWeyl hik (-1) * steinbergX (Ne.symm hij) (-(b * (((v⁻¹ : Rˣ)) : R)))
          * (steinbergWeyl hik (-1))⁻¹)
        * (steinbergWeyl hik (-1) * steinbergX hij a * (steinbergWeyl hik (-1))⁻¹)
        * (steinbergWeyl hik (-1) * steinbergX (Ne.symm hij) b * (steinbergWeyl hik (-1))⁻¹)
        * (steinbergWeyl hik (-1) * steinbergX hij (-((((v⁻¹ : Rˣ)) : R) * a))
          * (steinbergWeyl hik (-1))⁻¹)
        * (steinbergWeyl hik (-1) * (steinbergTorus hij v)⁻¹
          * (steinbergWeyl hik (-1))⁻¹) := by
        rw [dennisStein]
        group
    _ = dennisStein (Ne.symm hjk) a b v := by
        rw [steinbergWeyl_ik_neg_conj_col hij hik hjk,
          steinbergWeyl_ik_neg_conj_row hij hik hjk,
          steinbergWeyl_ik_neg_conj_col hij hik hjk,
          steinbergWeyl_ik_neg_conj_row hij hik hjk]
        have htor : steinbergWeyl hik (-1) * (steinbergTorus hij v)⁻¹
            * (steinbergWeyl hik (-1))⁻¹ = (steinbergTorus (Ne.symm hjk) v)⁻¹ := by
          rw [← steinbergTorus_ik_neg_conj hij hik hjk v]
          group
        rw [htor, dennisStein]

end GaloisForLFunctions.HTGeometry

end
