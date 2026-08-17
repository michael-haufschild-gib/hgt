import GaloisForLFunctions.HTGeometry.WeylTorusConjugation

/-!
# The Dennis–Stein symbol does not depend on the second index

Conjugation by `w_jk(-1)` — not `w_jk(1)` — exchanges the second index of the pair with no sign:

```text
w_jk(-1) x_ij(s) w_jk(-1)⁻¹ = x_ik(s) ,   w_jk(-1) x_ji(s) w_jk(-1)⁻¹ = x_ki(s) ,
w_jk(-1) w_ij(t) w_jk(-1)⁻¹ = w_ik(t) ,   w_jk(-1) h_ij(v) w_jk(-1)⁻¹ = h_ik(v) .
```

The torus goes across *exactly*, with no correction at all, because `h_ij(v) = w_ij(v) w_ij(-1)` and
the conjugation sends `w_ij(t)` to `w_ik(t)` on the nose.  Conjugating the defining word of the
Dennis–Stein symbol therefore produces the defining word of the symbol of the pair `(i,k)` with the
*same* arguments, and the symbol is central, so it is fixed:

```text
⟨a, b⟩_ij = ⟨a, b⟩_ik .
```

The corresponding conjugation by `w_jk(1)` costs a sign on both arguments and a torus factor; using
`-1` instead removes both.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

omit [DecidableEq n] [Fintype n] in
/-- `w_jk(-1)` sends a `j`-column generator to a `k`-column generator, with no sign. -/
theorem steinbergWeyl_jk_neg_conj_col {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (s : R) :
    steinbergWeyl hjk (-1) * steinbergX hij s * (steinbergWeyl hjk (-1))⁻¹
      = steinbergX hik s := by
  have h := steinbergWeyl_conj_col hjk (Ne.symm hij) (Ne.symm hik) (-1 : Rˣ) s
  simpa using h

omit [DecidableEq n] [Fintype n] in
/-- `w_jk(-1)` sends a `j`-row generator to a `k`-row generator, with no sign. -/
theorem steinbergWeyl_jk_neg_conj_row {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (s : R) :
    steinbergWeyl hjk (-1) * steinbergX (Ne.symm hij) s * (steinbergWeyl hjk (-1))⁻¹
      = steinbergX (Ne.symm hik) s := by
  have h := steinbergWeyl_conj_first hjk (Ne.symm hij) (Ne.symm hik) (-1 : Rˣ) s
  simpa using h

omit [DecidableEq n] [Fintype n] in
/-- `w_jk(-1)` carries the Weyl elements of `(i,j)` to those of `(i,k)` exactly. -/
theorem steinbergWeyl_jk_neg_conj_weyl {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (t : Rˣ) :
    steinbergWeyl hjk (-1) * steinbergWeyl hij t * (steinbergWeyl hjk (-1))⁻¹
      = steinbergWeyl hik t := by
  calc steinbergWeyl hjk (-1) * steinbergWeyl hij t * (steinbergWeyl hjk (-1))⁻¹
      = steinbergWeyl hjk (-1) * (steinbergX hij ((t : Rˣ) : R)
          * steinbergX (Ne.symm hij) (-((((t⁻¹ : Rˣ)) : R)))
          * steinbergX hij ((t : Rˣ) : R)) * (steinbergWeyl hjk (-1))⁻¹ := by rfl
    _ = (steinbergWeyl hjk (-1) * steinbergX hij ((t : Rˣ) : R) * (steinbergWeyl hjk (-1))⁻¹)
        * (steinbergWeyl hjk (-1) * steinbergX (Ne.symm hij) (-((((t⁻¹ : Rˣ)) : R)))
            * (steinbergWeyl hjk (-1))⁻¹)
        * (steinbergWeyl hjk (-1) * steinbergX hij ((t : Rˣ) : R)
            * (steinbergWeyl hjk (-1))⁻¹) := by group
    _ = steinbergX hik ((t : Rˣ) : R)
        * steinbergX (Ne.symm hik) (-((((t⁻¹ : Rˣ)) : R)))
        * steinbergX hik ((t : Rˣ) : R) := by
        rw [steinbergWeyl_jk_neg_conj_col hij hik hjk,
          steinbergWeyl_jk_neg_conj_row hij hik hjk]
    _ = steinbergWeyl hik t := by rfl

omit [DecidableEq n] [Fintype n] in
/-- **`w_jk(-1)` carries the torus of `(i,j)` to that of `(i,k)` exactly.** -/
theorem steinbergTorus_jk_neg_conj {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (v : Rˣ) :
    steinbergWeyl hjk (-1) * steinbergTorus hij v * (steinbergWeyl hjk (-1))⁻¹
      = steinbergTorus hik v := by
  calc steinbergWeyl hjk (-1) * steinbergTorus hij v * (steinbergWeyl hjk (-1))⁻¹
      = (steinbergWeyl hjk (-1) * steinbergWeyl hij v * (steinbergWeyl hjk (-1))⁻¹)
        * (steinbergWeyl hjk (-1) * steinbergWeyl hij (-1 : Rˣ)
            * (steinbergWeyl hjk (-1))⁻¹) := by
        rw [steinbergTorus]
        group
    _ = steinbergWeyl hik v * steinbergWeyl hik (-1 : Rˣ) := by
        rw [steinbergWeyl_jk_neg_conj_weyl hij hik hjk v,
          steinbergWeyl_jk_neg_conj_weyl hij hik hjk]
    _ = steinbergTorus hik v := by rw [steinbergTorus]

/-- **The Dennis–Stein symbol is independent of the second index.** -/
theorem dennisStein_index_independent {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b : R) (v : Rˣ) (hv : (v : R) = 1 + a * b) :
    dennisStein hij a b v = dennisStein hik a b v := by
  have hDc := Subgroup.mem_center_iff.1 (dennisStein_mem_center hij a b v hv
    (Ne.symm hik) (Ne.symm hjk))
  have hconjD : steinbergWeyl hjk (-1) * dennisStein hij a b v * (steinbergWeyl hjk (-1))⁻¹
      = dennisStein hij a b v := by
    rw [hDc (steinbergWeyl hjk (-1))]
    group
  rw [← hconjD]
  calc steinbergWeyl hjk (-1) * dennisStein hij a b v * (steinbergWeyl hjk (-1))⁻¹
      = (steinbergWeyl hjk (-1) * steinbergX (Ne.symm hij) (-(b * (((v⁻¹ : Rˣ)) : R)))
          * (steinbergWeyl hjk (-1))⁻¹)
        * (steinbergWeyl hjk (-1) * steinbergX hij a * (steinbergWeyl hjk (-1))⁻¹)
        * (steinbergWeyl hjk (-1) * steinbergX (Ne.symm hij) b * (steinbergWeyl hjk (-1))⁻¹)
        * (steinbergWeyl hjk (-1) * steinbergX hij (-((((v⁻¹ : Rˣ)) : R) * a))
          * (steinbergWeyl hjk (-1))⁻¹)
        * (steinbergWeyl hjk (-1) * (steinbergTorus hij v)⁻¹
          * (steinbergWeyl hjk (-1))⁻¹) := by
        rw [dennisStein]
        group
    _ = dennisStein hik a b v := by
        rw [steinbergWeyl_jk_neg_conj_row hij hik hjk,
          steinbergWeyl_jk_neg_conj_col hij hik hjk,
          steinbergWeyl_jk_neg_conj_row hij hik hjk,
          steinbergWeyl_jk_neg_conj_col hij hik hjk]
        have htor : steinbergWeyl hjk (-1) * (steinbergTorus hij v)⁻¹
            * (steinbergWeyl hjk (-1))⁻¹ = (steinbergTorus hik v)⁻¹ := by
          rw [← steinbergTorus_jk_neg_conj hij hik hjk v]
          group
        rw [htor, dennisStein]

end GaloisForLFunctions.HTGeometry

end
