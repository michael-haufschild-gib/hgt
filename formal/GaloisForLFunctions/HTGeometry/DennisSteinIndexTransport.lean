import GaloisForLFunctions.HTGeometry.WeylTorusConjugation

/-!
# Transporting a Dennis–Stein symbol to another index pair

The Weyl element `w_jk(1)` exchanges the second index of the pair `(i,j)` for `k`:

```text
w_jk(1) x_ij(s) w_jk(1)⁻¹ = x_ik(-s) ,     w_jk(1) x_ji(s) w_jk(1)⁻¹ = x_ki(-s) ,
w_jk(1) w_ij(t) w_jk(1)⁻¹ = w_ik(-t) ,     w_jk(1) h_ij(v) w_jk(1)⁻¹ = h_ik(-v) · h_ik(-1)⁻¹ .
```

Conjugating the defining word of `⟨a,b⟩_ij` therefore produces the defining word of `⟨-a,-b⟩_ik` —
the four elementary factors match on the nose, the unit `1 + ab = 1 + (-a)(-b)` is unchanged — and
the symbol is central, so it is fixed by the conjugation.  What is left is a discrepancy of torus
elements attached to the new pair:

```text
⟨a, b⟩_ij · h_ik(-v) · h_ik(-1)⁻¹ = ⟨-a, -b⟩_ik · h_ik(v) .
```

Together with the reversal relation for `(i,j) ↦ (j,i)`, this moves a symbol between any two index
pairs of a triple, which is what a three-index comparison of Dennis–Stein symbols needs.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

omit [DecidableEq n] [Fintype n] in
/-- `w_jk(1)` sends a `j`-column generator to a `k`-column generator, with a sign. -/
theorem steinbergWeyl_jk_conj_col {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (s : R) :
    steinbergWeyl hjk 1 * steinbergX hij s * (steinbergWeyl hjk 1)⁻¹
      = steinbergX hik (-s) := by
  have h := steinbergWeyl_conj_col hjk (Ne.symm hij) (Ne.symm hik) (1 : Rˣ) s
  simpa using h

omit [DecidableEq n] [Fintype n] in
/-- `w_jk(1)` sends a `j`-row generator to a `k`-row generator, with a sign. -/
theorem steinbergWeyl_jk_conj_row {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (s : R) :
    steinbergWeyl hjk 1 * steinbergX (Ne.symm hij) s * (steinbergWeyl hjk 1)⁻¹
      = steinbergX (Ne.symm hik) (-s) := by
  have h := steinbergWeyl_conj_first hjk (Ne.symm hij) (Ne.symm hik) (1 : Rˣ) s
  simpa using h

omit [DecidableEq n] [Fintype n] in
/-- `w_jk(1)` carries the Weyl elements of the pair `(i,j)` to those of `(i,k)`. -/
theorem steinbergWeyl_jk_conj_weyl {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (t : Rˣ) :
    steinbergWeyl hjk 1 * steinbergWeyl hij t * (steinbergWeyl hjk 1)⁻¹
      = steinbergWeyl hik (-t) := by
  have hval : -(((((-t)⁻¹ : Rˣ)) : R)) = (((t⁻¹ : Rˣ)) : R) := by
    rw [inv_neg]
    simp
  calc steinbergWeyl hjk 1 * steinbergWeyl hij t * (steinbergWeyl hjk 1)⁻¹
      = steinbergWeyl hjk 1 * (steinbergX hij ((t : Rˣ) : R)
          * steinbergX (Ne.symm hij) (-((((t⁻¹ : Rˣ)) : R)))
          * steinbergX hij ((t : Rˣ) : R)) * (steinbergWeyl hjk 1)⁻¹ := by
        rfl
    _ = (steinbergWeyl hjk 1 * steinbergX hij ((t : Rˣ) : R) * (steinbergWeyl hjk 1)⁻¹)
        * (steinbergWeyl hjk 1 * steinbergX (Ne.symm hij) (-((((t⁻¹ : Rˣ)) : R)))
            * (steinbergWeyl hjk 1)⁻¹)
        * (steinbergWeyl hjk 1 * steinbergX hij ((t : Rˣ) : R)
            * (steinbergWeyl hjk 1)⁻¹) := by group
    _ = steinbergX hik (-((t : Rˣ) : R))
        * steinbergX (Ne.symm hik) (-(-((((t⁻¹ : Rˣ)) : R))))
        * steinbergX hik (-((t : Rˣ) : R)) := by
        rw [steinbergWeyl_jk_conj_col hij hik hjk, steinbergWeyl_jk_conj_row hij hik hjk]
    _ = steinbergWeyl hik (-t) := by
        rw [steinbergWeyl, hval, neg_neg]
        norm_num

omit [DecidableEq n] [Fintype n] in
/-- `w_jk(1)` carries the torus of the pair `(i,j)` to that of `(i,k)`. -/
theorem steinbergTorus_jk_conj {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (v : Rˣ) :
    steinbergWeyl hjk 1 * steinbergTorus hij v * (steinbergWeyl hjk 1)⁻¹
      = steinbergTorus hik (-v) * (steinbergTorus hik (-1))⁻¹ := by
  have hone : steinbergWeyl hik (1 : Rˣ) * steinbergWeyl hik (-1 : Rˣ) = 1 := by
    have h : steinbergTorus hik (1 : Rˣ) = 1 := steinbergTorus_one hik
    rwa [steinbergTorus] at h
  calc steinbergWeyl hjk 1 * steinbergTorus hij v * (steinbergWeyl hjk 1)⁻¹
      = (steinbergWeyl hjk 1 * steinbergWeyl hij v * (steinbergWeyl hjk 1)⁻¹)
        * (steinbergWeyl hjk 1 * steinbergWeyl hij (-1 : Rˣ)
            * (steinbergWeyl hjk 1)⁻¹) := by
        rw [steinbergTorus]
        group
    _ = steinbergWeyl hik (-v) * steinbergWeyl hik (-(-1 : Rˣ)) := by
        rw [steinbergWeyl_jk_conj_weyl hij hik hjk v, steinbergWeyl_jk_conj_weyl hij hik hjk]
    _ = steinbergWeyl hik (-v) * steinbergWeyl hik (1 : Rˣ) := by norm_num
    _ = steinbergTorus hik (-v) * (steinbergTorus hik (-1))⁻¹ := by
        have h1 : steinbergWeyl hik (1 : Rˣ) = (steinbergWeyl hik (-1 : Rˣ))⁻¹ := by
          calc steinbergWeyl hik (1 : Rˣ)
              = steinbergWeyl hik (1 : Rˣ) * steinbergWeyl hik (-1 : Rˣ)
                * (steinbergWeyl hik (-1 : Rˣ))⁻¹ := by group
            _ = (steinbergWeyl hik (-1 : Rˣ))⁻¹ := by rw [hone, one_mul]
        rw [steinbergTorus, steinbergTorus, h1]
        group

/-- **The Dennis–Stein symbol transported to another index pair.** -/
theorem dennisStein_index_transport {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b : R) (v : Rˣ) (hv : (v : R) = 1 + a * b) :
    dennisStein hij a b v * (steinbergTorus hik (-v) * (steinbergTorus hik (-1))⁻¹)
      = dennisStein hik (-a) (-b) v * steinbergTorus hik v := by
  have hDc := Subgroup.mem_center_iff.1 (dennisStein_mem_center hij a b v hv
    (Ne.symm hik) (Ne.symm hjk))
  have hconjD : steinbergWeyl hjk 1 * dennisStein hij a b v * (steinbergWeyl hjk 1)⁻¹
      = dennisStein hij a b v := by
    rw [hDc (steinbergWeyl hjk 1)]
    group
  have hexp : steinbergWeyl hjk 1 * dennisStein hij a b v * (steinbergWeyl hjk 1)⁻¹
      = steinbergX (Ne.symm hik) (-(-(b * (((v⁻¹ : Rˣ)) : R))))
        * steinbergX hik (-a)
        * steinbergX (Ne.symm hik) (-b)
        * steinbergX hik (-(-((((v⁻¹ : Rˣ)) : R) * a)))
        * (steinbergTorus hik (-v) * (steinbergTorus hik (-1))⁻¹)⁻¹ := by
    calc steinbergWeyl hjk 1 * dennisStein hij a b v * (steinbergWeyl hjk 1)⁻¹
        = (steinbergWeyl hjk 1 * steinbergX (Ne.symm hij) (-(b * (((v⁻¹ : Rˣ)) : R)))
            * (steinbergWeyl hjk 1)⁻¹)
          * (steinbergWeyl hjk 1 * steinbergX hij a * (steinbergWeyl hjk 1)⁻¹)
          * (steinbergWeyl hjk 1 * steinbergX (Ne.symm hij) b * (steinbergWeyl hjk 1)⁻¹)
          * (steinbergWeyl hjk 1 * steinbergX hij (-((((v⁻¹ : Rˣ)) : R) * a))
            * (steinbergWeyl hjk 1)⁻¹)
          * (steinbergWeyl hjk 1 * (steinbergTorus hij v)⁻¹
            * (steinbergWeyl hjk 1)⁻¹) := by
          rw [dennisStein]
          group
      _ = steinbergX (Ne.symm hik) (-(-(b * (((v⁻¹ : Rˣ)) : R))))
          * steinbergX hik (-a)
          * steinbergX (Ne.symm hik) (-b)
          * steinbergX hik (-(-((((v⁻¹ : Rˣ)) : R) * a)))
          * (steinbergTorus hik (-v) * (steinbergTorus hik (-1))⁻¹)⁻¹ := by
          rw [steinbergWeyl_jk_conj_row hij hik hjk, steinbergWeyl_jk_conj_col hij hik hjk,
            steinbergWeyl_jk_conj_row hij hik hjk, steinbergWeyl_jk_conj_col hij hik hjk]
          have htor : steinbergWeyl hjk 1 * (steinbergTorus hij v)⁻¹
              * (steinbergWeyl hjk 1)⁻¹
              = (steinbergTorus hik (-v) * (steinbergTorus hik (-1))⁻¹)⁻¹ := by
            rw [← steinbergTorus_jk_conj hij hik hjk v]
            group
          rw [htor]
  have htarget : dennisStein hik (-a) (-b) v * steinbergTorus hik v
      = steinbergX (Ne.symm hik) (-(-(b * (((v⁻¹ : Rˣ)) : R))))
        * steinbergX hik (-a)
        * steinbergX (Ne.symm hik) (-b)
        * steinbergX hik (-(-((((v⁻¹ : Rˣ)) : R) * a))) := by
    have e1 : -((-b) * (((v⁻¹ : Rˣ)) : R)) = -(-(b * (((v⁻¹ : Rˣ)) : R))) := by ring
    have e2 : -((((v⁻¹ : Rˣ)) : R) * (-a)) = -(-((((v⁻¹ : Rˣ)) : R) * a)) := by ring
    rw [dennisStein, e1, e2]
    group
  rw [hconjD] at hexp
  rw [hexp, htarget]
  group

end GaloisForLFunctions.HTGeometry

end
