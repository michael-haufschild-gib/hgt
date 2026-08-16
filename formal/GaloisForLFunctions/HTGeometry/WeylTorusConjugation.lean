import GaloisForLFunctions.HTGeometry.DennisSteinWeylTransport

/-!
# Conjugation of the Weyl and torus elements by `w_ij(1)`

Conjugating the defining word of `w_ij(t)` termwise by `w_ij(1)` reverses the index order and
negates the parameter:

```text
w_ij(1) w_ij(t) w_ij(1)⁻¹ = w_ji(-t) ,
```

because `w_ij(1)` exchanges `x_ij(s) ↦ x_ji(-s)` and `x_ji(s) ↦ x_ij(-s)`, and `-(-t)⁻¹ = t⁻¹`.
Applying this to `h_ij(w) = w_ij(w) w_ij(-1)` gives

```text
w_ij(1) h_ij(w) w_ij(1)⁻¹ = w_ji(-w) w_ji(1) = h_ji(-w) · h_ji(-1)⁻¹ ,
```

using `h_ji(1) = 1`, which says exactly `w_ji(1) = w_ji(-1)⁻¹`, and `h_ji(-1) = w_ji(-1)²`.

Substituting this into the Weyl transport relation removes the conjugation and leaves a relation
between Dennis–Stein symbols in the two index orders and three torus elements.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

omit [DecidableEq n] [Fintype n] in
/-- **`w_ij(1)` conjugates the Weyl element into the opposite order with a sign.** -/
theorem steinbergWeyl_one_conj_weyl {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (t : Rˣ) :
    steinbergWeyl hij 1 * steinbergWeyl hij t * (steinbergWeyl hij 1)⁻¹
      = steinbergWeyl (Ne.symm hij) (-t) := by
  have hconj_ij : ∀ s : R, steinbergWeyl hij 1 * steinbergX hij s * (steinbergWeyl hij 1)⁻¹
      = steinbergX (Ne.symm hij) (-s) := by
    intro s
    have h := steinbergWeyl_conj_self hij hik hjk (1 : Rˣ) s
    simpa using h
  have hconj_ji : ∀ s : R,
      steinbergWeyl hij 1 * steinbergX (Ne.symm hij) s * (steinbergWeyl hij 1)⁻¹
        = steinbergX hij (-s) := by
    intro s
    have h := steinbergWeyl_conj_transpose hij hik hjk (1 : Rˣ) s
    simpa using h
  have hval : -(((((-t)⁻¹ : Rˣ)) : R)) = (((t⁻¹ : Rˣ)) : R) := by
    rw [inv_neg]
    simp
  calc steinbergWeyl hij 1 * steinbergWeyl hij t * (steinbergWeyl hij 1)⁻¹
      = steinbergWeyl hij 1 * (steinbergX hij ((t : Rˣ) : R)
          * steinbergX (Ne.symm hij) (-((((t⁻¹ : Rˣ)) : R)))
          * steinbergX hij ((t : Rˣ) : R)) * (steinbergWeyl hij 1)⁻¹ := by
        rfl
    _ = (steinbergWeyl hij 1 * steinbergX hij ((t : Rˣ) : R) * (steinbergWeyl hij 1)⁻¹)
        * (steinbergWeyl hij 1 * steinbergX (Ne.symm hij) (-((((t⁻¹ : Rˣ)) : R)))
            * (steinbergWeyl hij 1)⁻¹)
        * (steinbergWeyl hij 1 * steinbergX hij ((t : Rˣ) : R)
            * (steinbergWeyl hij 1)⁻¹) := by group
    _ = steinbergX (Ne.symm hij) (-((t : Rˣ) : R))
        * steinbergX hij (-(-((((t⁻¹ : Rˣ)) : R))))
        * steinbergX (Ne.symm hij) (-((t : Rˣ) : R)) := by
        rw [hconj_ij, hconj_ji]
    _ = steinbergWeyl (Ne.symm hij) (-t) := by
        rw [steinbergWeyl, hval, neg_neg]
        norm_num

omit [DecidableEq n] [Fintype n] in
/-- **`w_ij(1)` conjugates the torus into the opposite order.** -/
theorem steinbergTorus_one_conj {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (w : Rˣ) :
    steinbergWeyl hij 1 * steinbergTorus hij w * (steinbergWeyl hij 1)⁻¹
      = steinbergTorus (Ne.symm hij) (-w) * (steinbergTorus (Ne.symm hij) (-1))⁻¹ := by
  have hji : j ≠ i := Ne.symm hij
  have hone : steinbergWeyl hji (1 : Rˣ) * steinbergWeyl hji (-1 : Rˣ) = 1 := by
    have h : steinbergTorus hji (1 : Rˣ) = 1 := steinbergTorus_one hji
    rwa [steinbergTorus] at h
  calc steinbergWeyl hij 1 * steinbergTorus hij w * (steinbergWeyl hij 1)⁻¹
      = (steinbergWeyl hij 1 * steinbergWeyl hij w * (steinbergWeyl hij 1)⁻¹)
        * (steinbergWeyl hij 1 * steinbergWeyl hij (-1 : Rˣ)
            * (steinbergWeyl hij 1)⁻¹) := by
        rw [steinbergTorus]
        group
    _ = steinbergWeyl hji (-w) * steinbergWeyl hji (-(-1 : Rˣ)) := by
        rw [steinbergWeyl_one_conj_weyl hij hik hjk w, steinbergWeyl_one_conj_weyl hij hik hjk]
    _ = steinbergWeyl hji (-w) * steinbergWeyl hji (1 : Rˣ) := by norm_num
    _ = steinbergTorus hji (-w) * (steinbergTorus hji (-1))⁻¹ := by
        have h1 : steinbergWeyl hji (1 : Rˣ) = (steinbergWeyl hji (-1 : Rˣ))⁻¹ := by
          calc steinbergWeyl hji (1 : Rˣ)
              = steinbergWeyl hji (1 : Rˣ) * steinbergWeyl hji (-1 : Rˣ)
                * (steinbergWeyl hji (-1 : Rˣ))⁻¹ := by group
            _ = (steinbergWeyl hji (-1 : Rˣ))⁻¹ := by rw [hone, one_mul]
        rw [steinbergTorus, steinbergTorus, h1]
        group

/-- **The Weyl transport relation, with the conjugation eliminated.** -/
theorem dennisStein_index_reversal {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b : R) (w : Rˣ) (hw : (w : R) = 1 + a * b) :
    dennisStein hij a b w
        * (steinbergTorus (Ne.symm hij) (-w) * (steinbergTorus (Ne.symm hij) (-1))⁻¹)
      = dennisStein (Ne.symm hij) (-a) (-b) w * steinbergTorus (Ne.symm hij) w := by
  rw [← steinbergTorus_one_conj hij hik hjk w]
  exact dennisStein_weyl_transport hij hik hjk a b w hw

end GaloisForLFunctions.HTGeometry

end
