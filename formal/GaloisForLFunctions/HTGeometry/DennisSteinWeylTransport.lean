import GaloisForLFunctions.HTGeometry.DennisSteinAddLeft

/-!
# Transport of the Dennis–Stein symbol across the two index orders

Conjugating the Bruhat decomposition of `x_ij(a) · x_ji(b)` by the Weyl element `w_ij(1)` turns it
into the Bruhat decomposition of `x_ji(-a) · x_ij(-b)` in the opposite orientation, because

```text
w_ij(1) x_ij(t) w_ij(1)⁻¹ = x_ji(-t) ,      w_ij(1) x_ji(t) w_ij(1)⁻¹ = x_ij(-t) .
```

Both decompositions have the same unit `1 + ab = 1 + (-a)(-b)` and — after the signs are pushed
through — literally the same outer parameters, so the two central parts must agree:

```text
⟨a, b⟩_ij · w_ij(1) h_ij(w) w_ij(1)⁻¹  =  ⟨-a, -b⟩_ji · h_ji(w) .
```

This is the sign-and-order relation of the Dennis–Stein presentation: the symbol taken in the
opposite index order, with both arguments negated, differs from the original only by the Weyl
transport of the torus.  The Dennis–Stein symbol is central, so conjugation leaves it fixed and the
whole discrepancy is carried by the torus factors.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- **The Weyl transport relation for the Dennis–Stein symbol.** -/
theorem dennisStein_weyl_transport {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b : R) (w : Rˣ) (hw : (w : R) = 1 + a * b) :
    dennisStein hij a b w
        * (steinbergWeyl hij 1 * steinbergTorus hij w * (steinbergWeyl hij 1)⁻¹)
      = dennisStein (Ne.symm hij) (-a) (-b) w * steinbergTorus (Ne.symm hij) w := by
  have hconj_ij : ∀ t : R, steinbergWeyl hij 1 * steinbergX hij t * (steinbergWeyl hij 1)⁻¹
      = steinbergX (Ne.symm hij) (-t) := by
    intro t
    have h := steinbergWeyl_conj_self hij hik hjk (1 : Rˣ) t
    simpa using h
  have hconj_ji : ∀ t : R,
      steinbergWeyl hij 1 * steinbergX (Ne.symm hij) t * (steinbergWeyl hij 1)⁻¹
        = steinbergX hij (-t) := by
    intro t
    have h := steinbergWeyl_conj_transpose hij hik hjk (1 : Rˣ) t
    simpa using h
  have hDc := Subgroup.mem_center_iff.1 (dennisStein_mem_center hij a b w hw
    (Ne.symm hik) (Ne.symm hjk))
  have hconjD : steinbergWeyl hij 1 * dennisStein hij a b w * (steinbergWeyl hij 1)⁻¹
      = dennisStein hij a b w := by
    rw [hDc (steinbergWeyl hij 1)]
    group
  have hE := steinbergX_mul_opposite hij a b w
  have hconjE : steinbergWeyl hij 1 * (steinbergX hij a * steinbergX (Ne.symm hij) b)
      * (steinbergWeyl hij 1)⁻¹
      = steinbergX (Ne.symm hij) (-a) * steinbergX hij (-b) := by
    calc steinbergWeyl hij 1 * (steinbergX hij a * steinbergX (Ne.symm hij) b)
          * (steinbergWeyl hij 1)⁻¹
        = (steinbergWeyl hij 1 * steinbergX hij a * (steinbergWeyl hij 1)⁻¹)
          * (steinbergWeyl hij 1 * steinbergX (Ne.symm hij) b * (steinbergWeyl hij 1)⁻¹) := by
          group
      _ = steinbergX (Ne.symm hij) (-a) * steinbergX hij (-b) := by
          rw [hconj_ij, hconj_ji]
  have hleft : steinbergX (Ne.symm hij) (-a) * steinbergX hij (-b)
      = steinbergX hij (-(b * (((w⁻¹ : Rˣ)) : R)))
        * (dennisStein hij a b w
          * (steinbergWeyl hij 1 * steinbergTorus hij w * (steinbergWeyl hij 1)⁻¹))
        * steinbergX (Ne.symm hij) (-((((w⁻¹ : Rˣ)) : R) * a)) := by
    rw [← hconjE, hE]
    calc steinbergWeyl hij 1 * (steinbergX (Ne.symm hij) (b * (((w⁻¹ : Rˣ)) : R))
            * (dennisStein hij a b w * steinbergTorus hij w)
            * steinbergX hij ((((w⁻¹ : Rˣ)) : R) * a)) * (steinbergWeyl hij 1)⁻¹
        = (steinbergWeyl hij 1 * steinbergX (Ne.symm hij) (b * (((w⁻¹ : Rˣ)) : R))
            * (steinbergWeyl hij 1)⁻¹)
          * (steinbergWeyl hij 1 * dennisStein hij a b w * (steinbergWeyl hij 1)⁻¹)
          * (steinbergWeyl hij 1 * steinbergTorus hij w * (steinbergWeyl hij 1)⁻¹)
          * (steinbergWeyl hij 1 * steinbergX hij ((((w⁻¹ : Rˣ)) : R) * a)
            * (steinbergWeyl hij 1)⁻¹) := by group
      _ = steinbergX hij (-(b * (((w⁻¹ : Rˣ)) : R)))
          * (dennisStein hij a b w
            * (steinbergWeyl hij 1 * steinbergTorus hij w * (steinbergWeyl hij 1)⁻¹))
          * steinbergX (Ne.symm hij) (-((((w⁻¹ : Rˣ)) : R) * a)) := by
          rw [hconj_ji, hconjD, hconj_ij]
          group
  have hright : steinbergX (Ne.symm hij) (-a) * steinbergX hij (-b)
      = steinbergX hij (-(b * (((w⁻¹ : Rˣ)) : R)))
        * (dennisStein (Ne.symm hij) (-a) (-b) w * steinbergTorus (Ne.symm hij) w)
        * steinbergX (Ne.symm hij) (-((((w⁻¹ : Rˣ)) : R) * a)) := by
    have hOpp : steinbergX (Ne.symm hij) (-a) * steinbergX hij (-b)
        = steinbergX hij ((-b) * (((w⁻¹ : Rˣ)) : R))
          * (dennisStein (Ne.symm hij) (-a) (-b) w * steinbergTorus (Ne.symm hij) w)
          * steinbergX (Ne.symm hij) ((((w⁻¹ : Rˣ)) : R) * (-a)) :=
      steinbergX_mul_opposite (Ne.symm hij) (-a) (-b) w
    rw [hOpp, neg_mul, mul_neg]
  have hcancel := hleft.symm.trans hright
  exact mul_left_cancel (mul_right_cancel hcancel)

end GaloisForLFunctions.HTGeometry

end
