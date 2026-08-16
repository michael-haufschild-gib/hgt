import GaloisForLFunctions.HTGeometry.SteinbergTransportMoves

/-!
# Scaling the arguments of a Dennis–Stein symbol

Conjugating the defining word of `⟨a,b⟩` by the torus element `h_ik(t)` of a *different* index pair
scales the two arguments oppositely,

```text
x_ij(s) ↦ x_ij(t s) ,       x_ji(s) ↦ x_ji(s t⁻¹) ,
```

and leaves the unit `1 + ab = 1 + (ta)(bt⁻¹)` unchanged.  The symbol is central, so it is fixed by
the conjugation, and the whole discrepancy is the commutator of the two torus elements:

```text
⟨a, b⟩ = ⟨t a, b t⁻¹⟩ · [ h_ij(w), h_ik(t) ] ,        w = 1 + a b .
```

In particular, when `b` is a unit the choice `t = b` normalises the second argument to `1`:

```text
⟨a, b⟩ = ⟨b a, 1⟩ · [ h_ij(w), h_ik(b) ] .
```

Both torus elements commute in the matrix group, so the commutator lies in `K₂`; the relation says
that the entire dependence of `⟨a,b⟩` on the splitting of the product `ab` between its two arguments
is carried by that one commutator.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- **The scaling relation for the Dennis–Stein symbol.** -/
theorem dennisStein_scale {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b : R) (w t : Rˣ) (hw : (w : R) = 1 + a * b) :
    dennisStein hij a b w
      = dennisStein hij ((t : R) * a) (b * (((t⁻¹ : Rˣ)) : R)) w
        * (steinbergTorus hij w * steinbergTorus hik t * (steinbergTorus hij w)⁻¹
            * (steinbergTorus hik t)⁻¹) := by
  have hkj : k ≠ j := Ne.symm hjk
  have hrow : ∀ s : R, steinbergTorus hik t * steinbergX hij s * (steinbergTorus hik t)⁻¹
      = steinbergX hij ((t : R) * s) := fun s =>
    steinbergTorus_conj_first hik hij hkj t s
  have hcol : ∀ s : R,
      steinbergTorus hik t * steinbergX (Ne.symm hij) s * (steinbergTorus hik t)⁻¹
        = steinbergX (Ne.symm hij) (s * (((t⁻¹ : Rˣ)) : R)) := fun s =>
    steinbergTorus_conj_col hik hij hkj t s
  have hDc := Subgroup.mem_center_iff.1 (dennisStein_mem_center hij a b w hw
    (Ne.symm hik) (Ne.symm hjk))
  have hconjD : steinbergTorus hik t * dennisStein hij a b w * (steinbergTorus hik t)⁻¹
      = dennisStein hij a b w := by
    rw [hDc (steinbergTorus hik t)]
    group
  have hfour : steinbergX (Ne.symm hij) (-(b * (((w⁻¹ : Rˣ)) : R)) * (((t⁻¹ : Rˣ)) : R))
      * steinbergX hij ((t : R) * a)
      * steinbergX (Ne.symm hij) (b * (((t⁻¹ : Rˣ)) : R))
      * steinbergX hij ((t : R) * (-((((w⁻¹ : Rˣ)) : R) * a)))
      = dennisStein hij ((t : R) * a) (b * (((t⁻¹ : Rˣ)) : R)) w * steinbergTorus hij w := by
    have e1 : -(b * (((w⁻¹ : Rˣ)) : R)) * (((t⁻¹ : Rˣ)) : R)
        = -((b * (((t⁻¹ : Rˣ)) : R)) * (((w⁻¹ : Rˣ)) : R)) := by ring
    have e2 : (t : R) * (-((((w⁻¹ : Rˣ)) : R) * a))
        = -((((w⁻¹ : Rˣ)) : R) * ((t : R) * a)) := by ring
    rw [e1, e2, dennisStein]
    group
  calc dennisStein hij a b w
      = steinbergTorus hik t * dennisStein hij a b w * (steinbergTorus hik t)⁻¹ := hconjD.symm
    _ = (steinbergTorus hik t
            * steinbergX (Ne.symm hij) (-(b * (((w⁻¹ : Rˣ)) : R))) * (steinbergTorus hik t)⁻¹)
        * (steinbergTorus hik t * steinbergX hij a * (steinbergTorus hik t)⁻¹)
        * (steinbergTorus hik t * steinbergX (Ne.symm hij) b * (steinbergTorus hik t)⁻¹)
        * (steinbergTorus hik t * steinbergX hij (-((((w⁻¹ : Rˣ)) : R) * a))
            * (steinbergTorus hik t)⁻¹)
        * (steinbergTorus hik t * (steinbergTorus hij w)⁻¹ * (steinbergTorus hik t)⁻¹) := by
        rw [dennisStein]
        group
    _ = steinbergX (Ne.symm hij) (-(b * (((w⁻¹ : Rˣ)) : R)) * (((t⁻¹ : Rˣ)) : R))
        * steinbergX hij ((t : R) * a)
        * steinbergX (Ne.symm hij) (b * (((t⁻¹ : Rˣ)) : R))
        * steinbergX hij ((t : R) * (-((((w⁻¹ : Rˣ)) : R) * a)))
        * (steinbergTorus hik t * (steinbergTorus hij w)⁻¹ * (steinbergTorus hik t)⁻¹) := by
        rw [hcol, hrow, hcol, hrow]
    _ = (dennisStein hij ((t : R) * a) (b * (((t⁻¹ : Rˣ)) : R)) w * steinbergTorus hij w)
        * (steinbergTorus hik t * (steinbergTorus hij w)⁻¹ * (steinbergTorus hik t)⁻¹) := by
        rw [hfour]
    _ = dennisStein hij ((t : R) * a) (b * (((t⁻¹ : Rˣ)) : R)) w
        * (steinbergTorus hij w * steinbergTorus hik t * (steinbergTorus hij w)⁻¹
            * (steinbergTorus hik t)⁻¹) := by group

/-- **Normalising the second argument to `1`** when it is a unit. -/
theorem dennisStein_normalize_right {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a : R) (b w : Rˣ) (hw : (w : R) = 1 + a * (b : R)) :
    dennisStein hij a (b : R) w
      = dennisStein hij ((b : R) * a) 1 w
        * (steinbergTorus hij w * steinbergTorus hik b * (steinbergTorus hij w)⁻¹
            * (steinbergTorus hik b)⁻¹) := by
  have h := dennisStein_scale hij hik hjk a (b : R) w b hw
  have hval : (b : R) * (((b⁻¹ : Rˣ)) : R) = 1 := b.mul_inv
  rwa [hval] at h

end GaloisForLFunctions.HTGeometry

end
