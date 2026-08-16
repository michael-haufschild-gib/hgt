import GaloisForLFunctions.HTGeometry.DennisSteinScaling

/-!
# The Steinberg symbol as a coboundary of one-variable Dennis–Stein symbols

Every Dennis–Stein symbol whose first argument is `1` is determined by its unit alone:

```text
f(v) := ⟨1, v - 1⟩ ,        since  1 + 1·(v-1) = v .
```

Feeding `a = 1`, `b₁ = w - 1`, `b₂ = (W - 1) w` into the addition relation, and normalising the
second symbol with the scaling relation at `t = w`, turns the addition relation into a statement
about `f` alone:

```text
f(w) · f(W) · [ h_ij(W), h_ik(w) ] · {W, w}⁻¹ = f(w W) .
```

So the Steinberg symbol is the coboundary of the one-variable function `f`, corrected by the
commutator of two torus elements in different index pairs.  Every symbol `{W, w}` — in particular
`{u, 1-u}` — is thereby expressed through a function of a single unit.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- The Dennis–Stein symbol with first argument `1`, as a function of its unit. -/
def dennisSteinUnit {i j : n} (hij : i ≠ j) (v : Rˣ) : SteinbergGroup R n :=
  dennisStein hij 1 ((v : R) - 1) v

/-- The commutator of two torus elements attached to different index pairs. -/
def torusCommutator {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (w t : Rˣ) : SteinbergGroup R n :=
  steinbergTorus hij w * steinbergTorus hik t * (steinbergTorus hij w)⁻¹
    * (steinbergTorus hik t)⁻¹

/-- **The Steinberg symbol is the coboundary of `f(v) = ⟨1, v-1⟩`, up to a torus commutator.** -/
theorem steinbergSymbol_eq_dennisSteinUnit_coboundary {i j k : n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (w W : Rˣ) :
    dennisSteinUnit hij w * (dennisSteinUnit hij W * torusCommutator hij hik W w)
        * (steinbergSymbol hij W w)⁻¹
      = dennisSteinUnit hij (w * W) := by
  have hcw : (((w⁻¹ : Rˣ)) : R) * (w : R) = 1 := w.inv_mul
  have hw₁ : (w : R) = 1 + 1 * ((w : R) - 1) := by ring
  have hW : (W : R) = 1 + (((w⁻¹ : Rˣ)) : R) * 1 * ((((W : R) - 1)) * (w : R)) := by
    linear_combination (-((W : R) - 1)) * hcw
  have hkey := dennisStein_add_right hij hik hjk 1 ((w : R) - 1) (((W : R) - 1) * (w : R)) w W
    hw₁ hW
  have hscale := dennisStein_scale hij hik hjk ((((w⁻¹ : Rˣ)) : R) * 1)
    ((((W : R) - 1)) * (w : R)) W w hW
  have hA : (w : R) * ((((w⁻¹ : Rˣ)) : R) * 1) = 1 := by
    linear_combination hcw
  have hB : (((W : R) - 1) * (w : R)) * (((w⁻¹ : Rˣ)) : R) = (W : R) - 1 := by
    linear_combination ((W : R) - 1) * hcw
  rw [hA, hB] at hscale
  have hsum : ((w : R) - 1) + ((((W : R) - 1)) * (w : R)) = (((w * W : Rˣ)) : R) - 1 := by
    push_cast
    ring
  rw [hsum] at hkey
  rw [hscale] at hkey
  rw [dennisSteinUnit, dennisSteinUnit, dennisSteinUnit, torusCommutator]
  exact hkey

end GaloisForLFunctions.HTGeometry

end
