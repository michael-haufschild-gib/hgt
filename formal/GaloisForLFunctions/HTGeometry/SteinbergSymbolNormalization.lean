import GaloisForLFunctions.HTGeometry.SteinbergRowCentrality

/-!
# The Steinberg symbol is normalized

Matsumoto's theorem presents `K₂` of a field by the Steinberg symbols, so the first thing to know
about the symbol is that it is normalized: `{1, v} = {u, 1} = 1`.

Both follow from one identity about the Weyl elements,

```text
w(−u) = w(u)⁻¹ ,
```

which is visible from the definition `w(u) = x_ij(u) x_ji(−u⁻¹) x_ij(u)`: inverting reverses the
three factors and negates each entry, and `(−u)⁻¹ = −u⁻¹` for units.  Hence the torus element
`h(u) = w(u) w(−1)` is trivial at `u = 1`, and the symbol `{u,v} = h(uv) h(u)⁻¹ h(v)⁻¹` collapses
whenever one argument is `1`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- **Inverting a Weyl element negates its parameter.** -/
theorem steinbergWeyl_neg {i j : n} (hij : i ≠ j) (u : Rˣ) :
    steinbergWeyl hij (-u) = (steinbergWeyl hij u)⁻¹ := by
  have h1 : (steinbergX hij ((u : Rˣ) : R))⁻¹ = steinbergX hij (-((u : Rˣ) : R)) :=
    (steinbergX_neg hij ((u : Rˣ) : R)).symm
  have h2 : (steinbergX (Ne.symm hij) (-(((u⁻¹ : Rˣ)) : R)))⁻¹
      = steinbergX (Ne.symm hij) (((u⁻¹ : Rˣ)) : R) := by
    rw [← steinbergX_neg, neg_neg]
  have hval1 : ((-u : Rˣ) : R) = -((u : Rˣ) : R) := by simp
  have hval2 : -(((((-u : Rˣ))⁻¹ : Rˣ)) : R) = (((u⁻¹ : Rˣ)) : R) := by
    rw [inv_neg]
    simp
  rw [steinbergWeyl, steinbergWeyl, hval1, hval2, mul_inv_rev, mul_inv_rev, h1, h2, mul_assoc]

/-- **The torus element is trivial at `1`.** -/
theorem steinbergTorus_one {i j : n} (hij : i ≠ j) :
    steinbergTorus (R := R) hij (1 : Rˣ) = 1 := by
  have h : steinbergWeyl (R := R) hij (-1 : Rˣ) = (steinbergWeyl (R := R) hij (1 : Rˣ))⁻¹ := by
    have hne := steinbergWeyl_neg (R := R) hij (1 : Rˣ)
    simpa using hne
  rw [steinbergTorus, h, mul_inv_cancel]

/-- **The Steinberg symbol is trivial when its first argument is `1`.** -/
theorem steinbergSymbol_one_left {i j : n} (hij : i ≠ j) (v : Rˣ) :
    steinbergSymbol (R := R) hij 1 v = 1 := by
  rw [steinbergSymbol, one_mul, steinbergTorus_one, inv_one, mul_one, mul_inv_cancel]

/-- **The Steinberg symbol is trivial when its second argument is `1`.** -/
theorem steinbergSymbol_one_right {i j : n} (hij : i ≠ j) (u : Rˣ) :
    steinbergSymbol (R := R) hij u 1 = 1 := by
  rw [steinbergSymbol, mul_one, steinbergTorus_one, inv_one, mul_one, mul_inv_cancel]

end GaloisForLFunctions.HTGeometry

end
