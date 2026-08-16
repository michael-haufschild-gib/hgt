import GaloisForLFunctions.HTGeometry.DennisSteinAddRight

/-!
# The inverse relation for Dennis–Stein symbols

Taking `b₂ = -b₁` in the addition relation collapses the right-hand side, because `⟨a,0⟩ = 1` and
`w · W = 1 + a(b - b) = 1`.  What survives is

```text
⟨a, b⟩ · ⟨w⁻¹ a, -b⟩  =  {w⁻¹, w} ,        w = 1 + a b ,
```

so the two Dennis–Stein symbols obtained from `b` and `-b` are inverse to each other up to a single
torus symbol, and that symbol is the failure of `h` to invert:

```text
{w⁻¹, w} = (h(w) · h(w⁻¹))⁻¹ .
```

The second argument of the symbol therefore behaves like an additive parameter whose sign reversal
costs exactly one unit of the multiplicative obstruction.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

omit [DecidableEq n] [Fintype n] in
/-- **The symbol at an inverse pair measures the failure of `h` to invert.** -/
theorem steinbergSymbol_inv_left {i j : n} (hij : i ≠ j) (w : Rˣ) :
    steinbergSymbol hij w⁻¹ w = (steinbergTorus hij w * steinbergTorus hij w⁻¹)⁻¹ := by
  have h := steinbergTorus_mul hij w⁻¹ w
  rw [inv_mul_cancel, steinbergTorus_one] at h
  have h' : steinbergSymbol hij w⁻¹ w
      * (steinbergTorus hij w * steinbergTorus hij w⁻¹) = 1 := by
    rw [← mul_assoc]
    exact h.symm
  calc steinbergSymbol hij w⁻¹ w
      = steinbergSymbol hij w⁻¹ w * (steinbergTorus hij w * steinbergTorus hij w⁻¹)
        * (steinbergTorus hij w * steinbergTorus hij w⁻¹)⁻¹ := by group
    _ = (steinbergTorus hij w * steinbergTorus hij w⁻¹)⁻¹ := by rw [h', one_mul]

/-- **The Dennis–Stein inverse relation.** -/
theorem dennisStein_neg_right {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b : R) (w : Rˣ) (hw : (w : R) = 1 + a * b) :
    dennisStein hij a b w * dennisStein hij ((((w⁻¹ : Rˣ)) : R) * a) (-b) w⁻¹
      = steinbergSymbol hij w⁻¹ w := by
  have hcw : (((w⁻¹ : Rˣ)) : R) * (w : R) = 1 := w.inv_mul
  have hW : (((w⁻¹ : Rˣ)) : R) = 1 + (((w⁻¹ : Rˣ)) : R) * a * (-b) := by
    linear_combination hcw - (((w⁻¹ : Rˣ)) : R) * hw
  have hkey := dennisStein_add_right hij hik hjk a b (-b) w w⁻¹ hw hW
  rw [add_neg_cancel] at hkey
  have hunit : w * w⁻¹ = (1 : Rˣ) := mul_inv_cancel w
  rw [hunit, dennisStein_right_zero] at hkey
  rw [mul_inv_eq_one] at hkey
  exact hkey

/-- The inverse relation in the form of a single vanishing product. -/
theorem dennisStein_neg_right_torus {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b : R) (w : Rˣ) (hw : (w : R) = 1 + a * b) :
    steinbergTorus hij w * steinbergTorus hij w⁻¹
        * (dennisStein hij a b w * dennisStein hij ((((w⁻¹ : Rˣ)) : R) * a) (-b) w⁻¹) = 1 := by
  rw [dennisStein_neg_right hij hik hjk a b w hw, steinbergSymbol_inv_left, mul_inv_cancel]

end GaloisForLFunctions.HTGeometry

end
