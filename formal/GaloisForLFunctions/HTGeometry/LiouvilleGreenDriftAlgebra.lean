import Mathlib

/-!
# The normal-form contribution of a comparison drift

A Liouville–Green comparison model `V = I(cΞ)` (or `J(cΞ)`) solves an equation whose first-order
coefficient is

```text
B = Ξ'/Ξ − Ξ''/Ξ' ,
```

and passing to normal form replaces it by `B²/4 + B'/2`.  Writing `D = Ξ''/Ξ'`, so that
`Ξ'' = Ξ'·D`, that combination collapses:

```text
B²/4 + B'/2 = −(Ξ')²/(4Ξ²) + D²/4 − D'/2 ,
```

the cross terms `Ξ'D/Ξ` cancelling identically.  The point is what is *absent*: no `Ξ''/Ξ` survives,
so the model's normal-form potential is built from `Ξ'/Ξ` and from `D` alone.

For the prolate band `D` is a rational function of `y` — the square root of the WKB profile cancels
out of `Ξ''/Ξ'` — so the only transcendental ingredient left in the comparison is `(Ξ')²/Ξ², and the
leading `(1−y)^{−2}` singularities of the four terms cancel against the true normal form.  That
cancellation is what makes the comparison defect `O(1)` rather than `O(c²)`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {Ξ Ξ' Ξ'' D D' : ℝ → ℝ} {y : ℝ}

/-- The first-order coefficient of a Liouville–Green comparison equation. -/
def lgDrift (Ξ Ξ' D : ℝ → ℝ) (y : ℝ) : ℝ := Ξ' y / Ξ y - D y

theorem hasDerivAt_lgDrift (hΞ : HasDerivAt Ξ (Ξ' y) y) (hΞ' : HasDerivAt Ξ' (Ξ'' y) y)
    (hD : HasDerivAt D (D' y) y) (hΞ0 : Ξ y ≠ 0) :
    HasDerivAt (lgDrift Ξ Ξ' D)
      (Ξ'' y / Ξ y - Ξ' y ^ 2 / Ξ y ^ 2 - D' y) y := by
  have hquot : HasDerivAt (fun t => Ξ' t / Ξ t)
      ((Ξ'' y * Ξ y - Ξ' y * Ξ' y) / Ξ y ^ 2) y := HasDerivAt.fun_div hΞ' hΞ hΞ0
  have h := hquot.sub hD
  refine h.congr_deriv ?_
  field_simp

/-- **The normal-form contribution of the drift.**  With `Ξ'' = Ξ'·D` the cross terms cancel and no
`Ξ''/Ξ` survives. -/
theorem lgDrift_normalForm (hΞ0 : Ξ y ≠ 0) (hrel : Ξ'' y = Ξ' y * D y) :
    lgDrift Ξ Ξ' D y ^ 2 / 4 + (Ξ'' y / Ξ y - Ξ' y ^ 2 / Ξ y ^ 2 - D' y) / 2
      = -(Ξ' y ^ 2 / (4 * Ξ y ^ 2)) + D y ^ 2 / 4 - D' y / 2 := by
  rw [lgDrift, hrel]
  field_simp
  ring

/-- The same, packaged with the derivative statement. -/
theorem lgDrift_normalForm_of_hasDerivAt
    (hΞ : HasDerivAt Ξ (Ξ' y) y) (hΞ' : HasDerivAt Ξ' (Ξ'' y) y)
    (hD : HasDerivAt D (D' y) y) (hΞ0 : Ξ y ≠ 0) (hrel : Ξ'' y = Ξ' y * D y) :
    ∃ B' : ℝ, HasDerivAt (lgDrift Ξ Ξ' D) B' y ∧
      lgDrift Ξ Ξ' D y ^ 2 / 4 + B' / 2
        = -(Ξ' y ^ 2 / (4 * Ξ y ^ 2)) + D y ^ 2 / 4 - D' y / 2 :=
  ⟨Ξ'' y / Ξ y - Ξ' y ^ 2 / Ξ y ^ 2 - D' y,
    hasDerivAt_lgDrift hΞ hΞ' hD hΞ0, lgDrift_normalForm hΞ0 hrel⟩

end GaloisForLFunctions.HTGeometry
