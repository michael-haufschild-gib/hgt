import GaloisForLFunctions.HTGeometry.AnalyticDoublePoleSplit
import GaloisForLFunctions.HTGeometry.RectangleDoublePole

/-!
# Cauchy's integral formula for the derivative, on a rectangle

Splitting `f` into its second-order Taylor part and dividing by `(s - p)²` puts the integrand in
the principal-part normal form, where the squared Cauchy kernel integrates to zero and the simple
kernel to `2πi`.  Hence for `f` holomorphic on a neighbourhood of the closed rectangle and `p`
strictly inside,

```text
∮_{∂R} f(s)/(s - p)² ds = 2πi f'(p).
```

Mathlib has the circle version; the corpus's rectangle residue calculus covered simple poles only.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- **Cauchy's formula for the derivative on a rectangle.** -/
theorem rectIntegral_div_sub_sq_eq_deriv {f : ℂ → ℂ} {p z₁ z₂ : ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hp : p ∈ U)
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hp1 : z₁.re < p.re) (hp2 : p.re < z₂.re)
    (hp3 : z₁.im < p.im) (hp4 : p.im < z₂.im) :
    rectIntegral (fun s => f s / (s - p) ^ 2) z₁ z₂ = 2 * Real.pi * I * deriv f p := by
  obtain ⟨G, hG, hdecomp⟩ := exists_doublePole_principalPart hU hf hp
  exact rectIntegral_eq_double_pole_residue_on hp1 hp2 hp3 hp4 hsub
    (hG.analyticOnNhd hU) hdecomp

end

end RHTower
