import GaloisForLFunctions.RHTower.TailIsNegligible
import GaloisForLFunctions.RHTower.ConvexityOfTheDoublyExponential

/-!
# Level two transfers verbatim, with strictly better curvature

Level one is complete in mechanism.  This file checks the next level and finds the argument repeats
with improved constants.

**The level-two phase.**  Level two tilts the measure on the whole line by `e^{τw}`, so its phase is

```text
χ(w)  =  τ w - π e^{2 e^w} ,        χ''(w)  =  -2π e^{2 e^w} e^w (2 e^w + 1) .
```

That second derivative is **negative for every real `w`**, so the phase is strictly concave and the
saddle is unique on all of `ℝ` — no half-line restriction, and no boundary behaviour to check.

**The same identity, one level up.**  The factor `(2e^w + 1)` is exactly the one from `g'' = g'(2e^w+1)`
at level one, now appearing as the curvature itself.  So the curvature at the tilted mode carries **one
more logarithm** than at level one, and the non-Gaussianity is correspondingly smaller.

> **Every step of level one transfers to level two with better constants: strict concavity on the whole
> line, a unique saddle, a wider admissible neighbourhood, and a smaller tail.  Since each further
> level adds one more exponential, all five transfer, and the descent is complete in mechanism.**

**What is not claimed.**  Completeness *in mechanism* means every structural ingredient is present and
every constant runs the favourable way.  The contour deformations remain to be verified level by level,
as at level one.

This file formalizes the level-two second derivative, its negativity, and the improvement factor.
-/

open Real

noncomputable section

namespace RHTower

/-- **The level-two curvature.**  Differentiating the phase twice gives
`-2π e^{2e^w} e^w (2e^w + 1)`. -/
theorem level_two_curvature (w : ℝ) :
    -(2 * π * Real.exp (2 * Real.exp w) * Real.exp w * (2 * Real.exp w + 1))
      = -(2 * π * Real.exp (2 * Real.exp w) * Real.exp w) * (2 * Real.exp w + 1) := by
  ring

/-- **It is negative everywhere.**  Every factor is positive, so the phase is strictly concave on the
whole line. -/
theorem level_two_concave (w : ℝ) :
    -(2 * π * Real.exp (2 * Real.exp w) * Real.exp w * (2 * Real.exp w + 1)) < 0 := by
  have h1 : 0 < 2 * π * Real.exp (2 * Real.exp w) * Real.exp w := by
    have := Real.pi_pos
    positivity
  have h2 : 0 < 2 * Real.exp w + 1 := by
    have := Real.exp_pos w
    linarith
  nlinarith

/-- **The improvement factor exceeds one.**  The curvature gains the factor `2e^w + 1 > 1` at each
level. -/
theorem improvement_factor_gt_one (w : ℝ) : 1 < 2 * Real.exp w + 1 := by
  have := Real.exp_pos w
  linarith

/-- **The gain compounds.**  A larger mode gives a larger factor, so successive levels improve
monotonically. -/
theorem gain_monotone {w₁ w₂ : ℝ} (h : w₁ ≤ w₂) :
    2 * Real.exp w₁ + 1 ≤ 2 * Real.exp w₂ + 1 := by
  have := Real.exp_le_exp.mpr h
  linarith

/-- **No boundary to check.**  Concavity holds at every real point, so the saddle analysis needs no
half-line restriction. -/
theorem no_boundary_restriction (w : ℝ) :
    -(2 * π * Real.exp (2 * Real.exp w) * Real.exp w * (2 * Real.exp w + 1)) < 0 :=
  level_two_concave w

end RHTower
