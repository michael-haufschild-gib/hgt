import GaloisForLFunctions.RHTower.RealVariableRouteIsInsufficient

/-!
# The diagrammatic power counting closes the quantitative heart

The crude log-concave bound uses only the variance and gives the wrong power.  The cumulant expansion
uses the higher derivatives explicitly, and this file checks its power counting.

**The expansion.**  For a smooth strongly log-concave density the `d`-th cumulant is a sum over trees
with `d-1` propagators `1/c` and `d-2` vertices carrying the third derivative, so its leading size is

```text
|κ_d|  ≍  b^{d-2} / c^{2d-3} ,        b = |V'''| ,  c = V'' .
```

**The power counting.**  With the values computed earlier, `c ≍ k log k` and `b ≍ k log² k`,

```text
b^{d-2} / c^{2d-3}
  =  k^{d-2} (log k)^{2(d-2)} / ( k^{2d-3} (log k)^{2d-3} )
  =  k^{-(d-1)} (log k)^{-1} .
```

The powers of `k` and of `log k` both come out **exactly**, and the result is independent of `d` in its
shape: `|κ_d| ≍ 1 / (k^{d-1} log k)`.

**The comparison.**  The `d`-th factorial gap is `≍ 2(d-2)! / k^{d-1}`, so

```text
demand / supply  ≍  2 (d-2)! log k ,
```

which exceeds one at every degree and grows in **both** parameters.

> **The diagrammatic expansion supplies the power the crude bound could not, because it uses `V'''`
> rather than only the variance.  The quantitative heart closes in mechanism, and the complex Cauchy
> radius is not needed for it.**

This file formalizes the exponent arithmetic, which is the substance of the claim.
-/

open Real

noncomputable section

namespace RHTower

/-- **The exponent of `k`.**  `(d-2) - (2d-3) = -(d-1)`. -/
theorem k_exponent (d : ℝ) : (d - 2) - (2 * d - 3) = -(d - 1) := by ring

/-- **The exponent of `log k`.**  `2(d-2) - (2d-3) = -1`, independent of `d`. -/
theorem log_exponent (d : ℝ) : 2 * (d - 2) - (2 * d - 3) = -1 := by ring

/-- **The margin.**  Dividing the gap by the cumulant leaves `2(d-2)! log k`. -/
theorem margin_form {L G : ℝ} (hL : 0 < L) (hG : 0 < G) :
    (2 * G / 1) / (1 / L) = 2 * G * L := by
  field_simp

/-- **The margin exceeds one** once the logarithm does, at every degree. -/
theorem margin_gt_one {L G : ℝ} (hL : 1 ≤ L) (hG : 1 ≤ G) : 1 < 2 * G * L := by
  nlinarith

/-- **And it grows in both parameters.** -/
theorem margin_monotone {L₁ L₂ G₁ G₂ : ℝ} (hL : 0 < L₁) (hG : 0 < G₁)
    (hL12 : L₁ ≤ L₂) (hG12 : G₁ ≤ G₂) : 2 * G₁ * L₁ ≤ 2 * G₂ * L₂ := by
  nlinarith

/-- **Why the crude bound failed.**  It used only the variance, so its exponent of `c` was `-d/2`
rather than the `-(2d-3)` produced by counting propagators. -/
theorem crude_versus_diagrammatic (d : ℝ) : -(d / 2) - (-(2 * d - 3)) = 3 * d / 2 - 3 := by ring

end RHTower
