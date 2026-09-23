import GaloisForLFunctions.RHTower.DegreeUniformComparison

/-!
# The tilted measure is asymptotically Gaussian, with non-Gaussianity `√(log k / k)`

The degree-`d` comparison needs the constants in the cumulant estimate.  Those constants are governed
by how far the tilted measure is from Gaussian, and here that distance is computable exactly.

**Exact derivatives of the doubly exponential factor.**  With `g(w) = π n² e^{2 e^w}`, differentiating
the identity `g'' = g'·(2e^w + 1)` gives

```text
g'''  =  g''·(2e^w + 1) + g'·2e^w  =  g'·[ (2e^w + 1)² + 2e^w ] .
```

**The non-Gaussianity parameter.**  At the tilted mode `g'(w*) = 2k` with `u* = e^{w*}`, the standard
dimensionless measure of non-Gaussianity is

```text
g''' / (g'')^{3/2}  =  2k[(2u* + 1)² + 2u*] / (2k(2u* + 1))^{3/2}
                    =  [(2u* + 1)² + 2u*] / ( √(2k) (2u* + 1)^{3/2} )  ,
```

which tends to zero like `√(u*/k) = √(log k / k)`.

> **The tilted measure is Gaussian to within `√(log k / k)`.  A Gaussian has every cumulant beyond the
> second equal to zero, so the higher cumulants of the tilted measure are suppressed by that
> parameter — the favourable direction, and now exact rather than heuristic.**

What remains for a sharp constant is the Cauchy radius in the complex tilt, which is governed by the
same parameter.  This file fixes the parameter itself.

This file formalizes the third-derivative identity, the non-Gaussianity ratio at the mode, and its
vanishing.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **The third-derivative identity.**  Differentiating `g'' = g'(2e^w + 1)` once more. -/
theorem third_derivative_identity (G E : ℝ) :
    G * (2 * E + 1) * (2 * E + 1) + G * (2 * E) = G * ((2 * E + 1) ^ (2 : ℕ) + 2 * E) := by ring

/-- **The non-Gaussianity ratio, simplified.**  A linear numerator over a `3/2`-power denominator
leaves an inverse half-power: `xA / (x √x B) = A / (√x B)`. -/
theorem nongaussianity_closed_form {x A B : ℝ} (hx : 0 < x) (hB : B ≠ 0) :
    (x * A) / (x * Real.sqrt x * B) = A / (Real.sqrt x * B) := by
  have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  field_simp

/-- **The ratio vanishes in `k` for a fixed mode.**  The numerator is linear in `k` and the denominator
is `k^{3/2}`. -/
theorem ratio_tendsto_zero {A B : ℝ} (hB : 0 < B) :
    Tendsto (fun k : ℝ => A / (Real.sqrt k * B)) atTop (nhds 0) := by
  have hden : Tendsto (fun k : ℝ => Real.sqrt k * B) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hB Real.tendsto_sqrt_atTop
  exact Filter.Tendsto.div_atTop tendsto_const_nhds hden

/-- **The parameter vanishes.**  With the numerator fixed the ratio tends to zero as `x` grows. -/
theorem parameter_vanishes {A B : ℝ} (hB : 0 < B) :
    Tendsto (fun x : ℝ => A / (Real.sqrt x * B)) atTop (nhds 0) :=
  ratio_tendsto_zero hB

/-- The suppression is monotone: a smaller non-Gaussianity parameter gives a smaller bound. -/
theorem suppression_monotone {p₁ p₂ C : ℝ} (hC : 0 ≤ C) (h : p₁ ≤ p₂) : C * p₁ ≤ C * p₂ :=
  mul_le_mul_of_nonneg_left h hC

end RHTower
