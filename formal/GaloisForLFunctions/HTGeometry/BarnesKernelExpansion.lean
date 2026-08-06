import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The removable singularity of the Barnes cone kernel at the origin

The Mellin representation of the Barnes double zeta,

```text
Γ(s) ζ₂(s, x) = ∫_0^∞ t^(s-1) e^(-x t) / ((1 - e^(-ω₁ t))(1 - e^(-ω₂ t))) dt,
```

converges only for `Re s > 2`, because the kernel has a pole of order two at `t = 0`.  Continuing
past `s = 2` means subtracting the singular part, and that requires knowing that

```text
t² · e^(-x t) / ((1 - e^(-ω₁ t))(1 - e^(-ω₂ t)))
```

extends across `t = 0`.  The whole point is one factor: `z / (1 - e^(-ω z))` has a removable
singularity at the origin with value `1/ω`, because the denominator vanishes to first order there.

`hasDerivAt_one_sub_exp_neg_mul` is that first-order vanishing, and
`tendsto_div_one_sub_exp_neg_mul` is the resulting limit, obtained by reading the reciprocal of the
difference quotient — the division-by-zero convention makes `(slope)⁻¹` equal `z / (1 - e^(-ω z))`
identically, so no case split on the denominator is needed.
-/

open Complex Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The denominator of the cylinder kernel vanishes to first order at the origin. -/
theorem hasDerivAt_one_sub_exp_neg_mul (o : ℂ) :
    HasDerivAt (fun z : ℂ => 1 - Complex.exp (-(o * z))) o 0 := by
  have hlin : HasDerivAt (fun z : ℂ => -(o * z)) (-o) 0 := by
    have h0 : HasDerivAt (fun z : ℂ => (-o) * z) (-o) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (-o)
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards with z
    ring
  have hexp := hlin.cexp
  have h := hexp.const_sub (1 : ℂ)
  simpa using h

@[simp] theorem one_sub_exp_neg_mul_zero (o : ℂ) :
    (fun z : ℂ => 1 - Complex.exp (-(o * z))) 0 = 0 := by
  simp

/-- **The kernel factor has a removable singularity at the origin.**  As `z → 0`,

```text
z / (1 - e^(-ω z)) → 1/ω,
```

which is why `t² F(t)` extends continuously across `t = 0` for the two-dimensional cone kernel. -/
theorem tendsto_div_one_sub_exp_neg_mul {o : ℂ} (ho : o ≠ 0) :
    Tendsto (fun z : ℂ => z / (1 - Complex.exp (-(o * z)))) (𝓝[≠] (0 : ℂ)) (𝓝 o⁻¹) := by
  have hslope : Tendsto (slope (fun z : ℂ => 1 - Complex.exp (-(o * z))) 0) (𝓝[≠] (0 : ℂ))
      (𝓝 o) := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_one_sub_exp_neg_mul o)
  have hinv := hslope.inv₀ ho
  refine hinv.congr fun z => ?_
  rw [slope_def_field]
  simp only [mul_zero, neg_zero, Complex.exp_zero, sub_self, sub_zero]
  rw [inv_div]

end

end GaloisForLFunctions.HTGeometry
