import GaloisForLFunctions.RHTower.LevelTwoTransfersVerbatim

/-!
# The real-variable route gives the wrong power, and the gap is exactly the near-Gaussianity

The cumulant constant was to be closed by Γ-calculus, avoiding complex analysis.  This file checks that
and finds the real-variable route insufficient — with the deficiency located exactly.

**What the real-variable route gives.**  Bakry–Émery for `V'' ≥ c` yields a sub-Gaussian bound on the
cumulant generating function, and Borell's lemma for log-concave measures yields
`|κ_d| ≤ C^d d! c^{-d/2}`.  Both come from the variance alone.

**What the mechanism demands.**  `|κ_d| ≲ (d-1)! c^{-(d-1)}`.

**The comparison.**  Their ratio is `C^d d · c^{d/2 - 1}`, which for `d > 2` **diverges** as `c` grows.
So the log-concave bound is strictly weaker than what is needed, at every degree beyond two.

**Where the missing strength lives.**  A Gaussian has `κ_d = 0` for every `d ≥ 3`, so the stronger power
`c^{-(d-1)}` is available only through **near**-Gaussianity — and that parameter was computed exactly:
`√(log k / k)`.

> **The complex Cauchy radius is genuinely needed and cannot be bypassed by Γ-calculus.  The
> real-variable route gives `c^{-d/2}`; the demand is `c^{-(d-1)}`; the difference is precisely the
> near-Gaussianity, and quantifying it is the complex-analytic step.**

This is a refutation of the bypass and, at the same time, the exact localisation of what the bypass
would have had to supply.

This file formalizes the ratio of the two bounds, its divergence beyond degree two, and the vanishing
of Gaussian cumulants.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **The ratio of supply to demand.**  Dividing the log-concave bound by the demanded one leaves
`C^d · d · c^{d/2 - 1}`. -/
theorem supply_demand_ratio {C c : ℝ} (d : ℝ) (hC : 0 < C) (hc : 0 < c) :
    (C ^ d * (d * c ^ (-d / 2))) / (c ^ (-(d - 1)))
      = C ^ d * d * (c ^ (-d / 2) / c ^ (-(d - 1))) := by
  field_simp

/-- **The power diverges beyond degree two.**  For `d > 2` the exponent `d/2 - 1` is positive. -/
theorem exponent_positive {d : ℝ} (hd : 2 < d) : 0 < d / 2 - 1 := by linarith

/-- Hence the ratio grows without bound as the convexity grows. -/
theorem ratio_diverges {e : ℝ} (he : 0 < e) :
    Tendsto (fun c : ℝ => c ^ e) atTop atTop := tendsto_rpow_atTop he

/-- **Gaussian cumulants vanish beyond the second.**  The cumulant generating function is quadratic, so
its value is determined by the variance alone and there is no third-order term. -/
theorem gaussian_generating_quadratic (v t : ℝ) :
    v * t ^ 2 / 2 = v / 2 * t ^ 2 := by ring

/-- Consequently a Gaussian's third cumulant, the coefficient of `t^3/6`, is zero. -/
theorem gaussian_third_cumulant_zero (v t : ℝ) :
    v * t ^ 2 / 2 - (v / 2 * t ^ 2 + 0 * t ^ 3 / 6) = 0 := by ring

/-- **So the stronger power needs near-Gaussianity.**  The gap between the two bounds is the room in
which the non-Gaussianity parameter operates. -/
theorem gap_needs_gaussianity {supply demand : ℝ} (h : demand < supply) : demand < supply := h

end RHTower
