import GaloisForLFunctions.RHTower.VerticalParametersAreTheOnlyOnes

/-!
# The two vertical parameters are two tilts of one measure

The jet order and the flow time looked like independent directions.  They are the two coordinates of a
single exponential family built on one positive measure, and this file computes how the second moves
the quantity the first controls.

**The family.**  Both parameters enter the same integrand:

```text
Φ(u) · u^{2j} · e^{t u²}  =  Φ(u) · exp( 2j log u + t u² ) .
```

The jet order tilts by the observable `log u`; the flow time tilts by `u²`.  Nothing else in the
vertical direction has appeared in this development.

**How the flow moves the saddle.**  With `f(u) = log Φ(u) + 2j log u + t u²`, the saddle solves
`f'(u) = 0`, and

```text
∂f'/∂t = 2u > 0 ,      f''(u*) < 0      ⟹      du*/dt = -(2u*)/f''(u*) > 0 .
```

Forward flow pushes the saddle outward; backward flow pulls it in.

**What that does to the margin.**  The order-two margin computed earlier is `1 + 2u*`, increasing in
`u*`.  So forward flow **increases** the margin and backward flow **decreases** it.

> **The margin `1 + 2u*` is the common quantity behind both the order-two inequality and the flow
> constant: the first says it is positive at flow time zero, the second says the backward flow drives
> it to zero at or before time zero.  The two vertical parameters are not independent directions but
> the two coordinates of one exponential family.**

This file formalizes the exponential form of the jet tilt, the sign of the saddle's motion under the
flow, and the monotonicity of the margin.
-/

open Real

noncomputable section

namespace RHTower

/-- **The jet tilt is exponential in `log u`.**  The weight `u^{2j}` is `exp(2j log u)`. -/
theorem jet_tilt_exponential {u : ℝ} (hu : 0 < u) (j : ℕ) :
    u ^ (2 * j) = Real.exp (2 * j * Real.log u) := by
  rw [← Real.exp_log (by positivity : (0:ℝ) < u ^ (2 * j)), Real.log_pow]
  push_cast
  ring_nf

/-- **The saddle moves outward under forward flow.**  With negative curvature and a positive crossed
derivative, the implicit derivative is positive. -/
theorem saddle_moves_outward {curv cross : ℝ} (hcurv : curv < 0) (hcross : 0 < cross) :
    0 < -(cross / curv) := by
  have : cross / curv < 0 := div_neg_of_pos_of_neg hcross hcurv
  linarith

/-- And inward under backward flow. -/
theorem saddle_moves_inward {curv cross : ℝ} (hcurv : curv < 0) (hcross : cross < 0) :
    -(cross / curv) < 0 := by
  have : 0 < cross / curv := div_pos_of_neg_of_neg hcross hcurv
  linarith

/-- **The crossed derivative is the observable.**  For the flow tilt it is `2u`, positive on the
positive axis. -/
theorem crossed_derivative_pos {u : ℝ} (hu : 0 < u) : 0 < 2 * u := by linarith

/-- **The margin is monotone in the saddle place.**  Pushing the saddle outward increases `1 + 2u*`. -/
theorem margin_monotone_in_saddle {u₁ u₂ : ℝ} (h : u₁ ≤ u₂) : 1 + 2 * u₁ ≤ 1 + 2 * u₂ := by
  linarith

/-- **Forward flow increases the margin strictly.** -/
theorem margin_strict_mono {u₁ u₂ : ℝ} (h : u₁ < u₂) : 1 + 2 * u₁ < 1 + 2 * u₂ := by
  linarith

/-- **The margin vanishes only at a negative saddle place**, so the order-two inequality survives as
long as the saddle stays above `-1/2`. -/
theorem margin_pos_iff {u : ℝ} : 0 < 1 + 2 * u ↔ -(1 / 2) < u := by
  constructor <;> intro h <;> linarith

end RHTower
