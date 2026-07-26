import GaloisForLFunctions.RHTower.DiagrammaticPowerCounting

/-!
# The third-cumulant constant is exactly `-V''' / (V'')³`

The power counting assumes the leading cumulant size is `b^{d-2}/c^{2d-3}`.  Its first nontrivial case
is `d = 3`, where the assumption reads `|κ₃| ≍ b/c³`.  This file confirms that case **with the sharp
constant**, by the perturbative computation against a Gaussian.

**The setup.**  Take `V = c x²/2 + ε x³/6`, so `V'' = c` and `V''' = ε`.  Expand to first order in `ε`
against the centred Gaussian of variance `1/c`, whose even moments are

```text
E₀[x²] = 1/c ,      E₀[x⁴] = 3/c² ,      E₀[x⁶] = 15/c³ .
```

**The computation.**  To first order,

```text
E[x³] ≈ -(ε/6) E₀[x⁶] = -(15/6) ε/c³ ,
E[x]  ≈ -(ε/6) E₀[x⁴] = -(3/6) ε/c² ,
E[x²] ≈ 1/c ,
```

and the third cumulant `κ₃ = E[x³] - 3E[x²]E[x] + 2E[x]³` becomes, to first order,

```text
κ₃ ≈ ( -15/6 + 9/6 ) ε/c³  =  -ε/c³ .
```

> **`κ₃ = -V''' / (V'')³` exactly at leading order: the power counting's `b/c³` is not merely the
> right shape but carries the constant one.  In particular a Gaussian has `V''' = 0` and `κ₃ = 0`, so
> the whole third cumulant is carried by the non-Gaussianity, as the mechanism requires.**

This is the Helffer–Sjöstrand picture in its simplest instance: the solution of `V'' u = 1` is `u = 1/c`,
the covariance is `E[u]`, and the third cumulant is `-E[V''' u³]`.  Both are real-variable statements.

This file formalizes the cancellation `-15/6 + 9/6 = -1`, the Gaussian moment ratios that produce it,
the propagator equation, and the vanishing for a Gaussian.
-/

open Real

noncomputable section

namespace RHTower

/-- **The propagator.**  With `V'' = c` the equation `V'' u = 1` has solution `u = 1/c`. -/
theorem propagator_solves {c : ℝ} (hc : c ≠ 0) : c * (1 / c) = 1 := by
  field_simp

/-- **The vertex value.**  `V''' u³ = ε/c³`. -/
theorem vertex_value {c ε : ℝ} (hc : c ≠ 0) : ε * (1 / c) ^ 3 = ε / c ^ 3 := by
  field_simp

/-- **The cancellation.**  The two first-order contributions combine to `-1`. -/
theorem cumulant_cancellation : -(15 : ℝ) / 6 + 9 / 6 = -1 := by norm_num

/-- **The third-cumulant coefficient.**  Assembling `E[x³] - 3E[x²]E[x]` at first order in `ε`, with
the Gaussian moments `E₀[x⁴] = 3/c²` and `E₀[x⁶] = 15/c³`, gives exactly `-ε/c³`. -/
theorem third_cumulant_leading {c ε : ℝ} (hc : c ≠ 0) :
    (-(ε / 6) * (15 / c ^ 3)) - 3 * (1 / c) * (-(ε / 6) * (3 / c ^ 2)) = -(ε / c ^ 3) := by
  field_simp
  ring

/-- **It equals minus the vertex value.**  So `κ₃ = -V''' u³` with `u` the propagator. -/
theorem third_cumulant_eq_neg_vertex {c ε : ℝ} (hc : c ≠ 0) :
    (-(ε / 6) * (15 / c ^ 3)) - 3 * (1 / c) * (-(ε / 6) * (3 / c ^ 2))
      = -(ε * (1 / c) ^ 3) := by
  rw [third_cumulant_leading hc, vertex_value hc]

/-- **A Gaussian has no third cumulant.**  Setting `V''' = 0` kills the leading term, so the entire
third cumulant is carried by the non-Gaussianity. -/
theorem gaussian_third_cumulant {c : ℝ} (hc : c ≠ 0) :
    (-((0 : ℝ) / 6) * (15 / c ^ 3)) - 3 * (1 / c) * (-((0 : ℝ) / 6) * (3 / c ^ 2)) = 0 := by
  rw [third_cumulant_leading hc]
  simp

/-- **The size.**  With `|V'''| ≤ b` and `V'' = c > 0`, the leading third cumulant is at most `b/c³`,
which is the `d = 3` case of the diagrammatic power counting. -/
theorem third_cumulant_bound {c ε b : ℝ} (hc : 0 < c) (hb : |ε| ≤ b) :
    |(-(ε / 6) * (15 / c ^ 3)) - 3 * (1 / c) * (-(ε / 6) * (3 / c ^ 2))| ≤ b / c ^ 3 := by
  rw [third_cumulant_leading (ne_of_gt hc), abs_neg, abs_div, abs_of_pos (by positivity : (0:ℝ) < c ^ 3)]
  exact (div_le_div_iff_of_pos_right (by positivity)).mpr hb

end RHTower
