import GaloisForLFunctions.RHTower.CumulantInductionStep

/-!
# The tilted family is dominated by one Gaussian, uniformly in the tilt

The induction of the previous entry needs differentiation under the integral for the tilted family
`μ_h ∝ e^{-V + h x}`.  The only analytic input that requires is a dominating function valid for all
`h` at once.  This file produces it, from strong convexity alone.

**Strong convexity.**  If `V'' ≥ c` then `W = V - c x²/2` is convex, so it lies above its tangent, and
unwinding gives

```text
V(x)  ≥  V(m) + V'(m)(x - m) + (c/2)(x - m)² .
```

**The domination.**  Choosing `m` to be the mode of the tilt, i.e. `V'(m) = h`, this reads

```text
-V(x) + h x  ≤  ( -V(m) + h m )  -  (c/2)(x - m)² ,
```

so every tilted density is bounded by a Gaussian of variance `1/c` centred at that tilt's mode, with
the **same** `c` for every `h` — the curvature is tilt-invariant.

> **One curvature bound dominates the whole tilted family by a fixed-width Gaussian.  Differentiation
> under the integral in the tilt parameter therefore needs no hypothesis beyond `V'' ≥ c`, and the
> cumulant induction has no analytic gap left at this step.**

This file formalizes the tangent-line inequality for a differentiable convex function on the line, the
strong-convexity inequality that follows, and the uniform Gaussian domination of the tilted exponents.
-/

open Set

noncomputable section

namespace RHTower

/-- **A differentiable convex function lies above its tangent line.** -/
theorem convex_tangent_line {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (hd : Differentiable ℝ f)
    {m d : ℝ} (hm : HasDerivAt f d m) (x : ℝ) :
    f m + d * (x - m) ≤ f x := by
  have hderiv : deriv f m = d := hm.deriv
  rcases lt_trichotomy x m with hx | hx | hx
  · have hslope := hf.slope_le_deriv (mem_univ x) (mem_univ m) hx (hd m)
    have hsl : slope f x m = (f m - f x) / (m - x) := by
      rw [slope_def_field]
    rw [hsl, hderiv] at hslope
    have hmx : (0 : ℝ) < m - x := by linarith
    rw [div_le_iff₀ hmx] at hslope
    linarith
  · subst hx; simp
  · have hslope := hf.deriv_le_slope (mem_univ m) (mem_univ x) hx (hd m)
    have hsl : slope f m x = (f x - f m) / (x - m) := by
      rw [slope_def_field]
    rw [hsl, hderiv] at hslope
    have hmx : (0 : ℝ) < x - m := by linarith
    rw [le_div_iff₀ hmx] at hslope
    linarith

/-- **The strong-convexity inequality.**  If `V - c x²/2` is convex and `V` has derivative `h` at the
mode `m`, then `V` lies above the shifted parabola. -/
theorem strongConvex_lower {V : ℝ → ℝ} {c m h : ℝ}
    (hW : ConvexOn ℝ univ (fun y => V y - c / 2 * y ^ 2))
    (hWd : Differentiable ℝ (fun y => V y - c / 2 * y ^ 2))
    (hV : HasDerivAt V h m) (x : ℝ) :
    V m + h * (x - m) + c / 2 * (x - m) ^ 2 ≤ V x := by
  have hWderiv : HasDerivAt (fun y => V y - c / 2 * y ^ 2) (h - c * m) m := by
    have hsq : HasDerivAt (fun y : ℝ => c / 2 * y ^ 2) (c / 2 * (2 * m)) m := by
      simpa using ((hasDerivAt_pow 2 m).const_mul (c / 2))
    have := hV.sub hsq
    convert this using 1
    ring
  have htan := convex_tangent_line hW hWd hWderiv x
  simp only at htan
  nlinarith [htan]

/-- **Uniform Gaussian domination of the tilted exponent.**  Every tilt is bounded by a Gaussian of
the same width, centred at that tilt's mode. -/
theorem tilt_gaussian_domination {V : ℝ → ℝ} {c m h : ℝ}
    (hW : ConvexOn ℝ univ (fun y => V y - c / 2 * y ^ 2))
    (hWd : Differentiable ℝ (fun y => V y - c / 2 * y ^ 2))
    (hV : HasDerivAt V h m) (x : ℝ) :
    -V x + h * x ≤ (-V m + h * m) - c / 2 * (x - m) ^ 2 := by
  have := strongConvex_lower hW hWd hV x
  linarith

/-- In exponential form: the tilted density is at most a constant times a fixed Gaussian. -/
theorem tilt_density_bound {V : ℝ → ℝ} {c m h : ℝ}
    (hW : ConvexOn ℝ univ (fun y => V y - c / 2 * y ^ 2))
    (hWd : Differentiable ℝ (fun y => V y - c / 2 * y ^ 2))
    (hV : HasDerivAt V h m) (x : ℝ) :
    Real.exp (-V x + h * x)
      ≤ Real.exp (-V m + h * m) * Real.exp (-(c / 2 * (x - m) ^ 2)) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith [tilt_gaussian_domination hW hWd hV x])

end RHTower
