import GaloisForLFunctions.HTGeometry.OscillatorRecessiveLimits

/-!
# The ladder identity for the harmonic oscillator

For a solution of `v″ = (ξ² − μ)v` set

`A v = v′ + ξ v` ,   `B = v v′ + ξ v²` .

A single differentiation gives `B′ = (A v)² + (1 − μ)v²`, so by the fundamental theorem of calculus

`∫_{-R}^{R} (A v)² = B(R) − B(−R) + (μ − 1)∫_{-R}^{R} v²` .

When the boundary term vanishes at infinity — which it does for a square-integrable solution — this
becomes `‖A v‖² = (μ − 1)‖v‖²`, so `μ ≥ 1` for a nontrivial solution.  Moreover `A v` solves the
same equation with `μ` replaced by `μ − 2`, so the argument iterates.
-/

open Set MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The lowering operator applied to a solution. -/
noncomputable def oscLower (v v' : ℝ → ℝ) (x : ℝ) : ℝ := v' x + x * v x

/-- Derivative of the lowered solution. -/
noncomputable def oscLowerDeriv (mu : ℝ) (v v' : ℝ → ℝ) (x : ℝ) : ℝ :=
  (x ^ 2 - mu + 1) * v x + x * v' x

/-- Boundary function of the ladder identity. -/
noncomputable def oscBoundary (v v' : ℝ → ℝ) (x : ℝ) : ℝ := oscProduct v v' x + x * v x ^ 2

/-- A solution and its derivative are continuous. -/
theorem continuous_of_hasDerivAt {v v' : ℝ → ℝ} (hv : ∀ x, HasDerivAt v (v' x) x) :
    Continuous v :=
  continuous_iff_continuousAt.2 fun x => (hv x).continuousAt

/-- **Boundary derivative.**  `B′ = (A v)² + (1 − μ)v²`. -/
theorem hasDerivAt_oscBoundary {mu : ℝ} {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x) (x : ℝ) :
    HasDerivAt (oscBoundary v v') (oscLower v v' x ^ 2 + (1 - mu) * v x ^ 2) x := by
  have h1 := hasDerivAt_oscProduct hv hv' x
  have hb : HasDerivAt (fun y => v y ^ 2) (2 * v x * v' x) x := by
    refine ((hv x).pow 2).congr_deriv ?_
    push_cast
    ring
  have h2 : HasDerivAt (fun y => y * v y ^ 2) (v x ^ 2 + x * (2 * v x * v' x)) x := by
    refine ((hasDerivAt_id x).mul hb).congr_deriv ?_
    simp only [id_eq]
    ring
  refine (h1.add h2).congr_deriv ?_
  rw [oscLower]
  ring

/-- **The lowered solution solves the shifted equation.** -/
theorem hasDerivAt_oscLower {mu : ℝ} {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x) (x : ℝ) :
    HasDerivAt (oscLower v v') (oscLowerDeriv mu v v' x) x := by
  have h : HasDerivAt (fun y => v' y + y * v y)
      ((x ^ 2 - mu) * v x + (v x + x * v' x)) x := by
    refine ((hv' x).add ((hasDerivAt_id x).mul (hv x))).congr_deriv ?_
    simp only [id_eq]
    ring
  refine h.congr_deriv ?_
  rw [oscLowerDeriv]
  ring

theorem hasDerivAt_oscLowerDeriv {mu : ℝ} {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x) (x : ℝ) :
    HasDerivAt (oscLowerDeriv mu v v') ((x ^ 2 - (mu - 2)) * oscLower v v' x) x := by
  have hq : HasDerivAt (fun y : ℝ => y ^ 2 - mu + 1) (2 * x) x := by
    have := ((hasDerivAt_pow 2 x).sub_const mu).add_const 1
    simpa using this
  have h1 : HasDerivAt (fun y => (y ^ 2 - mu + 1) * v y)
      (2 * x * v x + (x ^ 2 - mu + 1) * v' x) x := hq.mul (hv x)
  have h2 : HasDerivAt (fun y => y * v' y) (v' x + x * ((x ^ 2 - mu) * v x)) x := by
    refine ((hasDerivAt_id x).mul (hv' x)).congr_deriv ?_
    simp only [id_eq]
    ring
  refine (h1.add h2).congr_deriv ?_
  rw [oscLower]
  ring

/-- **Ladder identity on a symmetric interval.** -/
theorem integral_oscLower_sq_interval {mu : ℝ} {v v' : ℝ → ℝ} (R : ℝ)
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x) :
    (∫ x in (-R)..R, oscLower v v' x ^ 2)
      = oscBoundary v v' R - oscBoundary v v' (-R)
        + (mu - 1) * ∫ x in (-R)..R, v x ^ 2 := by
  have hcv : Continuous v := continuous_of_hasDerivAt hv
  have hcv' : Continuous v' := continuous_of_hasDerivAt hv'
  have hcL : Continuous fun x => oscLower v v' x ^ 2 := by
    have : Continuous fun x => oscLower v v' x := by
      simp only [oscLower]
      exact hcv'.add (continuous_id.mul hcv)
    exact this.pow 2
  have hcs : Continuous fun x => v x ^ 2 := hcv.pow 2
  have hFTC : (∫ x in (-R)..R, (oscLower v v' x ^ 2 + (1 - mu) * v x ^ 2))
      = oscBoundary v v' R - oscBoundary v v' (-R) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_oscBoundary hv hv' x) ?_
    exact (hcL.add (continuous_const.mul hcs)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hcL.intervalIntegrable _ _)
    ((continuous_const.mul hcs).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul] at hFTC
  linarith

end GaloisForLFunctions.HTGeometry
