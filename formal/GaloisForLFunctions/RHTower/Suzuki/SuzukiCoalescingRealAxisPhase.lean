import GaloisForLFunctions.HTGeometry.HalfPlanePolePhase
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCoalescingHalfPlaneNormality

/-!
# The real-axis phase of the movable Cayley anchor

On the positive real axis the movable Cayley chart `b_c(z) = (z - ic)/(z + ic)` is unimodular, and
its continuous phase is `-2 arctan(c/x)`.  Differentiating gives the anchor phase rate

`d/dx arg b_c(x) = 2c/(x² + c²)`,

which is strictly positive, so the chart traverses the unit circle monotonically as `x` increases
through the positive axis, and the arc swept over a fixed interval has half-width comparable to `c`.

The phase rate is the orientation input for a boundary crossing count: the total gain over an
interval, together with strict monotonicity, determines how many times each unimodular level is
attained.
-/

noncomputable section

namespace RHTower

open Complex Real Set

/-- The continuous real-axis phase of the movable Cayley anchor. -/
def suzukiCayleyPhase (c x : ℝ) : ℝ := -2 * Real.arctan (c / x)

/-- The anchor is unimodular with the stated phase on the positive real axis. -/
theorem suzukiCoalescingCayley_eq_exp_phase {c x : ℝ} (hx : 0 < x) :
    suzukiCoalescingCayley c (x : ℂ) =
      Complex.exp ((suzukiCayleyPhase c x : ℂ) * I) := by
  have hr : 0 < Real.sqrt (x ^ (2 : ℕ) + c ^ (2 : ℕ)) := Real.sqrt_pos.mpr (by positivity)
  have hexp : ∀ θ : ℝ, Complex.exp ((θ : ℂ) * I)
      = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
    intro θ
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hden : (x : ℂ) + (c : ℂ) * I ≠ 0 := by
    intro hzero
    have := congrArg Complex.re hzero
    simp at this
    exact absurd this (ne_of_gt hx)
  have hrC : ((Real.sqrt (x ^ (2 : ℕ) + c ^ (2 : ℕ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hr
  have h1 : Complex.exp ((Real.arctan (c / x) : ℂ) * I)
      = ((x : ℂ) + (c : ℂ) * I) / ((Real.sqrt (x ^ (2 : ℕ) + c ^ (2 : ℕ)) : ℝ) : ℂ) := by
    rw [hexp, GaloisForLFunctions.HTGeometry.cos_arctan_div hx, GaloisForLFunctions.HTGeometry.sin_arctan_div hx]
    push_cast
    field_simp
  have h2 : Complex.exp (((-Real.arctan (c / x) : ℝ) : ℂ) * I)
      = ((x : ℂ) - (c : ℂ) * I) / ((Real.sqrt (x ^ (2 : ℕ) + c ^ (2 : ℕ)) : ℝ) : ℂ) := by
    rw [hexp, Real.cos_neg, Real.sin_neg, GaloisForLFunctions.HTGeometry.cos_arctan_div hx, GaloisForLFunctions.HTGeometry.sin_arctan_div hx]
    push_cast
    field_simp
    ring
  have hsplit : Complex.exp ((suzukiCayleyPhase c x : ℂ) * I)
      = Complex.exp (((-Real.arctan (c / x) : ℝ) : ℂ) * I)
        / Complex.exp ((Real.arctan (c / x) : ℂ) * I) := by
    rw [← Complex.exp_sub]
    congr 1
    rw [suzukiCayleyPhase]
    push_cast
    ring
  have hcancel : ((x : ℂ) - (c : ℂ) * I) / ((Real.sqrt (x ^ (2 : ℕ) + c ^ (2 : ℕ)) : ℝ) : ℂ)
      / (((x : ℂ) + (c : ℂ) * I) / ((Real.sqrt (x ^ (2 : ℕ) + c ^ (2 : ℕ)) : ℝ) : ℂ))
      = ((x : ℂ) - (c : ℂ) * I) / ((x : ℂ) + (c : ℂ) * I) := by
    field_simp
  rw [hsplit, h1, h2, suzukiCoalescingCayley, hcancel]

/-- `(40)`: the real-axis phase rate of the movable Cayley anchor. -/
theorem hasDerivAt_suzukiCayleyPhase (c : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (suzukiCayleyPhase c) (2 * c / (x ^ (2 : ℕ) + c ^ (2 : ℕ))) x := by
  have hinv : HasDerivAt (fun y : ℝ => c * y⁻¹) (c * -(x ^ (2 : ℕ))⁻¹) x :=
    (hasDerivAt_inv hx).const_mul c
  have harc : HasDerivAt Real.arctan (1 / (1 + (c * x⁻¹) ^ (2 : ℕ))) (c * x⁻¹) :=
    Real.hasDerivAt_arctan (c * x⁻¹)
  have hcomp := harc.comp x hinv
  simp only [Function.comp_def] at hcomp
  have hres : HasDerivAt (suzukiCayleyPhase c)
      (-2 * ((1 / (1 + (c * x⁻¹) ^ (2 : ℕ))) * (c * -(x ^ (2 : ℕ))⁻¹))) x := by
    have hfun : suzukiCayleyPhase c = fun y : ℝ => -2 * Real.arctan (c * y⁻¹) := by
      funext y
      rw [suzukiCayleyPhase, div_eq_mul_inv]
    rw [hfun]
    exact hcomp.const_mul (-2)
  convert hres using 1
  have hx2 : x ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx
  have hsum : (1 : ℝ) + (c * x⁻¹) ^ (2 : ℕ) ≠ 0 := by positivity
  field_simp

/-- The anchor phase is strictly increasing on the positive real axis. -/
theorem strictMonoOn_suzukiCayleyPhase {c : ℝ} (hc : 0 < c) :
    StrictMonoOn (suzukiCayleyPhase c) (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · intro x hx
    exact ContinuousAt.continuousWithinAt
      ((hasDerivAt_suzukiCayleyPhase c (ne_of_gt hx)).differentiableAt.continuousAt)
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hasDerivAt_suzukiCayleyPhase c (ne_of_gt hx)).deriv]
    have hxpos : 0 < x := hx
    positivity

/-- The anchor phase is continuous on the positive real axis. -/
theorem continuousOn_suzukiCayleyPhase (c : ℝ) :
    ContinuousOn (suzukiCayleyPhase c) (Ioi 0) := fun _x hx =>
  ContinuousAt.continuousWithinAt
    ((hasDerivAt_suzukiCayleyPhase c (ne_of_gt hx)).differentiableAt.continuousAt)

/-- The anchor chart is the half-plane factor with pole `ic`, so its globally continuous phase is
`polePhase 0 c`, valid on the whole real axis rather than only on the positive half. -/
theorem suzukiCoalescingCayley_eq_exp_polePhase {c : ℝ} (hc : 0 < c) (x : ℝ) :
    suzukiCoalescingCayley c (x : ℂ) =
      Complex.exp ((GaloisForLFunctions.HTGeometry.polePhase 0 c x : ℂ) * I) := by
  have h := GaloisForLFunctions.HTGeometry.polePhase_eq_exp (u := 0) (v := c) (x := x) hc
  rw [suzukiCoalescingCayley]
  rw [← h]
  push_cast
  ring_nf

end RHTower
