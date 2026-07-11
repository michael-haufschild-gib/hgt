/-
# The field-level functional equation: mirror symmetry of the modulus-slope field

The functional equation and Schwarz reflection make `‖ξ‖` invariant under the critical-line
reflection `lineReflect : z ↦ 1 − z̄`.  Since `lineReflect` maps the circle of radius `r` around
`ρ` onto the circle of radius `r` around `lineReflect ρ` (via `θ ↦ π − θ`), every circle average
of `log ‖ξ‖` is mirror-invariant, and so is the whole slope field:

* `xi_circleAverage_lineReflect` — `A(lineReflect ρ, r) = A(ρ, r)` for every center and radius;
* `modulusSlope_lineReflect` — the field-level functional equation
  `modulusSlope (lineReflect ρ) r₁ r₂ = modulusSlope ρ r₁ r₂`.

Consequences: the field is unconditionally flat past BOTH walls
(`modulusSlope_eq_zero_of_re_add_le_zero` mirrors the `Re > 1` wall to `Re < 0`), its
nontrivial support is a mirror-symmetric band around the strip, and every one-sided criterion
halves — the sub-unit RH criterion and the disproof certificate transport verbatim to the left
half-plane (`rh_iff_forall_leftHalf_modulusSlope_lt_one`,
`not_riemannHypothesis_of_leftHalf_modulusSlope_ne_zero`).
-/
import GaloisForLFunctions.RHTower.ModulusSlopeQuantization
import GaloisForLFunctions.RHTower.DictionarySign
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Complex Metric Real

namespace RHTower

noncomputable section

/-- The critical-line reflection carries the circle of radius `r` around `ρ` onto the circle of
the same radius around `lineReflect ρ`, reversing the angle across `π`. -/
theorem circleMap_lineReflect (ρ : ℂ) (r θ : ℝ) :
    circleMap (lineReflect ρ) r θ = lineReflect (circleMap ρ r (π - θ)) := by
  have h1 : (Complex.exp (((π - θ : ℝ) : ℂ) * Complex.I)).re = Real.cos (π - θ) :=
    Complex.exp_ofReal_mul_I_re _
  have h2 : (Complex.exp (((π - θ : ℝ) : ℂ) * Complex.I)).im = Real.sin (π - θ) :=
    Complex.exp_ofReal_mul_I_im _
  have hconj : (starRingEnd ℂ) (Complex.exp (((π - θ : ℝ) : ℂ) * Complex.I)) =
      -Complex.exp (((θ : ℝ) : ℂ) * Complex.I) := by
    refine Complex.ext ?_ ?_
    · rw [Complex.conj_re, h1, Real.cos_pi_sub, Complex.neg_re,
        Complex.exp_ofReal_mul_I_re]
    · rw [Complex.conj_im, h2, Real.sin_pi_sub, Complex.neg_im,
        Complex.exp_ofReal_mul_I_im]
  simp only [circleMap, lineReflect, map_add, map_mul, Complex.conj_ofReal, hconj]
  ring

/-- **Circle averages of `log ‖ξ‖` are mirror-symmetric across the critical line.**  The
functional equation and Schwarz reflection give `‖ξ ∘ lineReflect‖ = ‖ξ‖`, and the reflection
maps circles to circles of the same radius. -/
theorem xi_circleAverage_lineReflect (ρ : ℂ) (r : ℝ) :
    Real.circleAverage (fun z => Real.log ‖xi z‖) (lineReflect ρ) r =
      Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r := by
  have key : (∫ θ in (0:ℝ)..2 * π, Real.log ‖xi (circleMap (lineReflect ρ) r θ)‖) =
      ∫ θ in (0:ℝ)..2 * π, Real.log ‖xi (circleMap ρ r θ)‖ := by
    have h1 : (∫ θ in (0:ℝ)..2 * π, Real.log ‖xi (circleMap (lineReflect ρ) r θ)‖) =
        ∫ θ in (0:ℝ)..2 * π, Real.log ‖xi (circleMap ρ r (π - θ))‖ := by
      refine intervalIntegral.integral_congr fun θ _ => ?_
      rw [circleMap_lineReflect ρ r θ, xi_lineReflect]
      simp
    rw [h1]
    have h2 := intervalIntegral.integral_comp_sub_left
      (a := (0:ℝ)) (b := 2 * π) (fun θ => Real.log ‖xi (circleMap ρ r θ)‖) π
    have e1 : π - 2 * π = -π := by ring
    rw [e1, sub_zero] at h2
    rw [h2]
    have hper : Function.Periodic (fun θ : ℝ => Real.log ‖xi (circleMap ρ r θ)‖) (2 * π) :=
      fun x => by simp [periodic_circleMap ρ r x]
    have h3 := hper.intervalIntegral_add_eq (-π) 0
    rw [zero_add] at h3
    have e2 : -π + 2 * π = π := by ring
    rw [e2] at h3
    exact h3
  rw [Real.circleAverage_def, Real.circleAverage_def]
  exact congrArg (fun t => (2 * π)⁻¹ • t) key

/-- **The field-level functional equation.**  The modulus-slope field is invariant under the
critical-line reflection: the constraint that fixes ξ acts on the field itself. -/
theorem modulusSlope_lineReflect (ρ : ℂ) (r₁ r₂ : ℝ) :
    modulusSlope (lineReflect ρ) r₁ r₂ = modulusSlope ρ r₁ r₂ := by
  rw [modulusSlope, modulusSlope, xi_circleAverage_lineReflect, xi_circleAverage_lineReflect]

/-- **Flat past the left wall.**  The mirror of the `Re > 1` wall: any slope sample over a ball
beyond `Re = 0` on the left vanishes unconditionally.  Together with
`modulusSlope_eq_zero_of_one_le_sub_re`, the nontrivial support of the field is a
mirror-symmetric band around the critical strip. -/
theorem modulusSlope_eq_zero_of_re_add_le_zero {ρ : ℂ} {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (h₁₂ : r₁ < r₂) (hwall : ρ.re + r₂ ≤ 0) :
    modulusSlope ρ r₁ r₂ = 0 := by
  rw [← modulusSlope_lineReflect]
  refine modulusSlope_eq_zero_of_one_le_sub_re hr₁ h₁₂ ?_
  rw [lineReflect_re]
  linarith

/-- **The halved criterion.**  By mirror symmetry, RH is equivalently the sub-unit bound on the
LEFT half-plane: the field over any ball contained in `Re < 1/2` stays below `1`. -/
theorem rh_iff_forall_leftHalf_modulusSlope_lt_one :
    RiemannHypothesis ↔
      ∀ (ρ : ℂ) (r₁ r₂ : ℝ), 0 < r₁ → r₁ < r₂ → ρ.re + r₂ ≤ 1 / 2 →
        modulusSlope ρ r₁ r₂ < 1 := by
  rw [rh_iff_forall_rightHalf_modulusSlope_lt_one]
  constructor
  · intro h ρ r₁ r₂ hr₁ h₁₂ hhalf
    rw [← modulusSlope_lineReflect]
    refine h (lineReflect ρ) r₁ r₂ hr₁ h₁₂ ?_
    rw [lineReflect_re]
    linarith
  · intro h ρ r₁ r₂ hr₁ h₁₂ hhalf
    rw [← modulusSlope_lineReflect]
    refine h (lineReflect ρ) r₁ r₂ hr₁ h₁₂ ?_
    rw [lineReflect_re]
    linarith

/-- **The mirrored disproof certificate.**  One nonzero slope sample over a ball contained in
the LEFT half-plane `Re < 1/2` also refutes RH: the reflection transports it to a right-half
sample of equal value. -/
theorem not_riemannHypothesis_of_leftHalf_modulusSlope_ne_zero {ρ : ℂ} {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (h₁₂ : r₁ < r₂) (hhalf : ρ.re + r₂ ≤ 1 / 2)
    (hslope : modulusSlope ρ r₁ r₂ ≠ 0) : ¬ RiemannHypothesis := by
  refine not_riemannHypothesis_of_modulusSlope_ne_zero (ρ := lineReflect ρ) hr₁ h₁₂ ?_ ?_
  · rw [lineReflect_re]
    linarith
  · rwa [modulusSlope_lineReflect]

end

end RHTower
