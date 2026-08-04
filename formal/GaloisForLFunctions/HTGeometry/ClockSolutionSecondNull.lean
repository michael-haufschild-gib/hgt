import GaloisForLFunctions.HTGeometry.ClockSolutionTransverse
import GaloisForLFunctions.HTGeometry.ClockParametricDerivative

/-!
# The derivative along the second null coordinate

The first null coordinate is differentiated by the fundamental theorem of calculus applied to the
outer integral. The second one sits inside that integral, so differentiating it is the Leibniz rule:
the inner integral has the integrand as its derivative in its own upper limit, and the data are
continuous on the whole plane once the null coordinates are clamped, so no domination hypothesis has
to be checked.

Differentiating the result once more in the first null coordinate returns the step operator, so the
mixed derivative is the same in both orders, as the equality of the two continuous mixed partials
requires. That symmetric pair is what the chart d'Alembertian consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

open scoped Interval

/-- The inner integral of the clamped step is jointly continuous in its upper limit and in the
other null coordinate. -/
theorem continuous_clampedInnerSnd {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {z : ℂ} (hz : |z.im| ≤ ρ) :
    Continuous fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..p.1, clampedStep V T z p.2 t := by
  have hFc := continuous_clampedStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hz
  have huncurry : Continuous fun q : (ℝ × ℝ) × ℝ => clampedStep V T z q.1.2 q.2 :=
    hFc.comp (f := fun q : (ℝ × ℝ) × ℝ => ((q.1.2, q.2) : ℝ × ℝ))
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun (p : ℝ × ℝ) (t : ℝ) => clampedStep V T z p.2 t) huncurry continuous_fst

/-- **The solution is differentiable in the second null coordinate.** -/
theorem hasDerivAt_clockSolution_snd {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {ξ η : ℝ} (hξT : |ξ| ≤ T) (hη : |η| < T) {z : ℂ} (hz : |z.im| ≤ ρ) :
    HasDerivAt (fun y : ℝ => clockSolution V ξ y z)
      (∫ s in (0 : ℝ)..ξ, clampedStep V T z s η) η := by
  have hFc := continuous_clampedStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hz
  have hslice : ∀ s : ℝ, Continuous fun t : ℝ => clampedStep V T z s t :=
    fun s => hFc.comp (f := fun t : ℝ => ((s, t) : ℝ × ℝ))
      (continuous_const.prodMk continuous_id)
  have hswap : Continuous fun p : ℝ × ℝ => clampedStep V T z p.2 p.1 :=
    hFc.comp (f := fun p : ℝ × ℝ => ((p.2, p.1) : ℝ × ℝ))
      (continuous_snd.prodMk continuous_fst)
  have hjoint := continuous_clampedInnerSnd hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hz
  have hderiv : ∀ y s : ℝ,
      HasDerivAt (fun w : ℝ => ∫ t in (0 : ℝ)..w, clampedStep V T z s t)
        (clampedStep V T z s y) y :=
    fun y s => ((hslice s).integral_hasStrictDerivAt 0 y).hasDerivAt
  have hpar := hasDerivAt_parametric_intervalIntegral
    (f := fun (y : ℝ) (s : ℝ) => ∫ t in (0 : ℝ)..y, clampedStep V T z s t)
    (f' := fun (y : ℝ) (s : ℝ) => clampedStep V T z s y) hjoint hswap hderiv 0 ξ η
  have hbase := hpar.const_add (1 : ℂ)
  refine hbase.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hη) fun y hy => ?_
  exact clockSolution_eq_clamped hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hξT (le_of_lt hy) hz

/-- The derivative of the solution in the second null coordinate. -/
theorem deriv_clockSolution_snd {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {ξ η : ℝ} (hξT : |ξ| ≤ T) (hη : |η| < T) {z : ℂ} (hz : |z.im| ≤ ρ) :
    deriv (fun y : ℝ => clockSolution V ξ y z) η = ∫ s in (0 : ℝ)..ξ, clampedStep V T z s η :=
  (hasDerivAt_clockSolution_snd hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hξT hη hz).deriv

/-- **The characteristic clock equation in the other order.** Differentiating first in the second
null coordinate and then in the first returns the same step operator. -/
theorem hasDerivAt_deriv_clockSolution_snd {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {ξ η : ℝ} (hξ : |ξ| < T) (hη : |η| < T) {z : ℂ} (hz : |z.im| ≤ ρ) :
    HasDerivAt (fun x : ℝ => deriv (fun y : ℝ => clockSolution V x y z) η)
      (clockStripStep (V ξ η) (clockSolution V ξ η) z) ξ := by
  have hFc := continuous_clampedStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hz
  have hslice : Continuous fun s : ℝ => clampedStep V T z s η :=
    hFc.comp (f := fun s : ℝ => ((s, η) : ℝ × ℝ))
      (continuous_id.prodMk continuous_const)
  have hbase : HasDerivAt (fun x : ℝ => ∫ s in (0 : ℝ)..x, clampedStep V T z s η)
      (clampedStep V T z ξ η) ξ := (hslice.integral_hasStrictDerivAt 0 ξ).hasDerivAt
  rw [← clampedStep_eq (le_of_lt hξ) (le_of_lt hη)]
  refine hbase.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hξ) fun x hx => ?_
  exact deriv_clockSolution_snd hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall (le_of_lt hx) hη hz

end GaloisForLFunctions.HTGeometry
