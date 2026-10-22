import GaloisForLFunctions.RHTower.Deninger.DeningerTorusFlow
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating a torus integral in a parameter

On a compact space carrying a finite measure, a jointly continuous family with jointly continuous
derivative may be differentiated under the integral sign: the derivative is bounded on a compact
neighbourhood of the parameter, and a constant is integrable for a finite measure.

The characters of the torus are multiplicative in their argument, so translating the argument of a
character along the linear flow multiplies it by the one-frequency oscillation of that character.
Together these are what transposes the Kronecker derivative onto a character inside an integral.

* `deningerHasDerivAt_integral` : differentiation under the integral sign.
* `deningerMFourier_arg_add` : characters are multiplicative in the argument.
* `deningerMFourier_translate` : translating along the flow multiplies by the oscillation.
-/

namespace RHTower

open UnitAddTorus MeasureTheory Set Metric

section Parametric

/-- **Differentiation under the integral sign** for a jointly continuous family with jointly
continuous derivative on a compact space of finite measure. -/
theorem deningerHasDerivAt_integral {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {g g' : ℝ → X → ℂ}
    (hg : Continuous fun p : ℝ × X => g p.1 p.2)
    (hg' : Continuous fun p : ℝ × X => g' p.1 p.2)
    (hderiv : ∀ (t : ℝ) (x : X), HasDerivAt (fun t => g t x) (g' t x) t) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ x, g t x ∂μ) (∫ x, g' t₀ x ∂μ) t₀ := by
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall t₀ 1).prod isCompact_univ).exists_bound_of_continuousOn
      hg'.continuousOn
  have hslice : ∀ t : ℝ, Continuous fun x : X => g t x := fun t =>
    hg.comp (continuous_const.prodMk continuous_id)
  have hslice' : ∀ t : ℝ, Continuous fun x : X => g' t x := fun t =>
    hg'.comp (continuous_const.prodMk continuous_id)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ => C) (F := g) (F' := g') (s := ball t₀ 1)
    (ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall fun t => (hslice t).aestronglyMeasurable)
    ((hslice t₀).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hslice' t₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x t ht =>
      hC (t, x) ⟨ball_subset_closedBall ht, mem_univ x⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun x t _ => hderiv t x)).2

end Parametric

section Characters

/-- **Characters are multiplicative in the argument.** -/
theorem deningerFourier_arg_add {T : ℝ} {n : ℤ} (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  rw [fourier_apply, fourier_apply, fourier_apply, zsmul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

variable {d : Type*} [Fintype d]

/-- **The multivariate characters are multiplicative in the argument.** -/
theorem deningerMFourier_arg_add (n : d → ℤ) (x y : UnitAddTorus d) :
    mFourier n (x + y) = mFourier n x * mFourier n y := by
  show ∏ i : d, fourier (n i) ((x + y) i)
    = (∏ i : d, fourier (n i) (x i)) * ∏ i : d, fourier (n i) (y i)
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => deningerFourier_arg_add _ _

/-- **Translating along the linear flow multiplies a character by its oscillation.** -/
theorem deningerMFourier_translate (n : d → ℤ) (lam : d → ℝ) (t : ℝ) (η : UnitAddTorus d) :
    mFourier n (η + deningerTorusFlow lam t)
      = mFourier n η * Complex.exp ((2 * Real.pi * deningerFrequency n lam * t : ℝ) * Complex.I) := by
  rw [deningerMFourier_arg_add, deningerMFourier_flow]

end Characters

end RHTower
