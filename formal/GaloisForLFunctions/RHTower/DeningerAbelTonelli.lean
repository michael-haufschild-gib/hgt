import GaloisForLFunctions.RHTower.DeningerAbelCoefficient
import GaloisForLFunctions.RHTower.DeningerWeightedMoment

/-!
# The dilation-window Tonelli estimate

Each Abel difference is the integral of `H_h'` over the dilation window `[ix, (i+1)x]`: the
pullback is continuously differentiable on the ray, and the window sits inside it, so the
fundamental theorem of calculus applies with no further hypothesis.

This is the form the Tonelli exchange consumes — the set of dilations carrying a fixed `u` into
the `i`-th window is `[u/(i+1), u/i]`, of length `u/(i(i+1))`, so one Abel difference costs exactly
the coefficient `1/(i(i+1))` times the first weighted moment of `H_h'`.

* `deningerLogPullDeriv_continuousOn` : the derivative is continuous on the ray.
* `deningerAbelDifference_eq` : the difference is the integral of `H_h'` over the window.
* `deningerAbelDifference_eq` is what the Tonelli exchange consumes: integrating it over the ray
  and swapping the order of integration replaces the window by its measure `u/(i(i+1))`.
-/

namespace RHTower

open MeasureTheory SchwartzMap

noncomputable section

/-- The derivative of the pullback is continuous on the positive ray. -/
theorem deningerLogPullDeriv_continuousOn (h : 𝓢(ℝ, ℂ)) :
    ContinuousOn (deningerLogPullDeriv h) (Set.Ioi 0) := by
  have hderiv : Continuous (deriv (h : ℝ → ℂ)) := h.smooth'.continuous_deriv (by simp)
  refine ContinuousOn.mul ?_ ?_
  · exact hderiv.comp_continuousOn (Real.continuousOn_log.mono (fun x hx => ne_of_gt hx))
  · have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Ioi 0) :=
      continuousOn_inv₀.mono (fun x hx => ne_of_gt hx)
    exact Complex.continuous_ofReal.comp_continuousOn hinv

/-- **The Abel difference is the integral of the derivative over the dilation window.** -/
theorem deningerAbelDifference_eq (h : 𝓢(ℝ, ℂ)) {i : ℕ} (hi : 0 < i) {x : ℝ} (hx : 0 < x) :
    deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)
      = ∫ u in Set.Ioc ((i : ℝ) * x) (((i : ℝ) + 1) * x), deningerLogPullDeriv h u := by
  have hir : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have hlo : (0 : ℝ) < (i : ℝ) * x := mul_pos hir hx
  have hle : (i : ℝ) * x ≤ ((i : ℝ) + 1) * x := by nlinarith
  have hsub : Set.uIcc ((i : ℝ) * x) (((i : ℝ) + 1) * x) ⊆ Set.Ioi 0 := by
    rw [Set.uIcc_of_le hle]
    intro y hy
    exact lt_of_lt_of_le hlo hy.1
  have hderiv : ∀ y ∈ Set.uIcc ((i : ℝ) * x) (((i : ℝ) + 1) * x),
      HasDerivAt (deningerLogPull h) (deningerLogPullDeriv h y) y := fun y hy =>
    deningerLogPull_hasDerivAt h (hsub hy)
  have hint : IntervalIntegrable (deningerLogPullDeriv h) volume
      ((i : ℝ) * x) (((i : ℝ) + 1) * x) :=
    ContinuousOn.intervalIntegrable ((deningerLogPullDeriv_continuousOn h).mono hsub)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_of_le hle] at hftc
  exact hftc.symm

end

end RHTower
