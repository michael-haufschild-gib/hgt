import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# All moments make the Fourier transform smooth with bounded derivatives

Differentiating under the Fourier integral replaces the `n`-th derivative of `ℱG` by the transform
of `(2πiξ)^n G`, whose sup norm is at most the `L¹` norm of that argument.  So a density with every
moment has a transform that is `C^∞` with *every* derivative bounded — uniformly on the whole line.

Together with the Landau interpolation this is what turns a rapidly decreasing function into a
Schwartz function: the boundedness of the derivatives is free from the moments, and only the decay
of the function itself has to be proved.

* `deningerFourier_contDiff` : **`ℱG` is smooth.**
* `deningerFourier_iteratedDeriv_bound` : **every derivative of `ℱG` is bounded.**
-/

namespace RHTower

open MeasureTheory FourierTransform Real

open scoped ContDiff

noncomputable section

/-- **A density with every moment has a smooth Fourier transform.** -/
theorem deningerFourier_contDiff {G : ℝ → ℂ}
    (hmom : ∀ n : ℕ, Integrable fun v : ℝ => ‖v‖ ^ n * ‖G v‖) : ContDiff ℝ ∞ (𝓕 G) :=
  Real.contDiff_fourier (N := ⊤) fun n _ => hmom n

/-- **Every derivative of the Fourier transform of a density with every moment is bounded.** -/
theorem deningerFourier_iteratedDeriv_bound {G : ℝ → ℂ}
    (hmom : ∀ n : ℕ, Integrable fun v : ℝ => ‖v‖ ^ n * ‖G v‖)
    (hmeas : AEStronglyMeasurable G) (r : ℕ) :
    ∃ M : ℝ, ∀ x : ℝ, ‖iteratedDeriv r (𝓕 G) x‖ ≤ M := by
  set c : ℝ := (2 * π * ‖(innerSL ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖) ^ r with hc
  have hmaj : Integrable fun v : ℝ => c * (‖v‖ ^ r * ‖G v‖) := (hmom r).const_mul c
  refine ⟨∫ v : ℝ, c * (‖v‖ ^ r * ‖G v‖), fun x => ?_⟩
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.iteratedFDeriv_fourier (N := ⊤) (fun n _ => hmom n) hmeas (le_top)]
  refine le_trans (VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar
    volume (innerₗ ℝ) _ x) ?_
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _) hmaj ?_
  filter_upwards with v
  refine le_trans (VectorFourier.norm_fourierPowSMulRight_le
    (innerSL ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) G v r) (le_of_eq ?_)
  rw [hc]
  ring

end

end RHTower
