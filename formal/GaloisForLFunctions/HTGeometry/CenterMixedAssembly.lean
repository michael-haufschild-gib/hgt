import GaloisForLFunctions.HTGeometry.CenterMixedChangeOfVariables
import GaloisForLFunctions.HTGeometry.CenterMixedFactorization
import Mathlib

/-!
# Assembly of the center-mixed Fourier computation

Combining the sum-difference change of variables with the factorisation of the `u + v` weight gives
the shape actually met in the center-mixed Fourier integral: in the original coordinates the weight
`u + v = (w+t) + (w-t)` is `2w`, so

`∫ 2w · F (w+t) · G (w-t) dw dt = (1/2) [ (∫ u F) (∫ G) + (∫ F) (∫ v G) ]`.

Each factor on the right is a transform of the kernel, evaluated at a translated argument by the
shift rule.  This is the step at which the double integral over the plane becomes a product of
one-dimensional transforms of the Riemann theta kernel.
-/

open MeasureTheory Complex

namespace HTGeometry

/-- The `u + v` weighted product of two kernels is integrable on the plane as soon as each kernel
and each first moment is. -/
theorem integrable_prod_add_weight (F G : ℝ → ℂ)
    (hF : Integrable F) (hG : Integrable G)
    (huF : Integrable fun u : ℝ => (u : ℂ) * F u)
    (hvG : Integrable fun v : ℝ => (v : ℂ) * G v) :
    Integrable fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ)) * (F p.1 * G p.2) := by
  have h1 : Integrable fun p : ℝ × ℝ => ((p.1 : ℂ) * F p.1) * G p.2 := huF.mul_prod hG
  have h2 : Integrable fun p : ℝ × ℝ => F p.1 * ((p.2 : ℂ) * G p.2) := hF.mul_prod hvG
  have hsum := h1.add h2
  refine hsum.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Pi.add_apply]
  ring

/-- **Assembly.**  In the original coordinates the sum-difference weight is `2w`, and the double
integral factors into transforms of the two kernels. -/
theorem integral_sumDiff_add_weight (F G : ℝ → ℂ)
    (hF : Integrable F) (hG : Integrable G)
    (huF : Integrable fun u : ℝ => (u : ℂ) * F u)
    (hvG : Integrable fun v : ℝ => (v : ℂ) * G v) :
    ∫ p : ℝ × ℝ, (2 * (p.1 : ℂ)) * (F (p.1 + p.2) * G (p.1 - p.2))
      = (2 : ℝ)⁻¹ • ((∫ u : ℝ, (u : ℂ) * F u) * (∫ v : ℝ, G v)
          + (∫ u : ℝ, F u) * (∫ v : ℝ, (v : ℂ) * G v)) := by
  set H : ℝ × ℝ → ℂ := fun q => ((q.1 : ℂ) + (q.2 : ℂ)) * (F q.1 * G q.2) with hH
  have hHint : Integrable H := integrable_prod_add_weight F G hF hG huF hvG
  have hrewrite : ∀ p : ℝ × ℝ,
      H (p.1 + p.2, p.1 - p.2) = (2 * (p.1 : ℂ)) * (F (p.1 + p.2) * G (p.1 - p.2)) := by
    intro p
    simp only [hH]
    push_cast
    ring
  have hcv := integral_comp_sumDiff H hHint
  rw [integral_congr_ae (Filter.Eventually.of_forall hrewrite)] at hcv
  rw [hcv]
  congr 1
  simp only [hH]
  exact integral_prod_add_weight F G hF hG huF hvG

end HTGeometry
