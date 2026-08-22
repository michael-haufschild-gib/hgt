import GaloisForLFunctions.HTGeometry.L2FourierIntegralBridge

/-!
# The unitary `L²` Fourier transform against the classical Fourier integral

The statement is proved in
`GaloisForLFunctions.HTGeometry.coeFn_fourierTransform_ae_eq_fourierIntegral`; this file only
re-exports it under the name the `RHTower` layer uses.
-/

noncomputable section

open MeasureTheory
open FourierTransform
open scoped ENNReal BoundedContinuousFunction SchwartzMap

namespace RHTower

/-- If an `L²(ℝ)` representative is integrable, then mathlib's unitary `L²` Fourier transform is
almost everywhere equal to its classical `L¹` Fourier integral. -/
theorem l2_fourier_coeFn_eq_l1_fourier_of_integrable
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : Integrable (f : ℝ → ℂ)) :
    ((𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      (Real.Lp.fourierTransform ((memLp_one_iff_integrable.mpr hf).toLp f) : ℝ → ℂ) :=
  GaloisForLFunctions.HTGeometry.coeFn_fourierTransform_ae_eq_fourierIntegral f hf

end RHTower
