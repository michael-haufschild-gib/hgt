import GaloisForLFunctions.RHTower.HedenmalmThetaEigenTransform

/-!
# Convention bridge: the Hedenmalm eigen transform as a mathlib Fourier integral

The corpus's eigen transform uses the `e^{-izx}` normalization; mathlib's Fourier integral uses
`e^{-2πixξ}`.  On any horizontal line the two agree after tilting by the imaginary part and
rescaling the frequency by `2π`:

`T α z = 𝓕 (x ↦ u_α(x)·e^{z.im·x}) (z.re/(2π))`.

This is the convention linchpin for the prime-side assembly: it lets the corpus's L¹
convolution theorem and mathlib's Fourier inversion act on the eigen transforms directly.
-/

namespace RHTower

noncomputable section

open MeasureTheory Complex FourierTransform

/-- **The eigen transform is a tilted mathlib Fourier integral.**  For every `z`, the corpus
transform at `z` equals the mathlib Fourier integral of the `z.im`-tilted flow at frequency
`z.re/(2π)`. -/
theorem hedenmalmThetaEigenTransform_eq_fourier (α z : ℂ) :
    hedenmalmThetaEigenTransform α z =
      𝓕 (fun x : ℝ => hedenmalmCausalVolterra α x * Complex.exp ((z.im : ℂ) * (x : ℂ)))
        (z.re / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq, hedenmalmThetaEigenTransform]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show hedenmalmCausalVolterra α x * Complex.exp (-I * z * (x : ℂ)) =
    (Real.fourierChar (-(x * (z.re / (2 * Real.pi)))) : ℂ) •
      (hedenmalmCausalVolterra α x * Complex.exp ((z.im : ℂ) * (x : ℂ)))
  rw [Real.fourierChar_apply, smul_eq_mul]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by
    positivity
  have harg : ((2 * Real.pi * (-(x * (z.re / (2 * Real.pi)))) : ℝ) : ℂ) =
      -((x : ℂ) * (z.re : ℂ)) := by
    push_cast
    field_simp
  rw [harg, mul_comm ((Complex.exp (-((x : ℂ) * (z.re : ℂ)) * I)))
    (hedenmalmCausalVolterra α x * Complex.exp ((z.im : ℂ) * (x : ℂ))),
    mul_assoc (hedenmalmCausalVolterra α x), ← Complex.exp_add]
  congr 1
  congr 1
  linear_combination (I * (x : ℂ)) * (Complex.re_add_im z) +
    (-(z.im : ℂ) * (x : ℂ)) * Complex.I_sq

end

end RHTower
