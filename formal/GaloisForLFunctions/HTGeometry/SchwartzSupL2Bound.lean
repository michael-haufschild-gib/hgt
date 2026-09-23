import GaloisForLFunctions.HTGeometry.SchwartzOscillatorL2Bound

/-!
# The supremum of a Schwartz function is bounded by the `L¹` norm of its transform

Fourier inversion writes a Schwartz function as the inverse transform of its transform, and the
inverse transform is an integral whose integrand has the same pointwise norm as the transform.  So
the supremum of a Schwartz function is bounded by the `L¹` norm of its Fourier transform.

The `L²` norm of a Schwartz function is the square root of the integral of the square of its
pointwise norm; this is the form in which the `L¹` bound will be converted into an `L²` bound, by
inserting the weight `1 + x²`.

* `norm_toLp_sq_eq_integral` : `‖f‖₂² = ∫ ‖f t‖²`.
* `weightSchwartz` : multiplication by `1 + x²` on the Schwartz space.
* `norm_apply_le_integral_norm_fourier` : **`‖f x‖ ≤ ∫ ‖𝓕 f‖`.**
-/

open scoped Real SchwartzMap FourierTransform
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## The `L²` norm as an integral -/

theorem norm_toLp_sq_eq_integral (f : 𝓢(ℝ, ℂ)) :
    ‖f.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) = ∫ t : ℝ, ‖f t‖ ^ (2 : ℕ) := by
  have hinner : (inner ℂ (f.toLp 2 (volume : Measure ℝ)) (f.toLp 2 (volume : Measure ℝ)) : ℂ)
      = ((∫ t : ℝ, ‖f t‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [SchwartzMap.coeFn_toLp f 2 (volume : Measure ℝ)] with x hx
    rw [hx, RCLike.inner_apply, Complex.mul_conj']
    push_cast
    ring
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hre := congrArg Complex.re hinner
  simpa [← Complex.ofReal_pow] using hre

/-! ## The quadratic weight -/

/-- Multiplication by `1 + x²`, as an operator on the Schwartz space. -/
def weightSchwartz : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ) + mulXCLM.comp mulXCLM

@[simp] theorem weightSchwartz_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    weightSchwartz f x = (1 + (x : ℂ) ^ (2 : ℕ)) * f x := by
  simp only [weightSchwartz, add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, mulXCLM_apply]
  ring

/-! ## The supremum bound -/

/-- **The supremum of a Schwartz function is bounded by the `L¹` norm of its Fourier
transform.**  Fourier inversion writes the value as an integral of the transform against a unit
complex number. -/
theorem norm_apply_le_integral_norm_fourier (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖f x‖ ≤ ∫ t : ℝ, ‖𝓕 ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖ := by
  have hinv : 𝓕⁻ (𝓕 ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) = ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) :=
    f.continuous.fourierInv_fourier_eq f.integrable (𝓕 f).integrable
  have hval : f x = (𝓕⁻ (𝓕 ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ))) x := (congrFun hinv x).symm
  rw [hval]
  show ‖(VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ)
    (𝓕 ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ))) x‖ ≤ _
  rw [VectorFourier.fourierIntegral]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [Circle.smul_def]

end GaloisForLFunctions

end
