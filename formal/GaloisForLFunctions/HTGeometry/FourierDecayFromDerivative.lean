import GaloisForLFunctions.HTGeometry.SobolevWeightDecay

/-!
# Order-one Fourier decay from an integrable derivative

One integration by parts turns an integrable derivative into decay of the transform: the transform
of `f'` is `2π i ξ` times the transform of `f`, and every transform is bounded by the `L¹` norm of
its input.  So

`‖f̂(ξ)‖ · 2π|ξ| ≤ ‖f'‖₁`   and   `‖f̂(ξ)‖ ≤ ‖f‖₁`,

which are exactly the two hypotheses of the fractional Sobolev criterion.  Combining them puts
every integrable function with integrable derivative in each Sobolev weight below one half — the
threshold, and the reason a bounded-variation profile just misses `H^{1/2}`.
-/

open Real MeasureTheory FourierTransform

namespace GaloisForLFunctions.HTGeometry

/-- **Order-one decay.**  The transform of a function with integrable derivative decays like
`1/|ξ|`, with constant the `L¹` norm of the derivative. -/
theorem norm_fourier_mul_le_integral_norm_deriv {f : ℝ → ℂ}
    (hf : Integrable f) (hdiff : Differentiable ℝ f) (hf' : Integrable (deriv f)) (ξ : ℝ) :
    ‖fourier f ξ‖ * (2 * π * |ξ|) ≤ ∫ t, ‖deriv f t‖ := by
  have hkey := congrFun (Real.fourier_deriv hf hdiff hf') ξ
  have hbound : ‖fourier (deriv f) ξ‖ ≤ ∫ t, ‖deriv f t‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  rw [hkey] at hbound
  have hnorm : ‖(2 * (π : ℂ) * Complex.I * (ξ : ℂ)) • fourier f ξ‖ =
      ‖fourier f ξ‖ * (2 * π * |ξ|) := by
    rw [norm_smul]
    have h1 : ‖(2 * (π : ℂ) * Complex.I * (ξ : ℂ))‖ = 2 * π * |ξ| := by
      rw [norm_mul, norm_mul, norm_mul]
      simp [abs_of_nonneg Real.pi_nonneg]
    rw [h1]
    ring
  rw [hnorm] at hbound
  exact hbound

/-- Every transform is bounded by the `L¹` norm of its input. -/
theorem norm_fourier_le_integral_norm (f : ℝ → ℂ) (ξ : ℝ) :
    ‖fourier f ξ‖ ≤ ∫ t, ‖f t‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- **Fractional Sobolev membership from an integrable derivative.**  An integrable function whose
derivative is integrable lies in every Sobolev weight strictly below one half.  The exponent is
sharp for this hypothesis: order-one decay is exactly the borderline. -/
theorem memSobolevWeight_of_integrable_deriv {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1 / 2)
    {f : ℝ → ℂ} (hf : Integrable f) (hdiff : Differentiable ℝ f) (hf' : Integrable (deriv f)) :
    MemSobolevWeight s (fourier f) := by
  have hM : (0 : ℝ) ≤ ∫ t, ‖f t‖ := integral_nonneg fun _ => norm_nonneg _
  have hK : (0 : ℝ) ≤ (∫ t, ‖deriv f t‖) / (2 * π) := by
    have hpi : (0 : ℝ) < 2 * π := by positivity
    exact div_nonneg (integral_nonneg fun _ => norm_nonneg _) hpi.le
  refine memSobolevWeight_of_decay hs0 hs hM hK ?_ (fun ξ => norm_fourier_le_integral_norm f ξ) ?_
  · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) hf).aestronglyMeasurable
  · intro ξ hξ
    have hpi : (0 : ℝ) < 2 * π := by positivity
    have hmain := norm_fourier_mul_le_integral_norm_deriv hf hdiff hf' ξ
    rw [le_div_iff₀ hpi]
    calc ‖fourier f ξ‖ * |ξ| * (2 * π) = ‖fourier f ξ‖ * (2 * π * |ξ|) := by ring
      _ ≤ ∫ t, ‖deriv f t‖ := hmain

end GaloisForLFunctions.HTGeometry
