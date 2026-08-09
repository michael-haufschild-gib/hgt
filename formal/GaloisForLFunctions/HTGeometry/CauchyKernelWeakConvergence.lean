import GaloisForLFunctions.HTGeometry.LeafCauchyTransform

/-!
# Weak convergence transports the Cauchy transform

Off the real axis the Cauchy kernel `x ↦ (x − z)⁻¹` is a bounded continuous complex function of the
real variable, so its real and imaginary parts are bounded continuous test functions.  Weak
convergence of probability measures therefore carries the Cauchy transform along, coordinate by
coordinate.
-/

open scoped BigOperators
open MeasureTheory Filter Topology

namespace HTGeometry

/-- The Cauchy kernel is continuous in the real variable, off the real axis. -/
theorem continuous_cauchyKernel {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun x : ℝ => ((x : ℂ) - z)⁻¹ := by
  have hne : ∀ x : ℝ, ((x : ℂ) - z) ≠ 0 := by
    intro x hcon
    apply hz
    have hzx : z = ((x : ℝ) : ℂ) := by linear_combination -hcon
    rw [hzx]
    simp
  exact (Complex.continuous_ofReal.sub continuous_const).inv₀ hne

/-- The real part of the Cauchy kernel as a bounded continuous test function. -/
noncomputable def cauchyKernelRe (z : ℂ) (hz : z.im ≠ 0) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : ℝ => (((x : ℂ) - z)⁻¹).re)
    (Complex.continuous_re.comp (continuous_cauchyKernel hz)) |z.im|⁻¹
    fun x => le_trans (Complex.abs_re_le_norm _) (norm_cauchy_kernel_le x hz)

/-- The imaginary part of the Cauchy kernel as a bounded continuous test function. -/
noncomputable def cauchyKernelIm (z : ℂ) (hz : z.im ≠ 0) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : ℝ => (((x : ℂ) - z)⁻¹).im)
    (Complex.continuous_im.comp (continuous_cauchyKernel hz)) |z.im|⁻¹
    fun x => le_trans (Complex.abs_im_le_norm _) (norm_cauchy_kernel_le x hz)

@[simp] theorem cauchyKernelRe_apply {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) :
    cauchyKernelRe z hz x = (((x : ℂ) - z)⁻¹).re := rfl

@[simp] theorem cauchyKernelIm_apply {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) :
    cauchyKernelIm z hz x = (((x : ℂ) - z)⁻¹).im := rfl

/-- The complex Cauchy transform is its real and imaginary transforms. -/
theorem cauchyTransform_eq_re_add_im (μ : Measure ℝ) [IsFiniteMeasure μ] {z : ℂ}
    (hz : z.im ≠ 0) :
    ∫ x, ((x : ℂ) - z)⁻¹ ∂μ
      = (((∫ x, (((x : ℂ) - z)⁻¹).re ∂μ : ℝ)) : ℂ)
        + (((∫ x, (((x : ℂ) - z)⁻¹).im ∂μ : ℝ)) : ℂ) * Complex.I := by
  have hint : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ := integrable_cauchy_kernel μ hz
  have hre : ∫ x, (((x : ℂ) - z)⁻¹).re ∂μ = (∫ x, ((x : ℂ) - z)⁻¹ ∂μ).re := by
    simpa using Complex.reCLM.integral_comp_comm hint
  have him : ∫ x, (((x : ℂ) - z)⁻¹).im ∂μ = (∫ x, ((x : ℂ) - z)⁻¹ ∂μ).im := by
    simpa using Complex.imCLM.integral_comp_comm hint
  rw [hre, him, Complex.re_add_im]

/-- **Weak convergence carries the Cauchy transform.** -/
theorem tendsto_cauchyTransform_of_tendsto {ι : Type*} {F : Filter ι}
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hlim : Tendsto μs F (𝓝 μ)) {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun i => ∫ x, ((x : ℂ) - z)⁻¹ ∂(μs i : Measure ℝ)) F
      (𝓝 (∫ x, ((x : ℂ) - z)⁻¹ ∂(μ : Measure ℝ))) := by
  have hall := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim
  have hre := hall (cauchyKernelRe z hz)
  have him := hall (cauchyKernelIm z hz)
  have hcomb : Tendsto (fun i =>
      (((∫ x, (((x : ℂ) - z)⁻¹).re ∂(μs i : Measure ℝ) : ℝ)) : ℂ)
        + (((∫ x, (((x : ℂ) - z)⁻¹).im ∂(μs i : Measure ℝ) : ℝ)) : ℂ) * Complex.I) F
      (𝓝 ((((∫ x, (((x : ℂ) - z)⁻¹).re ∂(μ : Measure ℝ) : ℝ)) : ℂ)
        + (((∫ x, (((x : ℂ) - z)⁻¹).im ∂(μ : Measure ℝ) : ℝ)) : ℂ) * Complex.I)) := by
    refine (((Complex.continuous_ofReal.tendsto _).comp hre).add ?_)
    exact (((Complex.continuous_ofReal.tendsto _).comp him).mul_const Complex.I)
  rw [cauchyTransform_eq_re_add_im _ hz]
  refine hcomb.congr fun i => ?_
  exact (cauchyTransform_eq_re_add_im (μs i : Measure ℝ) hz).symm

end HTGeometry
