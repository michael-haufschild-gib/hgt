import GaloisForLFunctions.HTGeometry.LeafIntegral

/-!
# The Cauchy transform of a leaf

Off the real axis the Cauchy kernel is bounded, so it is integrable against a leaf and its integral is
the fiber sum

`m_τ(z) = ∑_{ξ ∈ F_τ} λ(ξ)/(ξ − z)`,

an explicit series indexed by the zeros of `B·τ − D`, with the Christoffel weights.  The transform is
bounded by `|Im z|⁻¹`, uniformly in the parameter.
-/

open scoped BigOperators
open MeasureTheory OnePoint
open scoped OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The vector-valued form of integration against a weighted Dirac family. -/
theorem integral_fiberMeasure_vector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (w : ℝ → ℝ) (F : Set ℝ) (f : ℝ → E) (hf : Integrable f (fiberMeasure w F)) :
    ∫ x, f x ∂(fiberMeasure w F)
      = ∑' p : ↥F, (ENNReal.ofReal (w (p : ℝ))).toReal • f (p : ℝ) := by
  have hf' : Integrable f (Measure.sum fun p : ↥F =>
      ENNReal.ofReal (w (p : ℝ)) • Measure.dirac (p : ℝ)) := hf
  have hsum : ∫ x, f x ∂(fiberMeasure w F)
      = ∑' p : ↥F, ∫ x, f x ∂(ENNReal.ofReal (w (p : ℝ)) • Measure.dirac (p : ℝ)) := by
    rw [fiberMeasure]
    exact integral_sum_measure hf'
  rw [hsum]
  refine tsum_congr fun p => ?_
  rw [integral_smul_measure, integral_dirac]

/-- **The Cauchy kernel is bounded off the real axis.** -/
theorem norm_cauchy_kernel_le (x : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ‖((x : ℂ) - z)⁻¹‖ ≤ |z.im|⁻¹ := by
  have him : |z.im| ≤ ‖(x : ℂ) - z‖ := by
    have h1 : |((x : ℂ) - z).im| ≤ ‖(x : ℂ) - z‖ := Complex.abs_im_le_norm _
    have h2 : ((x : ℂ) - z).im = -z.im := by simp
    rw [h2, abs_neg] at h1
    exact h1
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  rw [norm_inv, ← one_div, ← one_div]
  exact one_div_le_one_div_of_le hpos him

/-- The Cauchy kernel is integrable against any finite measure on `ℝ`, off the real axis. -/
theorem integrable_cauchy_kernel (μ : Measure ℝ) [IsFiniteMeasure μ] {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ := by
  refine Integrable.mono' (integrable_const |z.im|⁻¹) ?_
    (Filter.Eventually.of_forall fun x => norm_cauchy_kernel_le x hz)
  refine (Continuous.aestronglyMeasurable ?_)
  refine Continuous.inv₀ (by fun_prop) fun x => ?_
  intro hc
  have h2 : ((x : ℂ) - z).im = -z.im := by simp
  rw [hc] at h2
  simp only [Complex.zero_im] at h2
  exact hz (by linarith [h2])

/-- **The Cauchy transform of a leaf is the Christoffel-weighted fiber series.** -/
theorem cauchyTransform_nevLeaf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (tau : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ∫ x, ((x : ℂ) - z)⁻¹ ∂(nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ)
      = ∑' p : ↥((nevMatrixDataInf h h0b).finiteDenominatorFiber tau),
          (christoffelLimit s (p : ℝ)) • (((p : ℝ) : ℂ) - z)⁻¹ := by
  haveI : IsProbabilityMeasure (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ) := inferInstance
  have hrw := nevLeaf_eq_fiberMeasure h h0b h0 tau
  have hint : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹)
      (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ) :=
    integrable_cauchy_kernel _ hz
  have hint' : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹)
      (fiberMeasure (fun x => christoffelLimit s x)
        ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau)) := by
    rwa [hrw] at hint
  rw [hrw, integral_fiberMeasure_vector _ _ _ hint']
  refine tsum_congr fun p => ?_
  rw [ENNReal.toReal_ofReal (christoffelLimit_nonneg h _)]

/-- **The Cauchy transform is bounded by `|Im z|⁻¹`, uniformly in the parameter.** -/
theorem norm_cauchyTransform_nevLeaf_le (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (t : OnePoint ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ‖∫ x, ((x : ℂ) - z)⁻¹ ∂(nevLeaf h h0b h0 t : Measure ℝ)‖ ≤ |z.im|⁻¹ := by
  haveI : IsProbabilityMeasure (nevLeaf h h0b h0 t : Measure ℝ) := inferInstance
  have hbound := norm_integral_le_of_norm_le_const
    (μ := (nevLeaf h h0b h0 t : Measure ℝ)) (C := |z.im|⁻¹)
    (Filter.Eventually.of_forall fun x => norm_cauchy_kernel_le x hz)
  simpa using hbound

end HTGeometry
