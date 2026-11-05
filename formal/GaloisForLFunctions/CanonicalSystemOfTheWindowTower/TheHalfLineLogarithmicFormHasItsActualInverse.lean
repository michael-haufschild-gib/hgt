import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicFactorPreservesHalfLineSupport
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicCausalKernelHasItsFourierMultiplier
import GaloisForLFunctions.HTGeometry.L2ConvolutionFourierMultiplier

/-!
# The actual half-line logarithmic inverse

Causal convolution by the explicit probability density has range exactly the
finite logarithmic energy domain. The literal Fourier form pulls back to the
ordinary L² inner product. Convolution followed by its adjoint therefore gives
the unique finite-energy solution for every L² forcing on the positive half-line.
-/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform InnerProductSpace
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

open HTGeometry

/-- The actual causal density defines a whole-line Schur convolution operator. -/
def logarithmicConvolution : RealLineL2 →L[ℂ] RealLineL2 :=
  (convolutionKernel (fun x : ℝ => (logarithmicCausalKernel x : ℂ))
    (Complex.continuous_ofReal.measurable.comp measurable_logarithmicCausalKernel)
    integrable_complex_logarithmicCausalKernel).op

theorem logarithmicConvolution_coeFn (f : RealLineL2) :
    ((logarithmicConvolution f : RealLineL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ y : ℝ, (logarithmicCausalKernel (x - y) : ℂ) * (f : ℝ → ℂ) y :=
  (convolutionKernel (fun x : ℝ => (logarithmicCausalKernel x : ℂ))
    (Complex.continuous_ofReal.measurable.comp measurable_logarithmicCausalKernel)
    integrable_complex_logarithmicCausalKernel).op_coeFn f

/-- Causality of the literal convolution follows from the support of its density. -/
theorem logarithmicConvolution_mem_halfLine {f : RealLineL2} (hf : f ∈ RHTower.halfLineL2) :
    logarithmicConvolution f ∈ RHTower.halfLineL2 := by
  rw [RHTower.mem_halfLineL2_iff]
  have hfzero := (RHTower.mem_halfLineL2_iff f).mp hf
  filter_upwards [logarithmicConvolution_coeFn f] with x hx
  intro hxneg
  rw [hx]
  apply integral_eq_zero_of_ae
  filter_upwards [hfzero] with y hy
  change (logarithmicCausalKernel (x - y) : ℂ) * (f : ℝ → ℂ) y = 0
  by_cases hyneg : y < 0
  · rw [hy hyneg, mul_zero]
  · rw [logarithmicCausalKernel_of_nonpos (by linarith only [hxneg, le_of_not_gt hyneg]),
      Complex.ofReal_zero, zero_mul]

theorem integral_norm_complex_logarithmicCausalKernel :
    (∫ x : ℝ, ‖(logarithmicCausalKernel x : ℂ)‖) = 1 := by
  calc
    _ = ∫ x : ℝ, logarithmicCausalKernel x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Complex.norm_real, Real.norm_of_nonneg (logarithmicCausalKernel_nonneg x)]
    _ = 1 := logarithmicCausalKernel_mass_one.2

theorem norm_logarithmicConvolution_le_one : ‖logarithmicConvolution‖ ≤ 1 := by
  unfold logarithmicConvolution
  rw [convolutionKernel_op_eq_fourierMulCLM]
  exact (norm_fourierMulCLM_le _ _ _).trans_eq integral_norm_complex_logarithmicCausalKernel

/-- The Schur convolution and the reciprocal Fourier factor agree on every L² source. -/
theorem fourier_logarithmicConvolution (f : RealLineL2) :
    ((Lp.fourierTransformₗᵢ ℝ ℂ (logarithmicConvolution f) : RealLineL2) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (continuedLogReferenceFactor (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I))⁻¹ *
        ((Lp.fourierTransformₗᵢ ℝ ℂ f : RealLineL2) : ℝ → ℂ) ξ := by
  let g : ℝ → ℂ := fun x => (logarithmicCausalKernel x : ℂ)
  have hg : Integrable g := integrable_complex_logarithmicCausalKernel
  have he : fourierL2 ℝ (logarithmicConvolution f) =
      lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
        (continuous_fourier_of_integrable' hg).measurable
        (integral_nonneg fun x => norm_nonneg (g x)) (norm_fourier_apply_le_integral_norm g)
        (fourierL2 ℝ f) := by
    rw [logarithmicConvolution, convolutionKernel_op_eq_fourierMulCLM,
      fourierMulCLM_apply, fourierL2_fourierL2inv]
  change ((fourierL2 ℝ (logarithmicConvolution f) : RealLineL2) : ℝ → ℂ) =ᵐ[volume] _
  rw [he]
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
    (continuous_fourier_of_integrable' hg).measurable
    (integral_nonneg fun x => norm_nonneg (g x)) (norm_fourier_apply_le_integral_norm g)
    (fourierL2 ℝ f)] with ξ hξ
  rw [hξ]
  change 𝓕 (fun x : ℝ => (logarithmicCausalKernel x : ℂ)) ξ * _ = _
  rw [fourier_logarithmicCausalKernel]
  rfl

/-- Positive-half-line L², with its inherited Hilbert structure. -/
abbrev LogarithmicHalfLineL2 := RHTower.halfLineL2

instance : CompleteSpace LogarithmicHalfLineL2 :=
  RHTower.isClosed_halfLineL2.completeSpace_coe

/-- Causal convolution restricted to the actual positive-half-line space. -/
def logarithmicCausalOperator : LogarithmicHalfLineL2 →L[ℂ] LogarithmicHalfLineL2 :=
  (logarithmicConvolution.comp RHTower.halfLineL2.subtypeL).codRestrict
    RHTower.halfLineL2 (fun f => logarithmicConvolution_mem_halfLine f.property)

@[simp] theorem logarithmicCausalOperator_coe (f : LogarithmicHalfLineL2) :
    ((logarithmicCausalOperator f : LogarithmicHalfLineL2) : RealLineL2) = logarithmicConvolution f := rfl

theorem norm_logarithmicCausalOperator_le_one : ‖logarithmicCausalOperator‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖logarithmicConvolution (f : RealLineL2)‖ ≤ 1 * ‖(f : RealLineL2)‖
  exact (logarithmicConvolution.le_opNorm f).trans
    (mul_le_mul_of_nonneg_right norm_logarithmicConvolution_le_one (norm_nonneg _))

/-- The full multiplier graph domain is the literal finite logarithmic energy domain. -/
def HasLogarithmicEnergy (u : RealLineL2) : Prop :=
  MemLp (fun ξ : ℝ => continuedLogReferenceFactor (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) *
    ((Lp.fourierTransformₗᵢ ℝ ℂ u : RealLineL2) : ℝ → ℂ) ξ) 2 volume

/-- The unshifted positive logarithmic form on its actual Fourier domain. -/
def logarithmicHalfLineForm (u v : LogarithmicHalfLineL2) : ℂ :=
  ∫ ξ : ℝ, (positiveLogarithmicSymbol (2 * Real.pi * ξ) : ℂ) *
    star (((Lp.fourierTransformₗᵢ ℝ ℂ (u : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ) *
      ((Lp.fourierTransformₗᵢ ℝ ℂ (v : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ

private theorem continuous_logarithmicFrequencyFactor :
    Continuous (fun ξ : ℝ => continuedLogReferenceFactor (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) :=
  analyticOnNhd_continuedLogReferenceFactor.continuousOn.comp_continuous (by fun_prop)
    (fun ξ => Or.inl (by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero]
      norm_num))

/-- The graph-domain definition is exactly integrability of the literal logarithmic energy. -/
theorem hasLogarithmicEnergy_iff_integrable (u : RealLineL2) :
    HasLogarithmicEnergy u ↔ Integrable (fun ξ : ℝ => positiveLogarithmicSymbol (2 * Real.pi * ξ) *
      ‖((Lp.fourierTransformₗᵢ ℝ ℂ u : RealLineL2) : ℝ → ℂ) ξ‖ ^ 2) := by
  have hm := continuous_logarithmicFrequencyFactor.aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable (Lp.fourierTransformₗᵢ ℝ ℂ u))
  unfold HasLogarithmicEnergy
  simpa only [Pi.mul_apply, norm_mul, mul_pow, continuedLogReferenceFactor_imaginary_norm_sq] using!
    memLp_two_iff_integrable_sq_norm hm

/-- Finite logarithmic energy makes every mixed logarithmic form integral absolutely convergent. -/
theorem integrable_logarithmicHalfLineForm {u v : LogarithmicHalfLineL2}
    (hu : HasLogarithmicEnergy (u : RealLineL2)) (hv : HasLogarithmicEnergy (v : RealLineL2)) :
    Integrable (fun ξ : ℝ => (positiveLogarithmicSymbol (2 * Real.pi * ξ) : ℂ) *
      star (((Lp.fourierTransformₗᵢ ℝ ℂ (u : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ) *
        ((Lp.fourierTransformₗᵢ ℝ ℂ (v : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ) := by
  have hi := L2.integrable_inner (𝕜 := ℂ) (hu.toLp _) (hv.toLp _)
  apply hi.congr
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with ξ huξ hvξ
  rw [huξ, hvξ]
  let m := continuedLogReferenceFactor (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)
  have hmod : star m * m = (positiveLogarithmicSymbol (2 * Real.pi * ξ) : ℂ) := by
    rw [mul_comm, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact congrArg Complex.ofReal (continuedLogReferenceFactor_imaginary_norm_sq _)
  simp only [RCLike.inner_apply', starRingEnd_apply, star_mul]
  calc
    _ = (star m * m) *
        star (((Lp.fourierTransformₗᵢ ℝ ℂ (u : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ) *
          ((Lp.fourierTransformₗᵢ ℝ ℂ (v : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ := by ring
    _ = _ := by rw [hmod]

private theorem logarithmicFrequencyFactor_ne_zero (ξ : ℝ) :
    continuedLogReferenceFactor (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) ≠ 0 :=
  norm_pos_iff.mp (zero_lt_one.trans_le (one_le_norm_continuedLogReferenceFactor_imaginary _))

/-- Applying the inverse multiplier to an actual causal convolution recovers its source. -/
theorem logarithmicConvolution_factor_graph (f : RealLineL2) :
    (fun ξ : ℝ => continuedLogReferenceFactor (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) *
      ((Lp.fourierTransformₗᵢ ℝ ℂ (logarithmicConvolution f) : RealLineL2) : ℝ → ℂ) ξ) =ᵐ[volume]
      ((Lp.fourierTransformₗᵢ ℝ ℂ f : RealLineL2) : ℝ → ℂ) := by
  filter_upwards [fourier_logarithmicConvolution f] with ξ hξ
  rw [hξ, ← mul_assoc, mul_inv_cancel₀ (logarithmicFrequencyFactor_ne_zero ξ), one_mul]

theorem logarithmicConvolution_has_energy (f : RealLineL2) : HasLogarithmicEnergy (logarithmicConvolution f) := by
  exact (memLp_congr_ae (logarithmicConvolution_factor_graph f)).mpr
    (Lp.memLp (Lp.fourierTransformₗᵢ ℝ ℂ f))

/-- Every vector on the multiplier graph is recovered by literal convolution. -/
theorem logarithmicConvolution_eq_of_factor_graph {u v : RealLineL2}
    (huv : ((Lp.fourierTransformₗᵢ ℝ ℂ v : RealLineL2) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => continuedLogReferenceFactor (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) *
        ((Lp.fourierTransformₗᵢ ℝ ℂ u : RealLineL2) : ℝ → ℂ) ξ) :
    logarithmicConvolution v = u := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  apply Lp.ext
  filter_upwards [fourier_logarithmicConvolution v, huv] with ξ hv huvξ
  rw [hv, huvξ, ← mul_assoc, inv_mul_cancel₀ (logarithmicFrequencyFactor_ne_zero ξ), one_mul]

/-- Finite logarithmic energy is exactly the range of the causal convolution. -/
theorem hasLogarithmicEnergy_iff_mem_range (u : LogarithmicHalfLineL2) :
    HasLogarithmicEnergy (u : RealLineL2) ↔
      u ∈ LinearMap.range (logarithmicCausalOperator : LogarithmicHalfLineL2 →ₗ[ℂ] LogarithmicHalfLineL2) := by
  constructor
  · intro hu
    let F : ℝ → ℂ := fun ξ => continuedLogReferenceFactor (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) *
      ((Lp.fourierTransformₗᵢ ℝ ℂ (u : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ
    have hF : MemLp F 2 volume := hu
    let v : RealLineL2 := (Lp.fourierTransformₗᵢ ℝ ℂ).symm (hF.toLp F)
    have hv : ((Lp.fourierTransformₗᵢ ℝ ℂ v : RealLineL2) : ℝ → ℂ) =ᵐ[volume] F := by
      dsimp only [v]
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact hF.coeFn_toLp
    have hvs : v ∈ RHTower.halfLineL2 := logarithmicFactor_preserves_halfLine_support u.property hv
    refine ⟨⟨v, hvs⟩, ?_⟩
    apply Subtype.ext
    exact logarithmicConvolution_eq_of_factor_graph hv
  · rintro ⟨v, rfl⟩
    exact logarithmicConvolution_has_energy v

/-- Causal coordinates identify the literal logarithmic form with the ordinary L² inner product. -/
theorem logarithmicHalfLineForm_causalOperator (f g : LogarithmicHalfLineL2) :
    logarithmicHalfLineForm (logarithmicCausalOperator f) (logarithmicCausalOperator g) = inner ℂ f g := by
  have he : (fun ξ : ℝ => (positiveLogarithmicSymbol (2 * Real.pi * ξ) : ℂ) *
      star (((Lp.fourierTransformₗᵢ ℝ ℂ (logarithmicConvolution f) : RealLineL2) : ℝ → ℂ) ξ) *
        ((Lp.fourierTransformₗᵢ ℝ ℂ (logarithmicConvolution g) : RealLineL2) : ℝ → ℂ) ξ) =ᵐ[volume]
      fun ξ => inner ℂ
        (((Lp.fourierTransformₗᵢ ℝ ℂ (f : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ)
        (((Lp.fourierTransformₗᵢ ℝ ℂ (g : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ) := by
    filter_upwards [logarithmicConvolution_factor_graph f, logarithmicConvolution_factor_graph g] with ξ hf hg
    let m := continuedLogReferenceFactor (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)
    have hmod : (positiveLogarithmicSymbol (2 * Real.pi * ξ) : ℂ) = m * star m := by
      rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      exact congrArg Complex.ofReal (continuedLogReferenceFactor_imaginary_norm_sq _).symm
    calc
      _ = star (m * (((Lp.fourierTransformₗᵢ ℝ ℂ (logarithmicConvolution f) : RealLineL2) : ℝ → ℂ) ξ)) *
          (m * (((Lp.fourierTransformₗᵢ ℝ ℂ (logarithmicConvolution g) : RealLineL2) : ℝ → ℂ) ξ)) := by
        rw [hmod, star_mul]
        ring
      _ = _ := by rw [hf, hg, RCLike.inner_apply', starRingEnd_apply]
  calc
    _ = ∫ ξ : ℝ, inner ℂ
        (((Lp.fourierTransformₗᵢ ℝ ℂ (f : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ)
        (((Lp.fourierTransformₗᵢ ℝ ℂ (g : RealLineL2) : RealLineL2) : ℝ → ℂ) ξ) := integral_congr_ae he
    _ = inner ℂ (Lp.fourierTransformₗᵢ ℝ ℂ (f : RealLineL2))
        (Lp.fourierTransformₗᵢ ℝ ℂ (g : RealLineL2)) := (L2.inner_def _ _).symm
    _ = inner ℂ f g := (Lp.fourierTransformₗᵢ ℝ ℂ).inner_map_map _ _

/-- The actual half-line Green operator is the product of causal convolution and its adjoint. -/
def logarithmicHalfLineGreenOperator : LogarithmicHalfLineL2 →L[ℂ] LogarithmicHalfLineL2 :=
  logarithmicCausalOperator.comp logarithmicCausalOperator.adjoint

/-- The Green operator solves the literal logarithmic form equation against every finite-energy test. -/
theorem logarithmicHalfLineGreenOperator_solves (f : LogarithmicHalfLineL2) :
    HasLogarithmicEnergy (logarithmicHalfLineGreenOperator f : RealLineL2) ∧
    ∀ v : LogarithmicHalfLineL2, HasLogarithmicEnergy (v : RealLineL2) →
      logarithmicHalfLineForm v (logarithmicHalfLineGreenOperator f) = inner ℂ v f := by
  constructor
  · exact logarithmicConvolution_has_energy (logarithmicCausalOperator.adjoint f)
  · intro v hv
    obtain ⟨w, rfl⟩ := (hasLogarithmicEnergy_iff_mem_range v).mp hv
    change logarithmicHalfLineForm (logarithmicCausalOperator w)
      (logarithmicCausalOperator (logarithmicCausalOperator.adjoint f)) = _
    rw [logarithmicHalfLineForm_causalOperator]
    exact logarithmicCausalOperator.adjoint_inner_right w f

/-- The logarithmic Dirichlet equation has exactly one finite-energy half-line solution. -/
theorem logarithmicHalfLineGreenOperator_unique (f u : LogarithmicHalfLineL2)
    (hu : HasLogarithmicEnergy (u : RealLineL2))
    (hsolve : ∀ v : LogarithmicHalfLineL2, HasLogarithmicEnergy (v : RealLineL2) →
      logarithmicHalfLineForm v u = inner ℂ v f) :
    u = logarithmicHalfLineGreenOperator f := by
  obtain ⟨w, rfl⟩ := (hasLogarithmicEnergy_iff_mem_range u).mp hu
  have hw : w = logarithmicCausalOperator.adjoint f := by
    apply ext_inner_left ℂ
    intro v
    have h := hsolve (logarithmicCausalOperator v) (logarithmicConvolution_has_energy v)
    change logarithmicHalfLineForm (logarithmicCausalOperator v) (logarithmicCausalOperator w) =
      inner ℂ (logarithmicCausalOperator v) f at h
    rw [logarithmicHalfLineForm_causalOperator] at h
    exact h.trans (logarithmicCausalOperator.adjoint_inner_right v f).symm
  rw [hw]
  rfl

/-- Every L² forcing has exactly one solution in the literal finite logarithmic energy domain. -/
theorem existsUnique_logarithmicHalfLine_solution (f : LogarithmicHalfLineL2) :
    ∃! u : LogarithmicHalfLineL2, HasLogarithmicEnergy (u : RealLineL2) ∧
      ∀ v : LogarithmicHalfLineL2, HasLogarithmicEnergy (v : RealLineL2) →
        logarithmicHalfLineForm v u = inner ℂ v f := by
  refine ⟨logarithmicHalfLineGreenOperator f, logarithmicHalfLineGreenOperator_solves f, ?_⟩
  intro u hu
  exact logarithmicHalfLineGreenOperator_unique f u hu.1 hu.2

#print axioms hasLogarithmicEnergy_iff_integrable
#print axioms integrable_logarithmicHalfLineForm
#print axioms logarithmicHalfLineGreenOperator_solves
#print axioms existsUnique_logarithmicHalfLine_solution

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
