import GaloisForLFunctions.RHTower.CCMArchimedeanQuantizedTraceClass
import GaloisForLFunctions.HTGeometry.SchattenOneBanach
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Trace-norm continuity of the literal Hardy quantized differential

The actual Volterra factorization bounds the positive Hankel trace norm by
a continuous Schwartz derivative seminorm. Reflection, adjoint and Fourier
conjugation transport this continuity to both original Hardy crossblocks.
Thus the original quantized differential has a continuous lift to the genuine
Schatten-one Banach carrier, not merely pointwise trace-class membership.

This supplies the ideal-topology step for source cutoff admission. Convergence
of the original Gamma cutoff symbols in Schwartz topology remains separate.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped SchwartzMap ENNReal
namespace RHTower
local instance : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩

private theorem field_norm_bound (g : 𝓢(ℝ, ℂ)) :
    ‖ccmHankelDerivativeField g‖ ≤ Real.pi * ccmDerivativeDecayConstant g := by
  let C := ccmDerivativeDecayConstant g
  have hC : 0 ≤ C := ccmDerivativeDecayConstant_nonneg g
  have hi : Integrable (fun t : ℝ => (C^2*Real.pi)*(1+t^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hf := (memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (ccmHankelDerivativeField g))).mp
      (Lp.memLp (ccmHankelDerivativeField g))
  have hs : ‖ccmHankelDerivativeField g‖^2 ≤ C^2*Real.pi^2 := by
    rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    calc
      _ ≤ ∫ t, (C^2*Real.pi)*(1+t^2)⁻¹ ∂ccmPositiveMeasure := by
        apply integral_mono_ae hf hi.integrableOn
        filter_upwards [(ccmHankelDerivativeSlice_memLp g).coeFn_toLp,
          ae_restrict_mem measurableSet_Ici] with t ht hpos
        change ‖ccmHankelDerivativeField g t‖^2 ≤ _
        rw [show ccmHankelDerivativeField g t=ccmHankelDerivativeSlice g t from ht]
        simpa only [mul_assoc,mul_comm,mul_left_comm] using norm_ccmHankelDerivativeSlice_sq_le g hpos
      _ ≤ ∫ t : ℝ, (C^2*Real.pi)*(1+t^2)⁻¹ := by
        exact setIntegral_le_integral hi (Eventually.of_forall fun t => by positivity)
      _ = C^2*Real.pi^2 := by
        rw [integral_const_mul,integral_univ_inv_one_add_sq]
        ring
  change ‖ccmHankelDerivativeField g‖ ≤ Real.pi * C
  nlinarith [norm_nonneg (ccmHankelDerivativeField g), Real.pi_pos, mul_nonneg Real.pi_pos.le hC]

private theorem field_sub (g h : 𝓢(ℝ, ℂ)) :
    ccmHankelDerivativeField (g-h)=ccmHankelDerivativeField g-ccmHankelDerivativeField h := by
  apply Lp.ext
  filter_upwards [(ccmHankelDerivativeSlice_memLp (g-h)).coeFn_toLp,
    (ccmHankelDerivativeSlice_memLp g).coeFn_toLp,
    (ccmHankelDerivativeSlice_memLp h).coeFn_toLp,
    Lp.coeFn_sub (ccmHankelDerivativeField g) (ccmHankelDerivativeField h)] with t hgh hg hh hsub
  rw [hsub]
  simp only [Pi.sub_apply]
  change _ = _ at hgh hg hh
  rw [show ccmHankelDerivativeField (g-h) t=ccmHankelDerivativeSlice (g-h) t from hgh,
    show ccmHankelDerivativeField g t=ccmHankelDerivativeSlice g t from hg,
    show ccmHankelDerivativeField h t=ccmHankelDerivativeSlice h t from hh]
  unfold ccmHankelDerivativeSlice
  change _ • (ccmPositiveHalfLineProjection ((SchwartzMap.toLpCLM ℂ ℂ 2 volume)
    (SchwartzMap.translateCLM ℂ t (SchwartzMap.derivCLM ℂ ℂ (g-h))))) = _
  simp only [map_sub,smul_sub]
  rfl

private theorem positiveHankel_sub (g h : 𝓢(ℝ, ℂ)) :
    ccmPositiveHankel (g-h)=ccmPositiveHankel g-ccmPositiveHankel h := by
  unfold ccmPositiveHankel ccmHankelDerivativeSynthesis
  rw [field_sub]
  simp only [l2Synthesis,map_sub,ContinuousLinearMap.sub_comp]

private theorem decay_continuous : Continuous ccmDerivativeDecayConstant := by
  have hc : Continuous (fun g : 𝓢(ℝ, ℂ) =>
      (Finset.Iic (6,0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) g) :=
    Seminorm.continuous_finsetSup (fun i _ =>
      (schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm i)
  exact (hc.comp (SchwartzMap.derivCLM ℂ ℂ).continuous).const_mul _

/-- The actual positive Hankel operator in the genuine trace-norm carrier. -/
def ccmPositiveHankelNuclear (g : 𝓢(ℝ, ℂ)) : SchattenOneOperator SoninL2 :=
  ⟨ccmPositiveHankel g, ccmPositiveHankel_memSchattenClass_one g⟩

private theorem nuclear_norm_bound (g : 𝓢(ℝ, ℂ)) :
    ‖ccmPositiveHankelNuclear g‖ ≤
      ContinuousLinearMap.hsNorm ccmVolterraObserver * (Real.pi * ccmDerivativeDecayConstant g) := by
  change traceNorm SoninL2 (ccmPositiveHankel g) ≤ _
  rw [← rectTraceNorm_eq_traceNorm]
  have hh := rectTraceNorm_comp_le_hsNorm_mul_hsNorm_unrestricted
    ccmVolterraObserver_isHilbertSchmidt (ccmHankelDerivativeSynthesis_isHilbertSchmidt g)
  have hn : ContinuousLinearMap.hsNorm (ccmHankelDerivativeSynthesis g)=‖ccmHankelDerivativeField g‖ := by
    unfold ccmHankelDerivativeSynthesis ContinuousLinearMap.hsNorm
    rw [hsNormSq_l2Synthesis_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]
  rw [hn] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (field_norm_bound g) (Real.sqrt_nonneg _))

/-- Schwartz convergence of the actual positive Hankel symbols implies genuine trace-norm convergence. -/
theorem continuous_ccmPositiveHankelNuclear : Continuous ccmPositiveHankelNuclear := by
  rw [continuous_iff_continuousAt]
  intro g
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  have hz : ccmDerivativeDecayConstant (0 : 𝓢(ℝ, ℂ))=0 := by
    simp [ccmDerivativeDecayConstant]
  have ht := (((decay_continuous.comp
    (continuous_id.sub (continuous_const (y := g)))).tendsto g).const_mul Real.pi).const_mul
      (ContinuousLinearMap.hsNorm ccmVolterraObserver)
  have hlim : Tendsto (fun h : 𝓢(ℝ, ℂ) => ContinuousLinearMap.hsNorm ccmVolterraObserver *
      (Real.pi * ccmDerivativeDecayConstant (h-g))) (𝓝 g) (𝓝 0) := by
    simpa only [Function.comp_apply, Pi.sub_apply, id_eq, sub_self,hz,mul_zero] using ht
  apply squeeze_zero (fun h => norm_nonneg _) (fun h => ?_) hlim
  have he : ccmPositiveHankelNuclear h-ccmPositiveHankelNuclear g=
      ccmPositiveHankelNuclear (h-g) := by
    apply SchattenOneOperator.ext
    exact (positiveHankel_sub h g).symm
  rw [he]
  exact nuclear_norm_bound (h-g)

private def leftNuclear (L : SoninL2 →L[ℂ] SoninL2) :
    SchattenOneOperator SoninL2 →L[ℂ] SchattenOneOperator SoninL2 :=
  LinearMap.mkContinuous
    { toFun := fun T => ⟨L ∘L T.val, memSchattenClass_one_comp_left T.property L⟩
      map_add' := by
        intro S T
        apply SchattenOneOperator.ext
        exact ContinuousLinearMap.comp_add L S.val T.val
      map_smul' := by
        intro c T
        apply SchattenOneOperator.ext
        exact ContinuousLinearMap.comp_smul L c T.val }
    ‖L‖ (fun T => traceNorm_comp_left_le T.summable L)

private def rightNuclear (R : SoninL2 →L[ℂ] SoninL2) :
    SchattenOneOperator SoninL2 →L[ℂ] SchattenOneOperator SoninL2 :=
  LinearMap.mkContinuous
    { toFun := fun T => ⟨T.val ∘L R, memSchattenClass_one_comp_right T.property R⟩
      map_add' := by intro S T; apply SchattenOneOperator.ext; rfl
      map_smul' := by intro c T; apply SchattenOneOperator.ext; rfl }
    ‖R‖ (fun T => by
      change traceNorm SoninL2 (T.val ∘L R) ≤ ‖R‖ * traceNorm SoninL2 T.val
      simpa only [mul_comm] using traceNorm_comp_right_le T.summable R)

private def adjointNuclear : SchattenOneOperator SoninL2 →ₗᵢ⋆[ℂ] SchattenOneOperator SoninL2 where
  toFun T := ⟨ContinuousLinearMap.adjoint T.val,
    (memSchattenClass_adjoint_iff 1 T.val).mpr T.property⟩
  map_add' S T := by
    apply SchattenOneOperator.ext
    exact ContinuousLinearMap.adjoint.map_add S.val T.val
  map_smul' c T := by
    apply SchattenOneOperator.ext
    exact ContinuousLinearMap.adjoint.map_smulₛₗ c T.val
  norm_map' T := by
    change traceNorm SoninL2 (ContinuousLinearMap.adjoint T.val) = traceNorm SoninL2 T.val
    rw [← rectTraceNorm_eq_traceNorm, ← rectTraceNorm_eq_traceNorm, rectTraceNorm_adjoint]

private def upperNuclear (g : 𝓢(ℝ, ℂ)) : SchattenOneOperator SoninL2 :=
  rightNuclear l2Reflection (ccmPositiveHankelNuclear (FourierTransform.fourierInv g))

private theorem upperNuclear_coe (g : 𝓢(ℝ, ℂ)) :
    (upperNuclear g : SoninL2 →L[ℂ] SoninL2)=ccmTimeUpperCrossBlock g := by
  rw [ccmTimeUpperCrossBlock_eq_positiveBlock_comp_reflection,
    ccmPositiveFourierHankelBlock_eq_ccmPositiveHankel]
  rfl

private theorem upperNuclear_continuous : Continuous upperNuclear :=
  (rightNuclear l2Reflection).continuous.comp
    (continuous_ccmPositiveHankelNuclear.comp (FourierTransform.fourierInvCLM ℂ (𝓢(ℝ, ℂ))).continuous)

private def lowerNuclear (g : 𝓢(ℝ, ℂ)) : SchattenOneOperator SoninL2 :=
  adjointNuclear (upperNuclear (SchwartzMap.conjSLM g))

private theorem lowerNuclear_coe (g : 𝓢(ℝ, ℂ)) :
    (lowerNuclear g : SoninL2 →L[ℂ] SoninL2)=ccmTimeLowerCrossBlock g := by
  change ContinuousLinearMap.adjoint
    (upperNuclear (SchwartzMap.conjSLM g) : SoninL2 →L[ℂ] SoninL2)=_
  rw [upperNuclear_coe,adjoint_ccmTimeUpperCrossBlock_conj]

/-- The original real-line quantized differential, in the genuine Schatten-one carrier. -/
def ccmQuantizedDifferentialNuclear (g : 𝓢(ℝ, ℂ)) : SchattenOneOperator SoninL2 :=
  (2 : ℂ) • leftNuclear fourierUnitary.toLinearIsometry.toContinuousLinearMap
    (rightNuclear fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap
      (upperNuclear g-lowerNuclear g))

/-- Exact source identity of the nuclear lift, retaining both actual Hardy crossblocks. -/
theorem ccmQuantizedDifferentialNuclear_coe (g : 𝓢(ℝ, ℂ)) :
    (ccmQuantizedDifferentialNuclear g : SoninL2 →L[ℂ] SoninL2)=ccmQuantizedDifferential g := by
  rw [ccmQuantizedDifferential_eq_two_smul_crossBlocks,
    ccmHardyUpperCrossBlock_eq_fourierConjugate,
    ccmHardyLowerCrossBlock_eq_fourierConjugate]
  change (2 : ℂ) • (fourierUnitary.toLinearIsometry.toContinuousLinearMap ∘L
    ((upperNuclear g-lowerNuclear g).val ∘L
      fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap)) = _
  change (2 : ℂ) • (fourierUnitary.toLinearIsometry.toContinuousLinearMap ∘L
    (((upperNuclear g : SoninL2 →L[ℂ] SoninL2)-(lowerNuclear g : SoninL2 →L[ℂ] SoninL2)) ∘L
      fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap)) = _
  rw [upperNuclear_coe,lowerNuclear_coe,ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_sub]

/-- Schwartz convergence of symbols transports their literal Hardy commutators in trace norm. -/
theorem continuous_ccmQuantizedDifferentialNuclear : Continuous ccmQuantizedDifferentialNuclear := by
  have hl : Continuous lowerNuclear := adjointNuclear.continuous.comp
    (upperNuclear_continuous.comp SchwartzMap.conjSLM.continuous)
  exact ((leftNuclear fourierUnitary.toLinearIsometry.toContinuousLinearMap).continuous.comp
    ((rightNuclear fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap).continuous.comp
      (upperNuclear_continuous.sub hl))).const_smul (2 : ℂ)

end RHTower
