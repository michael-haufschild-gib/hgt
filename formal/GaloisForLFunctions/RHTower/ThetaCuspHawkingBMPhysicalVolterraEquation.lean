import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceForcedCausal
import GaloisForLFunctions.HTGeometry.FourierUniquenessL1
import GaloisForLFunctions.HTGeometry.HalfLineLaplaceFourier
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
open MeasureTheory Set Filter Topology Convolution
open scoped FourierTransform
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem positive_convolution (k : ℝ → ℂ) (f : ℝ → H) (t : ℝ) :
    (((Ioi (0:ℝ)).indicator k) ⋆[ContinuousLinearMap.lsmul ℂ ℂ]
      ((Ioi (0:ℝ)).indicator f)) t =
      (Ioi (0:ℝ)).indicator (fun t => ∫ u in (0:ℝ)..t, k (t-u) • f u) t := by
  rw [convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply]
  by_cases ht : 0 < t
  · rw [Set.indicator_of_mem (show t ∈ Ioi (0:ℝ) from ht),intervalIntegral.integral_of_le ht.le,
      integral_Ioc_eq_integral_Ioo,← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro u
    dsimp only
    by_cases hu : u ∈ Ioo (0:ℝ) t
    · simp only [Set.indicator_of_mem hu,Set.indicator_of_mem (show u ∈ Ioi (0:ℝ) from hu.1),
        Set.indicator_of_mem (show t-u ∈ Ioi (0:ℝ) from sub_pos.mpr hu.2)]
    · rw [Set.indicator_of_notMem hu]
      by_cases hu0 : 0 < u
      · have htu : ¬0 < t-u := by
          intro h
          exact hu ⟨hu0,sub_pos.mp h⟩
        rw [Set.indicator_of_notMem (show t-u ∉ Ioi (0:ℝ) from htu),zero_smul]
      · rw [Set.indicator_of_notMem (show u ∉ Ioi (0:ℝ) from hu0),smul_zero]
  · rw [Set.indicator_of_notMem (show t ∉ Ioi (0:ℝ) from ht)]
    apply integral_eq_zero_of_ae
    apply Eventually.of_forall
    intro u
    change (Ioi (0:ℝ)).indicator k (t-u) • (Ioi (0:ℝ)).indicator f u = 0
    by_cases hu : 0 < u
    · have htu : ¬0 < t-u := by linarith [le_of_not_gt ht]
      rw [Set.indicator_of_notMem (show t-u ∉ Ioi (0:ℝ) from htu),zero_smul]
    · rw [Set.indicator_of_notMem (show u ∉ Ioi (0:ℝ) from hu),smul_zero]

private theorem ray_mul (w : ℂ) (t u : ℝ) : expRay w (t-u)*expRay w u=expRay w t := by
  unfold expRay
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private def positiveRayKernel (w : ℂ) : ℝ → ℂ := (Ioi (0:ℝ)).indicator (expRay w)
private def positiveTimeKernel (w : ℂ) : ℝ → ℂ :=
  (Ioi (0:ℝ)).indicator (fun t => (t:ℂ)*expRay w t)

private theorem positiveRayKernel_integrable {w : ℂ} (hw : 0 < w.re) :
    Integrable (positiveRayKernel w) := by
  rw [positiveRayKernel,integrable_indicator_iff measurableSet_Ioi]
  simpa only [expRay,neg_mul] using!
    integrableOn_exp_mul_complex_Ioi (a := -w) (by simpa only [Complex.neg_re,neg_lt_zero] using hw) 0

private theorem positiveRayKernel_integral {w : ℂ} (hw : 0 < w.re) :
    (∫ t, positiveRayKernel w t) = w⁻¹ := by
  rw [positiveRayKernel,integral_indicator measurableSet_Ioi]
  simp only [expRay,← neg_mul]
  rw [integral_exp_mul_complex_Ioi (a := -w) (by simpa only [Complex.neg_re,neg_lt_zero] using hw) 0]
  simp

private theorem positiveTimeKernel_eq_convolution (w : ℂ) :
    positiveTimeKernel w = positiveRayKernel w ⋆[ContinuousLinearMap.lsmul ℂ ℂ] positiveRayKernel w := by
  funext t
  rw [positiveRayKernel,positive_convolution]
  by_cases ht : 0 < t
  · rw [positiveTimeKernel,Set.indicator_of_mem (show t ∈ Ioi (0:ℝ) from ht),Set.indicator_of_mem (show t ∈ Ioi (0:ℝ) from ht)]
    simp only [smul_eq_mul,ray_mul]
    rw [intervalIntegral.integral_const]
    simp only [sub_zero,Complex.real_smul]
  · rw [positiveTimeKernel,Set.indicator_of_notMem (show t ∉ Ioi (0:ℝ) from ht),Set.indicator_of_notMem (show t ∉ Ioi (0:ℝ) from ht)]

private theorem positiveTimeKernel_integrable {w : ℂ} (hw : 0 < w.re) :
    Integrable (positiveTimeKernel w) := by
  rw [positiveTimeKernel_eq_convolution]
  exact (positiveRayKernel_integrable hw).integrable_convolution _ (positiveRayKernel_integrable hw)

private theorem positiveTimeKernel_integral {w : ℂ} (hw : 0 < w.re) :
    (∫ t, positiveTimeKernel w t) = (w⁻¹)^2 := by
  rw [positiveTimeKernel_eq_convolution,
    integral_convolution _ (positiveRayKernel_integrable hw) (positiveRayKernel_integrable hw),
    positiveRayKernel_integral hw,ContinuousLinearMap.lsmul_apply,smul_eq_mul,pow_two]

omit [CompleteSpace H] in
private theorem weighted_primitive_convolution (w : ℂ) (f : ℝ → H) :
    (Ioi (0:ℝ)).indicator (fun t => expRay w t •
      ∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • f u) =
      positiveTimeKernel w ⋆[ContinuousLinearMap.lsmul ℂ ℂ]
        (Ioi (0:ℝ)).indicator (fun u => expRay w u • f u) := by
  funext t
  rw [positiveTimeKernel,positive_convolution]
  by_cases ht : 0 < t
  · rw [Set.indicator_of_mem (show t ∈ Ioi (0:ℝ) from ht),Set.indicator_of_mem (show t ∈ Ioi (0:ℝ) from ht),← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [smul_smul,smul_smul]
    congr 1
    rw [mul_assoc,ray_mul,mul_comm]
  · rw [Set.indicator_of_notMem (show t ∉ Ioi (0:ℝ) from ht),Set.indicator_of_notMem (show t ∉ Ioi (0:ℝ) from ht)]

omit [CompleteSpace H] in
private theorem weighted_primitive_integrable {w : ℂ} (hw : 0 < w.re) (f : ℝ → H)
    (hf : IntegrableOn (fun t => expRay w t • f t) (Ioi (0:ℝ))) :
    IntegrableOn (fun t => expRay w t • ∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • f u) (Ioi 0) := by
  rw [← integrable_indicator_iff measurableSet_Ioi,weighted_primitive_convolution]
  exact (positiveTimeKernel_integrable hw).integrable_convolution _
    ((integrable_indicator_iff measurableSet_Ioi).mpr hf)

private theorem weighted_primitive_laplace {w : ℂ} (hw : 0 < w.re) (f : ℝ → H)
    (hf : IntegrableOn (fun t => expRay w t • f t) (Ioi (0:ℝ))) :
    (∫ t in Ioi (0:ℝ), expRay w t • ∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • f u) =
      (w⁻¹)^2 • ∫ t in Ioi (0:ℝ), expRay w t • f t := by
  rw [← integral_indicator measurableSet_Ioi,weighted_primitive_convolution]
  rw [integral_convolution _ (positiveTimeKernel_integrable hw)
    ((integrable_indicator_iff measurableSet_Ioi).mpr hf),positiveTimeKernel_integral hw,
    integral_indicator measurableSet_Ioi,ContinuousLinearMap.lsmul_apply]

private theorem hilbert_laplace_unique_l1 (f : ℝ → H) (σ : ℝ)
    (hi : ∀ ξ : ℝ, IntegrableOn (fun t => expRay (rayLine σ ξ) t • f t) (Ioi (0:ℝ)))
    (hz : ∀ ξ : ℝ, (∫ t in Ioi (0:ℝ), expRay (rayLine σ ξ) t • f t) = 0) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))), f t = 0 := by
  let g : ℝ → H := (Ioi (0:ℝ)).indicator (fun t => expRay (σ:ℂ) t • f t)
  have hi0 : IntegrableOn (fun t => expRay (σ:ℂ) t • f t) (Ioi (0:ℝ)) := by
    simpa only [rayLine,mul_zero,Complex.ofReal_zero,zero_mul,add_zero] using hi 0
  have hg : Integrable g := (integrable_indicator_iff measurableSet_Ioi).mpr hi0
  have hp (v : H) : ∀ᵐ t ∂(volume : Measure ℝ), inner ℂ v (g t) = 0 := by
    let φ : ℝ → ℂ := fun t => inner ℂ v (f t)
    have he : rayDamp φ σ = fun t => inner ℂ v (g t) := by
      funext t
      by_cases ht : t ∈ Ioi (0:ℝ)
      · simp only [rayDamp,g,Set.indicator_of_mem ht,inner_smul_right,φ,mul_comm]
      · simp only [rayDamp,g,Set.indicator_of_notMem ht,inner_zero_right]
    have hφ : Integrable (rayDamp φ σ) := by
      rw [he]
      exact (innerSL ℂ v).integrable_comp hg
    have hFourier (ξ : ℝ) : 𝓕 (rayDamp φ σ) ξ = 0 := by
      rw [fourierIntegral_rayDamp,laplaceRay]
      have hc := (innerSL ℂ v).integral_comp_comm (hi ξ)
      simp only [innerSL_apply_apply,inner_smul_right] at hc
      calc
        (∫ t in Ioi (0:ℝ), φ t*expRay (rayLine σ ξ) t) =
            ∫ t in Ioi (0:ℝ), expRay (rayLine σ ξ) t*inner ℂ v (f t) := by
          apply integral_congr_ae
          exact Eventually.of_forall (fun t => mul_comm _ _)
        _ = inner ℂ v (∫ t in Ioi (0:ℝ), expRay (rayLine σ ξ) t • f t) := hc
        _ = 0 := by rw [hz,inner_zero_right]
    have hv := _root_.HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero hφ hFourier
    rw [he] at hv
    exact hv
  have hg0 : g =ᵐ[volume] 0 := by
    apply hg.ae_eq_zero_of_forall_setIntegral_eq_zero
    intro s hs hfin
    apply ext_inner_left ℂ
    intro v
    have hc := (innerSL ℂ v).integral_comp_comm (μ := volume.restrict s) hg.integrableOn
    simp only [innerSL_apply_apply] at hc
    rw [inner_zero_right,← hc]
    exact integral_eq_zero_of_ae (ae_restrict_of_ae (hp v))
  filter_upwards [ae_restrict_of_ae hg0,ae_restrict_mem measurableSet_Ioi] with t h0 ht
  change g t = 0 at h0
  change (Ioi (0:ℝ)).indicator (fun u => expRay (σ:ℂ) u • f u) t = 0 at h0
  rw [Set.indicator_of_mem ht] at h0
  exact (smul_eq_zero.mp h0).resolve_left (Complex.exp_ne_zero _)

open D4BMJointWave

omit [CompleteSpace H] in
private theorem weighted_clm_integrable (L : H →L[ℂ] H) (w : ℂ) (f : ℝ → H)
    (hf : IntegrableOn (fun t => expRay w t • f t) (Ioi (0:ℝ))) :
    IntegrableOn (fun t => expRay w t • L (f t)) (Ioi (0:ℝ)) := by
  simpa only [Function.comp_apply,map_smul] using! L.integrable_comp hf

private theorem weighted_clm_laplace (L : H →L[ℂ] H) (w : ℂ) (f : ℝ → H)
    (hf : IntegrableOn (fun t => expRay w t • f t) (Ioi (0:ℝ))) :
    (∫ t in Ioi (0:ℝ), expRay w t • L (f t)) =
      L (∫ t in Ioi (0:ℝ), expRay w t • f t) := by
  simpa only [map_smul] using L.integral_comp_comm hf

private theorem joint_covariance_inverse (v : jointEnergyOperator.domain) :
    formEmbeddingCovariance jointEmbedding (jointEnergyOperator v) = (v : SpatialSpace) := by
  let B := formEmbeddingCovariance jointEmbedding
  have hr : (v : SpatialSpace) ∈ B.range := by
    simpa only [jointEnergyOperator,friedrichsFormOperator,closedDenseInverse_domain] using v.property
  obtain ⟨y,hy⟩ := hr
  have hA : jointEnergyOperator v = y := by
    have hi := friedrichsFormOperator_apply_covariance jointEmbedding
      jointEmbedding_injective jointEmbedding_dense y
    have he : v = ⟨B y,hi.1⟩ := Subtype.ext hy.symm
    rw [he]
    exact hi.2
  rw [hA]
  exact hy

private def physicalCovarianceDefect (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ) : SpatialSpace :=
  formEmbeddingCovariance jointEmbedding (causalJointForcedResponse q branch a t)+
    (1-formEmbeddingCovariance jointEmbedding)
      (∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • causalJointForcedResponse q branch a u)-
    formEmbeddingCovariance jointEmbedding
      (∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • causalCuspSourceVector q branch a u)

private theorem physical_source_integrable (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : causalResponseShift q+1 < w.re) :
    IntegrableOn (fun t => expRay w t • causalCuspSourceVector q branch a t) (Ioi (0:ℝ)) := by
  have ht : causalPrincipalThreshold q < w.re := by
    have h := le_max_left (causalPrincipalThreshold q) (principalThreshold q)
    unfold causalResponseShift causalGreenThreshold at hw
    linarith
  simpa only [expRay,neg_mul] using! causalCuspSourceVector_laplace_integrable q branch a w ht

private theorem physical_defect_integrable (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : causalResponseShift q+1 < w.re) :
    IntegrableOn (fun t => expRay w t • physicalCovarianceDefect q branch a t) (Ioi (0:ℝ)) := by
  have hw0 : 0 < w.re := by have := causalResponseShift_pos q; linarith
  let B := formEmbeddingCovariance jointEmbedding
  let U := causalJointForcedResponse q branch a
  let F := causalCuspSourceVector q branch a
  have hU := causalJointForcedResponse_integrable q branch a w hw
  have hF := physical_source_integrable q branch a w hw
  have hP := weighted_primitive_integrable hw0 U hU
  have hQ := weighted_primitive_integrable hw0 F hF
  have h₁ := weighted_clm_integrable B w U hU
  have h₂ := weighted_clm_integrable (1-B) w
    (fun t => ∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • U u) hP
  have h₃ := weighted_clm_integrable B w
    (fun t => ∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • F u) hQ
  apply ((h₁.add h₂).sub h₃).congr
  apply Eventually.of_forall
  intro t
  simp only [Pi.add_apply,Pi.sub_apply,physicalCovarianceDefect,smul_sub,smul_add,B,U,F]

private theorem physical_defect_laplace (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : causalResponseShift q+1 < w.re) :
    (∫ t in Ioi (0:ℝ), expRay w t • physicalCovarianceDefect q branch a t) = 0 := by
  have hw0 : 0 < w.re := by have := causalResponseShift_pos q; linarith
  have hwn : w ≠ 0 := by intro he; simp only [he,Complex.zero_re,lt_self_iff_false] at hw0
  let B := formEmbeddingCovariance jointEmbedding
  let U := causalJointForcedResponse q branch a
  let F := causalCuspSourceVector q branch a
  have hU := causalJointForcedResponse_integrable q branch a w hw
  have hF := physical_source_integrable q branch a w hw
  have hP := weighted_primitive_integrable hw0 U hU
  have hQ := weighted_primitive_integrable hw0 F hF
  have h₁ := weighted_clm_integrable B w U hU
  have h₂ := weighted_clm_integrable (1-B) w
    (fun t => ∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • U u) hP
  have h₃ := weighted_clm_integrable B w
    (fun t => ∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • F u) hQ
  change (∫ t in Ioi (0:ℝ), expRay w t •
    (B (U t)+(1-B) (∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • U u)-
      B (∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • F u))) = 0
  simp only [smul_sub,smul_add]
  have h12 : IntegrableOn (fun t => expRay w t • B (U t)+
      expRay w t • (1-B) (∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • U u)) (Ioi (0:ℝ)) := by
    simpa only [Pi.add_apply] using! h₁.add h₂
  rw [integral_sub h12 h₃,integral_add h₁ h₂,
    weighted_clm_laplace B w U hU,
    weighted_clm_laplace (1-B) w _ hP,weighted_clm_laplace B w _ hQ,
    weighted_primitive_laplace hw0 U hU,weighted_primitive_laplace hw0 F hF]
  let V := ∫ t in Ioi (0:ℝ), expRay w t • U t
  let R := ∫ t in Ioi (0:ℝ), expRay w t • F t
  let c : ℂ := (w⁻¹)^2
  obtain ⟨hm,he⟩ := causalJointForcedResponse_operator q branch a w hw
  have hB := congrArg B he
  rw [map_add,map_smul,joint_covariance_inverse] at hB
  change V+(w^2-1) • B V=B R at hB
  have hc : c*(w^2-1)=1-c := by
    dsimp only [c]
    field_simp [hwn]
  have hscale := congrArg (fun z : SpatialSpace => c • z) hB
  rw [smul_add,smul_smul,hc,sub_smul,one_smul] at hscale
  change B V+(1-B) (c • V)-B (c • R)=0
  simp only [sub_apply,one_apply_eq_self,map_smul,smul_sub]
  apply sub_eq_zero.mpr
  calc
    B V+(c • V-c • B V)=c • V+(B V-c • B V) := by abel
    _ = c • B R := hscale

private theorem physical_defect_zero_positive (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))), physicalCovarianceDefect q branch a t=0 := by
  apply hilbert_laplace_unique_l1 (physicalCovarianceDefect q branch a) (causalResponseShift q+2)
  · intro ξ
    apply physical_defect_integrable
    rw [rayLine_re]
    linarith
  · intro ξ
    apply physical_defect_laplace
    rw [rayLine_re]
    linarith

private theorem doublePrimitive_zero_nonpos (f : ℝ → H)
    (hf : ∀ᵐ u ∂(volume : Measure ℝ), u < 0 → f u=0) {t : ℝ} (ht : t ≤ 0) :
    (∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • f u)=0 := by
  rw [intervalIntegral.integral_symm t 0,intervalIntegral.integral_of_le ht,
    integral_Ioc_eq_integral_Ioo]
  apply neg_eq_zero.mpr
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_of_ae hf,ae_restrict_mem measurableSet_Ioo] with u hu hmem
  change ((t-u:ℝ):ℂ) • f u=0
  rw [hu hmem.2,smul_zero]

/-- The constructed physical causal response satisfies the original bounded Bochner
Volterra equation almost everywhere on the whole time line. The physical source,
operator, source onset and time-L2 representative are all the original constructions. -/
theorem causalJointForcedResponse_bochner_covariance_equation (q : XiZeroCopy) (branch : Bool)
    (a : ℂ) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      formEmbeddingCovariance jointEmbedding (causalJointForcedResponse q branch a t)+
        (1-formEmbeddingCovariance jointEmbedding)
          (∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • causalJointForcedResponse q branch a u) =
        formEmbeddingCovariance jointEmbedding
          (∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • causalCuspSourceVector q branch a u) := by
  have hp := (ae_restrict_iff' measurableSet_Ioi).mp (physical_defect_zero_positive q branch a)
  have hF : ∀ᵐ u ∂(volume : Measure ℝ), u < 0 → causalCuspSourceVector q branch a u=0 :=
    Eventually.of_forall (fun u hu => causalCuspSourceVector_zero_of_nonpos q branch a u hu.le)
  have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
    have h := MeasureTheory.compl_mem_ae_iff.mpr (show volume ({0} : Set ℝ)=0 by simp)
    exact h
  filter_upwards [hp,causalJointForcedResponse_support q branch a,h0] with t hpos hneg ht0
  by_cases ht : 0 < t
  · exact sub_eq_zero.mp (hpos ht)
  · have htn : t < 0 := lt_of_le_of_ne (le_of_not_gt ht) ht0
    simp only [hneg htn,doublePrimitive_zero_nonpos _ (causalJointForcedResponse_support q branch a) htn.le,
      doublePrimitive_zero_nonpos _ hF htn.le,map_zero,add_zero]

end
end RHTower.D4BMJointSource
