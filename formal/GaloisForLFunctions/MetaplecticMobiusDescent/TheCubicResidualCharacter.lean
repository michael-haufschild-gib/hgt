/-
The residual cubic character adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicResidueIsNonzero

/-!
# The cubic character of the residual vector

Level-three matrices normalize the character kernel, act by measure
preserving homeomorphisms on its quotient, and induce unitary pullbacks
on `L²`. Initial source matching and analytic uniqueness preserve the
cubic character through continuation and in the actual nonzero residue.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified

lemma globalKubotaKernel_conjugate_mem (M : levelThree) (N : globalKubotaKernel) :
    (M:SL(2,O))*(N:SL(2,O))*(M:SL(2,O))⁻¹∈globalKubotaKernel := by
  obtain ⟨n,hn,hnval⟩ := N.property
  change (n:SL(2,O))=(N:SL(2,O)) at hnval
  refine ⟨M*n*M⁻¹,?_,?_⟩
  · change finiteCharacter (M*n*M⁻¹)=1
    change finiteCharacter n=1 at hn
    simp only [map_mul,map_inv,hn,mul_one,mul_inv_cancel]
  · change (M:SL(2,O))*(n:SL(2,O))*(M:SL(2,O))⁻¹=_
    rw [hnval]

def kernelConjugate (M : levelThree) : globalKubotaKernel ≃* globalKubotaKernel where
  toFun N := ⟨(M:SL(2,O))*(N:SL(2,O))*(M:SL(2,O))⁻¹,globalKubotaKernel_conjugate_mem M N⟩
  invFun N := ⟨(M⁻¹:levelThree)*(N:SL(2,O))*(M⁻¹:levelThree)⁻¹,globalKubotaKernel_conjugate_mem M⁻¹ N⟩
  left_inv N := by apply Subtype.ext; simp [mul_assoc]
  right_inv N := by apply Subtype.ext; simp [mul_assoc]
  map_mul' N P := by apply Subtype.ext; simp [mul_assoc]

lemma kernelConjugate_coe (M : levelThree) (N : globalKubotaKernel) :
    (kernelConjugate M N : SL(2,O))=(M:SL(2,O))*(N:SL(2,O))*(M:SL(2,O))⁻¹ := rfl

lemma level_action_respects_kernel (M : levelThree) (u v : HyperbolicSpace)
    (h : (integralOrbitRel globalKubotaKernel).r u v) :
    (integralOrbitRel globalKubotaKernel).r (complexMatrix M • u) (complexMatrix M • v) := by
  obtain ⟨N,hN⟩ := h
  refine ⟨kernelConjugate M N,?_⟩
  change integralComplexMatrix ((M:SL(2,O))*(N:SL(2,O))*(M:SL(2,O))⁻¹) •
    (complexMatrix M • u)=complexMatrix M • v
  rw [map_mul,map_mul,map_inv,mul_smul,mul_smul]
  change complexMatrix M • (integralComplexMatrix (N:SL(2,O)) •
    ((complexMatrix M)⁻¹ • (complexMatrix M • u)))=_
  rw [inv_smul_smul,hN]

def kernelLevelAction (M : levelThree) : KernelQuotient→KernelQuotient :=
  Quotient.map' (fun w => complexMatrix M • w) (level_action_respects_kernel M)

lemma kernelLevelAction_mk (M : levelThree) (w : HyperbolicSpace) :
    kernelLevelAction M (integralOrbitProjection globalKubotaKernel w)=
      integralOrbitProjection globalKubotaKernel (complexMatrix M • w) := rfl

lemma kernelLevelAction_one (q : KernelQuotient) : kernelLevelAction 1 q=q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection globalKubotaKernel (complexMatrix 1 • w)=integralOrbitProjection globalKubotaKernel w
    rw [map_one,one_smul]

lemma kernelLevelAction_mul (M N : levelThree) (q : KernelQuotient) :
    kernelLevelAction (M*N) q=kernelLevelAction M (kernelLevelAction N q) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection globalKubotaKernel (complexMatrix (M*N) • w)=
      integralOrbitProjection globalKubotaKernel (complexMatrix M • (complexMatrix N • w))
    rw [map_mul,mul_smul]

lemma kernelLevelAction_continuous (M : levelThree) : Continuous (kernelLevelAction M) :=
  (continuous_hyperbolic_action (complexMatrix M)).quotient_map' (level_action_respects_kernel M)

def kernelLevelHomeomorph (M : levelThree) : KernelQuotient ≃ₜ KernelQuotient where
  toFun := kernelLevelAction M
  invFun := kernelLevelAction M⁻¹
  left_inv q := by rw [←kernelLevelAction_mul,inv_mul_cancel,kernelLevelAction_one]
  right_inv q := by rw [←kernelLevelAction_mul,mul_inv_cancel,kernelLevelAction_one]
  continuous_toFun := kernelLevelAction_continuous M
  continuous_invFun := kernelLevelAction_continuous M⁻¹

lemma kernelLevelAction_eisenstein (M : levelThree) (s : ℂ) (hs : 2<s.re)
    (q : KernelQuotient) :
    kernelQuotientEisenstein s hs (kernelLevelAction M q)=
      complexCharacter M*kernelQuotientEisenstein s hs q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    exact hyperbolicEisenstein_automorphy M s hs w

lemma kernelLevelAction_seed (M : levelThree) (a b : ℝ) (s : ℂ) (q : KernelQuotient) :
    kernelQuotientSeed a b s (kernelLevelAction M q)=complexCharacter M*kernelQuotientSeed a b s q := by
  induction q using Quotient.inductionOn with
  | _ w => exact smoothCuspSeed_automorphy a b s M w

lemma kernelLevelAction_defect (M : levelThree) (a b : ℝ) (s : ℂ) (q : KernelQuotient) :
    kernelQuotientDefect a b s (kernelLevelAction M q)=complexCharacter M*kernelQuotientDefect a b s q := by
  induction q using Quotient.inductionOn with
  | _ w => exact smoothCuspSeedDefect_automorphy a b s M w

lemma kernelLevelAction_fundamentalDomain (M : levelThree) :
    IsFundamentalDomain globalKubotaKernel
      ((fun w : HyperbolicSpace => complexMatrix M • w) '' hyperbolicFundamentalSet globalKubotaKernel)
      hyperbolicVolume := by
  apply (hyperbolicFundamentalSet_isFundamentalDomain globalKubotaKernel
    globalKubotaKernel_le_levelThree hyperbolicVolume).image_of_equiv (MulAction.toPerm (complexMatrix M))
    (show Measure.QuasiMeasurePreserving (MulAction.toPerm (complexMatrix M)).symm hyperbolicVolume hyperbolicVolume from by
      exact (measurePreserving_smul (complexMatrix M)⁻¹ hyperbolicVolume).quasiMeasurePreserving)
    (kernelConjugate M⁻¹).toEquiv
  intro N w
  change complexMatrix M • (integralComplexMatrix
    ((M⁻¹:levelThree)*(N:SL(2,O))*(M⁻¹:levelThree)⁻¹) • w)=
      integralComplexMatrix (N:SL(2,O)) • (complexMatrix M • w)
  simp only [Subgroup.coe_inv,map_mul,map_inv]
  change complexMatrix M • (((complexMatrix M)⁻¹*integralComplexMatrix (N:SL(2,O))*
    ((complexMatrix M)⁻¹)⁻¹) • w)=_
  simp only [inv_inv,mul_smul,smul_inv_smul]

lemma kernelLevelAction_measurePreserving (M : levelThree) :
    MeasurePreserving (kernelLevelAction M) (integralQuotientVolume globalKubotaKernel)
      (integralQuotientVolume globalKubotaKernel) := by
  refine ⟨(kernelLevelAction_continuous M).measurable,?_⟩
  let act : HyperbolicSpace→HyperbolicSpace := fun w => complexMatrix M • w
  have hmap := (measurePreserving_smul (complexMatrix M) hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul (complexMatrix M)) (hyperbolicFundamentalSet globalKubotaKernel)
  have heq : kernelLevelAction M ∘ integralOrbitProjection globalKubotaKernel=
      integralOrbitProjection globalKubotaKernel ∘ act := by ext w; rfl
  change Measure.map (kernelLevelAction M)
    (Measure.map (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)))=_
  rw [Measure.map_map (kernelLevelAction_continuous M).measurable
    (measurable_integralOrbitProjection _),heq,
    ←Measure.map_map (measurable_integralOrbitProjection _) (continuous_hyperbolic_action _).measurable]
  change Measure.map (integralOrbitProjection globalKubotaKernel)
    (Measure.map act (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)))=_
  rw [hmap.map_eq]
  exact integralQuotientVolume_independent globalKubotaKernel globalKubotaKernel_le_levelThree _
    (kernelLevelAction_fundamentalDomain M)


def kernelLevelPullback (M : levelThree) : KernelQuotientL2 →ₗᵢ[ℂ] KernelQuotientL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (kernelLevelAction M) (kernelLevelAction_measurePreserving M)

lemma kernelLevelPullback_ae_eq (M : levelThree) (F : KernelQuotientL2) :
    kernelLevelPullback M F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => F (kernelLevelAction M q) :=
  Lp.coeFn_compMeasurePreserving F (kernelLevelAction_measurePreserving M)

lemma kernelLevelPullback_one (F : KernelQuotientL2) : kernelLevelPullback 1 F=F := by
  apply Lp.ext
  filter_upwards [kernelLevelPullback_ae_eq 1 F] with q hq
  simpa only [kernelLevelAction_one] using hq

lemma kernelLevelPullback_comp (M N : levelThree) (F : KernelQuotientL2) :
    kernelLevelPullback M (kernelLevelPullback N F)=kernelLevelPullback (N*M) F := by
  have hcomp := (kernelLevelAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelLevelPullback_ae_eq N F)
  apply Lp.ext
  filter_upwards [kernelLevelPullback_ae_eq M (kernelLevelPullback N F),hcomp,
    kernelLevelPullback_ae_eq (N*M) F] with q hp hn hnm
  rw [hp,hnm]
  exact hn.trans (congrArg F (kernelLevelAction_mul N M q).symm)

lemma kernelLevelPullback_surjective (M : levelThree) : Function.Surjective (kernelLevelPullback M) := by
  intro F
  refine ⟨kernelLevelPullback M⁻¹ F,?_⟩
  rw [kernelLevelPullback_comp,inv_mul_cancel,kernelLevelPullback_one]

def kernelLevelUnitary (M : levelThree) : KernelQuotientL2 ≃ₗᵢ[ℂ] KernelQuotientL2 :=
  LinearIsometryEquiv.ofSurjective (kernelLevelPullback M) (kernelLevelPullback_surjective M)

lemma kernelLevelUnitary_apply (M : levelThree) (F : KernelQuotientL2) :
    kernelLevelUnitary M F=kernelLevelPullback M F := rfl

lemma kernelLevelPullback_defect (M : levelThree) (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    kernelLevelPullback M (kernelL2Defect a b ha hab s)=
      complexCharacter M • kernelL2Defect a b ha hab s := by
  have hdef := kernelL2Defect_ae_eq a b ha hab s
  have hcomp := (kernelLevelAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hdef
  apply Lp.ext
  filter_upwards [kernelLevelPullback_ae_eq M (kernelL2Defect a b ha hab s),hcomp,hdef,
    Lp.coeFn_smul (complexCharacter M) (kernelL2Defect a b ha hab s)] with q hp hc hd hs
  change _=complexCharacter M * kernelL2Defect a b ha hab s q at hs
  rw [hp,hs,hd]
  exact hc.trans (kernelLevelAction_defect M a b s q)

lemma kernelLevelPullback_of_remainder_ae (M : levelThree) (a b : ℝ) (s : ℂ)
    (hs : 2<s.re) (F : KernelQuotientL2)
    (hF : F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelLevelPullback M F=complexCharacter M • F := by
  have hcomp := (kernelLevelAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hF
  apply Lp.ext
  filter_upwards [kernelLevelPullback_ae_eq M F,hcomp,hF,Lp.coeFn_smul (complexCharacter M) F]
    with q hp hc hf hsmul
  change _=complexCharacter M*F q at hsmul
  rw [hp,hsmul,hf]
  dsimp only [Function.comp_def] at hc
  rw [hc,kernelLevelAction_eisenstein,kernelLevelAction_seed,mul_sub]

lemma kernelCorrection_character_of_initial_overlap (M : levelThree) (a b : ℝ)
    (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ, ∀hs : 4<s.re, 0<s.im →
      kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
        fun q => kernelQuotientEisenstein s (by linarith) q-kernelQuotientSeed a b s q) :
    ∀s∈cuspUpperParameterRegion,
      kernelLevelPullback M (kernelEisensteinL2Correction a b ha hab s)=
        complexCharacter M • kernelEisensteinL2Correction a b ha hab s := by
  have hc : AnalyticOnNhd ℂ (kernelEisensteinL2Correction a b ha hab) cuspUpperParameterRegion := by
    intro s hs
    exact kernelEisensteinL2Correction_analyticAt_nonreal a b ha hab s (by linarith [hs.1]) hs.2.ne'
  have hl : AnalyticOnNhd ℂ (fun s => kernelLevelPullback M (kernelEisensteinL2Correction a b ha hab s))
      cuspUpperParameterRegion := by
    intro s hs
    exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := KernelQuotientL2)
      (kernelLevelPullback M).toContinuousLinearMap _).comp_of_eq (hc s hs) rfl
  have hr : AnalyticOnNhd ℂ (fun s => complexCharacter M • kernelEisensteinL2Correction a b ha hab s)
      cuspUpperParameterRegion := by
    intro s hs
    exact (hc s hs).const_smul (c := complexCharacter M)
  have hV : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s => kernelLevelPullback M (kernelEisensteinL2Correction a b ha hab s))
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (fun s => complexCharacter M • kernelEisensteinL2Correction a b ha hab s) := by
    filter_upwards [hV.mem_nhds (by norm_num)] with s hs
    exact kernelLevelPullback_of_remainder_ae M a b s (by linarith [hs.1]) _ (hoverlap s hs.1 hs.2)
  exact hl.eqOn_of_preconnected_of_eventuallyEq hr cuspUpperParameterRegion_convex.isPreconnected
    (by norm_num [cuspUpperParameterRegion]) hevent

lemma thetaApproach_tendsto_complex_punctured :
    Tendsto (fun t : ℝ => (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I)
      (𝓝[>] (0:ℝ)) (𝓝[≠] (4/3:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hh : Continuous (fun t : ℝ => (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I) := by fun_prop
    have ht := (hh.tendsto 0).mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using ht
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    change (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I≠(4/3:ℂ)
    intro he
    have him := congrArg Complex.im he
    simp at him
    linarith

lemma kernelEisensteinResidueVector_character_of_initial_overlap (M : levelThree) (a b : ℝ)
    (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ, ∀hs : 4<s.re, 0<s.im →
      kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
        fun q => kernelQuotientEisenstein s (by linarith) q-kernelQuotientSeed a b s q) :
    kernelLevelPullback M (kernelEisensteinResidueVector a b ha hab)=
      complexCharacter M • kernelEisensteinResidueVector a b ha hab := by
  have hlim := (kernelEisensteinResidueVector_limit a b ha hab).comp thetaApproach_tendsto_complex_punctured
  have hl := (kernelLevelPullback M).continuous.continuousAt.tendsto.comp hlim
  have hr := hlim.const_smul (complexCharacter M)
  have hevent :
      (fun t : ℝ => kernelLevelPullback M
        (((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I-4/3) •
          kernelEisensteinL2Correction a b ha hab ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I)))
      =ᶠ[𝓝[>] (0:ℝ)]
      (fun t : ℝ => complexCharacter M •
        (((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I-4/3) •
          kernelEisensteinL2Correction a b ha hab ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have hs : (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I∈cuspUpperParameterRegion := by
      simp only [cuspUpperParameterRegion,Set.mem_setOf_eq,Complex.add_re,Complex.add_im,
        Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
        Complex.I_im,mul_zero,mul_one,sub_zero,add_zero]
      norm_num
      exact ht
    rw [map_smul,kernelCorrection_character_of_initial_overlap M a b ha hab hoverlap _ hs]
    exact smul_comm _ _ _
  exact tendsto_nhds_unique_of_eventuallyEq hl hr hevent



/-- The actual nonzero residue transforms by the cubic multiplier. -/
lemma cubicEisensteinResidue_character (M : levelThree) :
    kernelLevelPullback M cubicEisensteinResidue = complexCharacter M • cubicEisensteinResidue := by
  apply kernelEisensteinResidueVector_character_of_initial_overlap M 2 3 (by norm_num) (by norm_num)
  intro s hs hi
  exact kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi

lemma cubicEisensteinResidue_nonzero_character :
    cubicEisensteinResidue ≠ 0 ∧ ∀ M : levelThree,
      kernelLevelPullback M cubicEisensteinResidue = complexCharacter M • cubicEisensteinResidue :=
  ⟨cubicEisensteinResidue_ne_zero,cubicEisensteinResidue_character⟩

#print axioms kernelLevelAction_measurePreserving
#print axioms cubicEisensteinResidue_nonzero_character
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
