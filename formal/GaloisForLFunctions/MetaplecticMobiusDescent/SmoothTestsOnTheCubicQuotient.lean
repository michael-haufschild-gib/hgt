/-
Smooth test functions and density adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicQuotientHasASmoothAtlas
import Mathlib.Geometry.Manifold.SmoothApprox

/-!
# Dense smooth tests on the cubic quotient

Invariant hyperbolic volume and its quotient measure have full support.
Smooth compactly supported functions therefore embed faithfully in `L²`.
Continuous compact approximation followed by smooth approximation proves density.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal ContDiff Manifold
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

instance fullSLContinuousAction : ContinuousConstSMul (SL(2,ℂ)) HyperbolicSpace :=
  ⟨continuous_hyperbolic_action⟩

instance hyperbolicVolume_fullSupport : Measure.IsOpenPosMeasure hyperbolicVolume where
  open_pos U hU hne := by
    obtain ⟨u,hu⟩ := hne
    have hcover : (Set.univ : Set HyperbolicSpace) ⊆ ⋃g:SL(2,ℂ),g • U := by
      intro w hw
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SL(2,ℂ)) u w
      exact Set.mem_iUnion.mpr ⟨g,u,hu,hg⟩
    obtain ⟨seq,hseq⟩ := isLindelof_univ.indexed_countable_subcover
      (fun g : SL(2,ℂ) => g • U) (fun g => isOpenMap_smul g U hU) hcover
    intro hzero
    have hz : hyperbolicVolume (⋃n:ℕ,seq n • U)=0 := by
      apply measure_iUnion_null
      intro n
      rw [measure_smul,hzero]
    have htotal : hyperbolicVolume Set.univ=0 := measure_mono_null hseq hz
    exact hyperbolicVolume_ne_zero (Measure.measure_univ_eq_zero.mp htotal)

instance kernelQuotientVolume_fullSupport :
    Measure.IsOpenPosMeasure (integralQuotientVolume globalKubotaKernel) where
  open_pos U hU hne := by
    let quotientProjection := integralOrbitProjection globalKubotaKernel
    have hp : Measurable quotientProjection := measurable_integralOrbitProjection _
    have hpre : IsOpen (quotientProjection ⁻¹' U) := hU.preimage (continuous_integralOrbitProjection _)
    have hpren : (quotientProjection ⁻¹' U).Nonempty := by
      obtain ⟨q,hq⟩ := hne
      obtain ⟨w,rfl⟩ := Quotient.mk_surjective q
      exact ⟨w,hq⟩
    intro hzero
    have hd : hyperbolicVolume ((quotientProjection ⁻¹' U)∩hyperbolicFundamentalSet globalKubotaKernel)=0 := by
      simpa only [integralQuotientVolume,quotientProjection,Measure.map_apply (measurable_integralOrbitProjection _) hU.measurableSet,
        Measure.restrict_apply ((measurable_integralOrbitProjection _) hU.measurableSet)] using hzero
    have hinv : ∀M:globalKubotaKernel,M • (quotientProjection ⁻¹' U)=quotientProjection ⁻¹' U := by
      intro M
      ext w
      constructor
      · rintro ⟨u,hu,rfl⟩
        change quotientProjection (M • u)∈U
        change quotientProjection u∈U at hu
        rwa [show quotientProjection (M • u)=quotientProjection u from integralOrbitProjection_eq _ M u]
      · intro hw
        refine ⟨M⁻¹ • w,?_,smul_inv_smul M w⟩
        change quotientProjection (M⁻¹ • w)∈U
        rwa [show quotientProjection (M⁻¹ • w)=quotientProjection w from integralOrbitProjection_eq _ M⁻¹ w]
    have hz := (globalKubotaKernel_isFundamentalDomain hyperbolicVolume).measure_zero_of_invariant (quotientProjection ⁻¹' U) hinv hd
    exact hpre.measure_ne_zero _ hpren hz

lemma kernel_continuous_eq_of_ae_eq (f g : IntegralOrbitQuotient globalKubotaKernel → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (he : f =ᵐ[integralQuotientVolume globalKubotaKernel] g) : f=g :=
  (MeasureTheory.Measure.eq_of_ae_eq he hf hg)

def kernelSmoothTests : Submodule ℂ (KernelQuotient→ℂ) where
  carrier f := ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f ∧ HasCompactSupport f
  zero_mem' := ⟨contMDiff_const,HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1,hf.2.add hg.2⟩
  smul_mem' c f hf := by
    have hc : ContDiff ℝ ∞ (fun z : ℂ => c*z) := contDiff_const.mul contDiff_id
    exact ⟨hc.contMDiff.comp hf.1,hf.2.smul_left⟩

lemma kernelSmoothTests_memLp (f : kernelSmoothTests) :
    MemLp f.1 2 (integralQuotientVolume globalKubotaKernel) :=
  f.2.1.continuous.memLp_of_hasCompactSupport f.2.2

def kernelSmoothTestsToL2 : kernelSmoothTests→ₗ[ℂ]KernelQuotientL2 where
  toFun f := (kernelSmoothTests_memLp f).toLp f.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma kernelSmoothTestsToL2_injective : Function.Injective kernelSmoothTestsToL2 := by
  intro f g hfg
  apply Subtype.ext
  apply kernel_continuous_eq_of_ae_eq _ _ f.2.1.continuous g.2.1.continuous
  exact ((kernelSmoothTests_memLp f).toLp_eq_toLp_iff (kernelSmoothTests_memLp g)).mp hfg

lemma kernelL2_smooth_compact_approx (f : KernelQuotientL2) (ε : ℝ) (hε : 0<ε) :
    ∃g : kernelSmoothTests,
      eLpNorm ((f : KernelQuotient→ℂ)-g.1) 2 (integralQuotientVolume globalKubotaKernel)≤
        ENNReal.ofReal ε := by
  obtain ⟨g,hgK,hfg,hgc,hgLp⟩ := kernelL2_continuous_compact_approx f
    (ENNReal.ofReal (ε/2)) (by positivity)
  let mass : ℝ≥0∞ := (integralQuotientVolume globalKubotaKernel Set.univ)^((2:ℝ≥0∞).toReal⁻¹)
  have hm : mass≠(∞:ℝ≥0∞) := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  let deltaLoss : ℝ := ε/(2*(mass.toReal+1))
  have hδ : 0<deltaLoss := div_pos hε (by positivity)
  obtain ⟨k,hkg,hksupp⟩ := hgc.exists_contMDiff_approx 𝓘(ℝ,SpatialCoordinates) ⊤
    (ε := fun _ => deltaLoss) continuous_const (fun _ => hδ)
  have hkK : HasCompactSupport (k : KernelQuotient→ℂ) :=
    HasCompactSupport.of_support_subset_isCompact hgK (hksupp.trans (subset_tsupport g))
  let kt : kernelSmoothTests := ⟨k,k.contMDiff,hkK⟩
  have hkgLp : eLpNorm (g-(k : KernelQuotient→ℂ)) 2 (integralQuotientVolume globalKubotaKernel)≤
      ENNReal.ofReal (ε/2) := by
    have hb : ∀ᵐ q ∂integralQuotientVolume globalKubotaKernel,‖g q-k q‖≤deltaLoss :=
      Filter.Eventually.of_forall fun q => by
        simpa only [dist_eq_norm,norm_sub_rev] using (hkg q).le
    have hmul : mass.toReal*deltaLoss≤ε/2 := by
      have he : deltaLoss*(2*(mass.toReal+1))=ε := div_mul_cancel₀ _ (by positivity)
      have hp := ENNReal.toReal_nonneg (a := mass)
      nlinarith [mul_nonneg hp hδ.le]
    calc
      _ ≤ mass*ENNReal.ofReal deltaLoss := eLpNorm_le_of_ae_bound hb
      _ = ENNReal.ofReal (mass.toReal*deltaLoss) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hm]
      _ ≤ ENNReal.ofReal (ε/2) := ENNReal.ofReal_le_ofReal hmul
  refine ⟨kt,?_⟩
  have he : (f : KernelQuotient→ℂ)-kt.1=((f : KernelQuotient→ℂ)-g)+(g-(k : KernelQuotient→ℂ)) := by
    funext q
    change f q-k q=(f q-g q)+(g q-k q)
    ring
  rw [he]
  calc
    _ ≤ eLpNorm ((f : KernelQuotient→ℂ)-g) 2 (integralQuotientVolume globalKubotaKernel)+
        eLpNorm (g-(k : KernelQuotient→ℂ)) 2 (integralQuotientVolume globalKubotaKernel) :=
      eLpNorm_add_le ((Lp.memLp f).aestronglyMeasurable.sub hgLp.aestronglyMeasurable)
        (hgc.sub k.contMDiff.continuous).aestronglyMeasurable (by norm_num)
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2) := add_le_add hfg hkgLp
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

lemma kernelSmoothTestsToL2_dense : DenseRange kernelSmoothTestsToL2 := by
  apply Metric.denseRange_iff.mpr
  intro f ε hε
  obtain ⟨g,hg⟩ := kernelL2_smooth_compact_approx f (ε/2) (by positivity)
  refine ⟨g,?_⟩
  have he : ‖f-kernelSmoothTestsToL2 g‖=
      (eLpNorm ((f : KernelQuotient→ℂ)-g.1) 2 (integralQuotientVolume globalKubotaKernel)).toReal := by
    rw [Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    exact (Lp.coeFn_sub _ _).trans ((Filter.EventuallyEq.refl _ _).sub
      (kernelSmoothTests_memLp g).coeFn_toLp)
  rw [dist_eq_norm,he]
  exact lt_of_le_of_lt ((ENNReal.toReal_mono (by simp) hg).trans_eq (ENNReal.toReal_ofReal (by positivity)))
    (by linarith)

#print axioms kernelQuotientVolume_fullSupport
#print axioms kernelSmoothTestsToL2_injective
#print axioms kernelSmoothTestsToL2_dense
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
