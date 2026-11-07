/-
Weighted cubic Fourier tests adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicScatteringContinuation
import GaloisForLFunctions.MetaplecticMobiusDescent.WeightedCubicWhittakerAverages
import GaloisForLFunctions.MetaplecticMobiusDescent.CompactCubicQuotientPullbacks

/-!
# Height-weighted Fourier tests of the residual cubic family

Bounded continuous height weights give bounded `L²` Fourier pairings on
the cusp strip. Their meromorphic continuation and residue limits retain
the same actual source. On the initial open half-plane, each nonzero
Fourier mode factors into the scattering series and its weighted
Whittaker height average.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified

def cuspWeightedFourierPhase (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (w : HyperbolicSpace) : ℂ :=
  ρ (hyperbolicHeight w)*cuspFourierPhase h w

lemma cuspWeightedFourierPhase_continuous (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) :
    Continuous (cuspWeightedFourierPhase ρ h) :=
  (ρ.continuous.comp hyperbolicHeight_continuous).mul (cuspFourierPhase_continuous h)

lemma cuspWeightedFourierPhase_bound (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (w : HyperbolicSpace) :
    ‖cuspWeightedFourierPhase ρ h w‖≤‖ρ‖ := by
  rw [cuspWeightedFourierPhase,norm_mul,cuspFourierPhase_norm,mul_one]
  exact ρ.norm_coe_le_norm _

lemma cuspWeightedFourierTest_memLp (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) :
    MemLp (fun w => star (cuspWeightedFourierPhase ρ h w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip 5 6)) := by
  apply MemLp.of_bound (cuspWeightedFourierPhase_continuous ρ h).star.aestronglyMeasurable ‖ρ‖
  exact Eventually.of_forall (fun w => by rw [norm_star]; exact cuspWeightedFourierPhase_bound ρ h w)

def cuspWeightedFourierTestL2 (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) : CuspStripL2 :=
  (cuspWeightedFourierTest_memLp ρ h).toLp (fun w => star (cuspWeightedFourierPhase ρ h w))

def kernelCuspWeightedFourier (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) : KernelQuotientL2→L[ℂ]ℂ :=
  (innerSL ℂ (cuspWeightedFourierTestL2 ρ h)).comp kernelCuspPullback

lemma kernelCuspWeightedFourier_integral (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (F : KernelQuotientL2) :
    kernelCuspWeightedFourier ρ h F=∫w in cuspPeriodStrip 5 6,
      F (integralOrbitProjection globalKubotaKernel w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  change inner ℂ (cuspWeightedFourierTestL2 ρ h) (kernelCuspPullback F)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (cuspWeightedFourierTest_memLp ρ h),kernelCuspPullback_ae_eq F] with w hw hp
  rw [RCLike.inner_apply,cuspWeightedFourierTestL2,hw,hp]
  simp only [starRingEnd_apply,star_star]

lemma kernelCuspWeightedFourier_restrict (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (F : KernelQuotientL2) :
    kernelCuspWeightedFourier ρ h (kernelMassRestrictionCLM kernelCuspAverageCompact
      kernelCuspAverageCompact_isCompact.measurableSet F)=kernelCuspWeightedFourier ρ h F := by
  rw [kernelCuspWeightedFourier_integral,kernelCuspWeightedFourier_integral]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (kernelMassRestriction_coe kernelCuspAverageCompact kernelCuspAverageCompact_isCompact.measurableSet F)
    (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  exact congrArg (fun z : ℂ => z*cuspWeightedFourierPhase ρ h w)
    (hw.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩) _))

def kernelCuspWeightedFourierFamily (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (s : ℂ) : ℂ :=
  kernelCuspWeightedFourier ρ h
    (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact
      2 3 (by norm_num) (by norm_num) s)

lemma kernelCuspWeightedFourierFamily_meromorphicAt (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) :
    MeromorphicAt (kernelCuspWeightedFourierFamily ρ h) (4/3:ℂ) :=
  meromorphicAt_clm (kernelCuspWeightedFourier ρ h)
    (kernelLocalCorrectedSeed_meromorphicAt kernelCuspAverageCompact kernelCuspAverageCompact_isCompact
      2 3 (by norm_num) (by norm_num))

lemma kernelCuspWeightedFourierFamily_analyticAt_nonreal (ρ : BoundedContinuousFunction ℝ ℂ) (h : O)
    (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelCuspWeightedFourierFamily ρ h) s := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    (kernelCuspWeightedFourier ρ h) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal kernelCuspAverageCompact
        kernelCuspAverageCompact_isCompact 2 3 (by norm_num) (by norm_num) s hs hi) rfl

lemma kernelCuspWeightedFourierFamily_residue_limit (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) :
    Tendsto (fun s : ℂ => (s-4/3)*kernelCuspWeightedFourierFamily ρ h s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspWeightedFourier ρ h cubicEisensteinResidue)) := by
  have hh := (kernelCuspWeightedFourier ρ h).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit kernelCuspAverageCompact kernelCuspAverageCompact_isCompact)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,kernelCuspWeightedFourier_restrict,
    kernelCuspWeightedFourierFamily] using hh

lemma kernelCuspWeightedFourierFamily_initial (ρ : BoundedContinuousFunction ℝ ℂ) (h : O)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelCuspWeightedFourierFamily ρ h s=∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  rw [kernelCuspWeightedFourierFamily,kernelCuspWeightedFourier_integral]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (cubicEisensteinLocalFamily_initial_ae kernelCuspAverageCompact kernelCuspAverageCompact_isCompact s hs hi)
    (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  dsimp only [Function.comp_def] at hw
  rw [hw,Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩),
    kernelQuotientEisenstein_mk]

def cuspWeightedWhittakerHeightFactor (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (h : O) : ℂ :=
  ∫v in Set.Icc (5:ℝ) 6,ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))

lemma hyperbolicEisenstein_cusp_weighted_fourier_nonzero (ρ : BoundedContinuousFunction ℝ ℂ)
    (s : ℂ) (hs : 2<s.re) (h : O) (hh : h≠0) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWeightedWhittakerHeightFactor ρ s h := by
  let g : HyperbolicSpace→ℂ := fun w => hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).mul (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg)]
  have hexp : ∀v∈Set.Icc (5:ℝ) 6,
      ((∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3)=
        (((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
          (ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))) := by
    intro v hv
    have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
    have hinner : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
        ρ v*(eisensteinFourierCoefficient v hpos s h*((9*Real.sqrt 3/2:ℝ):ℂ)) := by
      simp_rw [g,cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint,
        cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
      have hrearr : (∫z in periodDomain,upperEisenstein z v hpos s*
          (ρ v*tracePhase (-cuspFrequency h*z)))=
          ρ v*(∫z in periodDomain,upperEisenstein z v hpos s*tracePhase (-cuspFrequency h*z)) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by ring)
      rw [hrearr,eisensteinFourierCoefficient]
      congr 1
      exact (div_mul_cancel₀ _ cusp_volume_ne_zero).symm
    rw [hinner,eisensteinFourierCoefficient_formula v hpos s hs h,if_neg hh,zero_add]
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    have hp : (v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    rw [hp]
    ring
  calc
    _ = ∫v in Set.Icc (5:ℝ) 6,(((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
        (ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))) :=
      setIntegral_congr_fun measurableSet_Icc hexp
    _ = _ := integral_const_mul _ _

lemma kernelCuspWeightedFourierFamily_initial_factor (ρ : BoundedContinuousFunction ℝ ℂ)
    (h : O) (hh : h≠0) (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelCuspWeightedFourierFamily ρ h s=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWeightedWhittakerHeightFactor ρ s h := by
  rw [kernelCuspWeightedFourierFamily_initial ρ h s hs hi,
    hyperbolicEisenstein_cusp_weighted_fourier_nonzero ρ s (by linarith) h hh]


#print axioms kernelCuspWeightedFourierFamily_residue_limit
#print axioms kernelCuspWeightedFourierFamily_initial_factor
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
