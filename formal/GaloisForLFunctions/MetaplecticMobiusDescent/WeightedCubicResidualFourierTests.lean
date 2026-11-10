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


lemma cuspWeightedWhittakerHeightFactor_analyticAt
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (s : ℂ) (hs : 1 < s.re) :
    AnalyticAt ℂ (fun w => cuspWeightedWhittakerHeightFactor ρ w h) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
  simpa only [cuspWeightedWhittakerHeightFactor, mul_assoc] using
    cuspWeightedWhittakerAverage_differentiableAt ρ (cuspFrequency h) w hw

/-- Cross multiplication continues the weighted Fourier identity without
dividing by a Whittaker factor that might vanish away from the residue. -/
theorem kernelCuspWeightedFourierFamily_cross_identity
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (hh : h ≠ 0) :
    Set.EqOn
      (fun s => kernelCuspWeightedFourierFamily ρ h s * cuspWhittakerHeightFactor s h)
      (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s *
        cuspWeightedWhittakerHeightFactor ρ s h)
      {s : ℂ | 1 < s.re ∧ 0 < s.im} := by
  have hconvex : Convex ℝ {s : ℂ | 1 < s.re ∧ 0 < s.im} :=
    ((convex_Ioi (1 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hl : AnalyticOnNhd ℂ
      (fun s => kernelCuspWeightedFourierFamily ρ h s * cuspWhittakerHeightFactor s h)
      {s : ℂ | 1 < s.re ∧ 0 < s.im} := fun s hs =>
    (kernelCuspWeightedFourierFamily_analyticAt_nonreal ρ h s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt h s hs.1)
  have hr : AnalyticOnNhd ℂ
      (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s *
        cuspWeightedWhittakerHeightFactor ρ s h)
      {s : ℂ | 1 < s.re ∧ 0 < s.im} := fun s hs =>
    (kernelCuspFourierFamily_analyticAt_nonreal h 2 3 (by norm_num) (by norm_num)
      s hs.1.ne' hs.2.ne').mul (cuspWeightedWhittakerHeightFactor_analyticAt ρ h s hs.1)
  apply hl.eqOn_of_preconnected_of_eventuallyEq hr hconvex.isPreconnected
    (show (5 + Complex.I : ℂ) ∈ {s : ℂ | 1 < s.re ∧ 0 < s.im} by norm_num)
  have hopen : IsOpen {s : ℂ | 4 < s.re ∧ 0 < s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  filter_upwards [hopen.mem_nhds (by norm_num : (5 + Complex.I : ℂ) ∈
    {s : ℂ | 4 < s.re ∧ 0 < s.im})] with s hs
  rw [kernelCuspWeightedFourierFamily_initial_factor ρ h hh s hs.1 hs.2,
    cubicEisensteinFourierFamily_initial h hh s hs.1 hs.2]
  ring

/-- Every bounded height weight detects the same scattering residue. -/
theorem kernelCuspWeightedFourier_residue
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (hh : h ≠ 0) :
    kernelCuspWeightedFourier ρ h cubicEisensteinResidue =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * nonzeroScatteringResidue h *
        cuspWeightedWhittakerHeightFactor ρ (4 / 3) h := by
  have hbase := (cuspWhittakerHeightFactor_analyticAt h (4 / 3) (by norm_num)).continuousAt.tendsto.mono_left
    (show 𝓝[≠] (4 / 3 : ℂ) ≤ 𝓝 (4 / 3 : ℂ) from nhdsWithin_le_nhds)
  have hweight := (cuspWeightedWhittakerHeightFactor_analyticAt ρ h (4 / 3)
    (by norm_num)).continuousAt.tendsto.mono_left
      (show 𝓝[≠] (4 / 3 : ℂ) ≤ 𝓝 (4 / 3 : ℂ) from nhdsWithin_le_nhds)
  have hl := ((kernelCuspWeightedFourierFamily_residue_limit ρ h).mul hbase).comp
    thetaApproach_tendsto_complex_punctured
  have hr := ((kernelCuspFourierFamily_residue_limit h 2 3 (by norm_num) (by norm_num)).mul
    hweight).comp thetaApproach_tendsto_complex_punctured
  have hevent :
      (fun t : ℝ =>
        (((4 / 3 : ℂ) + t + t * Complex.I - 4 / 3) *
          kernelCuspWeightedFourierFamily ρ h ((4 / 3 : ℂ) + t + t * Complex.I)) *
            cuspWhittakerHeightFactor ((4 / 3 : ℂ) + t + t * Complex.I) h)
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ =>
        (((4 / 3 : ℂ) + t + t * Complex.I - 4 / 3) *
          kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num)
            ((4 / 3 : ℂ) + t + t * Complex.I)) *
              cuspWeightedWhittakerHeightFactor ρ ((4 / 3 : ℂ) + t + t * Complex.I) h) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    have hs : (4 / 3 : ℂ) + t + t * Complex.I ∈ {s : ℂ | 1 < s.re ∧ 0 < s.im} := by
      constructor
      · norm_num
        linarith
      · simpa using ht
    simpa only [mul_assoc] using congrArg
      (fun z : ℂ => ((4 / 3 : ℂ) + t + t * Complex.I - 4 / 3) * z)
      (kernelCuspWeightedFourierFamily_cross_identity ρ h hh hs)
  have heq : kernelCuspWeightedFourier ρ h cubicEisensteinResidue *
      cuspWhittakerHeightFactor (4 / 3) h =
        kernelCuspFourier h cubicEisensteinResidue *
          cuspWeightedWhittakerHeightFactor ρ (4 / 3) h :=
    tendsto_nhds_unique_of_eventuallyEq hl hr hevent
  apply mul_right_cancel₀ (cuspWhittakerHeightFactor_center_ne_zero h)
  rw [heq, nonzeroScatteringResidue]
  field_simp [cusp_volume_ne_zero, cuspWhittakerHeightFactor_center_ne_zero h]

/-- Normalization converting the scattering residue to the coefficient of
the height profile `v K_{1/3}(4π|frequency|v)`. -/
def cubicResidualFourierCoefficient (h : O) : ℂ :=
  nonzeroScatteringResidue h *
    ((2 * Real.pi : ℂ) / Complex.Gamma (4 / 3) *
      (2 * Real.pi * ‖cuspFrequency h‖ : ℂ) ^ (1 / 3 : ℂ))

lemma sourceFourierKernel_residual_height (h : O) (hh : h ≠ 0) (v : ℝ) (hv : 0 < v) :
    (v : ℂ) ^ (-(4 / 3 : ℂ) - 1) * sourceFourierKernel (4 / 3) (cuspFrequency h * v) =
      ((2 * Real.pi : ℂ) / Complex.Gamma (4 / 3) *
        (2 * Real.pi * ‖cuspFrequency h‖ : ℂ) ^ (1 / 3 : ℂ)) *
          (schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2) := by
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  rw [sourceFourierKernel_four_thirds _ (mul_ne_zero (cuspFrequency_ne_zero h hh) hv0),
    norm_mul, Complex.norm_of_nonneg hv.le]
  simp only [Complex.ofReal_mul, ← mul_assoc]
  have hsplit : (2 * Real.pi * ‖cuspFrequency h‖ * v : ℂ) ^ (1 / 3 : ℂ) =
      (2 * Real.pi * ‖cuspFrequency h‖ : ℂ) ^ (1 / 3 : ℂ) * (v : ℂ) ^ (1 / 3 : ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg
        (show 0 ≤ 2 * Real.pi * ‖cuspFrequency h‖ by positivity) hv.le (1 / 3 : ℂ)
  rw [hsplit]
  have hpower : (v : ℂ) ^ (-(4 / 3 : ℂ) - 1) * (v : ℂ) ^ (1 / 3 : ℂ) *
      (v : ℂ) ^ 2 = 1 := by
    rw [← Complex.cpow_natCast (v : ℂ) 2, ← Complex.cpow_add _ _ hv0,
      ← Complex.cpow_add _ _ hv0]
    norm_num
  calc
    _ = ((2 * Real.pi : ℂ) / Complex.Gamma (4 / 3) *
        (2 * Real.pi * ‖cuspFrequency h‖ : ℂ) ^ (1 / 3 : ℂ) *
          schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v)) / (v : ℂ) ^ 2 := by
      apply (eq_div_iff (pow_ne_zero 2 hv0)).mpr
      linear_combination
        ((2 * Real.pi : ℂ) / Complex.Gamma (4 / 3) *
          (2 * Real.pi * ‖cuspFrequency h‖ : ℂ) ^ (1 / 3 : ℂ) *
            schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v)) * hpower
    _ = _ := by ring

/-- The actual residual vector has the cubic Bessel height profile, tested
against every bounded continuous weight on the cusp strip. -/
theorem kernelCuspWeightedFourier_residue_bessel
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (hh : h ≠ 0) :
    kernelCuspWeightedFourier ρ h cubicEisensteinResidue =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * cubicResidualFourierCoefficient h *
        (∫ v in Set.Icc (5 : ℝ) 6,
          ρ v * (schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2)) := by
  rw [kernelCuspWeightedFourier_residue ρ h hh, cuspWeightedWhittakerHeightFactor,
    cubicResidualFourierCoefficient]
  have hfactor :
      (∫ v in Set.Icc (5 : ℝ) 6,
        ρ v * ((v : ℂ) ^ (-(4 / 3 : ℂ) - 1) * sourceFourierKernel (4 / 3) (cuspFrequency h * v))) =
      ((2 * Real.pi : ℂ) / Complex.Gamma (4 / 3) *
        (2 * Real.pi * ‖cuspFrequency h‖ : ℂ) ^ (1 / 3 : ℂ)) *
          (∫ v in Set.Icc (5 : ℝ) 6,
            ρ v * (schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    dsimp only
    rw [sourceFourierKernel_residual_height h hh v (lt_of_lt_of_le (by norm_num) hv.1)]
    ring
  rw [hfactor]
  ring

/-- The weighted Fourier bounds are uniform in the lattice frequency. -/
theorem kernelCuspWeightedFourier_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (F : KernelQuotientL2),
      ‖kernelCuspWeightedFourier ρ h F‖ ≤ C * ‖ρ‖ * ‖F‖ := by
  let mass : ℝ :=
    (measureUnivNNReal (hyperbolicVolume.restrict (cuspPeriodStrip 5 6)) : ℝ) ^
      (2 : ℝ≥0∞).toReal⁻¹
  have hmass : 0 ≤ mass := Real.rpow_nonneg (by positivity) _
  refine ⟨mass * ‖kernelCuspPullback‖, mul_nonneg hmass (norm_nonneg _), ?_⟩
  intro ρ h F
  have htest : ‖cuspWeightedFourierTestL2 ρ h‖ ≤ mass * ‖ρ‖ := by
    apply Lp.norm_le_of_ae_bound (norm_nonneg ρ)
    filter_upwards [MemLp.coeFn_toLp (cuspWeightedFourierTest_memLp ρ h)] with w hw
    change ‖cuspWeightedFourierTestL2 ρ h w‖ ≤ ‖ρ‖
    rw [cuspWeightedFourierTestL2, hw, norm_star]
    exact cuspWeightedFourierPhase_bound ρ h w
  change ‖inner ℂ (cuspWeightedFourierTestL2 ρ h) (kernelCuspPullback F)‖ ≤ _
  calc
    _ ≤ ‖cuspWeightedFourierTestL2 ρ h‖ * ‖kernelCuspPullback F‖ := norm_inner_le_norm _ _
    _ ≤ (mass * ‖ρ‖) * (‖kernelCuspPullback‖ * ‖F‖) :=
      mul_le_mul htest (kernelCuspPullback.le_opNorm F) (norm_nonneg _)
        (mul_nonneg hmass (norm_nonneg _))
    _ = _ := by ring

/-- A compact coordinate hull of any positive-height period strip. -/
def cuspIntervalHull (a b : ℝ) : Set HyperbolicSpace :=
  cuspCoordinateLift '' (Set.Icc a b ×ˢ Metric.closedBall (0 : ℂ) (∑ i, ‖periodBasis i‖))

lemma cuspIntervalHull_isCompact (a b : ℝ) (ha : 0 < a) : IsCompact (cuspIntervalHull a b) :=
  (isCompact_Icc.prod (isCompact_closedBall _ _)).image_of_continuousOn
    (fun q hq => (cuspCoordinateLift_continuousAt q (ha.trans_le hq.1.1)).continuousWithinAt)

lemma cuspPeriodStrip_subset_intervalHull (a b : ℝ) :
    cuspPeriodStrip a b ⊆ cuspIntervalHull a b := by
  intro w hw
  obtain ⟨z, v, hv, rfl⟩ := upperPoint_surjective w
  have hz : z ∈ periodDomain := by simpa only [hyperbolicHorizontal_upperPoint] using hw.1
  have hvab : v ∈ Set.Icc a b := by simpa only [hyperbolicHeight_upperPoint] using hw.2
  refine ⟨(v, z), ⟨hvab, ?_⟩, cuspCoordinateLift_positive v z hv⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using norm_mem_periodDomain z hz

lemma kernelCuspInterval_projection_bound (a b : ℝ) (ha : 0 < a) :
    Measure.map (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (cuspPeriodStrip a b)) ≤
        (kernelCompactMultiplicity (cuspIntervalHull a b) (cuspIntervalHull_isCompact a b ha) : ℝ≥0∞) •
          integralQuotientVolume globalKubotaKernel := by
  apply le_trans _ (kernelCompactMultiplicity_spec _ (cuspIntervalHull_isCompact a b ha))
  apply Measure.map_mono _ (measurable_integralOrbitProjection _)
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.restrict_apply hS, Measure.restrict_apply hS]
  exact measure_mono (Set.inter_subset_inter_left S (cuspPeriodStrip_subset_intervalHull a b))

lemma kernelCuspInterval_projection_quasiMeasurePreserving (a b : ℝ) (ha : 0 < a) :
    Measure.QuasiMeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (cuspPeriodStrip a b))
      (integralQuotientVolume globalKubotaKernel) :=
  ⟨measurable_integralOrbitProjection _,
    Measure.absolutelyContinuous_of_le_smul (kernelCuspInterval_projection_bound a b ha)⟩

lemma cuspInterval_measure_ne_top (a b : ℝ) (ha : 0 < a) :
    hyperbolicVolume (cuspPeriodStrip a b) ≠ (⊤ : ℝ≥0∞) := by
  have hb := kernelCuspInterval_projection_bound a b ha Set.univ
  rw [Measure.map_apply (measurable_integralOrbitProjection _) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply_univ, Measure.smul_apply] at hb
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)) hb

def kernelCuspIntervalPullback (a b : ℝ) (ha : 0 < a) :
    KernelQuotientL2 →L[ℂ] Lp ℂ 2 (hyperbolicVolume.restrict (cuspPeriodStrip a b)) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (integralOrbitProjection globalKubotaKernel)
    ⟨measurable_integralOrbitProjection _, rfl⟩).toContinuousLinearMap.comp
      (dominatedComplexL2 (by simp) (kernelCuspInterval_projection_bound a b ha))

lemma kernelCuspIntervalPullback_ae (a b : ℝ) (ha : 0 < a) (F : KernelQuotientL2) :
    kernelCuspIntervalPullback a b ha F =ᵐ[hyperbolicVolume.restrict (cuspPeriodStrip a b)]
      fun w => F (integralOrbitProjection globalKubotaKernel w) := by
  have hm : MeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (cuspPeriodStrip a b))
      (Measure.map (integralOrbitProjection globalKubotaKernel)
        (hyperbolicVolume.restrict (cuspPeriodStrip a b))) :=
    ⟨measurable_integralOrbitProjection _, rfl⟩
  exact (Lp.coeFn_compMeasurePreserving _ hm).trans
    (hm.quasiMeasurePreserving.ae_eq_comp
      (dominatedComplexL2_ae (by simp) (kernelCuspInterval_projection_bound a b ha) F))

def kernelCuspIntervalCompact (a b : ℝ) : Set KernelQuotient :=
  integralOrbitProjection globalKubotaKernel '' cuspIntervalHull a b

lemma kernelCuspIntervalCompact_isCompact (a b : ℝ) (ha : 0 < a) :
    IsCompact (kernelCuspIntervalCompact a b) :=
  (cuspIntervalHull_isCompact a b ha).image (continuous_integralOrbitProjection _)

lemma cuspIntervalWeightedFourier_memLp (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) :
    MemLp (fun w => star (cuspWeightedFourierPhase ρ h w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip a b)) := by
  letI : IsFiniteMeasure (hyperbolicVolume.restrict (cuspPeriodStrip a b)) :=
    isFiniteMeasure_restrict.mpr (cuspInterval_measure_ne_top a b ha)
  apply MemLp.of_bound (cuspWeightedFourierPhase_continuous ρ h).star.aestronglyMeasurable ‖ρ‖
  exact Eventually.of_forall (fun w => by rw [norm_star]; exact cuspWeightedFourierPhase_bound ρ h w)

/-- Fourier pairing on any compact positive height interval; bounded
multiplicity replaces the injective high-cusp chart. -/
def kernelCuspIntervalFourier (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) : KernelQuotientL2 →L[ℂ] ℂ :=
  (innerSL ℂ ((cuspIntervalWeightedFourier_memLp a b ha ρ h).toLp
    (fun w => star (cuspWeightedFourierPhase ρ h w)))).comp (kernelCuspIntervalPullback a b ha)

lemma kernelCuspIntervalFourier_integral (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (F : KernelQuotientL2) :
    kernelCuspIntervalFourier a b ha ρ h F = ∫ w in cuspPeriodStrip a b,
      F (integralOrbitProjection globalKubotaKernel w) * cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume := by
  change inner ℂ _ (kernelCuspIntervalPullback a b ha F) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (cuspIntervalWeightedFourier_memLp a b ha ρ h),
    kernelCuspIntervalPullback_ae a b ha F] with w hw hp
  rw [RCLike.inner_apply, hw, hp]
  simp only [starRingEnd_apply, star_star]

lemma kernelCuspIntervalFourier_restrict (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (F : KernelQuotientL2) :
    kernelCuspIntervalFourier a b ha ρ h
      (kernelMassRestrictionCLM (kernelCuspIntervalCompact a b)
        (kernelCuspIntervalCompact_isCompact a b ha).measurableSet F) =
      kernelCuspIntervalFourier a b ha ρ h F := by
  rw [kernelCuspIntervalFourier_integral, kernelCuspIntervalFourier_integral]
  have he := (kernelCuspInterval_projection_quasiMeasurePreserving a b ha).ae_eq_comp
    (kernelMassRestriction_coe _ (kernelCuspIntervalCompact_isCompact a b ha).measurableSet F)
  apply integral_congr_ae
  filter_upwards [he, ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  rw [hw, Set.indicator_of_mem (Set.mem_image_of_mem _
    (cuspPeriodStrip_subset_intervalHull a b hwm))]

def kernelCuspIntervalFourierFamily (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (s : ℂ) : ℂ :=
  kernelCuspIntervalFourier a b ha ρ h
    (kernelLocalCorrectedSeed (kernelCuspIntervalCompact a b) (kernelCuspIntervalCompact_isCompact a b ha)
      2 3 (by norm_num) (by norm_num) s)

lemma kernelCuspIntervalFourierFamily_residue_limit (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) :
    Tendsto (fun s : ℂ => (s - 4 / 3) * kernelCuspIntervalFourierFamily a b ha ρ h s)
      (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (kernelCuspIntervalFourier a b ha ρ h cubicEisensteinResidue)) := by
  have ht := (kernelCuspIntervalFourier a b ha ρ h).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit _ (kernelCuspIntervalCompact_isCompact a b ha))
  simpa only [Function.comp_def, map_smul, smul_eq_mul, kernelCuspIntervalFourier_restrict,
    kernelCuspIntervalFourierFamily] using ht

lemma kernelCuspIntervalFourierFamily_analyticAt (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (s : ℂ) (hs : 1 < s.re) (hi : 0 < s.im) :
    AnalyticAt ℂ (kernelCuspIntervalFourierFamily a b ha ρ h) s :=
  (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    (kernelCuspIntervalFourier a b ha ρ h) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal _ (kernelCuspIntervalCompact_isCompact a b ha)
        2 3 (by norm_num) (by norm_num) s hs.ne' hi.ne') rfl

lemma cuspInterval_integral_coordinates (a b : ℝ) (ha : 0 < a) (g : HyperbolicSpace → ℂ)
    (hg : AEStronglyMeasurable g hyperbolicVolume)
    (hint : IntegrableOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q) / (q.1 : ℂ) ^ 3)
      (Set.Icc a b ×ˢ periodDomain) volume) :
    (∫ w in cuspPeriodStrip a b, g w ∂hyperbolicVolume) =
      ∫ v in Set.Icc a b, (∫ z in periodDomain, g (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 := by
  let S := spatialComplexSplit ⁻¹' (Set.Icc a b ×ˢ periodDomain)
  have hS : MeasurableSet S := spatialComplexSplit.measurable
    (measurableSet_Icc.prod periodDomain_measurable)
  have hpos : S ⊆ euclideanUpperHalf := fun p hp => ha.trans_le hp.1.1
  have hpre : hyperbolicEuclideanCoordinates ⁻¹' S = cuspPeriodStrip a b := by
    ext w
    change spatialComplexSplit (hyperbolicEuclideanCoordinates w) ∈ (Set.Icc a b ×ˢ periodDomain) ↔ _
    rw [spatialComplexSplit_coordinates]
    exact and_comm
  have hm := euclideanToHyperbolic_measurePreserving_on S hS
  rw [hpre] at hm
  have hh := hg.mono_measure (Measure.restrict_le_self (s := cuspPeriodStrip a b))
  have he : (∫ w in cuspPeriodStrip a b, g w ∂hyperbolicVolume) =
      ∫ p in S, g (euclideanToHyperbolic p) ∂hyperbolicEuclideanVolume := by
    rw [← hm.map_eq] at hh ⊢
    exact integral_map hm.measurable.aemeasurable hh
  rw [he, hyperbolicEuclidean_setIntegral_complex S hS hpos]
  have hsplit := spatialComplexSplit.measurableEmbedding.setIntegral_map
    (fun q : ℝ × ℂ => g (cuspCoordinateLift q) / (q.1 : ℂ) ^ 3)
    (Set.Icc a b ×ˢ periodDomain) («μ» := (volume : Measure EuclideanSpatial))
  rw [spatialComplexSplit_preserves_volume.map_eq] at hsplit
  have heq : (∫ p in S, g (euclideanToHyperbolic p) / (p 2 : ℂ) ^ 3) =
      ∫ q in Set.Icc a b ×ˢ periodDomain, g (cuspCoordinateLift q) / (q.1 : ℂ) ^ 3 := by
    rw [hsplit]
    simp only [S, cuspCoordinateLift, spatialComplexSplit.symm_apply_apply, spatialComplexSplit_fst]
  rw [heq]
  change (∫ q in Set.Icc a b ×ˢ periodDomain,
    g (cuspCoordinateLift q) / (q.1 : ℂ) ^ 3 ∂((volume : Measure ℝ).prod volume)) = _
  rw [setIntegral_prod _ hint]
  congr 1
  ext v
  exact integral_div ((v : ℂ) ^ 3) (fun z => g (cuspCoordinateLift (v, z)))

lemma cuspInterval_continuous_integrable (a b : ℝ) (ha : 0 < a)
    (g : HyperbolicSpace → ℂ) (hg : Continuous g) :
    IntegrableOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q) / (q.1 : ℂ) ^ 3)
      (Set.Icc a b ×ˢ periodDomain) volume := by
  have hc : ContinuousOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q) / (q.1 : ℂ) ^ 3)
      (Set.Icc a b ×ˢ Metric.closedBall (0 : ℂ) (∑ i, ‖periodBasis i‖)) := by
    intro q hq
    have hpos := ha.trans_le hq.1.1
    exact ((hg.continuousAt.comp (cuspCoordinateLift_continuousAt q hpos)).div
      ((Complex.continuous_ofReal.comp continuous_fst).continuousAt.pow 3)
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hpos.ne'))).continuousWithinAt
  apply (hc.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))).mono_set
  intro q hq
  refine ⟨hq.1, ?_⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using norm_mem_periodDomain q.2 hq.2

lemma kernelCuspIntervalFourierFamily_initial (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (s : ℂ) (hs : 4 < s.re) (hi : 0 < s.im) :
    kernelCuspIntervalFourierFamily a b ha ρ h s = ∫ w in cuspPeriodStrip a b,
      hyperbolicEisenstein s w * cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume := by
  rw [kernelCuspIntervalFourierFamily, kernelCuspIntervalFourier_integral]
  have he := (kernelCuspInterval_projection_quasiMeasurePreserving a b ha).ae_eq_comp
    (cubicEisensteinLocalFamily_initial_ae _ (kernelCuspIntervalCompact_isCompact a b ha) s hs hi)
  apply integral_congr_ae
  filter_upwards [he, ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  rw [hw, Set.indicator_of_mem (Set.mem_image_of_mem _
    (cuspPeriodStrip_subset_intervalHull a b hwm)), kernelQuotientEisenstein_mk]

def cuspIntervalWhittakerFactor (a b : ℝ) (ρ : BoundedContinuousFunction ℝ ℂ)
    (s : ℂ) (h : O) : ℂ :=
  ∫ v in Set.Icc a b, ρ v * ((v : ℂ) ^ (-s - 1) * sourceFourierKernel s (cuspFrequency h * v))

lemma cuspIntervalWhittakerFactor_analyticAt (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (s : ℂ) (hs : 1 < s.re) :
    AnalyticAt ℂ (fun w => cuspIntervalWhittakerFactor a b ρ w h) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
  simpa only [cuspIntervalWhittakerFactor, mul_assoc] using
    cuspWeightedWhittakerInterval_differentiableAt ρ a b ha (cuspFrequency h) w hw

lemma kernelCuspIntervalFourierFamily_initial_factor (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (hh : h ≠ 0)
    (s : ℂ) (hs : 4 < s.re) (hi : 0 < s.im) :
    kernelCuspIntervalFourierFamily a b ha ρ h s =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * scatteringCoefficient s h *
        cuspIntervalWhittakerFactor a b ρ s h := by
  rw [kernelCuspIntervalFourierFamily_initial a b ha ρ h s hs hi]
  let g : HyperbolicSpace → ℂ := fun w => hyperbolicEisenstein s w * cuspWeightedFourierPhase ρ h w
  have hg : Continuous g := (hyperbolicEisenstein_continuous s (by linarith)).mul
    (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspInterval_integral_coordinates a b ha g hg.aestronglyMeasurable
    (cuspInterval_continuous_integrable a b ha g hg)]
  have hinner (v : ℝ) (hv : 0 < v) :
      (∫ z in periodDomain, g (cuspCoordinateLift (v, z))) =
        ρ v * (eisensteinFourierCoefficient v hv s h * ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ)) := by
    simp_rw [g, cuspCoordinateLift_positive v _ hv, hyperbolicEisenstein_upperPoint,
      cuspWeightedFourierPhase, hyperbolicHeight_upperPoint, cuspFourierPhase, hyperbolicHorizontal_upperPoint]
    have he : (∫ z in periodDomain, upperEisenstein z v hv s *
        (ρ v * tracePhase (-cuspFrequency h * z))) =
        ρ v * (∫ z in periodDomain, upperEisenstein z v hv s * tracePhase (-cuspFrequency h * z)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by ring)
    rw [he, eisensteinFourierCoefficient]
    congr 1
    exact (div_mul_cancel₀ _ cusp_volume_ne_zero).symm
  rw [cuspIntervalWhittakerFactor, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  dsimp only
  have hpos := ha.trans_le hv.1
  have hv0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  rw [hinner v hpos, eisensteinFourierCoefficient_formula v hpos s (by linarith) h,
    if_neg hh, zero_add]
  have hp : (v : ℂ) ^ (-s - 1) = (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 := by
    rw [show -s - 1 = (2 - s) - 3 by ring, Complex.cpow_sub _ _ hv0]
    congr 1
    exact Complex.cpow_natCast _ 3
  rw [hp]
  ring

theorem kernelCuspIntervalFourierFamily_cross_identity (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (hh : h ≠ 0) :
    Set.EqOn
      (fun s => kernelCuspIntervalFourierFamily a b ha ρ h s * cuspWhittakerHeightFactor s h)
      (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s *
        cuspIntervalWhittakerFactor a b ρ s h)
      {s : ℂ | 1 < s.re ∧ 0 < s.im} := by
  have hconvex : Convex ℝ {s : ℂ | 1 < s.re ∧ 0 < s.im} :=
    ((convex_Ioi (1 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hl : AnalyticOnNhd ℂ
      (fun s => kernelCuspIntervalFourierFamily a b ha ρ h s * cuspWhittakerHeightFactor s h)
      {s : ℂ | 1 < s.re ∧ 0 < s.im} := fun s hs =>
    (kernelCuspIntervalFourierFamily_analyticAt a b ha ρ h s hs.1 hs.2).mul
      (cuspWhittakerHeightFactor_analyticAt h s hs.1)
  have hr : AnalyticOnNhd ℂ
      (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s *
        cuspIntervalWhittakerFactor a b ρ s h)
      {s : ℂ | 1 < s.re ∧ 0 < s.im} := fun s hs =>
    (kernelCuspFourierFamily_analyticAt_nonreal h 2 3 (by norm_num) (by norm_num)
      s hs.1.ne' hs.2.ne').mul (cuspIntervalWhittakerFactor_analyticAt a b ha ρ h s hs.1)
  apply hl.eqOn_of_preconnected_of_eventuallyEq hr hconvex.isPreconnected
    (show (5 + Complex.I : ℂ) ∈ {s : ℂ | 1 < s.re ∧ 0 < s.im} by norm_num)
  have hopen : IsOpen {s : ℂ | 4 < s.re ∧ 0 < s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  filter_upwards [hopen.mem_nhds (by norm_num : (5 + Complex.I : ℂ) ∈
    {s : ℂ | 4 < s.re ∧ 0 < s.im})] with s hs
  rw [kernelCuspIntervalFourierFamily_initial_factor a b ha ρ h hh s hs.1 hs.2,
    cubicEisensteinFourierFamily_initial h hh s hs.1 hs.2]
  ring

/-- The same arithmetic residue controls Fourier tests at every positive
height, including strips where the quotient projection is not injective. -/
theorem kernelCuspIntervalFourier_residue (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (hh : h ≠ 0) :
    kernelCuspIntervalFourier a b ha ρ h cubicEisensteinResidue =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * nonzeroScatteringResidue h *
        cuspIntervalWhittakerFactor a b ρ (4 / 3) h := by
  have hbase := (cuspWhittakerHeightFactor_analyticAt h (4 / 3) (by norm_num)).continuousAt.tendsto.mono_left
    (show 𝓝[≠] (4 / 3 : ℂ) ≤ 𝓝 (4 / 3 : ℂ) from nhdsWithin_le_nhds)
  have hweight := (cuspIntervalWhittakerFactor_analyticAt a b ha ρ h (4 / 3)
    (by norm_num)).continuousAt.tendsto.mono_left
      (show 𝓝[≠] (4 / 3 : ℂ) ≤ 𝓝 (4 / 3 : ℂ) from nhdsWithin_le_nhds)
  have hl := ((kernelCuspIntervalFourierFamily_residue_limit a b ha ρ h).mul hbase).comp
    thetaApproach_tendsto_complex_punctured
  have hr := ((kernelCuspFourierFamily_residue_limit h 2 3 (by norm_num) (by norm_num)).mul
    hweight).comp thetaApproach_tendsto_complex_punctured
  have hevent :
      (fun t : ℝ =>
        (((4 / 3 : ℂ) + t + t * Complex.I - 4 / 3) *
          kernelCuspIntervalFourierFamily a b ha ρ h ((4 / 3 : ℂ) + t + t * Complex.I)) *
            cuspWhittakerHeightFactor ((4 / 3 : ℂ) + t + t * Complex.I) h)
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ =>
        (((4 / 3 : ℂ) + t + t * Complex.I - 4 / 3) *
          kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num)
            ((4 / 3 : ℂ) + t + t * Complex.I)) *
              cuspIntervalWhittakerFactor a b ρ ((4 / 3 : ℂ) + t + t * Complex.I) h) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    have hs : (4 / 3 : ℂ) + t + t * Complex.I ∈ {s : ℂ | 1 < s.re ∧ 0 < s.im} := by
      constructor
      · norm_num
        linarith
      · simpa using ht
    simpa only [mul_assoc] using congrArg
      (fun z : ℂ => ((4 / 3 : ℂ) + t + t * Complex.I - 4 / 3) * z)
      (kernelCuspIntervalFourierFamily_cross_identity a b ha ρ h hh hs)
  have heq : kernelCuspIntervalFourier a b ha ρ h cubicEisensteinResidue *
      cuspWhittakerHeightFactor (4 / 3) h =
        kernelCuspFourier h cubicEisensteinResidue *
          cuspIntervalWhittakerFactor a b ρ (4 / 3) h :=
    tendsto_nhds_unique_of_eventuallyEq hl hr hevent
  apply mul_right_cancel₀ (cuspWhittakerHeightFactor_center_ne_zero h)
  rw [heq, nonzeroScatteringResidue]
  field_simp [cusp_volume_ne_zero, cuspWhittakerHeightFactor_center_ne_zero h]

theorem kernelCuspIntervalFourier_residue_bessel (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (hh : h ≠ 0) :
    kernelCuspIntervalFourier a b ha ρ h cubicEisensteinResidue =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * cubicResidualFourierCoefficient h *
        (∫ v in Set.Icc a b,
          ρ v * (schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2)) := by
  rw [kernelCuspIntervalFourier_residue a b ha ρ h hh, cuspIntervalWhittakerFactor,
    cubicResidualFourierCoefficient]
  have hfactor :
      (∫ v in Set.Icc a b,
        ρ v * ((v : ℂ) ^ (-(4 / 3 : ℂ) - 1) * sourceFourierKernel (4 / 3) (cuspFrequency h * v))) =
      ((2 * Real.pi : ℂ) / Complex.Gamma (4 / 3) *
        (2 * Real.pi * ‖cuspFrequency h‖ : ℂ) ^ (1 / 3 : ℂ)) *
          (∫ v in Set.Icc a b,
            ρ v * (schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    dsimp only
    rw [sourceFourierKernel_residual_height h hh v (ha.trans_le hv.1)]
    ring
  rw [hfactor]
  ring

theorem kernelCuspIntervalFourier_uniform_bound (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (F : KernelQuotientL2),
      ‖kernelCuspIntervalFourier a b ha ρ h F‖ ≤ C * ‖ρ‖ * ‖F‖ := by
  letI : IsFiniteMeasure (hyperbolicVolume.restrict (cuspPeriodStrip a b)) :=
    isFiniteMeasure_restrict.mpr (cuspInterval_measure_ne_top a b ha)
  let mass : ℝ :=
    (measureUnivNNReal (hyperbolicVolume.restrict (cuspPeriodStrip a b)) : ℝ) ^
      (2 : ℝ≥0∞).toReal⁻¹
  have hmass : 0 ≤ mass := Real.rpow_nonneg (by positivity) _
  refine ⟨mass * ‖kernelCuspIntervalPullback a b ha‖, mul_nonneg hmass (norm_nonneg _), ?_⟩
  intro ρ h F
  have htest : ‖(cuspIntervalWeightedFourier_memLp a b ha ρ h).toLp
      (fun w => star (cuspWeightedFourierPhase ρ h w))‖ ≤ mass * ‖ρ‖ := by
    apply Lp.norm_le_of_ae_bound (norm_nonneg ρ)
    filter_upwards [MemLp.coeFn_toLp (cuspIntervalWeightedFourier_memLp a b ha ρ h)] with w hw
    rw [hw, norm_star]
    exact cuspWeightedFourierPhase_bound ρ h w
  change ‖inner ℂ _ (kernelCuspIntervalPullback a b ha F)‖ ≤ _
  calc
    _ ≤ ‖(cuspIntervalWeightedFourier_memLp a b ha ρ h).toLp _‖ *
        ‖kernelCuspIntervalPullback a b ha F‖ := norm_inner_le_norm _ _
    _ ≤ (mass * ‖ρ‖) * (‖kernelCuspIntervalPullback a b ha‖ * ‖F‖) :=
      mul_le_mul htest ((kernelCuspIntervalPullback a b ha).le_opNorm F) (norm_nonneg _)
        (mul_nonneg hmass (norm_nonneg _))
    _ = _ := by ring

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
