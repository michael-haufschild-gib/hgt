/-
Weighted residual Fourier tests adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicScatteringContinuation
import GaloisForLFunctions.MetaplecticMobiusDescent.WeightedCubicWhittakerAverages
import GaloisForLFunctions.MetaplecticMobiusDescent.CompactCubicQuotientPullbacks

/-!
# Weighted residual Fourier tests

Bounded continuous height weights give bounded `L²` Fourier pairings of the cubic residue
on every compact positive height interval. Analytic continuation identifies the pairings with
cubic Bessel height profiles, uniformly in the lattice frequency. Schläfli bounds give
subexponential coefficient growth, and exponential Bessel decay reconstructs the continuous
residual Fourier series `cubicResidualFunction`. The module ends with the real period
coordinates `periodVector` and `periodTorus` of the cusp lattice.
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
  exact measure_mono (fun w hw => ⟨hw.1, cuspPeriodStrip_subset_intervalHull a b hw.2⟩)

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
  dsimp only [Function.comp_def] at hw
  have hm : integralOrbitProjection globalKubotaKernel w ∈ kernelCuspIntervalCompact a b :=
    Set.mem_image_of_mem _ (cuspPeriodStrip_subset_intervalHull a b hwm)
  rw [hw, Set.indicator_of_mem hm]

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
  dsimp only [Function.comp_def] at hw
  have hm : integralOrbitProjection globalKubotaKernel w ∈ kernelCuspIntervalCompact a b :=
    Set.mem_image_of_mem _ (cuspPeriodStrip_subset_intervalHull a b hwm)
  rw [hw, Set.indicator_of_mem hm, kernelQuotientEisenstein_mk]

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

lemma cubicResidualFourierCoefficient_interval_bound (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖cubicResidualFourierCoefficient h‖ *
        ‖∫ v in Set.Icc a b,
          schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := kernelCuspIntervalFourier_uniform_bound a b ha
  let area : ℂ := ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ)
  have harea : 0 < ‖area‖ := norm_pos_iff.mpr cusp_volume_ne_zero
  refine ⟨C * ‖BoundedContinuousFunction.const ℝ (1 : ℂ)‖ *
    ‖cubicEisensteinResidue‖ / ‖area‖, by positivity, ?_⟩
  intro h hh
  have hb := hbound (BoundedContinuousFunction.const ℝ (1 : ℂ)) h cubicEisensteinResidue
  rw [kernelCuspIntervalFourier_residue_bessel a b ha _ h hh] at hb
  simp only [BoundedContinuousFunction.const_apply, one_mul, norm_mul] at hb
  apply (le_div_iff₀ harea).mpr
  calc
    _ = ‖area‖ * ‖cubicResidualFourierCoefficient h‖ *
        ‖∫ v in Set.Icc a b,
          schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2‖ := by ring
    _ ≤ _ := hb

def cubicSchlafliDensity (x t : ℝ) : ℝ :=
  t ^ (-(2 : ℝ) / 3) * Real.exp (-t - x ^ 2 / (4 * t))

lemma cubicSchlafliDensity_eq (x t : ℝ) (ht : 0 < t) :
    ((t : ℂ) ^ ((1 / 3 : ℂ) - 1) *
      Complex.exp (-(t : ℂ) - (x : ℂ) ^ 2 / (4 * t))).re = cubicSchlafliDensity x t := by
  have he := congrArg Complex.re (schlafliIntegrand_real (1 / 3) x t ht)
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.ofReal_re] at he
  convert he using 1 <;> norm_num [cubicSchlafliDensity]

lemma cubicSchlafliDensity_integrable (x : ℝ) :
    IntegrableOn (cubicSchlafliDensity x) (Set.Ioi 0) := by
  apply (schlafliIntegral_integrable (1 / 3) x (by norm_num)).re.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact cubicSchlafliDensity_eq x t ht

lemma cubicSchlafliIntegral_re (x : ℝ) :
    (schlafliIntegral (1 / 3) x).re = ∫ t in Set.Ioi 0, cubicSchlafliDensity x t := by
  unfold schlafliIntegral
  have hre := integral_re (schlafliIntegral_integrable (1 / 3) x (by norm_num))
  change (∫ t : ℝ in Set.Ioi 0, ((t : ℂ) ^ ((1 / 3 : ℂ) - 1) *
    Complex.exp (-(t : ℂ) - (x : ℂ) ^ 2 / (4 * t))).re) =
    (∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ ((1 / 3 : ℂ) - 1) *
      Complex.exp (-(t : ℂ) - (x : ℂ) ^ 2 / (4 * t))).re at hre
  rw [← hre]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact cubicSchlafliDensity_eq x t ht

lemma schlafliBesselK_one_third_re (x : ℝ) (hx : 0 < x) :
    (schlafliBesselK (1 / 3) x).re =
      (1 / 2 : ℝ) * (x / 2) ^ (-(1 : ℝ) / 3) *
        ∫ t in Set.Ioi 0, cubicSchlafliDensity x t := by
  have hp := (Complex.ofReal_cpow (show 0 ≤ x / 2 by positivity) (-(1 : ℝ) / 3)).symm
  push_cast at hp
  simp only [neg_div] at hp
  rw [schlafliBesselK, hp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [cubicSchlafliIntegral_re]
  norm_num

/-- A positive interval of the Schläfli integral gives an exponential lower
bound with a constant independent of its argument. -/
theorem schlafliBesselK_one_third_exp_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 0 < x →
      c * Real.exp (-9 * x / 4) ≤ (schlafliBesselK (1 / 3) x).re := by
  let c : ℝ := (1 / 2) * (1 / 2 : ℝ) ^ (-(1 : ℝ) / 3) * (2 : ℝ) ^ (-(2 : ℝ) / 3)
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  intro x hx
  have hsub : Set.Icc x (2 * x) ⊆ Set.Ioi 0 := fun t ht => hx.trans_le ht.1
  have hi := cubicSchlafliDensity_integrable x
  have hlower (t : ℝ) (ht : t ∈ Set.Icc x (2 * x)) :
      (2 * x) ^ (-(2 : ℝ) / 3) * Real.exp (-9 * x / 4) ≤ cubicSchlafliDensity x t := by
    have ht0 := hx.trans_le ht.1
    have hp := Real.rpow_le_rpow_of_nonpos ht0 ht.2 (by norm_num : -(2 : ℝ) / 3 ≤ 0)
    have hfrac : x ^ 2 / (4 * t) ≤ x / 4 :=
      (div_le_iff₀ (by positivity : 0 < 4 * t)).mpr
        (by nlinarith only [mul_nonneg hx.le (sub_nonneg.mpr ht.1)])
    exact mul_le_mul hp (Real.exp_le_exp.mpr (by linarith [ht.2]))
      (Real.exp_pos _).le (Real.rpow_nonneg ht0.le _)
  have hmono := setIntegral_mono_on
    (integrableOn_const (hs := isCompact_Icc.measure_ne_top) :
      IntegrableOn (fun _ : ℝ => (2 * x) ^ (-(2 : ℝ) / 3) * Real.exp (-9 * x / 4))
        (Set.Icc x (2 * x)))
    (hi.mono_set hsub) measurableSet_Icc hlower
  have hextend : (∫ t in Set.Icc x (2 * x), cubicSchlafliDensity x t) ≤
      ∫ t in Set.Ioi 0, cubicSchlafliDensity x t := by
    apply setIntegral_mono_set hi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
    · exact Eventually.of_forall hsub
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul,
    show 2 * x - x = x by ring] at hmono
  have hscaled := mul_le_mul_of_nonneg_left (hmono.trans hextend)
    (show 0 ≤ (1 / 2 : ℝ) * (x / 2) ^ (-(1 : ℝ) / 3) by positivity)
  rw [← schlafliBesselK_one_third_re x hx] at hscaled
  have hhalf : (x / 2) ^ (-(1 : ℝ) / 3) = (1 / 2 : ℝ) ^ (-(1 : ℝ) / 3) * x ^ (-(1 : ℝ) / 3) := by
    rw [show x / 2 = (1 / 2) * x by ring, Real.mul_rpow (by norm_num) hx.le]
  have htwo : (2 * x) ^ (-(2 : ℝ) / 3) = (2 : ℝ) ^ (-(2 : ℝ) / 3) * x ^ (-(2 : ℝ) / 3) :=
    Real.mul_rpow (by norm_num) hx.le
  have hpower : x ^ (-(1 : ℝ) / 3) * x * x ^ (-(2 : ℝ) / 3) = 1 := by
    calc
      _ = x ^ (-(1 : ℝ) / 3) * x ^ (1 : ℝ) * x ^ (-(2 : ℝ) / 3) := by rw [Real.rpow_one]
      _ = x ^ ((-(1 : ℝ) / 3 + 1) + (-(2 : ℝ) / 3)) := by
        rw [← Real.rpow_add hx, ← Real.rpow_add hx]
      _ = 1 := by norm_num
  have hnormalize : (1 / 2 : ℝ) * (x / 2) ^ (-(1 : ℝ) / 3) *
      (x * ((2 * x) ^ (-(2 : ℝ) / 3) * Real.exp (-9 * x / 4))) = c * Real.exp (-9 * x / 4) := by
    rw [hhalf, htwo]
    calc
      _ = c * (x ^ (-(1 : ℝ) / 3) * x * x ^ (-(2 : ℝ) / 3)) * Real.exp (-9 * x / 4) := by
        dsimp [c]
        ring
      _ = _ := by rw [hpower, mul_one]
  rwa [hnormalize] at hscaled

lemma cubicResidualBesselDensity_integrable (a b : ℝ) (ha : 0 < a) (h : O) (hh : h ≠ 0) :
    IntegrableOn (fun v : ℝ =>
      schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2)
      (Set.Icc a b) := by
  let B : ℂ := (2 * Real.pi : ℂ) / Complex.Gamma (4 / 3) *
    (2 * Real.pi * ‖cuspFrequency h‖ : ℂ) ^ (1 / 3 : ℂ)
  have hB : B ≠ 0 := by
    apply mul_ne_zero
    · exact div_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
    · apply Complex.cpow_ne_zero_iff.mpr
      exact Or.inl (mul_ne_zero
        (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (cuspFrequency_ne_zero h hh))))
  have hsource : IntegrableOn (fun v : ℝ => (v : ℂ) ^ (-(4 / 3 : ℂ) - 1) *
      sourceFourierKernel (4 / 3) (cuspFrequency h * v)) (Set.Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    intro v hv
    have hpos := ha.trans_le hv.1
    exact ((Complex.continuousAt_ofReal_cpow_const v (-(4 / 3 : ℂ) - 1) (Or.inr hpos.ne')).mul
      ((sourceFourierKernel_continuous_freq (4 / 3) (by norm_num)).continuousAt.comp
        ((Complex.continuous_ofReal.const_mul (cuspFrequency h)).continuousAt))).continuousWithinAt
  apply (hsource.div_const B).congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  apply (div_eq_iff hB).mpr
  simpa only [B, mul_comm] using sourceFourierKernel_residual_height h hh v (ha.trans_le hv.1)

/-- Bounds on every positive height interval force subexponential coefficient growth. -/
theorem cubicBesselCoefficient_subexponential (coeff : O → ℂ)
    (hinterval : ∀ a b : ℝ, 0 < a → ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖coeff h‖ * ‖∫ v in Set.Icc a b,
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2‖ ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖coeff h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖) := by
  obtain ⟨c, hc, hK⟩ := schlafliBesselK_one_third_exp_lower
  let b : ℝ := ε / (9 * Real.pi)
  let a : ℝ := b / 2
  have hb : 0 < b := div_pos hε (by positivity)
  have ha : 0 < a := half_pos hb
  have hab : a < b := by dsimp [a]; linarith
  obtain ⟨C, hC, hbound⟩ := hinterval a b ha
  let D : ℝ := (b - a) * c / b ^ 2
  have hD : 0 < D := div_pos (mul_pos (sub_pos.mpr hab) hc) (sq_pos_of_pos hb)
  refine ⟨C / D, div_nonneg hC hD.le, ?_⟩
  intro h hh
  have hr : 0 < ‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hi := cubicResidualBesselDensity_integrable a b ha h hh
  let L : ℝ := c * Real.exp (-(ε * ‖cuspFrequency h‖)) / b ^ 2
  have hpoint (v : ℝ) (hv : v ∈ Set.Icc a b) :
      L ≤ (schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2).re := by
    have hvp := ha.trans_le hv.1
    have hscale : 9 * Real.pi * b = ε := by dsimp [b]; field_simp
    have hexponent : -(ε * ‖cuspFrequency h‖) ≤ -9 * (4 * Real.pi * ‖cuspFrequency h‖ * v) / 4 := by
      have hm := mul_le_mul_of_nonneg_left hv.2 (show 0 ≤ 9 * Real.pi * ‖cuspFrequency h‖ by positivity)
      nlinarith only [hm, congrArg (fun z : ℝ => z * ‖cuspFrequency h‖) hscale]
    have hnum := (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hc.le).trans
      (hK (4 * Real.pi * ‖cuspFrequency h‖ * v) (by positivity))
    rw [← Complex.ofReal_pow, Complex.div_ofReal_re]
    exact (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hvp)
      ((sq_le_sq₀ hvp.le hb.le).mpr hv.2)).trans
        (div_le_div_of_nonneg_right hnum (sq_nonneg v))
  have hire : IntegrableOn (fun v : ℝ =>
      (schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2).re)
      (Set.Icc a b) := hi.re
  have hre := integral_re hi
  change (∫ v in Set.Icc a b,
    (schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2).re) =
    (∫ v in Set.Icc a b,
      schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2).re at hre
  have hmono := setIntegral_mono_on
    (integrableOn_const (hs := isCompact_Icc.measure_ne_top) :
      IntegrableOn (fun _ : ℝ => L) (Set.Icc a b)) hire measurableSet_Icc hpoint
  rw [setIntegral_const, Real.volume_real_Icc_of_le hab.le, smul_eq_mul, hre] at hmono
  have hlow : D * Real.exp (-(ε * ‖cuspFrequency h‖)) ≤
      ‖∫ v in Set.Icc a b,
        schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2‖ := by
    calc
      D * Real.exp (-(ε * ‖cuspFrequency h‖)) = (b - a) * L := by dsimp only [D, L]; ring
      _ ≤ (∫ v in Set.Icc a b,
          schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2).re := hmono
      _ ≤ _ := Complex.re_le_norm _
  have hmul := (mul_le_mul_of_nonneg_left hlow (norm_nonneg (coeff h))).trans
    (hbound h hh)
  calc
    _ ≤ C / (D * Real.exp (-(ε * ‖cuspFrequency h‖))) :=
      (le_div_iff₀ (mul_pos hD (Real.exp_pos _))).mpr hmul
    _ = (C / D) * Real.exp (ε * ‖cuspFrequency h‖) := by
      rw [Real.exp_neg]
      field_simp

/-- Arbitrarily low compact cusp strips force subexponential growth of the actual scattering residues. -/
theorem cubicResidualFourierCoefficient_subexponential (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖cubicResidualFourierCoefficient h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖) :=
  cubicBesselCoefficient_subexponential cubicResidualFourierCoefficient
    cubicResidualFourierCoefficient_interval_bound ε hε

lemma cubicSchlafliIntegral_ofReal (x : ℝ) :
    schlafliIntegral (1 / 3) x = ((∫ t in Set.Ioi 0, cubicSchlafliDensity x t : ℝ) : ℂ) := by
  unfold schlafliIntegral
  calc
    _ = ∫ t in Set.Ioi (0 : ℝ), ((cubicSchlafliDensity x t : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have he := schlafliIntegrand_real (1 / 3) x t ht
      norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at he
      convert he using 1 <;> norm_num [cubicSchlafliDensity]
    _ = _ := integral_ofReal

lemma schlafliBesselK_one_third_norm (x : ℝ) (hx : 0 < x) :
    ‖schlafliBesselK (1 / 3) x‖ =
      (1 / 2 : ℝ) * (x / 2) ^ (-(1 : ℝ) / 3) *
        ∫ t in Set.Ioi 0, cubicSchlafliDensity x t := by
  have hp := (Complex.ofReal_cpow (show 0 ≤ x / 2 by positivity) (-(1 : ℝ) / 3)).symm
  push_cast at hp
  simp only [neg_div] at hp
  have hnonneg : 0 ≤ ∫ t in Set.Ioi 0, cubicSchlafliDensity x t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
  rw [schlafliBesselK, hp, cubicSchlafliIntegral_ofReal]
  have he : (1 / 2 : ℂ) * ((x / 2) ^ (-(1 : ℝ) / 3) : ℝ) *
      ((∫ t in Set.Ioi 0, cubicSchlafliDensity x t : ℝ) : ℂ) =
      (((1 / 2 : ℝ) * (x / 2) ^ (-(1 : ℝ) / 3) *
        ∫ t in Set.Ioi 0, cubicSchlafliDensity x t : ℝ) : ℂ) := by push_cast; rfl
  simp only [neg_div] at he ⊢
  rw [he, Complex.norm_of_nonneg (mul_nonneg (by positivity) hnonneg)]

/-- The Schläfli exponential absorbs half its argument uniformly away
from zero; the remaining integrand is an integrable Gamma density. -/
theorem schlafliBesselK_one_third_exp_upper (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, δ ≤ x →
      ‖schlafliBesselK (1 / 3) x‖ ≤ C * Real.exp (-x / 2) := by
  let g : ℝ → ℝ := fun t => t ^ (-(2 : ℝ) / 3) * Real.exp (-t / 2)
  have hg : IntegrableOn g (Set.Ioi 0) := by
    have hh := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := -(2 : ℝ) / 3) (p := (1 : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    simpa only [g, Real.rpow_one, show ∀ t : ℝ, -(1 / 2) * t = -t / 2 by intro t; ring] using hh
  have hg0 : 0 ≤ ∫ t in Set.Ioi 0, g t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
  refine ⟨(1 / 2) * (δ / 2) ^ (-(1 : ℝ) / 3) * ∫ t in Set.Ioi 0, g t,
    mul_nonneg (by positivity) hg0, ?_⟩
  intro x hx
  have hxp := hδ.trans_le hx
  have hpoint (t : ℝ) (ht : 0 < t) :
      cubicSchlafliDensity x t ≤ Real.exp (-x / 2) * g t := by
    have hfrac : x / 2 - t / 2 ≤ x ^ 2 / (4 * t) :=
      (le_div_iff₀ (by positivity : 0 < 4 * t)).mpr
        (by nlinarith only [sq_nonneg (x - t), sq_nonneg t])
    calc
      _ ≤ t ^ (-(2 : ℝ) / 3) * Real.exp (-x / 2 + -t / 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hfrac]))
          (Real.rpow_nonneg ht.le _)
      _ = _ := by rw [Real.exp_add]; dsimp [g]; ring
  have hb := setIntegral_mono_on (cubicSchlafliDensity_integrable x)
    (hg.const_mul (Real.exp (-x / 2))) measurableSet_Ioi hpoint
  rw [integral_const_mul] at hb
  have hp : (x / 2) ^ (-(1 : ℝ) / 3) ≤ (δ / 2) ^ (-(1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith only [hx]) (by norm_num)
  rw [schlafliBesselK_one_third_norm x hxp]
  calc
    _ ≤ (1 / 2 : ℝ) * (x / 2) ^ (-(1 : ℝ) / 3) *
        (Real.exp (-x / 2) * ∫ t in Set.Ioi 0, g t) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (1 / 2 : ℝ) * (δ / 2) ^ (-(1 : ℝ) / 3) *
        (Real.exp (-x / 2) * ∫ t in Set.Ioi 0, g t) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num))
        (mul_nonneg (Real.exp_pos _).le hg0)
    _ = _ := by ring

lemma exp_neg_mul_le_inverse_cube (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) :
    Real.exp (-ε * r) ≤ (6 / ε ^ 3) * r ^ (-3 : ℝ) := by
  have hp := Real.pow_div_factorial_le_exp (ε * r) (mul_pos hε hr).le 3
  norm_num only [Nat.factorial] at hp
  have hi := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (ε * r) ^ 3 / 6) hp
  rw [one_div, ← Real.exp_neg] at hi
  rw [Real.rpow_neg hr.le]
  norm_num only [Real.rpow_ofNat]
  have he : (6 / ε ^ 3) * (r ^ 3)⁻¹ = ((ε * r) ^ 3 / 6)⁻¹ := by field_simp
  rw [he]
  simpa only [neg_mul, one_div] using hi

lemma summable_exp_neg_ringComplex_norm (ε : ℝ) (hε : 0 < ε) :
    Summable (fun h : O => Real.exp (-ε * ‖ringComplex h‖)) := by
  have hs := (summable_embedding_rpow (-3) (by norm_num)).mul_left (6 / ε ^ 3)
  have hz : Summable (fun h : O => if h = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq 0 (1 : ℝ)).summable
  apply Summable.of_nonneg_of_le (fun h => (Real.exp_pos _).le) _ (hz.add hs)
  intro h
  by_cases hh : h = 0
  · subst h
    norm_num [Pi.add_apply]
  · simpa only [Pi.add_apply, if_neg hh, zero_add] using
      exp_neg_mul_le_inverse_cube ε ‖ringComplex h‖ hε (norm_pos_iff.mpr (ringComplex_ne_zero hh))

lemma summable_exp_neg_cuspFrequency_norm (ε : ℝ) (hε : 0 < ε) :
    Summable (fun h : O => Real.exp (-ε * ‖cuspFrequency h‖)) := by
  have hd : 0 < ‖(3 : ℂ) * ringComplex traceLambda‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) (ringComplex_ne_zero traceLambda_ne_zero))
  apply (summable_exp_neg_ringComplex_norm (ε / ‖(3 : ℂ) * ringComplex traceLambda‖)
    (div_pos hε hd)).congr
  intro h
  congr 1
  rw [cuspFrequency, norm_div]
  ring

lemma cuspFrequency_norm_lower (h : O) (hh : h ≠ 0) :
    ‖(3 : ℂ) * ringComplex traceLambda‖⁻¹ ≤ ‖cuspFrequency h‖ := by
  have hn := one_le_normSq_embedding h hh
  rw [Complex.normSq_eq_norm_sq] at hn
  have hr : 1 ≤ ‖ringComplex h‖ := by nlinarith only [hn, norm_nonneg (ringComplex h)]
  rw [cuspFrequency, norm_div, inv_eq_one_div]
  exact div_le_div_of_nonneg_right hr (norm_nonneg _)

/-- The nonconstant residual Fourier mode, expressed using the native
Fourier kernel so that continuity requires no Bessel regularity theorem. -/
def cubicResidualNonzeroTerm (h : O) (p : ℝ × ℂ) : ℂ :=
  if h = 0 then 0 else nonzeroScatteringResidue h * (p.1 : ℂ) ^ (2 / 3 : ℂ) *
    sourceFourierKernel (4 / 3) (cuspFrequency h * p.1) * tracePhase (cuspFrequency h * p.2)

lemma cubicResidualNonzeroTerm_bessel (h : O) (hh : h ≠ 0) (v : ℝ) (hv : 0 < v) (z : ℂ) :
    cubicResidualNonzeroTerm h (v, z) = cubicResidualFourierCoefficient h * (v : ℂ) *
      schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) * tracePhase (cuspFrequency h * z) := by
  rw [cubicResidualNonzeroTerm, if_neg hh]
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hp : (v : ℂ) ^ 3 * (v : ℂ) ^ (-(4 / 3 : ℂ) - 1) = (v : ℂ) ^ (2 / 3 : ℂ) := by
    rw [← Complex.cpow_ofNat (v : ℂ) 3, ← Complex.cpow_add _ _ hv0]
    congr 1
    ring
  calc
    _ = nonzeroScatteringResidue h * (v : ℂ) ^ 3 *
        ((v : ℂ) ^ (-(4 / 3 : ℂ) - 1) * sourceFourierKernel (4 / 3) (cuspFrequency h * v)) *
          tracePhase (cuspFrequency h * z) := by rw [← hp]; ring
    _ = _ := by
      rw [sourceFourierKernel_residual_height h hh v hv, cubicResidualFourierCoefficient]
      field_simp

lemma cubicResidualNonzeroTerm_continuousOn (h : O) :
    ContinuousOn (cubicResidualNonzeroTerm h) {p : ℝ × ℂ | 0 < p.1} := by
  unfold cubicResidualNonzeroTerm
  by_cases hh : h = 0
  · simp only [if_pos hh]
    exact continuousOn_const
  simp only [if_neg hh]
  intro p hp
  have hpow : ContinuousAt (fun q : ℝ × ℂ => (q.1 : ℂ) ^ (2 / 3 : ℂ)) p :=
    (Complex.continuousAt_ofReal_cpow_const p.1 (2 / 3 : ℂ) (Or.inr hp.ne')).comp continuousAt_fst
  have hsource : ContinuousAt (fun q : ℝ × ℂ => sourceFourierKernel (4 / 3) (cuspFrequency h * q.1)) p :=
    (sourceFourierKernel_continuous_freq (4 / 3) (by norm_num)).continuousAt.comp (by fun_prop)
  have hphase : Continuous (fun q : ℝ × ℂ => tracePhase (cuspFrequency h * q.2)) := by
    change Continuous (fun q : ℝ × ℂ => Complex.exp (2 * Real.pi * Complex.I *
      ((cuspFrequency h * q.2) + starRingEnd ℂ (cuspFrequency h * q.2))))
    fun_prop
  exact (((continuousAt_const.mul hpow).mul hsource).mul hphase.continuousAt).continuousWithinAt

/-- Subexponential residues and exponential Bessel decay leave a summable
majorant uniform in the horizontal coordinate and in compact height strips. -/
theorem cubicBesselCoefficient_strip_bound (c : O → ℂ)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ h : O, h ≠ 0 →
      ‖c h‖ ≤ C * Real.exp (ε * ‖cuspFrequency h‖)) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : O), h ≠ 0 → ∀ v : ℝ, v ∈ Set.Icc a b →
      ‖c h * (v : ℂ) * schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v)‖ ≤ C * Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖) := by
  have hb : 0 < b := ha.trans_le hab
  let δ : ℝ := 4 * Real.pi * a * ‖(3 : ℂ) * ringComplex traceLambda‖⁻¹
  have hd : 0 < ‖(3 : ℂ) * ringComplex traceLambda‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) (ringComplex_ne_zero traceLambda_ne_zero))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨B, hB, hBessel⟩ := schlafliBesselK_one_third_exp_upper δ hδ
  obtain ⟨A, hA, hcoeff⟩ := hsub (Real.pi * a) (mul_pos Real.pi_pos ha)
  refine ⟨A * b * B, by positivity, ?_⟩
  intro h hh v hp
  have hv : 0 < v := ha.trans_le hp.1
  have hx : δ ≤ 4 * Real.pi * ‖cuspFrequency h‖ * v := by
    have hm := mul_le_mul (cuspFrequency_norm_lower h hh) hp.1 ha.le (norm_nonneg _)
    have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 4 * Real.pi by positivity)
    dsimp [δ]
    nlinarith only [hm']
  rw [norm_mul, norm_mul, Complex.norm_of_nonneg hv.le]
  calc
    _ ≤ (A * Real.exp ((Real.pi * a) * ‖cuspFrequency h‖)) * b *
        (B * Real.exp (-(4 * Real.pi * ‖cuspFrequency h‖ * v) / 2)) :=
      mul_le_mul (mul_le_mul (hcoeff h hh) hp.2 hv.le (by positivity))
        (hBessel _ hx) (norm_nonneg _) (by positivity)
    _ = (A * b * B) * Real.exp ((Real.pi * a) * ‖cuspFrequency h‖ +
        -(4 * Real.pi * ‖cuspFrequency h‖ * v) / 2) := by rw [Real.exp_add]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      have hm := mul_le_mul_of_nonneg_left hp.1
        (show 0 ≤ 2 * Real.pi * ‖cuspFrequency h‖ by positivity)
      nlinarith only [hm]

theorem cubicResidualNonzeroTerm_strip_bound (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : O) (p : ℝ × ℂ), p.1 ∈ Set.Icc a b →
      ‖cubicResidualNonzeroTerm h p‖ ≤ C * Real.exp (-(Real.pi * a) * ‖cuspFrequency h‖) := by
  obtain ⟨C, hC, hb⟩ := cubicBesselCoefficient_strip_bound cubicResidualFourierCoefficient
    cubicResidualFourierCoefficient_subexponential a b ha hab
  refine ⟨C, hC, ?_⟩
  intro h p hp
  by_cases hh : h = 0
  · simp only [cubicResidualNonzeroTerm, if_pos hh, norm_zero]
    positivity
  rw [show p = (p.1, p.2) from rfl, cubicResidualNonzeroTerm_bessel h hh _ (ha.trans_le hp.1),
    norm_mul, tracePhase_norm, mul_one]
  exact hb h hh p.1 hp

theorem cubicResidualNonzeroTerm_summable_norm (p : ℝ × ℂ) (hp : 0 < p.1) :
    Summable (fun h : O => ‖cubicResidualNonzeroTerm h p‖) := by
  obtain ⟨C, hC, hbound⟩ := cubicResidualNonzeroTerm_strip_bound p.1 p.1 hp le_rfl
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun h => hbound h p ⟨le_rfl, le_rfl⟩)
    ((summable_exp_neg_cuspFrequency_norm (Real.pi * p.1) (mul_pos Real.pi_pos hp)).mul_left C)

def cubicResidualNonzeroSeries (p : ℝ × ℂ) : ℂ := ∑' h : O, cubicResidualNonzeroTerm h p

lemma cubicResidualNonzeroSeries_continuousOn_strip (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn cubicResidualNonzeroSeries {p : ℝ × ℂ | p.1 ∈ Set.Icc a b} := by
  obtain ⟨C, hC, hbound⟩ := cubicResidualNonzeroTerm_strip_bound a b ha hab
  exact continuousOn_tsum
    (fun h => (cubicResidualNonzeroTerm_continuousOn h).mono (fun p hp => ha.trans_le hp.1))
    ((summable_exp_neg_cuspFrequency_norm (Real.pi * a) (mul_pos Real.pi_pos ha)).mul_left C)
    hbound

theorem cubicResidualNonzeroSeries_continuousOn :
    ContinuousOn cubicResidualNonzeroSeries {p : ℝ × ℂ | 0 < p.1} := by
  intro p hp
  change 0 < p.1 at hp
  have ha : 0 < p.1 / 2 := half_pos hp
  have hab : p.1 / 2 ≤ 2 * p.1 := by linarith only [hp]
  have hnhds : {q : ℝ × ℂ | q.1 ∈ Set.Icc (p.1 / 2) (2 * p.1)} ∈ 𝓝 p :=
    continuousAt_fst.preimage_mem_nhds (Icc_mem_nhds (by linarith only [hp]) (by linarith only [hp]))
  exact ((cubicResidualNonzeroSeries_continuousOn_strip _ _ ha hab).continuousAt hnhds).continuousWithinAt

/-- The Mellin transform of a bounded height weight on a positive compact
interval is entire; compactness bounds its logarithmic derivative. -/
def cuspIntervalMellin (a b : ℝ) (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) : ℂ :=
  ∫ v in Set.Icc a b, ρ v * (v : ℂ) ^ s

lemma cuspIntervalMellin_integrable (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) :
    IntegrableOn (fun v : ℝ => ρ v * (v : ℂ) ^ s) (Set.Icc a b) := by
  apply ContinuousOn.integrableOn_Icc
  apply ρ.continuous.continuousOn.mul
  intro v hv
  exact (Complex.continuousAt_ofReal_cpow_const v s (Or.inr (ha.trans_le hv.1).ne')).continuousWithinAt

theorem cuspIntervalMellin_differentiable (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) : Differentiable ℂ (cuspIntervalMellin a b ρ) := by
  let L : ℝ → ℂ := fun v => (Real.log (max a v) : ℂ)
  have hL : Continuous L := Complex.continuous_ofReal.comp
    ((continuous_const.max continuous_id).log (fun v => (ha.trans_le (le_max_left a v)).ne'))
  let F : ℂ → ℝ → ℂ := fun s v => ρ v * Complex.exp (L v * s)
  let D : ℂ → ℝ → ℂ := fun s v => ρ v * (Complex.exp (L v * s) * L v)
  have hF (s : ℂ) : Continuous (F s) := ρ.continuous.mul ((hL.mul_const s).cexp)
  have hD : Continuous (fun p : ℂ × ℝ => D p.1 p.2) :=
    (ρ.continuous.comp continuous_snd).mul
      ((((hL.comp continuous_snd).mul continuous_fst).cexp).mul (hL.comp continuous_snd))
  have hder (s : ℂ) (v : ℝ) : HasDerivAt (fun w => F w v) (D s v) s := by
    simpa only [F, D, id_eq, mul_one] using
      (((hasDerivAt_id s).const_mul (L v)).cexp).const_mul (ρ v)
  have heq : cuspIntervalMellin a b ρ = fun s => ∫ v in Set.Icc a b, F s v := by
    funext s
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    dsimp only [cuspIntervalMellin, F, L]
    rw [max_eq_right hv.1, Complex.ofReal_log (ha.trans_le hv.1).le,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ha.trans_le hv.1).ne')]
  rw [heq]
  intro s
  obtain ⟨C, hC⟩ := ((isCompact_closedBall s (1 : ℝ)).prod
    (isCompact_Icc : IsCompact (Set.Icc a b))).exists_bound_of_continuousOn hD.continuousOn
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := volume.restrict (Set.Icc a b)) (F := F) (F' := D) (bound := fun _ => C)
    (Metric.ball_mem_nhds s (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall (fun w => (hF w).aestronglyMeasurable))
    ((hF s).continuousOn.integrableOn_Icc)
    ((hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv w hw
      exact hC (w, v) ⟨Metric.ball_subset_closedBall hw, hv⟩)
    (integrable_const C) (Eventually.of_forall (fun v w _ => hder w v))
  exact hd.2.differentiableAt

lemma cuspIntervalMellin_analyticAt (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) :
    AnalyticAt ℂ (cuspIntervalMellin a b ρ) s :=
  (cuspIntervalMellin_differentiable a b ha ρ).analyticAt s

lemma kernelCuspIntervalFourierFamily_zero_initial (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (hs : 4 < s.re) (hi : 0 < s.im) :
    kernelCuspIntervalFourierFamily a b ha ρ 0 s =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) *
        (cuspIntervalMellin a b ρ (s - 3) +
          ((Real.pi : ℂ) / (s - 1)) * scatteringCoefficient s 0 * cuspIntervalMellin a b ρ (-s - 1)) := by
  let g : HyperbolicSpace → ℂ := fun w => hyperbolicEisenstein s w * cuspWeightedFourierPhase ρ 0 w
  have hg : Continuous g := (hyperbolicEisenstein_continuous s (by linarith)).mul
    (cuspWeightedFourierPhase_continuous ρ 0)
  rw [kernelCuspIntervalFourierFamily_initial a b ha ρ 0 s hs hi,
    cuspInterval_integral_coordinates a b ha g hg.aestronglyMeasurable
      (cuspInterval_continuous_integrable a b ha g hg)]
  have hpoint (v : ℝ) (hv : v ∈ Set.Icc a b) :
      (∫ z in periodDomain, g (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 =
        ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) *
          (ρ v * (v : ℂ) ^ (s - 3) + (((Real.pi : ℂ) / (s - 1)) * scatteringCoefficient s 0) *
            (ρ v * (v : ℂ) ^ (-s - 1))) := by
    have hpos := ha.trans_le hv.1
    have hinner : (∫ z in periodDomain, g (cuspCoordinateLift (v, z))) =
        ρ v * (eisensteinFourierCoefficient v hpos s 0 * ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ)) := by
      simp_rw [g, cuspCoordinateLift_positive v _ hpos, hyperbolicEisenstein_upperPoint,
        cuspWeightedFourierPhase, hyperbolicHeight_upperPoint, cuspFourierPhase, hyperbolicHorizontal_upperPoint]
      have he : (∫ z in periodDomain, upperEisenstein z v hpos s * (ρ v * tracePhase (-cuspFrequency 0 * z))) =
          ρ v * ∫ z in periodDomain, upperEisenstein z v hpos s * tracePhase (-cuspFrequency 0 * z) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by ring)
      rw [he, eisensteinFourierCoefficient]
      congr 1
      exact (div_mul_cancel₀ _ cusp_volume_ne_zero).symm
    rw [hinner, eisensteinConstantCoefficient_formula v hpos s (by linarith)]
    have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    have hout : (v : ℂ) ^ (-s - 1) = (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 := by
      rw [show -s - 1 = (2 - s) - 3 by ring, Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    have hin : (v : ℂ) ^ (s - 3) = (v : ℂ) ^ s / (v : ℂ) ^ 3 := by
      rw [Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    rw [hout, hin]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc hpoint, integral_const_mul,
    integral_add (cuspIntervalMellin_integrable a b ha ρ _)
      ((cuspIntervalMellin_integrable a b ha ρ _).const_mul _), integral_const_mul]
  rfl

/-- Subtract the entire incoming mode before comparing constant Fourier
coefficients at different heights. -/
def cuspIntervalOutgoingFamily (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) : ℂ :=
  kernelCuspIntervalFourierFamily a b ha ρ 0 s -
    ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * cuspIntervalMellin a b ρ (s - 3)

lemma cuspIntervalOutgoingFamily_analyticAt (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (hs : 1 < s.re) (hi : 0 < s.im) :
    AnalyticAt ℂ (cuspIntervalOutgoingFamily a b ha ρ) s :=
  (kernelCuspIntervalFourierFamily_analyticAt a b ha ρ 0 s hs hi).sub
    (analyticAt_const.mul ((cuspIntervalMellin_analyticAt a b ha ρ _).comp_of_eq
      (analyticAt_id.sub analyticAt_const) rfl))

theorem cuspIntervalOutgoingFamily_cross_identity (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (c d : ℝ) (hc : 0 < c)
    (η : BoundedContinuousFunction ℝ ℂ) :
    Set.EqOn
      (fun s => cuspIntervalOutgoingFamily a b ha ρ s * cuspIntervalMellin c d η (-s - 1))
      (fun s => cuspIntervalOutgoingFamily c d hc η s * cuspIntervalMellin a b ρ (-s - 1))
      {s : ℂ | 1 < s.re ∧ 0 < s.im} := by
  have hconvex : Convex ℝ {s : ℂ | 1 < s.re ∧ 0 < s.im} :=
    ((convex_Ioi (1 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hl : AnalyticOnNhd ℂ
      (fun s => cuspIntervalOutgoingFamily a b ha ρ s * cuspIntervalMellin c d η (-s - 1))
      {s : ℂ | 1 < s.re ∧ 0 < s.im} := fun s hs =>
    (cuspIntervalOutgoingFamily_analyticAt a b ha ρ s hs.1 hs.2).mul
      ((cuspIntervalMellin_analyticAt c d hc η _).comp_of_eq (analyticAt_id.neg.sub analyticAt_const) rfl)
  have hr : AnalyticOnNhd ℂ
      (fun s => cuspIntervalOutgoingFamily c d hc η s * cuspIntervalMellin a b ρ (-s - 1))
      {s : ℂ | 1 < s.re ∧ 0 < s.im} := fun s hs =>
    (cuspIntervalOutgoingFamily_analyticAt c d hc η s hs.1 hs.2).mul
      ((cuspIntervalMellin_analyticAt a b ha ρ _).comp_of_eq (analyticAt_id.neg.sub analyticAt_const) rfl)
  apply hl.eqOn_of_preconnected_of_eventuallyEq hr hconvex.isPreconnected
    (show (5 + Complex.I : ℂ) ∈ {s : ℂ | 1 < s.re ∧ 0 < s.im} by norm_num)
  have hopen : IsOpen {s : ℂ | 4 < s.re ∧ 0 < s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  filter_upwards [hopen.mem_nhds (by norm_num : (5 + Complex.I : ℂ) ∈
    {s : ℂ | 4 < s.re ∧ 0 < s.im})] with s hs
  simp only [cuspIntervalOutgoingFamily,
    kernelCuspIntervalFourierFamily_zero_initial a b ha ρ s hs.1 hs.2,
    kernelCuspIntervalFourierFamily_zero_initial c d hc η s hs.1 hs.2]
  ring

lemma cuspIntervalOutgoingFamily_residue_limit (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) :
    Tendsto (fun s : ℂ => (s - 4 / 3) * cuspIntervalOutgoingFamily a b ha ρ s)
      (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (kernelCuspIntervalFourier a b ha ρ 0 cubicEisensteinResidue)) := by
  have hlin : Tendsto (fun s : ℂ => s - 4 / 3) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa only [id_eq, sub_self] using (tendsto_id.sub_const (4 / 3 : ℂ)).mono_left
      (show 𝓝[≠] (4 / 3 : ℂ) ≤ 𝓝 (4 / 3 : ℂ) from nhdsWithin_le_nhds)
  have hcont : ContinuousAt (fun s : ℂ => ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) *
      cuspIntervalMellin a b ρ (s - 3)) (4 / 3) := continuousAt_const.mul
    ((cuspIntervalMellin_differentiable a b ha ρ).continuous.continuousAt.comp (continuousAt_id.sub_const 3))
  have hz := hlin.mul (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [cuspIntervalOutgoingFamily, mul_sub, zero_mul, sub_zero] using
    (kernelCuspIntervalFourierFamily_residue_limit a b ha ρ 0).sub hz

/-- The constant residual mode is fixed by the arithmetic constant-term
residue, for every bounded height weight and every positive height strip. -/
theorem kernelCuspIntervalFourier_zero_residue (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) :
    kernelCuspIntervalFourier a b ha ρ 0 cubicEisensteinResidue =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * (3 * (Real.pi : ℂ)) * constantArithmeticResidue *
        cuspIntervalMellin a b ρ (-(4 / 3 : ℂ) - 1) := by
  let η := BoundedContinuousFunction.const ℝ (1 : ℂ)
  have hmellin : cuspIntervalMellin 5 6 η (-(4 / 3 : ℂ) - 1) =
      cuspScatterHeightFactor (4 / 3) := by
    simp only [cuspIntervalMellin, η, BoundedContinuousFunction.const_apply, one_mul]
    exact cuspScatterHeightFactor_integral (4 / 3) (by norm_num)
  have havg : kernelCuspIntervalFourier 5 6 (by norm_num) η 0 cubicEisensteinResidue =
      cuspConstantAverageResidue := by
    rw [← cubicEisensteinResidue_cusp_average, kernelCuspIntervalFourier_integral,
      kernelCuspStripAverage_hyperbolic]
    simp only [cuspWeightedFourierPhase, η, BoundedContinuousFunction.const_apply,
      cuspFourierPhase, cuspFrequency, map_zero, zero_div, neg_zero, zero_mul,
      AddChar.map_zero_eq_one, mul_one]
  have hweight (c d : ℝ) (hc : 0 < c) (ξ : BoundedContinuousFunction ℝ ℂ) :
      Tendsto (fun s : ℂ => cuspIntervalMellin c d ξ (-s - 1)) (𝓝[≠] (4 / 3 : ℂ))
        (𝓝 (cuspIntervalMellin c d ξ (-(4 / 3 : ℂ) - 1))) :=
    ((cuspIntervalMellin_differentiable c d hc ξ).continuous.continuousAt.comp
      (continuousAt_id.neg.sub_const 1)).tendsto.mono_left nhdsWithin_le_nhds
  have hl := ((cuspIntervalOutgoingFamily_residue_limit a b ha ρ).mul
    (hweight 5 6 (by norm_num) η)).comp thetaApproach_tendsto_complex_punctured
  have hr := ((cuspIntervalOutgoingFamily_residue_limit 5 6 (by norm_num) η).mul
    (hweight a b ha ρ)).comp thetaApproach_tendsto_complex_punctured
  have hevent :
      (fun t : ℝ => (((4 / 3 : ℂ) + t + t * Complex.I - 4 / 3) *
        cuspIntervalOutgoingFamily a b ha ρ ((4 / 3 : ℂ) + t + t * Complex.I)) *
          cuspIntervalMellin 5 6 η (-((4 / 3 : ℂ) + t + t * Complex.I) - 1))
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => (((4 / 3 : ℂ) + t + t * Complex.I - 4 / 3) *
        cuspIntervalOutgoingFamily 5 6 (by norm_num) η ((4 / 3 : ℂ) + t + t * Complex.I)) *
          cuspIntervalMellin a b ρ (-((4 / 3 : ℂ) + t + t * Complex.I) - 1)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    have hs : (4 / 3 : ℂ) + t + t * Complex.I ∈ {s : ℂ | 1 < s.re ∧ 0 < s.im} := by
      constructor
      · norm_num
        linarith
      · simpa using ht
    simpa only [mul_assoc] using congrArg
      (fun z : ℂ => ((4 / 3 : ℂ) + t + t * Complex.I - 4 / 3) * z)
      (cuspIntervalOutgoingFamily_cross_identity a b ha ρ 5 6 (by norm_num) η hs)
  have heq : kernelCuspIntervalFourier a b ha ρ 0 cubicEisensteinResidue *
      cuspIntervalMellin 5 6 η (-(4 / 3 : ℂ) - 1) =
      kernelCuspIntervalFourier 5 6 (by norm_num) η 0 cubicEisensteinResidue *
        cuspIntervalMellin a b ρ (-(4 / 3 : ℂ) - 1) :=
    tendsto_nhds_unique_of_eventuallyEq hl hr hevent
  rw [hmellin, havg] at heq
  have hne : cuspScatterHeightFactor (4 / 3 : ℂ) ≠ 0 := by
    intro he
    have hpos := cuspScatterHeightFactor_center_re_pos
    rw [he, Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  apply mul_right_cancel₀ hne
  rw [heq, cuspConstantAverageResidue]
  ring

def cubicResidualFullModeAmplitude (v : ℝ) (h : O) : ℂ :=
  if h = 0 then (3 * (Real.pi : ℂ)) * constantArithmeticResidue * (v : ℂ) ^ (2 / 3 : ℂ)
  else cubicResidualFourierCoefficient h * (v : ℂ) *
    schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v)

lemma cubicResidualFullModeAmplitude_zero_density (v : ℝ) (hv : 0 < v) :
    cubicResidualFullModeAmplitude v 0 / (v : ℂ) ^ 3 =
      (3 * (Real.pi : ℂ)) * constantArithmeticResidue * (v : ℂ) ^ (-(4 / 3 : ℂ) - 1) := by
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hp : (v : ℂ) ^ (-(4 / 3 : ℂ) - 1) = (v : ℂ) ^ (2 / 3 : ℂ) / (v : ℂ) ^ 3 := by
    rw [show -(4 / 3 : ℂ) - 1 = (2 / 3 : ℂ) - 3 by ring, Complex.cpow_sub _ _ hv0]
    congr 1
    exact Complex.cpow_natCast _ 3
  rw [cubicResidualFullModeAmplitude, if_pos rfl, hp]
  ring

lemma cubicResidualFullModeAmplitude_nonzero_density (v : ℝ) (hv : 0 < v) (h : O) (hh : h ≠ 0) :
    cubicResidualFullModeAmplitude v h / (v : ℂ) ^ 3 = cubicResidualFourierCoefficient h *
      (schlafliBesselK (1 / 3) (4 * Real.pi * ‖cuspFrequency h‖ * v) / (v : ℂ) ^ 2) := by
  rw [cubicResidualFullModeAmplitude, if_neg hh]
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp

theorem kernelCuspIntervalFourier_residue_full (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) :
    kernelCuspIntervalFourier a b ha ρ h cubicEisensteinResidue =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) *
        ∫ v in Set.Icc a b, ρ v * (cubicResidualFullModeAmplitude v h / (v : ℂ) ^ 3) := by
  by_cases hh : h = 0
  · subst h
    rw [kernelCuspIntervalFourier_zero_residue a b ha ρ, ← mul_assoc,
      cuspIntervalMellin, ← integral_const_mul, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    dsimp only
    rw [cubicResidualFullModeAmplitude_zero_density v (ha.trans_le hv.1)]
    ring
  · rw [kernelCuspIntervalFourier_residue_bessel a b ha ρ h hh,
      ← integral_const_mul, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    dsimp only
    rw [cubicResidualFullModeAmplitude_nonzero_density v (ha.trans_le hv.1) h hh]
    ring

def cubicResidualNonzeroAmplitude (v : ℝ) (h : O) : ℂ :=
  if h = 0 then 0 else cubicResidualFullModeAmplitude v h

lemma cubicResidualNonzeroTerm_eq_amplitude (v : ℝ) (hv : 0 < v) (h : O) (z : ℂ) :
    cubicResidualNonzeroTerm h (v, z) = cubicResidualNonzeroAmplitude v h * tracePhase (cuspFrequency h * z) := by
  by_cases hh : h = 0
  · simp only [cubicResidualNonzeroTerm, cubicResidualNonzeroAmplitude, if_pos hh, zero_mul]
  · rw [cubicResidualNonzeroTerm_bessel h hh v hv z, cubicResidualNonzeroAmplitude,
      if_neg hh, cubicResidualFullModeAmplitude, if_neg hh]

lemma integral_cusp_character_product (h k : O) :
    (∫ z in periodDomain, tracePhase (cuspFrequency h * z) * tracePhase (-cuspFrequency k * z)) =
      if h = k then ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) else 0 := by
  have hphase (z : ℂ) : tracePhase (cuspFrequency h * z) * tracePhase (-cuspFrequency k * z) =
      tracePhase (-cuspFrequency (k - h) * z) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    unfold cuspFrequency
    rw [map_sub]
    ring
  simp_rw [hphase]
  simpa only [sub_eq_zero, eq_comm] using integral_cusp_character (k - h)

/-- Normal convergence permits coefficient extraction term by term. -/
theorem cubicResidualNonzeroSeries_fourier (v : ℝ) (hv : 0 < v) (k : O) :
    (∫ z in periodDomain, cubicResidualNonzeroSeries (v, z) * tracePhase (-cuspFrequency k * z)) =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * cubicResidualNonzeroAmplitude v k := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  letI : IsFiniteMeasure (volume.restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  let f : O → ℂ → ℂ := fun h z => cubicResidualNonzeroAmplitude v h *
    tracePhase (cuspFrequency h * z) * tracePhase (-cuspFrequency k * z)
  have hc (h : O) : Continuous (f h) := by
    change Continuous (fun z : ℂ => cubicResidualNonzeroAmplitude v h *
      Complex.exp (2 * Real.pi * Complex.I * ((cuspFrequency h * z) + starRingEnd ℂ (cuspFrequency h * z))) *
      Complex.exp (2 * Real.pi * Complex.I * ((-cuspFrequency k * z) + starRingEnd ℂ (-cuspFrequency k * z))))
    fun_prop
  obtain ⟨C, hC, hbound⟩ := cubicResidualNonzeroTerm_strip_bound v v hv le_rfl
  have hb (h : O) (z : ℂ) : ‖f h z‖ ≤ C * Real.exp (-(Real.pi * v) * ‖cuspFrequency h‖) := by
    dsimp only [f]
    rw [← cubicResidualNonzeroTerm_eq_amplitude v hv h z, norm_mul, tracePhase_norm, mul_one]
    exact hbound h (v, z) ⟨le_rfl, le_rfl⟩
  have hi (h : O) : IntegrableOn (f h) periodDomain :=
    (integrable_const (C * Real.exp (-(Real.pi * v) * ‖cuspFrequency h‖))).mono'
      (hc h).aestronglyMeasurable (Eventually.of_forall (hb h))
  have hnorm (h : O) : (∫ z in periodDomain, ‖f h z‖) ≤
      volume.real periodDomain * (C * Real.exp (-(Real.pi * v) * ‖cuspFrequency h‖)) := by
    simpa only [setIntegral_const, smul_eq_mul] using
      integral_mono_ae (hi h).norm (integrable_const (C * Real.exp (-(Real.pi * v) * ‖cuspFrequency h‖)))
        (Eventually.of_forall (hb h))
  have hsum : Summable (fun h : O => ∫ z in periodDomain, ‖f h z‖) :=
    Summable.of_nonneg_of_le (fun h => integral_nonneg (fun z => norm_nonneg _)) hnorm
      (((summable_exp_neg_cuspFrequency_norm (Real.pi * v) (mul_pos Real.pi_pos hv)).mul_left C).mul_left
        (volume.real periodDomain))
  have hterm (h : O) : (∫ z in periodDomain, f h z) =
      if h = k then ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * cubicResidualNonzeroAmplitude v h else 0 := by
    dsimp only [f]
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_cusp_character_product]
    split_ifs <;> ring
  calc
    _ = ∫ z in periodDomain, ∑' h : O, f h z := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        change (∑' h : O, cubicResidualNonzeroTerm h (v, z)) * tracePhase (-cuspFrequency k * z) = _
        rw [← tsum_mul_right]
        exact tsum_congr (fun h => by rw [cubicResidualNonzeroTerm_eq_amplitude v hv h z]))
    _ = ∑' h : O, ∫ z in periodDomain, f h z := (integral_tsum_of_summable_integral_norm hi hsum).symm
    _ = ∑' h : O, if h = k then ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * cubicResidualNonzeroAmplitude v h else 0 :=
      tsum_congr hterm
    _ = _ := by simp

/-- The continuous Fourier reconstruction with its arithmetic constant mode. -/
def cubicResidualFunction (w : HyperbolicSpace) : ℂ :=
  (3 * (Real.pi : ℂ)) * constantArithmeticResidue * (hyperbolicHeight w : ℂ) ^ (2 / 3 : ℂ) +
    cubicResidualNonzeroSeries (hyperbolicHeight w, hyperbolicHorizontal w)

theorem cubicResidualFunction_continuous : Continuous cubicResidualFunction := by
  apply continuous_iff_continuousAt.mpr
  intro w
  have hpower := (Complex.continuousAt_ofReal_cpow_const (hyperbolicHeight w) (2 / 3 : ℂ)
    (Or.inr (hyperbolicHeight_pos w).ne')).comp hyperbolicHeight_continuous.continuousAt
  have hseries := (cubicResidualNonzeroSeries_continuousOn.continuousAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds (hyperbolicHeight_pos w))).comp
      (hyperbolicHeight_continuous.continuousAt.prodMk hyperbolicHorizontal_continuous.continuousAt)
  exact (continuousAt_const.mul hpower).add hseries

lemma periodDomain_continuous_integrable (f : ℂ → ℂ) (hf : Continuous f) :
    IntegrableOn f periodDomain := by
  apply (hf.continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : ℂ) (∑ i, ‖periodBasis i‖))).mono_set
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using norm_mem_periodDomain z hz

lemma cubicResidualNonzeroSeries_height_continuous (v : ℝ) (hv : 0 < v) :
    Continuous (fun z : ℂ => cubicResidualNonzeroSeries (v, z)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (cubicResidualNonzeroSeries_continuousOn.continuousAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds hv)).comp
      (f := fun z : ℂ => (v, z)) (by fun_prop)

theorem cubicResidualFunction_fourier (v : ℝ) (hv : 0 < v) (k : O) :
    (∫ z in periodDomain, cubicResidualFunction (upperPoint z v hv) * tracePhase (-cuspFrequency k * z)) =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * cubicResidualFullModeAmplitude v k := by
  have hphase : Continuous (fun z : ℂ => tracePhase (-cuspFrequency k * z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2 * Real.pi * Complex.I *
      ((-cuspFrequency k * z) + starRingEnd ℂ (-cuspFrequency k * z))))
    fun_prop
  simp only [cubicResidualFunction, hyperbolicHeight_upperPoint, hyperbolicHorizontal_upperPoint, add_mul]
  have hconstant : IntegrableOn (fun z : ℂ =>
      3 * (Real.pi : ℂ) * constantArithmeticResidue * (v : ℂ) ^ (2 / 3 : ℂ) *
        tracePhase (-cuspFrequency k * z)) periodDomain :=
    periodDomain_continuous_integrable _ (continuous_const.mul hphase)
  have hseries : IntegrableOn (fun z : ℂ =>
      cubicResidualNonzeroSeries (v, z) * tracePhase (-cuspFrequency k * z)) periodDomain := by
    simpa only [Pi.mul_def] using periodDomain_continuous_integrable _
      ((cubicResidualNonzeroSeries_height_continuous v hv).mul hphase)
  rw [integral_add hconstant hseries,
    integral_const_mul, integral_cusp_character, cubicResidualNonzeroSeries_fourier v hv k]
  by_cases hk : k = 0
  · simp only [hk, cubicResidualNonzeroAmplitude, cubicResidualFullModeAmplitude,
      ite_true, mul_zero, add_zero]
    ring
  · simp only [if_neg hk, cubicResidualNonzeroAmplitude, mul_zero, zero_add]

theorem cubicResidualFunction_weightedFourier (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) :
    (∫ w in cuspPeriodStrip a b, cubicResidualFunction w * cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume) =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) *
        ∫ v in Set.Icc a b, ρ v * (cubicResidualFullModeAmplitude v h / (v : ℂ) ^ 3) := by
  let g : HyperbolicSpace → ℂ := fun w => cubicResidualFunction w * cuspWeightedFourierPhase ρ h w
  have hg : Continuous g := cubicResidualFunction_continuous.mul (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspInterval_integral_coordinates a b ha g hg.aestronglyMeasurable
    (cuspInterval_continuous_integrable a b ha g hg), ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hvp := ha.trans_le hv.1
  dsimp only
  simp_rw [g, cuspCoordinateLift_positive v _ hvp, cuspWeightedFourierPhase,
    hyperbolicHeight_upperPoint, cuspFourierPhase, hyperbolicHorizontal_upperPoint]
  have hinner : (∫ z in periodDomain, cubicResidualFunction (upperPoint z v hvp) *
      (ρ v * tracePhase (-cuspFrequency h * z))) =
      ρ v * ∫ z in periodDomain, cubicResidualFunction (upperPoint z v hvp) * tracePhase (-cuspFrequency h * z) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by ring)
  rw [hinner, cubicResidualFunction_fourier v hvp h]
  ring

theorem cubicEisensteinResidue_weightedFourier_eq (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) :
    kernelCuspIntervalFourier a b ha ρ h cubicEisensteinResidue =
      ∫ w in cuspPeriodStrip a b, cubicResidualFunction w * cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume := by
  rw [kernelCuspIntervalFourier_residue_full, cubicResidualFunction_weightedFourier a b ha]

lemma kernelCuspCoordinates_memLp (a b : ℝ) (ha : 0 < a) (F : KernelQuotientL2) :
    MemLp (fun q : ℝ × ℂ => F (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift q))) 2
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict periodDomain)) := by
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
  have hF := (MemLp.ae_eq (kernelCuspIntervalPullback_ae a b ha F)
    (MeasureTheory.Lp.memLp (kernelCuspIntervalPullback a b ha F))).comp_measurePreserving hm
  have hvol := euclideanVolume_le_heightCube_hyperbolic S hS hpos (max 1 b) (by positivity)
    (fun p hp => hp.1.2.trans (le_max_right 1 b))
  have hFE := (hF.smul_measure (c := ENNReal.ofReal ((max 1 b) ^ 3)) ENNReal.ofReal_ne_top).mono_measure hvol
  have hsplit := spatialComplexSplit_preserves_volume.restrict_preimage
    (s := Set.Icc a b ×ˢ periodDomain) (measurableSet_Icc.prod periodDomain_measurable)
  have hpull := hFE.comp_measurePreserving hsplit.symm
  simpa only [Measure.prod_restrict, Measure.volume_eq_prod, Function.comp_def, S, cuspCoordinateLift] using hpull

lemma kernelCuspSections_memLp (a b : ℝ) (ha : 0 < a) (F : KernelQuotientL2) :
    ∀ᵐ v ∂volume.restrict (Set.Icc a b),
      MemLp (fun z : ℂ => F (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v, z)))) 2
        (volume.restrict periodDomain) := by
  have hf := kernelCuspCoordinates_memLp a b ha F
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, hf.norm.integrable_sq.prod_right_ae] with v hv hi
  exact (memLp_two_iff_integrable_sq_norm hv).mpr hi

lemma kernelCuspFourierCoordinate_integrable (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (F : KernelQuotientL2) :
    IntegrableOn (fun q : ℝ × ℂ =>
      (F (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift q)) *
        cuspWeightedFourierPhase ρ h (cuspCoordinateLift q)) / (q.1 : ℂ) ^ 3)
      (Set.Icc a b ×ˢ periodDomain) := by
  letI : IsFiniteMeasure (volume.restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  have hF := (kernelCuspCoordinates_memLp a b ha F).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcoord : Measurable cuspCoordinateLift :=
    euclideanToHyperbolic_measurable.comp spatialComplexSplit.symm.measurable
  have hm : Measurable (fun q : ℝ × ℂ =>
      cuspWeightedFourierPhase ρ h (cuspCoordinateLift q) / (q.1 : ℂ) ^ 3) :=
    ((cuspWeightedFourierPhase_continuous ρ h).measurable.comp hcoord).div (by fun_prop)
  have hb : ∀ᵐ q ∂((volume.restrict (Set.Icc a b)).prod (volume.restrict periodDomain)),
      ‖cuspWeightedFourierPhase ρ h (cuspCoordinateLift q) / (q.1 : ℂ) ^ 3‖ ≤ ‖ρ‖ / a ^ 3 := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod periodDomain_measurable)] with q hq
    have hpos : 0 < q.1 := ha.trans_le hq.1.1
    rw [norm_div, norm_pow, Complex.norm_of_nonneg hpos.le]
    exact (div_le_div_of_nonneg_right (cuspWeightedFourierPhase_bound ρ h (cuspCoordinateLift q))
      (by positivity)).trans (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        (pow_le_pow_left₀ ha.le hq.1.1 3))
  simpa only [IntegrableOn, Measure.prod_restrict, ← Measure.volume_eq_prod, mul_div_assoc] using
    hF.mul_bdd hm.aestronglyMeasurable hb

/-- The slice coefficient includes the hyperbolic height density. -/
def kernelCuspSliceCoefficient (F : KernelQuotientL2) (h : O) (v : ℝ) : ℂ :=
  (∫ z in periodDomain, F (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v, z))) *
    tracePhase (-cuspFrequency h * z)) / (v : ℂ) ^ 3

lemma kernelCuspIntervalFourier_eq_slice_integral (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (F : KernelQuotientL2) :
    kernelCuspIntervalFourier a b ha ρ h F =
      ∫ v in Set.Icc a b, ρ v * kernelCuspSliceCoefficient F h v := by
  rw [kernelCuspIntervalFourier_integral]
  have hg : StronglyMeasurable (fun w =>
      F (integralOrbitProjection globalKubotaKernel w) * cuspWeightedFourierPhase ρ h w) :=
    ((MeasureTheory.Lp.stronglyMeasurable F).comp_measurable (measurable_integralOrbitProjection _)).mul
      (cuspWeightedFourierPhase_continuous ρ h).stronglyMeasurable
  rw [cuspInterval_integral_coordinates a b ha _ hg.aestronglyMeasurable
    (kernelCuspFourierCoordinate_integrable a b ha ρ h F)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos := ha.trans_le hv.1
  simp only [kernelCuspSliceCoefficient]
  rw [← mul_div_assoc]
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [cuspWeightedFourierPhase, cuspFourierPhase, cuspCoordinateLift_positive v z hpos,
      hyperbolicHeight_upperPoint, hyperbolicHorizontal_upperPoint]
    ring)

lemma kernelCuspSliceCoefficient_integrable (a b : ℝ) (ha : 0 < a)
    (h : O) (F : KernelQuotientL2) :
    IntegrableOn (kernelCuspSliceCoefficient F h) (Set.Icc a b) := by
  have hi := kernelCuspFourierCoordinate_integrable a b ha (BoundedContinuousFunction.const ℝ 1) h F
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
  apply hi.integral_prod_left.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hpos := ha.trans_le hv.1
  rw [integral_div, kernelCuspSliceCoefficient]
  apply congrArg (fun c : ℂ => c / (v : ℂ) ^ 3)
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [cuspWeightedFourierPhase, cuspFourierPhase, cuspCoordinateLift_positive v z hpos,
      hyperbolicHeight_upperPoint, hyperbolicHorizontal_upperPoint]
    simp only [BoundedContinuousFunction.const_apply, one_mul])

lemma interval_ae_eq_of_boundedContinuous_tests (a b : ℝ) (f g : ℝ → ℂ)
    (hf : IntegrableOn f (Set.Icc a b)) (hg : IntegrableOn g (Set.Icc a b))
    (heq : ∀ ρ : BoundedContinuousFunction ℝ ℂ,
      (∫ v in Set.Icc a b, ρ v * f v) = ∫ v in Set.Icc a b, ρ v * g v) :
    f =ᵐ[volume.restrict (Set.Icc a b)] g := by
  apply ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable hg.locallyIntegrable
  intro test htest hsupp
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous htest.continuous
  let ρ : BoundedContinuousFunction ℝ ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun v => (test v : ℂ))
      (Complex.continuous_ofReal.comp htest.continuous) C (fun v => by
        simpa only [Complex.norm_real, Real.norm_eq_abs] using hC v)
  have hh := heq ρ
  change (∫ v in Set.Icc a b, (test v : ℂ) * f v) = ∫ v in Set.Icc a b, (test v : ℂ) * g v at hh
  simpa only [Complex.real_smul] using hh

lemma cubicResidualFullMode_density_integrable (a b : ℝ) (ha : 0 < a) (h : O) :
    IntegrableOn (fun v : ℝ => cubicResidualFullModeAmplitude v h / (v : ℂ) ^ 3) (Set.Icc a b) := by
  by_cases hh : h = 0
  · subst h
    have hi : IntegrableOn (fun v : ℝ => (3 * (Real.pi : ℂ)) * constantArithmeticResidue *
        (v : ℂ) ^ (-(4 / 3 : ℂ) - 1)) (Set.Icc a b) := by
      apply ContinuousOn.integrableOn_Icc
      intro v hv
      exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const v _
        (Or.inr (ha.trans_le hv.1).ne'))).continuousWithinAt
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (cubicResidualFullModeAmplitude_zero_density v (ha.trans_le hv.1)).symm
  · apply ((cubicResidualBesselDensity_integrable a b ha h hh).const_mul
      (cubicResidualFourierCoefficient h)).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (cubicResidualFullModeAmplitude_nonzero_density v (ha.trans_le hv.1) h hh).symm

theorem cubicEisensteinResidue_slice_coefficient_ae (a b : ℝ) (ha : 0 < a) (h : O) :
    kernelCuspSliceCoefficient cubicEisensteinResidue h =ᵐ[volume.restrict (Set.Icc a b)]
      (fun v => ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * (cubicResidualFullModeAmplitude v h / (v : ℂ) ^ 3)) := by
  apply interval_ae_eq_of_boundedContinuous_tests a b _ _
    (kernelCuspSliceCoefficient_integrable a b ha h cubicEisensteinResidue)
    ((cubicResidualFullMode_density_integrable a b ha h).const_mul _)
  intro ρ
  rw [← kernelCuspIntervalFourier_eq_slice_integral a b ha ρ h cubicEisensteinResidue,
    kernelCuspIntervalFourier_residue_full, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => by ring)

theorem cubicEisensteinResidue_all_fourier_integrals_ae (a b : ℝ) (ha : 0 < a) :
    ∀ᵐ v ∂volume.restrict (Set.Icc a b), ∀ h : O,
      (∫ z in periodDomain, cubicEisensteinResidue
        (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v, z))) * tracePhase (-cuspFrequency h * z)) =
        ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * cubicResidualFullModeAmplitude v h := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  have hall := ae_all_iff.mpr (fun h => cubicEisensteinResidue_slice_coefficient_ae a b ha h)
  filter_upwards [hall, ae_restrict_mem measurableSet_Icc] with v hv hvmem
  intro h
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ha.trans_le hvmem.1).ne'
  have he := hv h
  unfold kernelCuspSliceCoefficient at he
  rw [← mul_div_assoc] at he
  exact (div_left_inj' (pow_ne_zero 3 hv0)).mp he

open scoped NNReal Pointwise

/-- Real coordinates for the cusp lattice and its dual characters. -/
def periodVector : (Fin 2 → ℝ) ≃L[ℝ] ℂ := periodBasis.equivFunL.symm

def periodTorus (z : ℂ) : UnitAddTorus (Fin 2) :=
  fun i => (periodBasis.equivFunL z i : UnitAddCircle)

def periodFrequencyEquiv : (Fin 2 → ℤ) ≃ O :=
  (finTwoArrowEquiv ℤ).trans
    (({ toFun := fun z => (z.1 + z.2, z.1)
        invFun := fun z => (z.2, z.1 - z.2)
        left_inv := by rintro ⟨k, l⟩; simp
        right_inv := by rintro ⟨k, l⟩; simp } : (ℤ × ℤ) ≃ (ℤ × ℤ)).trans
      Coordinates.coordinateEquiv.symm)

lemma periodVector_apply (x : Fin 2 → ℝ) :
    periodVector x = 3 * ((x 0 : ℂ) + (x 1 : ℂ) * ringComplex omega) := by
  change periodBasis.equivFun.symm x = _
  rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, periodBasis_zero, periodBasis_one]
  simp only [Complex.real_smul]
  ring

lemma periodTorus_periodVector (x : Fin 2 → ℝ) :
    periodTorus (periodVector x) = fun i => (x i : UnitAddCircle) := by
  change (fun i => ((periodBasis.equivFunL (periodBasis.equivFunL.symm x)) i : UnitAddCircle)) = _
  rw [periodBasis.equivFunL.apply_symm_apply]

lemma periodVector_character (n : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    tracePhase (cuspFrequency (periodFrequencyEquiv n) * periodVector x) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((n 0 : ℂ) * (x 0 : ℂ) + (n 1 : ℂ) * (x 1 : ℂ))) := by
  have hd : ringComplex traceLambda ≠ 0 := ringComplex_ne_zero traceLambda_ne_zero
  have harg : cuspFrequency (periodFrequencyEquiv n) * periodVector x =
      (((n 0 + n 1 : ℤ) : ℂ) + (n 0 : ℂ) * ringComplex omega) *
        ((x 0 : ℂ) + (x 1 : ℂ) * ringComplex omega) / ringComplex traceLambda := by
    change cuspFrequency (Coordinates.eval (n 0 + n 1) (n 0)) * periodVector x = _
    rw [cuspFrequency, periodVector_apply, ringComplex_eval]
    field_simp
  rw [harg]
  change Complex.exp (2 * Real.pi * Complex.I * (_ + starRingEnd ℂ _)) = _
  congr 1
  rw [map_div₀, complex_traceLambda_conjugate]
  simp only [map_add, map_mul, map_intCast, Complex.conj_ofReal, complex_omega_conjugate]
  field_simp [hd]
  simp only [traceLambda, map_add, map_mul, map_one, map_ofNat]
  push_cast
  ring

lemma periodTorus_mFourier (n : Fin 2 → ℤ) (z : ℂ) :
    UnitAddTorus.mFourier n (periodTorus z) =
      tracePhase (cuspFrequency (periodFrequencyEquiv n) * z) := by
  obtain ⟨x, rfl⟩ := periodVector.surjective z
  rw [periodTorus_periodVector, periodVector_character]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two,
    fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_add]
  congr 1
  ring

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
