/-
Cubic Fourier tests adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicResidualCharacter
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicWhittakerAverages
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicFourierBesselKernel

/-!
# Bounded Fourier tests of the actual cubic residual family

Restriction to an injective compact cusp strip followed by horizontal
Fourier pairing defines a bounded linear functional on quotient `L²`.
It transports the meromorphic family and residue limit. Initial source
matching identifies its nonzero modes with the scattering coefficient
times the explicit Whittaker height average.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified

lemma arithmeticDirichletTerm_differentiable (h : O) (c : LevelLower) :
    Differentiable ℂ (fun s : ℂ => arithmeticDirichletTerm s h c) := by
  by_cases hc : c.1=0
  · simp only [arithmeticDirichletTerm,if_pos hc]
    exact differentiable_const _
  · have hq : ((‖ringComplex c.1‖^2:ℝ):ℂ)≠0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (ringComplex_ne_zero hc)))
    simp only [arithmeticDirichletTerm,if_neg hc]
    exact (differentiable_id.neg.const_cpow (Or.inl hq)).mul_const _

lemma arithmeticDirichletTerm_norm_mono (h : O)
    (a : ℝ) (s : ℂ) (ha : a≤ s.re) (c : LevelLower) :
    ‖arithmeticDirichletTerm s h c‖≤‖arithmeticDirichletTerm (a:ℂ) h c‖ := by
  by_cases hc : c.1=0
  · simp only [arithmeticDirichletTerm,if_pos hc,norm_zero,le_refl]
  · have hpos : 0<‖ringComplex c.1‖^2 := sq_pos_of_pos
      (norm_pos_iff.mpr (ringComplex_ne_zero hc))
    have hq : 1≤‖ringComplex c.1‖^2 := by
      rw [ringComplex_norm_sq_eq_absNorm_span]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
    simp only [arithmeticDirichletTerm,if_neg hc,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos,Complex.neg_re,Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg ha))
      (norm_nonneg _)

theorem arithmeticDirichletSeries_differentiableAt (h : O)
    (s : ℂ) (hs : 2<s.re) :
    DifferentiableAt ℂ (fun z => arithmeticDirichletSeries z h) s := by
  let a : ℝ := (2+s.re)/2
  have ha : 2<a := by dsimp [a]; linarith
  have has : a<s.re := by dsimp [a]; linarith
  have hsum := arithmeticDirichletTerm_summable_norm (a:ℂ) (by simpa using ha) h
  have hopen : IsOpen {z : ℂ | a<z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun z => arithmeticDirichletSeries z h) {z : ℂ | a<z.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun c => (arithmeticDirichletTerm_differentiable h c).differentiableOn) hopen
    intro c z hz
    exact arithmeticDirichletTerm_norm_mono h a z hz.le c
  exact (hd s has).differentiableAt (hopen.mem_nhds has)

theorem scatteringCoefficient_differentiableAt (h : O)
    (s : ℂ) (hs : 2<s.re) :
    DifferentiableAt ℂ (fun z => scatteringCoefficient z h) s :=
  (arithmeticDirichletSeries_differentiableAt h s hs).div_const _

theorem scatteringCoefficient_analyticOnNhd (h : O) :
    AnalyticOnNhd ℂ (fun z => scatteringCoefficient z h) {z : ℂ | 2<z.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (scatteringCoefficient_differentiableAt h z hz).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re


lemma cuspPeriodStrip_measure_ne_top : hyperbolicVolume (cuspPeriodStrip 5 6)≠(⊤:ℝ≥0∞) := by
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hh := hm.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
  simp only [Set.preimage_univ,Measure.restrict_apply_univ] at hh
  rw [hh]
  exact measure_ne_top _ _

instance cubicFourierStripFiniteVolume : IsFiniteMeasure (hyperbolicVolume.restrict (cuspPeriodStrip 5 6)) :=
  isFiniteMeasure_restrict.mpr cuspPeriodStrip_measure_ne_top

abbrev CuspStripL2 := Lp ℂ 2 (hyperbolicVolume.restrict (cuspPeriodStrip 5 6))

def kernelCuspPullback : KernelQuotientL2→L[ℂ]CuspStripL2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ (integralOrbitProjection globalKubotaKernel)
    (kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num))).toContinuousLinearMap.comp
    (LpToLpRestrictCLM KernelQuotient ℂ ℂ (integralQuotientVolume globalKubotaKernel) 2 kernelCuspStripSet)

lemma kernelCuspPullback_ae_eq (F : KernelQuotientL2) :
    kernelCuspPullback F=ᵐ[hyperbolicVolume.restrict (cuspPeriodStrip 5 6)]
      fun w => F (integralOrbitProjection globalKubotaKernel w) := by
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hr := LpToLpRestrictCLM_coeFn ℂ kernelCuspStripSet F
  have hc := hm.quasiMeasurePreserving.ae_eq_comp hr
  have hp := Lp.coeFn_compMeasurePreserving
    (LpToLpRestrictCLM KernelQuotient ℂ ℂ (integralQuotientVolume globalKubotaKernel) 2 kernelCuspStripSet F) hm
  filter_upwards [hp,hc] with w hw hc
  exact hw.trans hc

def cuspFourierPhase (h : O) (w : HyperbolicSpace) : ℂ :=
  tracePhase (-cuspFrequency h*hyperbolicHorizontal w)

lemma cuspFourierPhase_continuous (h : O) : Continuous (cuspFourierPhase h) := by
  have hc : Continuous (fun z : ℂ => tracePhase (-cuspFrequency h*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-cuspFrequency h*z)+starRingEnd ℂ (-cuspFrequency h*z))))
    fun_prop
  exact hc.comp hyperbolicHorizontal_continuous

lemma cuspFourierPhase_norm (h : O) (w : HyperbolicSpace) : ‖cuspFourierPhase h w‖=1 :=
  tracePhase_norm _

lemma cuspFourierTest_memLp (h : O) :
    MemLp (fun w => star (cuspFourierPhase h w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip 5 6)) := by
  apply MemLp.of_bound (cuspFourierPhase_continuous h).star.aestronglyMeasurable 1
  exact Eventually.of_forall (fun w => by rw [norm_star,cuspFourierPhase_norm])

def cuspFourierTestL2 (h : O) : CuspStripL2 :=
  (cuspFourierTest_memLp h).toLp (fun w => star (cuspFourierPhase h w))

def kernelCuspFourier (h : O) : KernelQuotientL2→L[ℂ]ℂ :=
  (innerSL ℂ (cuspFourierTestL2 h)).comp kernelCuspPullback

lemma kernelCuspFourier_integral (h : O) (F : KernelQuotientL2) :
    kernelCuspFourier h F=∫w in cuspPeriodStrip 5 6,
      F (integralOrbitProjection globalKubotaKernel w)*cuspFourierPhase h w∂hyperbolicVolume := by
  change inner ℂ (cuspFourierTestL2 h) (kernelCuspPullback F)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (cuspFourierTest_memLp h),kernelCuspPullback_ae_eq F] with w hw hp
  rw [RCLike.inner_apply,cuspFourierTestL2,hw,hp]
  simp only [starRingEnd_apply,star_star]

lemma kernelCuspFourier_restrict (h : O) (F : KernelQuotientL2) :
    kernelCuspFourier h (kernelMassRestrictionCLM kernelCuspAverageCompact
      kernelCuspAverageCompact_isCompact.measurableSet F)=kernelCuspFourier h F := by
  rw [kernelCuspFourier_integral,kernelCuspFourier_integral]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (kernelMassRestriction_coe kernelCuspAverageCompact kernelCuspAverageCompact_isCompact.measurableSet F)
    (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  exact congrArg (fun z : ℂ => z*cuspFourierPhase h w)
    (hw.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩) _))

def kernelCuspFourierFamily (h : O) (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : ℂ :=
  kernelCuspFourier h
    (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s)

lemma kernelCuspFourierFamily_meromorphicAt (h : O) (a b : ℝ) (ha : 0<a) (hab : a<b) :
    MeromorphicAt (kernelCuspFourierFamily h a b ha hab) (4/3:ℂ) :=
  meromorphicAt_clm (kernelCuspFourier h)
    (kernelLocalCorrectedSeed_meromorphicAt kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab)

lemma kernelCuspFourierFamily_residue_limit (h : O) (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Tendsto (fun s : ℂ => (s-4/3)*kernelCuspFourierFamily h a b ha hab s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspFourier h (kernelEisensteinResidueVector a b ha hab))) := by
  have hh := (kernelCuspFourier h).continuous.continuousAt.tendsto.comp
    (kernelLocalCorrectedSeed_residue_limit kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,kernelCuspFourier_restrict,kernelCuspFourierFamily] using hh

lemma kernelCuspFourierFamily_actual_integral (h : O) (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    kernelCuspFourierFamily h a b ha hab s=∫w in cuspPeriodStrip 5 6,
      kernelCorrectedSeed a b ha hab s (integralOrbitProjection globalKubotaKernel w)*
        cuspFourierPhase h w∂hyperbolicVolume := by
  rw [kernelCuspFourierFamily,kernelCuspFourier_integral]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (kernelLocalCorrectedSeed_ae_eq kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s)
    (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  exact congrArg (fun z : ℂ => z*cuspFourierPhase h w)
    (hw.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩) _))

lemma kernelCuspFourierFamily_of_initial_overlap (h : O) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re)
    (hoverlap : kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelCuspFourierFamily h a b ha hab s=∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s w*cuspFourierPhase h w∂hyperbolicVolume := by
  have hcorrected : kernelCorrectedSeed a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s hs := by
    filter_upwards [hoverlap] with q hq
    change kernelQuotientSeed a b s q+kernelEisensteinL2Correction a b ha hab s q=_
    rw [hq]
    ring
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hp := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hcorrected (s := kernelCuspStripSet))
  rw [kernelCuspFourierFamily_actual_integral]
  apply integral_congr_ae
  filter_upwards [hp] with w hw
  exact congrArg (fun z : ℂ => z*cuspFourierPhase h w)
    (hw.trans (kernelQuotientEisenstein_mk s hs w))


lemma hyperbolicEisenstein_cusp_fourier_average (s : ℂ) (hs : 2<s.re) (h : O) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w*cuspFourierPhase h w∂hyperbolicVolume)=
      ∫v in Set.Icc (5:ℝ) 6,
        (((if h=0 then (v:ℂ)^s else 0)+
          (v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*scatteringCoefficient s h)*
          ((9*Real.sqrt 3/2:ℝ):ℂ))/(v:ℂ)^3 := by
  let g : HyperbolicSpace→ℂ := fun w => hyperbolicEisenstein s w*cuspFourierPhase h w
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).mul (cuspFourierPhase_continuous h)
  rw [cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  have hh : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
      eisensteinFourierCoefficient v hpos s h*((9*Real.sqrt 3/2:ℝ):ℂ) := by
    simp_rw [g,cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint,
      cuspFourierPhase,hyperbolicHorizontal_upperPoint]
    rw [eisensteinFourierCoefficient]
    exact (div_mul_cancel₀ _ cusp_volume_ne_zero).symm
  dsimp only
  rw [hh,eisensteinFourierCoefficient_formula v hpos s hs h]

def cuspWhittakerHeightFactor (s : ℂ) (h : O) : ℂ :=
  ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v)

lemma hyperbolicEisenstein_cusp_fourier_nonzero (s : ℂ) (hs : 2<s.re) (h : O) (hh : h≠0) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w*cuspFourierPhase h w∂hyperbolicVolume)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h := by
  rw [hyperbolicEisenstein_cusp_fourier_average s hs h]
  simp only [if_neg hh,zero_add]
  have heq : (∫v in Set.Icc (5:ℝ) 6,
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*scatteringCoefficient s h)*
        ((9*Real.sqrt 3/2:ℝ):ℂ)/(v:ℂ)^3)=
      ∫v in Set.Icc (5:ℝ) 6,
        (((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
          ((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith [hv.1])
    have hp : (v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    dsimp only
    rw [hp]
    ring
  rw [heq,integral_const_mul]
  rfl

lemma cuspWhittakerHeightFactor_bessel (s : ℂ) (hs : 1<s.re) (h : O) (hh : h≠0) :
    cuspWhittakerHeightFactor s h=
      ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1)*
        ((2*Real.pi:ℂ)/Complex.Gamma s*
          (2*Real.pi*‖cuspFrequency h*v‖:ℂ)^(s-1)*
          schlafliBesselK (s-1) (4*Real.pi*‖cuspFrequency h*v‖)) := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  dsimp only
  rw [sourceFourierKernel_bessel s _ hs
    (mul_ne_zero (cuspFrequency_ne_zero h hh) (Complex.ofReal_ne_zero.mpr hpos.ne'))]

def kernelResidualFourierDatum (h : O) (a b : ℝ) (ha : 0<a) (hab : a<b) : ℂ :=
  kernelCuspFourier h (kernelEisensteinResidueVector a b ha hab)

lemma kernelCuspFourierFamily_nonzero_of_initial_overlap (h : O) (hh : h≠0)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) (hs : 2<s.re)
    (hoverlap : kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelCuspFourierFamily h a b ha hab s=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h := by
  rw [kernelCuspFourierFamily_of_initial_overlap h a b ha hab s hs hoverlap,
    hyperbolicEisenstein_cusp_fourier_nonzero s hs h hh]


lemma cubicEisensteinFourierFamily_initial (h : O) (hh : h ≠ 0)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s =
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h := by
  apply kernelCuspFourierFamily_nonzero_of_initial_overlap h hh 2 3
    (by norm_num) (by norm_num) s (by linarith)
  exact kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi

#print axioms kernelCuspFourierFamily_residue_limit
#print axioms cubicEisensteinFourierFamily_initial
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
