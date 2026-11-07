/-
Nonvanishing of the cubic residual vector adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicCuspConstantAverages
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicInitialResolventMatching

/-!
# The actual cubic residual vector is nonzero

Initial source matching identifies the compact cusp average in the
convergent half-plane. Analytic uniqueness continues that identity through
the upper parameter region; boundary continuity then identifies its
residue with the nonzero arithmetic constant-term residue. The resulting
actual `L²` vector satisfies the `8/9` Laplace eigenvalue equation.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified

lemma kernelSpectralResolvent_analyticAt_of_isUnit (z : ℂ)
    (hz : IsUnit (kernelSpectralFormOperator z)) :
    AnalyticAt ℂ kernelSpectralResolvent z := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)
    (F := KernelQuotientL2→L[ℂ]KernelQuotientL2) kernelL2SandwichCLM
      (Ring.inverse (kernelSpectralFormOperator z))).comp_of_eq
    (kernelSpectralFormInverse_analyticAt_of_isUnit z hz) rfl

lemma kernelEisensteinResolvent_analyticAt_of_isUnit (s : ℂ)
    (hs : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s))) :
    AnalyticAt ℂ kernelEisensteinResolvent s := by
  exact (kernelSpectralResolvent_analyticAt_of_isUnit _ hs).comp_of_eq
    (by unfold kernelEisensteinSpectralParameter; fun_prop) rfl

lemma kernelCuspAverageFamily_analyticAt_of_isUnit (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s))) :
    AnalyticAt ℂ (kernelCuspAverageFamily a b ha hab) s := by
  have hcor : AnalyticAt ℂ (kernelEisensteinL2Correction a b ha hab) s :=
    ((ContinuousLinearMap.apply ℂ KernelQuotientL2).analyticAt_bilinear
      (kernelL2Defect a b ha hab s,kernelEisensteinResolvent s)).comp₂
      ((kernelL2Defect_entire a b ha hab).analyticAt s)
      (kernelEisensteinResolvent_analyticAt_of_isUnit s hs)
  have hlocal : AnalyticAt ℂ
      (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab) s :=
    ((kernelLocalSeedL2_entire kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha).analyticAt s).add
      ((ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := KernelQuotientL2)
        (kernelMassRestrictionCLM kernelCuspAverageCompact kernelCuspAverageCompact_isCompact.measurableSet)
        (kernelEisensteinL2Correction a b ha hab s)).comp_of_eq hcor rfl)
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    kernelCuspStripAverage _).comp_of_eq hlocal rfl

lemma kernelCuspAverageFamily_analyticAt_nonreal (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelCuspAverageFamily a b ha hab) s :=
  kernelCuspAverageFamily_analyticAt_of_isUnit a b ha hab s
    (kernelSpectralFormOperator_isUnit_nonreal _ (kernelEisensteinSpectralParameter_nonreal s hs hi))

def cuspUpperParameterRegion : Set ℂ := {s | (4/3:ℝ)<s.re ∧ 0<s.im}

lemma cuspUpperParameterRegion_isOpen : IsOpen cuspUpperParameterRegion :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

lemma cuspUpperParameterRegion_convex : Convex ℝ cuspUpperParameterRegion :=
  ((convex_Ioi (4/3:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)

lemma cuspConstantAverage_analyticOn_upper : AnalyticOnNhd ℂ cuspConstantAverage cuspUpperParameterRegion := by
  apply (Complex.analyticOnNhd_iff_differentiableOn cuspUpperParameterRegion_isOpen).mpr
  intro s hs
  apply (cuspConstantAverage_differentiableAt s hs.1 ?_).differentiableWithinAt
  intro he
  subst s
  norm_num [cuspUpperParameterRegion] at hs

lemma kernelCuspAverageFamily_eq_upper_of_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ,4<s.re → 0<s.im →
      kernelCuspAverageFamily a b ha hab s=
        ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume) :
    Set.EqOn (kernelCuspAverageFamily a b ha hab) cuspConstantAverage cuspUpperParameterRegion := by
  have hleft : AnalyticOnNhd ℂ (kernelCuspAverageFamily a b ha hab) cuspUpperParameterRegion := by
    intro s hs
    exact kernelCuspAverageFamily_analyticAt_nonreal a b ha hab s (by linarith [hs.1]) hs.2.ne'
  have hstart : (5+Complex.I:ℂ)∈cuspUpperParameterRegion := by
    norm_num [cuspUpperParameterRegion]
  have hV : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : kernelCuspAverageFamily a b ha hab =ᶠ[𝓝 (5+Complex.I:ℂ)] cuspConstantAverage := by
    filter_upwards [hV.mem_nhds (by norm_num)] with s hs
    exact (hoverlap s hs.1 hs.2).trans (hyperbolicEisenstein_cusp_average_eq s (by linarith [hs.1]))
  exact hleft.eqOn_of_preconnected_of_eventuallyEq cuspConstantAverage_analyticOn_upper
    cuspUpperParameterRegion_convex.isPreconnected hstart hevent

lemma kernelCuspAverageFamily_eq_real_of_upper (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hupper : Set.EqOn (kernelCuspAverageFamily a b ha hab) cuspConstantAverage cuspUpperParameterRegion)
    (x : ℝ) (hx : (4/3:ℝ)<x) (hx2 : x≠2)
    (hunit : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter (x:ℂ)))) :
    kernelCuspAverageFamily a b ha hab (x:ℂ)=cuspConstantAverage (x:ℂ) := by
  have hpath : Tendsto (fun t : ℝ => (x:ℂ)+(t:ℂ)*Complex.I) (𝓝[>] (0:ℝ)) (𝓝 (x:ℂ)) := by
    have hcont : Continuous (fun t : ℝ => (x:ℂ)+(t:ℂ)*Complex.I) :=
      (Complex.continuous_ofReal.mul_const Complex.I).const_add (x:ℂ)
    have hh := (hcont.tendsto 0).mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using hh
  have hleft := (kernelCuspAverageFamily_analyticAt_of_isUnit a b ha hab (x:ℂ) hunit).continuousAt.tendsto.comp hpath
  have hx2' : (x:ℂ)≠2 := by exact_mod_cast hx2
  have hright := (cuspConstantAverage_differentiableAt (x:ℂ) hx hx2').continuousAt.tendsto.comp hpath
  have hevent : (fun t : ℝ => kernelCuspAverageFamily a b ha hab ((x:ℂ)+(t:ℂ)*Complex.I))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ => cuspConstantAverage ((x:ℂ)+(t:ℂ)*Complex.I)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    apply hupper
    simpa only [cuspUpperParameterRegion,Set.mem_setOf_eq,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.add_im,
      Complex.mul_im,mul_zero,zero_mul,sub_zero,add_zero,zero_add,mul_one] using And.intro hx ht
  exact tendsto_nhds_unique_of_eventuallyEq hleft hright hevent

lemma realAbove_tendsto_complex_punctured :
    Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] (4/3:ℝ)) (𝓝[≠] (4/3:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · convert Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 ; norm_num
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change (4/3:ℝ)<x at hx
    change (x:ℂ)≠(4/3:ℂ)
    intro he
    have hh := congrArg Complex.re he
    norm_num at hh
    linarith [hx]

lemma kernelEisensteinResidueVector_average_of_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ,4<s.re → 0<s.im →
      kernelCuspAverageFamily a b ha hab s=
        ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume) :
    kernelCuspStripAverage (kernelEisensteinResidueVector a b ha hab)=cuspConstantAverageResidue := by
  have hupper := kernelCuspAverageFamily_eq_upper_of_overlap a b ha hab hoverlap
  have hleft := (kernelCuspAverageFamily_residue_limit a b ha hab).comp realAbove_tendsto_complex_punctured
  have hunit := realAbove_tendsto_complex_punctured.eventually kernelEisensteinPencil_eventually_isUnit
  have hlt : ∀ᶠx : ℝ in 𝓝[>] (4/3:ℝ),x<2 := by
    have hh : ∀ᶠx : ℝ in 𝓝 (4/3:ℝ),x<2 := Iio_mem_nhds (by norm_num)
    exact hh.filter_mono nhdsWithin_le_nhds
  have hevent : (fun x : ℝ => ((x:ℂ)-4/3)*kernelCuspAverageFamily a b ha hab (x:ℂ))
      =ᶠ[𝓝[>] (4/3:ℝ)] (fun x : ℝ => ((x:ℂ)-4/3)*cuspConstantAverage (x:ℂ)) := by
    filter_upwards [self_mem_nhdsWithin,hunit,hlt] with x hx hux hxx
    rw [kernelCuspAverageFamily_eq_real_of_upper a b ha hab hupper x hx hxx.ne hux]
  exact tendsto_nhds_unique_of_eventuallyEq hleft cuspConstantAverage_oneSidedResidue hevent

lemma kernelEisensteinResidueVector_ne_zero_of_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ,4<s.re → 0<s.im →
      kernelCuspAverageFamily a b ha hab s=
        ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume) :
    kernelEisensteinResidueVector a b ha hab≠0 := by
  intro he
  have hh := kernelEisensteinResidueVector_average_of_overlap a b ha hab hoverlap
  rw [he,map_zero] at hh
  exact cuspConstantAverageResidue_ne_zero hh.symm
lemma kernelCuspAverageFamily_eq_of_initial_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re)
    (hoverlap : kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelCuspAverageFamily a b ha hab s=
      ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume := by
  have hcorrected : kernelCorrectedSeed a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s hs := by
    filter_upwards [hoverlap] with q hq
    change kernelQuotientSeed a b s q+kernelEisensteinL2Correction a b ha hab s q=_
    rw [hq]
    ring
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hrestr := ae_restrict_of_ae hcorrected (s := kernelCuspStripSet)
  have hp := hm.quasiMeasurePreserving.ae_eq_comp hrestr
  rw [kernelCuspAverageFamily_actual_integral]
  apply integral_congr_ae
  filter_upwards [hp] with w hw
  exact hw.trans (kernelQuotientEisenstein_mk s hs w)

def cubicEisensteinResidue : KernelQuotientL2 :=
  kernelEisensteinResidueVector 2 3 (by norm_num) (by norm_num)

/-- The constant cusp average proves that the actual residual vector is nonzero. -/
lemma cubicEisensteinResidue_ne_zero : cubicEisensteinResidue ≠ 0 := by
  apply kernelEisensteinResidueVector_ne_zero_of_overlap 2 3 (by norm_num) (by norm_num)
  intro s hs hi
  apply kernelCuspAverageFamily_eq_of_initial_overlap 2 3 (by norm_num) (by norm_num) s (by linarith)
  exact kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi

lemma cubicEisensteinResidue_eigenvector :
    (cubicEisensteinResidue,(8/9:ℂ) • cubicEisensteinResidue)∈kernelEnergyLaplacian.graph :=
  kernelEisensteinResidueVector_graph 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinResidue_limit :
    Tendsto (fun s : ℂ => (s-4/3) • kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num) s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 cubicEisensteinResidue) :=
  kernelEisensteinResidueVector_limit 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinResidue_cusp_average :
    kernelCuspStripAverage cubicEisensteinResidue=cuspConstantAverageResidue := by
  apply kernelEisensteinResidueVector_average_of_overlap 2 3 (by norm_num) (by norm_num)
  intro s hs hi
  apply kernelCuspAverageFamily_eq_of_initial_overlap 2 3 (by norm_num) (by norm_num) s (by linarith)
  exact kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi

lemma cubicEisensteinCorrection_not_continuousAt :
    ¬ContinuousAt (kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num)) (4/3:ℂ) := by
  intro hc
  have hh := ((tendsto_id.sub_const (4/3:ℂ)).smul hc.tendsto).mono_left
    (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  simp only [sub_self,zero_smul] at hh
  exact cubicEisensteinResidue_ne_zero (tendsto_nhds_unique cubicEisensteinResidue_limit hh)

lemma cubicEisensteinResidue_local_limit (S : Set KernelQuotient) (hS : IsCompact S) :
    Tendsto (fun s : ℂ => (s-4/3) •
      kernelLocalCorrectedSeed S hS 2 3 (by norm_num) (by norm_num) s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (kernelMassRestrictionCLM S hS.measurableSet cubicEisensteinResidue)) :=
  kernelLocalCorrectedSeed_residue_limit S hS 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinLocalFamily_initial_ae (S : Set KernelQuotient) (hS : IsCompact S)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    (kernelLocalCorrectedSeed S hS 2 3 (by norm_num) (by norm_num) s : KernelQuotient→ℂ)
      =ᵐ[integralQuotientVolume globalKubotaKernel]
        S.indicator (kernelQuotientEisenstein s (by linarith)) := by
  have hlocal := kernelLocalCorrectedSeed_ae_eq S hS 2 3 (by norm_num) (by norm_num) s
  have hoverlap := kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi
  filter_upwards [hlocal,hoverlap] with q hq hc
  rw [hq]
  by_cases hmem : q∈S
  · rw [Set.indicator_of_mem hmem,Set.indicator_of_mem hmem]
    change kernelQuotientSeed 2 3 s q+kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num) s q=_
    rw [hc]
    ring
  · rw [Set.indicator_of_notMem hmem,Set.indicator_of_notMem hmem]

lemma cubicEisensteinLocalFamily_meromorphicAt (S : Set KernelQuotient) (hS : IsCompact S) :
    MeromorphicAt (kernelLocalCorrectedSeed S hS 2 3 (by norm_num) (by norm_num)) (4/3:ℂ) :=
  kernelLocalCorrectedSeed_meromorphicAt S hS 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinLocalFamily_not_continuousAt :
    ¬ContinuousAt (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact
      2 3 (by norm_num) (by norm_num)) (4/3:ℂ) := by
  have hnonzero : kernelMassRestrictionCLM kernelCuspAverageCompact
      kernelCuspAverageCompact_isCompact.measurableSet cubicEisensteinResidue≠0 := by
    intro hz
    have hh := congrArg kernelCuspStripAverage hz
    rw [kernelCuspStripAverage_restrict,map_zero,cubicEisensteinResidue_cusp_average] at hh
    exact cuspConstantAverageResidue_ne_zero hh
  intro hc
  have hh := ((tendsto_id.sub_const (4/3:ℂ)).smul hc.tendsto).mono_left
    (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  simp only [sub_self,zero_smul] at hh
  exact hnonzero (tendsto_nhds_unique
    (cubicEisensteinResidue_local_limit kernelCuspAverageCompact kernelCuspAverageCompact_isCompact) hh)


#print axioms cubicEisensteinResidue_ne_zero
#print axioms cubicEisensteinResidue_eigenvector
#print axioms cubicEisensteinResidue_cusp_average
#print axioms cubicEisensteinLocalFamily_initial_ae
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
