import GaloisForLFunctions.RHTower.Suzuki.SuzukiHlogBumpMultiplier
import GaloisForLFunctions.RHTower.Suzuki.SuzukiBoundaryLayerFormCore
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Smooth weighted form core for the Connes--Consani aperture form

This module proves the dilation-and-mollification stages of Connes--Consani (2021), Lemma `core`,
in the literal Suzuki logarithmic form norm.

An arbitrary aperture-supported form vector is first compressed strictly into the aperture.  A
shrinking normalized bump is then convolved with a pointwise-supported representative.  The
convolution is globally smooth, compactly supported in the original aperture, and its Fourier
transform is exactly the shrinking-bump multiplier constructed in
`SuzukiHlogBumpMultiplier`.  Strong multiplier convergence therefore occurs in
`L²(ℝ, (1 + log⁺ |ξ|) dξ)`, not merely in ordinary `L²`.

The endpoint proves that smooth compactly supported aperture tests form a dense subset of the
complete weighted form domain.  The subsequent Laurent-polynomial stage still has to identify
periodic Fourier truncations with the source algebraic core.
-/

open MeasureTheory Set Filter Topology FourierTransform
open scoped Convolution

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem integrable_of_indicatorCutoff_central_eq_self
    {b : ℝ} (u : SoninL2)
    (hfix : indicatorCutoff (centralInterval b)
      (measurableSet_centralInterval b) u = u) :
    Integrable (u : ℝ → ℂ) := by
  have huOn : IntegrableOn (u : ℝ → ℂ) (Icc (-b) b) volume :=
    ((Lp.memLp u).locallyIntegrable (by norm_num)).integrableOn_isCompact isCompact_Icc
  have hcut := indicatorCutoff_ae (centralInterval b)
    (measurableSet_centralInterval b) u
  rw [hfix] at hcut
  apply huOn.integrable_of_ae_notMem_eq_zero
  filter_upwards [hcut] with x hx hnot
  rw [centralInterval, Set.indicator_of_notMem hnot] at hx
  exact hx

theorem indicatorCutoff_suzukiHlogFormInwardDilate_small
    (a : SuzukiPositiveAperture) (n : ℕ) (f : SuzukiHlogFormDomain a) :
    indicatorCutoff
        (centralInterval (a.1 / suzukiHlogInwardScale n))
        (measurableSet_centralInterval (a.1 / suzukiHlogInwardScale n))
        (suzukiHlogFormEmbedding a (suzukiHlogFormInwardDilate a n f)) =
      suzukiHlogFormEmbedding a (suzukiHlogFormInwardDilate a n f) := by
  change indicatorCutoff
        (centralInterval (a.1 / suzukiHlogInwardScale n))
        (measurableSet_centralInterval (a.1 / suzukiHlogInwardScale n))
        (suzukiHlogFourierToTime (suzukiHlogDirectInwardDilate n f.1)) =
      suzukiHlogFourierToTime (suzukiHlogDirectInwardDilate n f.1)
  rw [suzukiHlogFourierToTime_directInwardDilate,
    indicatorCutoff_dilation]
  apply congrArg (dilation (suzukiHlogInwardScale n)
    (suzukiHlogInwardScale_pos n))
  have hscale_ne : suzukiHlogInwardScale n ≠ 0 :=
    (suzukiHlogInwardScale_pos n).ne'
  have hrad : suzukiHlogInwardScale n *
      (a.1 / suzukiHlogInwardScale n) = a.1 := by
    field_simp
  rw [hrad]
  have hfix := indicatorCutoff_suzukiHlogFormEmbedding a f
  change indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1)
      (suzukiHlogFourierToTime f.1) = suzukiHlogFourierToTime f.1 at hfix
  exact hfix

theorem integrable_suzukiHlogFormInwardEmbedding
    (a : SuzukiPositiveAperture) (n : ℕ) (f : SuzukiHlogFormDomain a) :
    Integrable
      (suzukiHlogFormEmbedding a (suzukiHlogFormInwardDilate a n f) : ℝ → ℂ) :=
  integrable_of_indicatorCutoff_central_eq_self _
    (indicatorCutoff_suzukiHlogFormInwardDilate_small a n f)

/-- Strict support margin created by inward dilation. -/
def suzukiHlogInwardGap (a : SuzukiPositiveAperture) (n : ℕ) : ℝ :=
  a.1 - a.1 / suzukiHlogInwardScale n

theorem suzukiHlogInwardScale_one_lt (n : ℕ) :
    1 < suzukiHlogInwardScale n := by
  unfold suzukiHlogInwardScale
  have h : 0 < (((n + 1 : ℕ) : ℝ))⁻¹ := by positivity
  linarith

theorem suzukiHlogInwardGap_pos (a : SuzukiPositiveAperture) (n : ℕ) :
    0 < suzukiHlogInwardGap a n := by
  unfold suzukiHlogInwardGap
  exact sub_pos.mpr (div_lt_self a.2 (suzukiHlogInwardScale_one_lt n))

/-- A shrinking mollifier width using only half of the inward support margin. -/
def suzukiHlogMollifierWidth (a : SuzukiPositiveAperture) (n m : ℕ) : ℝ :=
  (suzukiHlogInwardGap a n / 2) * (1 / ((m : ℝ) + 1))

theorem suzukiHlogMollifierWidth_pos
    (a : SuzukiPositiveAperture) (n m : ℕ) :
    0 < suzukiHlogMollifierWidth a n m := by
  unfold suzukiHlogMollifierWidth
  exact mul_pos (div_pos (suzukiHlogInwardGap_pos a n) (by norm_num))
    (div_pos (by norm_num) (by positivity))

theorem suzukiHlogMollifierWidth_tendsto
    (a : SuzukiPositiveAperture) (n : ℕ) :
    Tendsto (fun m => suzukiHlogMollifierWidth a n m) atTop (nhds 0) := by
  unfold suzukiHlogMollifierWidth
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul
    (suzukiHlogInwardGap a n / 2))

theorem suzukiHlogMollifierWidth_lt_gap
    (a : SuzukiPositiveAperture) (n m : ℕ) :
    suzukiHlogMollifierWidth a n m < suzukiHlogInwardGap a n := by
  have hgap := suzukiHlogInwardGap_pos a n
  have hfrac : 1 / ((m : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg m : 0 ≤ (m : ℝ))]
  unfold suzukiHlogMollifierWidth
  nlinarith

/-- Pointwise-supported representative of the inward form vector.  The cutoff removes arbitrary
null-set values of the `L²` representative, which is essential for a literal support theorem about
its convolution. -/
def suzukiHlogInwardCutoffRep
    (a : SuzukiPositiveAperture) (n : ℕ) (f : SuzukiHlogFormDomain a) (x : ℝ) : ℂ :=
  (centralInterval (a.1 / suzukiHlogInwardScale n)).indicator
    (fun y => (suzukiHlogFormEmbedding a (suzukiHlogFormInwardDilate a n f) : ℝ → ℂ) y) x

theorem suzukiHlogInwardCutoffRep_ae
    (a : SuzukiPositiveAperture) (n : ℕ) (f : SuzukiHlogFormDomain a) :
    suzukiHlogInwardCutoffRep a n f =ᵐ[volume]
      (suzukiHlogFormEmbedding a (suzukiHlogFormInwardDilate a n f) : ℝ → ℂ) := by
  have hcut := indicatorCutoff_ae
    (centralInterval (a.1 / suzukiHlogInwardScale n))
    (measurableSet_centralInterval (a.1 / suzukiHlogInwardScale n))
    (suzukiHlogFormEmbedding a (suzukiHlogFormInwardDilate a n f))
  rw [indicatorCutoff_suzukiHlogFormInwardDilate_small a n f] at hcut
  exact hcut.symm

theorem integrable_suzukiHlogInwardCutoffRep
    (a : SuzukiPositiveAperture) (n : ℕ) (f : SuzukiHlogFormDomain a) :
    Integrable (suzukiHlogInwardCutoffRep a n f) :=
  (integrable_suzukiHlogFormInwardEmbedding a n f).congr
    (suzukiHlogInwardCutoffRep_ae a n f).symm

theorem support_suzukiHlogInwardCutoffRep_subset
    (a : SuzukiPositiveAperture) (n : ℕ) (f : SuzukiHlogFormDomain a) :
    Function.support (suzukiHlogInwardCutoffRep a n f) ⊆
      Icc (-(a.1 / suzukiHlogInwardScale n))
        (a.1 / suzukiHlogInwardScale n) := by
  intro x hx
  change x ∈ centralInterval (a.1 / suzukiHlogInwardScale n)
  by_contra hnot
  exact hx (Set.indicator_of_notMem hnot _)

theorem hasCompactSupport_suzukiHlogInwardCutoffRep
    (a : SuzukiPositiveAperture) (n : ℕ) (f : SuzukiHlogFormDomain a) :
    HasCompactSupport (suzukiHlogInwardCutoffRep a n f) := by
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal (support_suzukiHlogInwardCutoffRep_subset a n f) isClosed_Icc)

theorem support_complexBumpMollifier_subset {ε : ℝ} (hε : 0 < ε) :
    Function.support (complexBumpMollifier hε) ⊆ Icc (-ε) ε := by
  intro x hx
  have hxreal : bumpMollifier hε x ≠ 0 := by
    intro hzero
    exact hx (by simp [complexBumpMollifier, hzero])
  have hxball : x ∈ Metric.ball (0 : ℝ) ε := by
    change x ∈ Metric.ball (0 : ℝ) (widthBump hε).rOut
    rw [← (widthBump hε).support_normed_eq (μ := (volume : Measure ℝ))]
    exact hxreal
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hxball
  rcases abs_lt.mp hxball with ⟨hleft, hright⟩
  exact ⟨hleft.le, hright.le⟩

/-- Time-side convolution of an inward-compressed form vector with a shrinking smooth bump. -/
def suzukiHlogMollifiedTime
    (a : SuzukiPositiveAperture) (n m : ℕ) (f : SuzukiHlogFormDomain a) : ℝ → ℂ :=
  complexBumpMollifier (suzukiHlogMollifierWidth_pos a n m) ⋆[
    ContinuousLinearMap.mul ℝ ℂ]
      suzukiHlogInwardCutoffRep a n f

theorem contDiff_suzukiHlogMollifiedTime
    (a : SuzukiPositiveAperture) (n m : ℕ) (f : SuzukiHlogFormDomain a) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiHlogMollifiedTime a n m f) := by
  exact (hasCompactSupport_complexBumpMollifier
      (suzukiHlogMollifierWidth_pos a n m)).contDiff_convolution_left
    (ContinuousLinearMap.mul ℝ ℂ)
    (contDiff_complexBumpMollifier (suzukiHlogMollifierWidth_pos a n m))
    (integrable_suzukiHlogInwardCutoffRep a n f).locallyIntegrable

theorem integrable_suzukiHlogMollifiedTime
    (a : SuzukiPositiveAperture) (n m : ℕ) (f : SuzukiHlogFormDomain a) :
    Integrable (suzukiHlogMollifiedTime a n m f) :=
  (integrable_complexBumpMollifier (suzukiHlogMollifierWidth_pos a n m)).integrable_convolution
    (ContinuousLinearMap.mul ℝ ℂ) (integrable_suzukiHlogInwardCutoffRep a n f)

theorem support_suzukiHlogMollifiedTime_subset
    (a : SuzukiPositiveAperture) (n m : ℕ) (f : SuzukiHlogFormDomain a) :
    Function.support (suzukiHlogMollifiedTime a n m f) ⊆ Icc (-a.1) a.1 := by
  intro x hx
  have hxsum := MeasureTheory.support_convolution_subset
    (ContinuousLinearMap.mul ℝ ℂ) hx
  rcases hxsum with ⟨y, hy, z, hz, rfl⟩
  have hy' := support_complexBumpMollifier_subset
    (suzukiHlogMollifierWidth_pos a n m) hy
  have hz' := support_suzukiHlogInwardCutoffRep_subset a n f hz
  have hmargin := suzukiHlogMollifierWidth_lt_gap a n m
  unfold suzukiHlogInwardGap at hmargin
  constructor <;> linarith [hy'.1, hy'.2, hz'.1, hz'.2]

theorem hasCompactSupport_suzukiHlogMollifiedTime
    (a : SuzukiPositiveAperture) (n m : ℕ) (f : SuzukiHlogFormDomain a) :
    HasCompactSupport (suzukiHlogMollifiedTime a n m f) := by
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal (support_suzukiHlogMollifiedTime_subset a n m f) isClosed_Icc)

theorem tsupport_suzukiHlogMollifiedTime_subset
    (a : SuzukiPositiveAperture) (n m : ℕ) (f : SuzukiHlogFormDomain a) :
    tsupport (suzukiHlogMollifiedTime a n m f) ⊆ Icc (-a.1) a.1 :=
  closure_minimal (support_suzukiHlogMollifiedTime_subset a n m f) isClosed_Icc

theorem fourier_suzukiHlogInwardCutoffRep_ae
    (a : SuzukiPositiveAperture) (n : ℕ) (f : SuzukiHlogFormDomain a) :
    (fun ξ => 𝓕 (suzukiHlogInwardCutoffRep a n f) ξ) =ᵐ[volume]
      (suzukiHlogFormInwardDilate a n f).1 := by
  let u : SoninL2 := suzukiHlogFormEmbedding a (suzukiHlogFormInwardDilate a n f)
  have huInt : Integrable (u : ℝ → ℂ) :=
    integrable_suzukiHlogFormInwardEmbedding a n f
  let u1 : Lp ℂ 1 (volume : Measure ℝ) :=
    (memLp_one_iff_integrable.mpr huInt).toLp u
  have hu1coe : (u1 : ℝ → ℂ) =ᵐ[volume] (u : ℝ → ℂ) :=
    MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr huInt)
  have hclassical : ∀ ξ : ℝ,
      (Real.Lp.fourierTransform u1 : ℝ → ℂ) ξ = 𝓕 (u : ℝ → ℂ) ξ := by
    intro ξ
    rw [Real.Lp.fourierTransform_apply]
    exact Real.fourier_congr_ae hu1coe ξ
  have hL2 :
      ((fourierUnitary u : SoninL2) : ℝ → ℂ) =ᵐ[volume]
        (fun ξ => 𝓕 (u : ℝ → ℂ) ξ) :=
    (l2_fourier_coeFn_eq_l1_fourier_of_integrable u huInt).trans
      (Filter.Eventually.of_forall hclassical)
  have hL2' :
      ((suzukiHlogWeightedToL2 (suzukiHlogFormInwardDilate a n f).1 : SoninL2) :
          ℝ → ℂ) =ᵐ[volume]
        (fun ξ => 𝓕 (u : ℝ → ℂ) ξ) := by
    rw [← fourierUnitary_suzukiHlogFourierToTime]
    exact hL2
  have hrepFourier : ∀ ξ : ℝ,
      𝓕 (suzukiHlogInwardCutoffRep a n f) ξ = 𝓕 (u : ℝ → ℂ) ξ :=
    fun ξ => Real.fourier_congr_ae (suzukiHlogInwardCutoffRep_ae a n f) ξ
  have hrepFourierAe :
      (fun ξ => 𝓕 (suzukiHlogInwardCutoffRep a n f) ξ) =ᵐ[volume]
        (fun ξ => 𝓕 (u : ℝ → ℂ) ξ) :=
    Filter.Eventually.of_forall hrepFourier
  exact hrepFourierAe.trans
    (hL2'.symm.trans (suzukiHlogWeightedToL2_coeFn
      (suzukiHlogFormInwardDilate a n f).1))

/-- The real-bilinear convolution used for smoothness is pointwise the standard complex
multiplication convolution used by the Fourier convolution theorem. -/
theorem suzukiHlogMollifiedTime_eq_complexConvolution
    (a : SuzukiPositiveAperture) (n m : ℕ) (f : SuzukiHlogFormDomain a) :
    suzukiHlogMollifiedTime a n m f =
      complexBumpMollifier (suzukiHlogMollifierWidth_pos a n m) ⋆[
        ContinuousLinearMap.mul ℂ ℂ]
          suzukiHlogInwardCutoffRep a n f := by
  funext x
  rw [suzukiHlogMollifiedTime, MeasureTheory.convolution_def,
    MeasureTheory.convolution_def]
  apply integral_congr_ae
  filter_upwards with t
  rfl

theorem fourier_suzukiHlogMollifiedTime
    (a : SuzukiPositiveAperture) (n m : ℕ) (f : SuzukiHlogFormDomain a) (ξ : ℝ) :
    𝓕 (suzukiHlogMollifiedTime a n m f) ξ =
      𝓕 (complexBumpMollifier (suzukiHlogMollifierWidth_pos a n m)) ξ *
        𝓕 (suzukiHlogInwardCutoffRep a n f) ξ := by
  rw [suzukiHlogMollifiedTime_eq_complexConvolution]
  exact Real.fourier_mul_convolution_eq
    (integrable_complexBumpMollifier (suzukiHlogMollifierWidth_pos a n m))
    (integrable_suzukiHlogInwardCutoffRep a n f) ξ

/-- Direct weighted Fourier vector obtained by multiplying the inward vector by the bump symbol. -/
def suzukiHlogMollifiedFourierVector
    (a : SuzukiPositiveAperture) (n m : ℕ) (f : SuzukiHlogFormDomain a) :
    SuzukiHlogFourierL2 :=
  suzukiHlogBumpFourierMul (suzukiHlogMollifierWidth_pos a n m)
    (suzukiHlogFormInwardDilate a n f).1

/-- The inverse weighted Fourier transform of the direct multiplier vector is exactly the smooth
compactly supported time convolution. -/
theorem suzukiHlogFourierToTime_mollifiedFourierVector
    (a : SuzukiPositiveAperture) (n m : ℕ) (f : SuzukiHlogFormDomain a) :
    suzukiHlogFourierToTime (suzukiHlogMollifiedFourierVector a n m f) =
      suzukiComplexTestL2 (suzukiHlogMollifiedTime a n m f)
        (contDiff_suzukiHlogMollifiedTime a n m f)
        (hasCompactSupport_suzukiHlogMollifiedTime a n m f) := by
  apply fourierUnitary.injective
  rw [fourierUnitary_suzukiHlogFourierToTime]
  apply Lp.ext
  let test : SoninL2 :=
    suzukiComplexTestL2 (suzukiHlogMollifiedTime a n m f)
      (contDiff_suzukiHlogMollifiedTime a n m f)
      (hasCompactSupport_suzukiHlogMollifiedTime a n m f)
  have htestCoe : (test : ℝ → ℂ) =ᵐ[volume]
      suzukiHlogMollifiedTime a n m f := by
    exact suzukiComplexTestL2_coeFn (suzukiHlogMollifiedTime a n m f)
      (contDiff_suzukiHlogMollifiedTime a n m f)
      (hasCompactSupport_suzukiHlogMollifiedTime a n m f)
  have htestInt : Integrable (test : ℝ → ℂ) :=
    (integrable_suzukiHlogMollifiedTime a n m f).congr htestCoe.symm
  let test1 : Lp ℂ 1 (volume : Measure ℝ) :=
    (memLp_one_iff_integrable.mpr htestInt).toLp test
  have htest1Coe : (test1 : ℝ → ℂ) =ᵐ[volume] (test : ℝ → ℂ) :=
    MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr htestInt)
  have htestClassical : ∀ ξ : ℝ,
      (Real.Lp.fourierTransform test1 : ℝ → ℂ) ξ =
        𝓕 (suzukiHlogMollifiedTime a n m f) ξ := by
    intro ξ
    rw [Real.Lp.fourierTransform_apply]
    exact Real.fourier_congr_ae (htest1Coe.trans htestCoe) ξ
  have htestFourier :
      ((fourierUnitary test : SoninL2) : ℝ → ℂ) =ᵐ[volume]
        (fun ξ => 𝓕 (suzukiHlogMollifiedTime a n m f) ξ) :=
    (l2_fourier_coeFn_eq_l1_fourier_of_integrable test htestInt).trans
      (Filter.Eventually.of_forall htestClassical)
  have hweighted := suzukiHlogWeightedToL2_coeFn
    (suzukiHlogMollifiedFourierVector a n m f)
  have hmul := (lpBoundedMulCLM_coeFn
    (p := 2) (μ := suzukiHlogMeasure)
    (measurable_fourier_complexBumpMollifier
      (suzukiHlogMollifierWidth_pos a n m)) zero_le_one
    (norm_fourier_complexBumpMollifier_le_one
      (suzukiHlogMollifierWidth_pos a n m))
    (suzukiHlogFormInwardDilate a n f).1).filter_mono
      (ae_mono volume_le_suzukiHlogMeasure)
  have hmul' :
      (suzukiHlogMollifiedFourierVector a n m f : ℝ → ℂ) =ᵐ[volume]
        (fun ξ =>
          𝓕 (complexBumpMollifier (suzukiHlogMollifierWidth_pos a n m)) ξ *
            ((suzukiHlogFormInwardDilate a n f).1 : ℝ → ℂ) ξ) := by
    simpa [suzukiHlogMollifiedFourierVector, suzukiHlogBumpFourierMul] using hmul
  have htestFourier' :
      ((fourierUnitary
        (suzukiComplexTestL2 (suzukiHlogMollifiedTime a n m f)
          (contDiff_suzukiHlogMollifiedTime a n m f)
          (hasCompactSupport_suzukiHlogMollifiedTime a n m f)) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
        (fun ξ => 𝓕 (suzukiHlogMollifiedTime a n m f) ξ) := by
    exact htestFourier
  have hrep := fourier_suzukiHlogInwardCutoffRep_ae a n f
  filter_upwards [hweighted, hmul', htestFourier', hrep] with ξ hw hmulξ htestξ hrepξ
  rw [hw, hmulξ, htestξ, fourier_suzukiHlogMollifiedTime, hrepξ]

/-- Form-domain realization of the smooth mollified time function. -/
noncomputable def suzukiHlogMollifiedFormVector
    (a : SuzukiPositiveAperture) (n m : ℕ) (f : SuzukiHlogFormDomain a) :
    SuzukiHlogFormDomain a :=
  Classical.choose (exists_suzukiHlogFormDomain_eq_smoothComplexTest a
    (suzukiHlogMollifiedTime a n m f)
    (contDiff_suzukiHlogMollifiedTime a n m f)
    (hasCompactSupport_suzukiHlogMollifiedTime a n m f)
    (tsupport_suzukiHlogMollifiedTime_subset a n m f))

theorem suzukiHlogFormEmbedding_mollifiedFormVector
    (a : SuzukiPositiveAperture) (n m : ℕ) (f : SuzukiHlogFormDomain a) :
    suzukiHlogFormEmbedding a (suzukiHlogMollifiedFormVector a n m f) =
      suzukiComplexTestL2 (suzukiHlogMollifiedTime a n m f)
        (contDiff_suzukiHlogMollifiedTime a n m f)
        (hasCompactSupport_suzukiHlogMollifiedTime a n m f) :=
  Classical.choose_spec (exists_suzukiHlogFormDomain_eq_smoothComplexTest a
    (suzukiHlogMollifiedTime a n m f)
    (contDiff_suzukiHlogMollifiedTime a n m f)
    (hasCompactSupport_suzukiHlogMollifiedTime a n m f)
    (tsupport_suzukiHlogMollifiedTime_subset a n m f))

theorem suzukiHlogMollifiedFormVector_fst
    (a : SuzukiPositiveAperture) (n m : ℕ) (f : SuzukiHlogFormDomain a) :
    (suzukiHlogMollifiedFormVector a n m f).1 =
      suzukiHlogMollifiedFourierVector a n m f := by
  apply suzukiHlogFourierToTime_injective
  change suzukiHlogFormEmbedding a (suzukiHlogMollifiedFormVector a n m f) =
    suzukiHlogFourierToTime (suzukiHlogMollifiedFourierVector a n m f)
  rw [suzukiHlogFormEmbedding_mollifiedFormVector,
    suzukiHlogFourierToTime_mollifiedFourierVector]

/-- At fixed inward compression, smooth compactly supported mollifications converge in the exact
weighted form norm. -/
theorem suzukiHlogMollifiedFormVector_tendsto_inward
    (a : SuzukiPositiveAperture) (n : ℕ) (f : SuzukiHlogFormDomain a) :
    Tendsto (fun m => suzukiHlogMollifiedFormVector a n m f) atTop
      (nhds (suzukiHlogFormInwardDilate a n f)) := by
  rw [tendsto_subtype_rng]
  have h := suzukiHlogBumpFourierMul_tendsto
    (fun m => suzukiHlogMollifierWidth_pos a n m)
    (suzukiHlogMollifierWidth_tendsto a n)
    (suzukiHlogFormInwardDilate a n f).1
  have hfun :
      (fun m => (suzukiHlogMollifiedFormVector a n m f).1) =
        fun m => suzukiHlogMollifiedFourierVector a n m f := by
    funext m
    exact suzukiHlogMollifiedFormVector_fst a n m f
  rw [hfun]
  exact h

/-- Smooth compactly supported aperture tests, represented inside the complete weighted form
domain. -/
def suzukiHlogSmoothApertureCore (a : SuzukiPositiveAperture) :
    Set (SuzukiHlogFormDomain a) :=
  {q | ∃ (g : ℝ → ℂ) (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g)
      (hgsupp : HasCompactSupport g),
      tsupport g ⊆ Icc (-a.1) a.1 ∧
      suzukiHlogFormEmbedding a q = suzukiComplexTestL2 g hgdiff hgsupp}

theorem suzukiHlogMollifiedFormVector_mem_smoothApertureCore
    (a : SuzukiPositiveAperture) (n m : ℕ) (f : SuzukiHlogFormDomain a) :
    suzukiHlogMollifiedFormVector a n m f ∈ suzukiHlogSmoothApertureCore a := by
  exact ⟨suzukiHlogMollifiedTime a n m f,
    contDiff_suzukiHlogMollifiedTime a n m f,
    hasCompactSupport_suzukiHlogMollifiedTime a n m f,
    tsupport_suzukiHlogMollifiedTime_subset a n m f,
    suzukiHlogFormEmbedding_mollifiedFormVector a n m f⟩

/-- Every inward-compressed vector lies in the form-norm closure of smooth aperture tests. -/
theorem suzukiHlogFormInwardDilate_mem_closure_smoothApertureCore
    (a : SuzukiPositiveAperture) (n : ℕ) (f : SuzukiHlogFormDomain a) :
    suzukiHlogFormInwardDilate a n f ∈ closure (suzukiHlogSmoothApertureCore a) :=
  mem_closure_of_tendsto (suzukiHlogMollifiedFormVector_tendsto_inward a n f)
    (Filter.Eventually.of_forall
      (fun m => suzukiHlogMollifiedFormVector_mem_smoothApertureCore a n m f))

/-- **Weighted smooth form core.**  Globally smooth compactly supported aperture tests are dense in
Suzuki's exact `H^log` form domain.  This completes the dilation-plus-mollification stages of
Connes--Consani (2021), Lemma `core`. -/
theorem dense_suzukiHlogSmoothApertureCore (a : SuzukiPositiveAperture) :
    Dense (suzukiHlogSmoothApertureCore a) := by
  intro f
  exact isClosed_closure.mem_of_tendsto (suzukiHlogFormInwardDilate_tendsto a f)
    (Filter.Eventually.of_forall
      (fun n => suzukiHlogFormInwardDilate_mem_closure_smoothApertureCore a n f))

end RHTower

