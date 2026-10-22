import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchwartzFourierXi
import GaloisForLFunctions.RHTower.XiThetaSchwartzL2Nonclosability
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Spectral orientation classification for the Hedenmalm theta source

Every positive measure of temperate growth defines a continuous spectral form on
Schwartz space.  This module identifies its radical with the kernel of the
Fourier-to-`L²(μ)` carrier, proves that the measure-to-form construction is
faithful, and classifies theta nullity as support on the real `Xi` divisor.

The resulting nonzero theta-null forms are necessarily nonclosable through
ordinary Lebesgue `L²`: within the full temperate spectral-measure class,
ordinary-`L²` closability is equivalent to the spectral measure being zero.
-/

open Complex Function Filter Set MeasureTheory
open scoped Topology FourierTransform SchwartzMap

noncomputable section

namespace RHTower

/-- The canonical spectral carrier: Fourier transform followed by inclusion in `L²(μ)`. -/
def xiThetaSpectralCarrier (μ : Measure ℝ) [μ.HasTemperateGrowth] :
    SchwartzMap ℝ ℂ →L[ℂ] Lp ℂ 2 μ :=
  SchwartzMap.toLpCLM ℂ ℂ 2 μ ∘L SchwartzMap.fourierTransformCLM ℂ

/-- The spectral carrier vanishes exactly when the Fourier transform vanishes almost everywhere
for the spectral measure. -/
theorem xiThetaSpectralCarrier_eq_zero_iff
    (μ : Measure ℝ) [μ.HasTemperateGrowth] (u : SchwartzMap ℝ ℂ) :
    xiThetaSpectralCarrier μ u = 0 ↔
      (fun t => FourierTransform.fourier u t) =ᵐ[μ] 0 := by
  change (FourierTransform.fourier u).toLp 2 μ = 0 ↔ _
  rw [MeasureTheory.Lp.eq_zero_iff_ae_eq_zero]
  constructor
  · intro h
    exact ((FourierTransform.fourier u).coeFn_toLp 2 μ).symm.trans h
  · intro h
    exact (FourierTransform.fourier u).coeFn_toLp 2 μ |>.trans h

/-- The radical of a spectral form is exactly the kernel of its Fourier-to-`L²(μ)` carrier. -/
theorem spectralMeasureForm_mem_leftRadical_iff_carrier_eq_zero
    (μ : Measure ℝ) [μ.HasTemperateGrowth] (u : SchwartzMap ℝ ℂ) :
    u ∈ (SchwartzMap.spectralMeasureForm μ).leftRadical ↔
      xiThetaSpectralCarrier μ u = 0 := by
  rw [xiThetaSpectralCarrier_eq_zero_iff]
  constructor
  · intro hu
    have hq : SchwartzMap.spectralMeasureForm μ u u = 0 := hu u
    rw [SchwartzMap.spectralMeasureForm_apply] at hq
    let g : SchwartzMap ℝ ℂ := SchwartzMap.pointwiseMulConj
      (FourierTransform.fourier u) (FourierTransform.fourier u)
    have hgint : Integrable g μ := g.integrable
    have hnormint : Integrable
        (fun x : ℝ => normSq (FourierTransform.fourier u x)) μ := by
      exact hgint.re.congr (by
        filter_upwards with x
        simp [g, Complex.mul_conj, Complex.normSq])
    have hcomplex :
        (∫ x, (normSq (FourierTransform.fourier u x) : ℂ) ∂μ) = 0 := by
      rw [← hq]
      apply integral_congr_ae
      filter_upwards with x
      simp [Complex.mul_conj, Complex.normSq]
    have hreal :
        (∫ x, normSq (FourierTransform.fourier u x) ∂μ) = 0 := by
      rw [integral_complex_ofReal] at hcomplex
      exact_mod_cast hcomplex
    have haeNorm :
        (fun x : ℝ => normSq (FourierTransform.fourier u x)) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun x => normSq_nonneg (FourierTransform.fourier u x)) hnormint).mp hreal
    filter_upwards [haeNorm] with x hx
    exact normSq_eq_zero.mp hx
  · intro hu v
    rw [SchwartzMap.spectralMeasureForm_apply]
    apply integral_eq_zero_of_ae
    filter_upwards [hu] with x hx
    rw [hx]
    simp

/-- A compactly supported smooth complex spectral bump centered at `t`. -/
def complexSpectralBump (t : ℝ) : SchwartzMap ℝ ℂ := by
  let b : ContDiffBump t := ⟨1, 2, by norm_num, by norm_num⟩
  exact (b.hasCompactSupport.comp_left rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp b.contDiff)

@[simp] theorem complexSpectralBump_apply_center (t : ℝ) :
    complexSpectralBump t t = 1 := by
  rw [complexSpectralBump]
  let b : ContDiffBump t := ⟨1, 2, by norm_num, by norm_num⟩
  change (b t : ℂ) = 1
  exact_mod_cast b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num))

/-- Faithfulness of the spectral-measure construction: the spectral form vanishes identically
exactly when its positive measure is zero. -/
theorem spectralMeasureForm_eq_zero_iff_measure_eq_zero
    (μ : Measure ℝ) [μ.HasTemperateGrowth] :
    (∀ u v : SchwartzMap ℝ ℂ, SchwartzMap.spectralMeasureForm μ u v = 0) ↔
      μ = 0 := by
  constructor
  · intro hzero
    rw [← Measure.support_eq_empty_iff]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    let φ : SchwartzMap ℝ ℂ := complexSpectralBump t
    let u : SchwartzMap ℝ ℂ := FourierTransform.fourierInv φ
    have hq := hzero u u
    rw [SchwartzMap.spectralMeasureForm_apply] at hq
    have hFourier : FourierTransform.fourier u = φ :=
      FourierTransform.fourier_fourierInv_eq φ
    simp only [hFourier] at hq
    let g : SchwartzMap ℝ ℂ := SchwartzMap.pointwiseMulConj φ φ
    have hgint : Integrable g μ := g.integrable
    have hnormint : Integrable (fun x : ℝ => normSq (φ x)) μ := by
      exact hgint.re.congr (by
        filter_upwards with x
        simp [g, Complex.mul_conj, Complex.normSq])
    have hcomplex : (∫ x, (normSq (φ x) : ℂ) ∂μ) = 0 := by
      rw [← hq]
      apply integral_congr_ae
      filter_upwards with x
      simp [Complex.mul_conj, Complex.normSq]
    have hreal : (∫ x, normSq (φ x) ∂μ) = 0 := by
      rw [integral_complex_ofReal] at hcomplex
      exact_mod_cast hcomplex
    have hae : (fun x : ℝ => normSq (φ x)) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => normSq_nonneg (φ x)) hnormint).mp hreal
    let b : ContDiffBump t := ⟨1, 2, by norm_num, by norm_num⟩
    have hballzero : μ (Metric.ball t b.rIn) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hae] with x hx
      intro hxball
      have hb1 : b x = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hxball)
      have hφ1 : φ x = 1 := by
        change (b x : ℂ) = 1
        exact_mod_cast hb1
      rw [hφ1, normSq_one] at hx
      norm_num at hx
    exact (Measure.mem_support_iff_forall t).mp ht
      (Metric.ball t b.rIn) (Metric.ball_mem_nhds t b.rIn_pos) |>.ne' hballzero
  · rintro rfl
    simp [SchwartzMap.spectralMeasureForm_apply]

/-- Theta nullity is exactly support of the spectral measure on the real centered `Xi` divisor. -/
theorem spectralMeasureForm_xiTheta_null_iff_support_realDivisor
    (μ : Measure ℝ) [μ.HasTemperateGrowth] :
    SchwartzMap.spectralMeasureForm μ
        xiThetaSchwartzSource xiThetaSchwartzSource = 0 ↔
      μ.support ⊆ xiRealZeroSet := by
  constructor
  · intro hnull
    have hint : Integrable xiRealNormSq μ :=
      integrable_xiRealNormSq_of_fourier_eq_XiC
        μ xiThetaSchwartzSource fourier_xiThetaSchwartzSource
    have hcomplex : (∫ t, (xiRealNormSq t : ℂ) ∂μ) = 0 := by
      rw [← spectralMeasureForm_self_eq_integral_xiRealNormSq
        μ xiThetaSchwartzSource fourier_xiThetaSchwartzSource]
      exact hnull
    have hreal : (∫ t, xiRealNormSq t ∂μ) = 0 := by
      rw [integral_complex_ofReal] at hcomplex
      exact_mod_cast hcomplex
    exact measureSupport_subset_xiRealZeroSet_of_integral_normSq_eq_zero
      μ hint hreal
  · intro hsupp
    rw [spectralMeasureForm_xiThetaSchwartzSource_self_eq_integral_xiRealNormSq]
    apply integral_eq_zero_of_ae
    filter_upwards [μ.support_mem_ae] with t ht
    have hz : XiC (t : ℂ) = 0 := hsupp ht
    simp [xiRealNormSq, hz]

/-- Diagonal theta nullity puts the theta source in the full left radical of a positive spectral
form. -/
theorem spectralMeasureForm_xiTheta_left_eq_zero_of_self_eq_zero
    (μ : Measure ℝ) [μ.HasTemperateGrowth]
    (hnull : SchwartzMap.spectralMeasureForm μ
      xiThetaSchwartzSource xiThetaSchwartzSource = 0)
    (v : SchwartzMap ℝ ℂ) :
    SchwartzMap.spectralMeasureForm μ xiThetaSchwartzSource v = 0 := by
  have hsupp :=
    (spectralMeasureForm_xiTheta_null_iff_support_realDivisor μ).mp hnull
  rw [SchwartzMap.spectralMeasureForm_apply]
  apply integral_eq_zero_of_ae
  filter_upwards [μ.support_mem_ae] with t ht
  rw [fourier_xiThetaSchwartzSource, show XiC (t : ℂ) = 0 from hsupp ht]
  simp

/-- Exact closure classification for temperate spectral orientations of the Hedenmalm theta
source: under theta nullity, sequential closability through ordinary Lebesgue `L²` is equivalent
to the spectral measure being zero. -/
theorem spectralMeasureForm_xiTheta_sequentiallyL2Closable_iff_measure_eq_zero
    (μ : Measure ℝ) [μ.HasTemperateGrowth]
    (hnull : SchwartzMap.spectralMeasureForm μ
      xiThetaSchwartzSource xiThetaSchwartzSource = 0) :
    (SchwartzMap.spectralMeasureForm μ).IsSequentiallyClosableThrough
        xiThetaSchwartzToL2 ↔
      μ = 0 := by
  rw [xiThetaSchwartzForm_sequentiallyL2Closable_iff_zero
    (SchwartzMap.spectralMeasureForm μ)
    (SchwartzMap.spectralMeasureForm_isNonnegative μ)
    (SchwartzMap.spectralMeasureForm_momentumSymmetric μ)
    (spectralMeasureForm_xiTheta_left_eq_zero_of_self_eq_zero μ hnull)]
  exact spectralMeasureForm_eq_zero_iff_measure_eq_zero μ

/-- **Premise-free spectral cone intersection law.** The theta-null spectral cone and the
ordinary-Lebesgue-`L²` closable cone intersect exactly at the zero measure. -/
theorem spectralMeasureForm_xiTheta_null_and_closable_iff_measure_eq_zero
    (μ : Measure ℝ) [μ.HasTemperateGrowth] :
    (SchwartzMap.spectralMeasureForm μ
        xiThetaSchwartzSource xiThetaSchwartzSource = 0 ∧
      (SchwartzMap.spectralMeasureForm μ).IsSequentiallyClosableThrough
        xiThetaSchwartzToL2) ↔
      μ = 0 := by
  constructor
  · rintro ⟨hnull, hclose⟩
    exact (spectralMeasureForm_xiTheta_sequentiallyL2Closable_iff_measure_eq_zero
      μ hnull).mp hclose
  · intro hμ
    subst μ
    have hnull : SchwartzMap.spectralMeasureForm (0 : Measure ℝ)
        xiThetaSchwartzSource xiThetaSchwartzSource = 0 := by
      simp [SchwartzMap.spectralMeasureForm_apply]
    exact ⟨hnull,
      (spectralMeasureForm_xiTheta_sequentiallyL2Closable_iff_measure_eq_zero
        (0 : Measure ℝ) hnull).mpr rfl⟩

end RHTower
