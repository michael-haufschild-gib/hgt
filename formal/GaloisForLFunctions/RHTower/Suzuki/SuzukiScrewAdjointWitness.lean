import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewFirstDerivativeRegularity
import GaloisForLFunctions.RHTower.Suzuki.SuzukiDirichletAdjointDomain
import GaloisForLFunctions.RHTower.Suzuki.SuzukiH01FormDomain
import GaloisForLFunctions.HTGeometry.L2PairingEnergy
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Measurable

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct Convolution
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

local instance (a : SuzukiPositiveAperture) : CompleteSpace (SuzukiApertureZeroMean a) :=
  (suzukiApertureZeroMean_isClosed a).completeSpace_coe

/-- Compactly supported weak derivative of Suzuki's source screw on the aperture-difference
interval. -/
def suzukiSourceScrewDerivativeCutoff (a : SuzukiPositiveAperture) (x : ℝ) : ℂ :=
  (Icc (-2 * a.1) (2 * a.1)).indicator
    (fun y => ((deriv GaloisForLFunctions.RHTower.suzukiSourceScrew y : ℝ) : ℂ)) x

set_option maxHeartbeats 100000 in
theorem aestronglyMeasurable_suzukiSourceScrewDerivativeCutoff
    (a : SuzukiPositiveAperture) :
    AEStronglyMeasurable (suzukiSourceScrewDerivativeCutoff a) volume := by
  change AEStronglyMeasurable
    ((Icc (-2 * a.1) (2 * a.1)).indicator
      (fun y => ((deriv GaloisForLFunctions.RHTower.suzukiSourceScrew y : ℝ) : ℂ)))
    volume
  apply AEStronglyMeasurable.indicator _ measurableSet_Icc
  exact Complex.continuous_ofReal.comp_aestronglyMeasurable
    (aestronglyMeasurable_deriv
      GaloisForLFunctions.RHTower.suzukiSourceScrew volume)

set_option maxHeartbeats 100000 in
theorem integrable_suzukiSourceScrewDerivativeCutoff
    (a : SuzukiPositiveAperture) :
    Integrable (suzukiSourceScrewDerivativeCutoff a) volume := by
  have hinterval :=
    (GaloisForLFunctions.RHTower.absolutelyContinuousOnInterval_suzukiSourceScrew
      (-2 * a.1) (2 * a.1)).intervalIntegrable_deriv
  have hle : -2 * a.1 ≤ 2 * a.1 := by linarith [a.2]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle,
    ← integrableOn_Icc_iff_integrableOn_Ioc] at hinterval
  have hcomplex : IntegrableOn
      (fun x : ℝ =>
        ((deriv GaloisForLFunctions.RHTower.suzukiSourceScrew x : ℝ) : ℂ))
      (Icc (-2 * a.1) (2 * a.1)) :=
    Complex.ofRealCLM.integrable_comp hinterval
  change Integrable
    ((Icc (-2 * a.1) (2 * a.1)).indicator
      (fun x => ((deriv GaloisForLFunctions.RHTower.suzukiSourceScrew x : ℝ) : ℂ)))
    volume
  exact hcomplex.integrable_indicator measurableSet_Icc

set_option maxHeartbeats 100000 in
theorem memLp_suzukiSourceScrewDerivativeCutoff
    (a : SuzukiPositiveAperture) :
    MemLp (suzukiSourceScrewDerivativeCutoff a) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (aestronglyMeasurable_suzukiSourceScrewDerivativeCutoff a)).2
  have hinterval :=
    GaloisForLFunctions.RHTower.intervalIntegrable_deriv_suzukiSourceScrew_sq
      (-2 * a.1) (2 * a.1)
  have hle : -2 * a.1 ≤ 2 * a.1 := by linarith [a.2]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle,
    ← integrableOn_Icc_iff_integrableOn_Ioc] at hinterval
  have hnorm : IntegrableOn
      (fun x : ℝ =>
        ‖((deriv GaloisForLFunctions.RHTower.suzukiSourceScrew x : ℝ) : ℂ)‖ ^ 2)
      (Icc (-2 * a.1) (2 * a.1)) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hinterval
  have hglobal := hnorm.integrable_indicator measurableSet_Icc
  refine hglobal.congr (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Icc (-2 * a.1) (2 * a.1)
  · rw [indicator_of_mem hx]
    unfold suzukiSourceScrewDerivativeCutoff
    dsimp only
    rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx]
    unfold suzukiSourceScrewDerivativeCutoff
    dsimp only
    rw [indicator_of_notMem hx]
    simp

def suzukiSourceScrewDerivativeCutoffL2 (a : SuzukiPositiveAperture) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_suzukiSourceScrewDerivativeCutoff a).toLp
    (suzukiSourceScrewDerivativeCutoff a)

theorem suzukiSourceScrewDerivativeCutoffL2_coeFn
    (a : SuzukiPositiveAperture) :
    (suzukiSourceScrewDerivativeCutoffL2 a : ℝ → ℂ) =ᵐ[volume]
      suzukiSourceScrewDerivativeCutoff a :=
  (memLp_suzukiSourceScrewDerivativeCutoff a).coeFn_toLp

/-- Cauchy--Schwarz for the literal bilinear complex integral, expressed through the exact
`L²` pairing functional rather than a pointwise bounded-kernel estimate. -/
theorem norm_integral_mul_le_l2
    {f g : ℝ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ‖∫ x : ℝ, f x * g x‖ ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
  let F : Lp ℂ 2 (volume : Measure ℝ) := hf.toLp f
  let G : Lp ℂ 2 (volume : Measure ℝ) := hg.toLp g
  have hF : (F : ℝ → ℂ) =ᵐ[volume] f := hf.coeFn_toLp
  have hG : (G : ℝ → ℂ) =ᵐ[volume] g := hg.coeFn_toLp
  calc
    ‖∫ x : ℝ, f x * g x‖ = ‖∫ x : ℝ, F x * G x‖ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hF, hG] with x hFx hGx
      rw [hFx, hGx]
    _ = ‖(HTGeometry.complexMulBilinear.lpPairing
          (volume : Measure ℝ) 2 2 F) G‖ := by
      rw [ContinuousLinearMap.lpPairing_eq_integral]
      rfl
    _ ≤ ‖HTGeometry.complexMulBilinear.lpPairing
          (volume : Measure ℝ) 2 2 F‖ * ‖G‖ :=
      (HTGeometry.complexMulBilinear.lpPairing
        (volume : Measure ℝ) 2 2 F).le_opNorm G
    _ = ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
      rw [HTGeometry.norm_complexMulBilinear_lpPairing]

/-- Whole-line convolution of the zero-extended aperture vector with the compact source-screw
weak derivative.  On the aperture this is the weak derivative of the literal raw screw
convolution. -/
def suzukiRawScrewDerivativeConvolution
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) (t : ℝ) : ℂ :=
  convolution (suzukiApertureZeroExtend f)
    (suzukiSourceScrewDerivativeCutoff a)
    (ContinuousLinearMap.mul ℂ ℂ) volume t

theorem integrable_suzukiRawScrewDerivativeConvolution
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    Integrable (suzukiRawScrewDerivativeConvolution a f) volume := by
  exact (integrable_suzukiApertureZeroExtend a f).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_suzukiSourceScrewDerivativeCutoff a)

theorem norm_suzukiRawScrewDerivativeConvolution_le
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) (t : ℝ) :
    ‖suzukiRawScrewDerivativeConvolution a f t‖ ≤
      ‖suzukiApertureZeroExtendL2 f‖ * ‖suzukiSourceScrewDerivativeCutoffL2 a‖ := by
  let τ : ℝ → ℝ := fun u => t - u
  have hτ : MeasurePreserving τ (volume : Measure ℝ) volume :=
    (volume : Measure ℝ).measurePreserving_sub_left t
  have hshift : MemLp (suzukiSourceScrewDerivativeCutoff a ∘ τ) 2 volume :=
    (memLp_suzukiSourceScrewDerivativeCutoff a).comp_measurePreserving hτ
  rw [suzukiRawScrewDerivativeConvolution, convolution_mul]
  calc
    ‖∫ u : ℝ, suzukiApertureZeroExtend f u *
        suzukiSourceScrewDerivativeCutoff a (t - u)‖ ≤
      ‖(suzukiApertureZeroExtend_memLp f).toLp
          (suzukiApertureZeroExtend f)‖ *
        ‖hshift.toLp (suzukiSourceScrewDerivativeCutoff a ∘ τ)‖ := by
      simpa only [Function.comp_apply, τ] using
        norm_integral_mul_le_l2 (suzukiApertureZeroExtend_memLp f) hshift
    _ = ‖suzukiApertureZeroExtendL2 f‖ *
        ‖suzukiSourceScrewDerivativeCutoffL2 a‖ := by
      congr 1
      rw [← Lp.toLp_compMeasurePreserving
        (memLp_suzukiSourceScrewDerivativeCutoff a) hτ,
        Lp.norm_compMeasurePreserving]
      rfl

theorem memLp_suzukiRawScrewDerivativeConvolution
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    MemLp (suzukiRawScrewDerivativeConvolution a f) 2 volume := by
  have hzint := integrable_suzukiRawScrewDerivativeConvolution a f
  apply (memLp_two_iff_integrable_sq_norm hzint.aestronglyMeasurable).2
  have hsq : Integrable (fun t : ℝ =>
      ‖suzukiRawScrewDerivativeConvolution a f t‖ *
        ‖suzukiRawScrewDerivativeConvolution a f t‖) volume :=
    hzint.norm.mul_bdd hzint.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact norm_suzukiRawScrewDerivativeConvolution_le a f t)
  simpa only [pow_two] using hsq

def suzukiRawScrewDerivativeConvolutionL2
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_suzukiRawScrewDerivativeConvolution a f).toLp
    (suzukiRawScrewDerivativeConvolution a f)

theorem suzukiRawScrewDerivativeConvolutionL2_coeFn
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    (suzukiRawScrewDerivativeConvolutionL2 a f : ℝ → ℂ) =ᵐ[volume]
      suzukiRawScrewDerivativeConvolution a f :=
  (memLp_suzukiRawScrewDerivativeConvolution a f).coeFn_toLp

theorem suzukiSourceScrewDerivativeCutoff_sub_eq
    (a : SuzukiPositiveAperture) (s u : ℝ)
    (hs : s ∈ Icc (-a.1) a.1) (hu : u ∈ Icc (-a.1) a.1) :
    suzukiSourceScrewDerivativeCutoff a (s - u) =
      ((deriv GaloisForLFunctions.RHTower.suzukiSourceScrew (s - u) : ℝ) : ℂ) := by
  unfold suzukiSourceScrewDerivativeCutoff
  rw [indicator_of_mem]
  constructor <;> linarith [hs.1, hs.2, hu.1, hu.2]

/-- FTC for Suzuki's compact source-screw derivative after aperture translation. -/
theorem intervalIntegral_suzukiSourceScrewDerivativeCutoff_sub
    (a : SuzukiPositiveAperture) (t : SuzukiApertureInterval a.1) {u : ℝ}
    (hu : u ∈ Icc (-a.1) a.1) :
    (∫ s in (t : ℝ)..a.1, suzukiSourceScrewDerivativeCutoff a (s - u)) =
      ((GaloisForLFunctions.RHTower.suzukiSourceScrew (a.1 - u) -
        GaloisForLFunctions.RHTower.suzukiSourceScrew ((t : ℝ) - u) : ℝ) : ℂ) := by
  have hta : (t : ℝ) ≤ a.1 := t.property.2
  calc
    (∫ s in (t : ℝ)..a.1, suzukiSourceScrewDerivativeCutoff a (s - u)) =
        ∫ s in (t : ℝ)..a.1,
          ((deriv GaloisForLFunctions.RHTower.suzukiSourceScrew (s - u) : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with s
      intro hs
      rw [uIoc_of_le hta] at hs
      exact suzukiSourceScrewDerivativeCutoff_sub_eq a s u
        ⟨le_trans t.property.1 hs.1.le, hs.2⟩ hu
    _ = ((∫ s in (t : ℝ)..a.1,
          deriv GaloisForLFunctions.RHTower.suzukiSourceScrew (s - u) : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_ofReal]
    _ = ((∫ x in (t : ℝ) - u..a.1 - u,
          deriv GaloisForLFunctions.RHTower.suzukiSourceScrew x : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_comp_sub_right]
    _ = ((GaloisForLFunctions.RHTower.suzukiSourceScrew (a.1 - u) -
        GaloisForLFunctions.RHTower.suzukiSourceScrew ((t : ℝ) - u) : ℝ) : ℂ) := by
      rw [(GaloisForLFunctions.RHTower.absolutelyContinuousOnInterval_suzukiSourceScrew
        ((t : ℝ) - u) (a.1 - u)).integral_deriv_eq_sub]

theorem integral_suzukiApertureZeroExtend_mul
    (a : ℝ) (f : SuzukiApertureIntervalL2 a) (φ : ℝ → ℂ) :
    (∫ x : ℝ, suzukiApertureZeroExtend f x * φ x) =
      ∫ u : SuzukiApertureInterval a, f u * φ (u : ℝ) ∂volume := by
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [← integral_subtype measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [suzukiApertureRepresentative_ae f] with u hu
    rw [suzukiApertureZeroExtend_apply, hu]
  · intro x hx
    rw [suzukiApertureZeroExtend_eq_zero_of_notMem f hx, zero_mul]

/-- Integrating the negative weak derivative convolution from `t` to the right endpoint gives
the raw Suzuki screw convolution at `t`, modulo its endpoint constant. -/
theorem intervalIntegral_neg_suzukiRawScrewDerivativeConvolution
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1)
    (t : SuzukiApertureInterval a.1) :
    (∫ s in (t : ℝ)..a.1, -suzukiRawScrewDerivativeConvolution a f s) =
      ∫ u : SuzukiApertureInterval a.1,
        ((GaloisForLFunctions.RHTower.suzukiSourceScrew
              ((t : ℝ) - (u : ℝ)) -
            GaloisForLFunctions.RHTower.suzukiSourceScrew
              (a.1 - (u : ℝ)) : ℝ) : ℂ) * f u ∂volume := by
  let F : ℝ → ℂ := suzukiApertureZeroExtend f
  let h : ℝ → ℂ := suzukiSourceScrewDerivativeCutoff a
  have hF : Integrable F volume := integrable_suzukiApertureZeroExtend a f
  have hh : Integrable h volume := integrable_suzukiSourceScrewDerivativeCutoff a
  have hprodGlobal : Integrable
      (fun p : ℝ × ℝ => F p.2 * h (p.1 - p.2))
      ((volume : Measure ℝ).prod volume) := by
    change Integrable
      (fun p : ℝ × ℝ => ((ContinuousLinearMap.mul ℂ ℂ) (F p.2))
        (h (p.1 - p.2))) ((volume : Measure ℝ).prod volume)
    exact hF.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hh
  have hprod : Integrable
      (fun p : ℝ × ℝ => F p.2 * h (p.1 - p.2))
      (((volume : Measure ℝ).restrict (uIoc (t : ℝ) a.1)).prod volume) :=
    hprodGlobal.mono_measure
      (Measure.prod_mono Measure.restrict_le_self (le_refl volume))
  calc
    (∫ s in (t : ℝ)..a.1, -suzukiRawScrewDerivativeConvolution a f s) =
        -(∫ s in (t : ℝ)..a.1, ∫ u : ℝ, F u * h (s - u)) := by
      rw [intervalIntegral.integral_neg]
      congr 1
    _ = -(∫ u : ℝ, ∫ s in (t : ℝ)..a.1, F u * h (s - u)) := by
      rw [intervalIntegral_integral_swap hprod]
    _ = ∫ u : ℝ, F u *
        (((GaloisForLFunctions.RHTower.suzukiSourceScrew ((t : ℝ) - u) -
          GaloisForLFunctions.RHTower.suzukiSourceScrew (a.1 - u) : ℝ) : ℂ)) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with u
      by_cases hu : u ∈ Icc (-a.1) a.1
      · rw [intervalIntegral.integral_const_mul,
          intervalIntegral_suzukiSourceScrewDerivativeCutoff_sub a t hu]
        push_cast
        ring
      · rw [show F u = 0 by
          exact suzukiApertureZeroExtend_eq_zero_of_notMem f hu]
        simp
    _ = ∫ u : SuzukiApertureInterval a.1,
        ((GaloisForLFunctions.RHTower.suzukiSourceScrew
              ((t : ℝ) - (u : ℝ)) -
            GaloisForLFunctions.RHTower.suzukiSourceScrew
              (a.1 - (u : ℝ)) : ℝ) : ℂ) * f u ∂volume := by
      dsimp only [F]
      rw [integral_suzukiApertureZeroExtend_mul]
      apply integral_congr_ae
      filter_upwards with u
      ring

theorem memLp_neg_suzukiRawScrewDerivativeConvolution_restrict
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    MemLp (fun t : SuzukiApertureInterval a.1 =>
      -suzukiRawScrewDerivativeConvolution a f (t : ℝ)) 2 volume := by
  have hrestricted :=
    (memLp_suzukiRawScrewDerivativeConvolution a f).restrict
      (Icc (-a.1) a.1)
  have hcoe : MeasurePreserving
      (fun t : SuzukiApertureInterval a.1 => (t : ℝ))
      (volume : Measure (SuzukiApertureInterval a.1))
      ((volume : Measure ℝ).restrict (Icc (-a.1) a.1)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hcomp := hrestricted.comp_measurePreserving hcoe
  change MemLp
    (-(suzukiRawScrewDerivativeConvolution a f ∘
      fun t : SuzukiApertureInterval a.1 => (t : ℝ))) 2 volume
  exact hcomp.neg

/-- Literal `L²(-a,a)` witness for the maximal-adjoint range equation. -/
def suzukiRawScrewAdjointWitness
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    SuzukiApertureIntervalL2 a.1 :=
  (memLp_neg_suzukiRawScrewDerivativeConvolution_restrict a f).toLp
    (fun t : SuzukiApertureInterval a.1 =>
      -suzukiRawScrewDerivativeConvolution a f (t : ℝ))

theorem suzukiRawScrewAdjointWitness_coeFn
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    (suzukiRawScrewAdjointWitness a f : SuzukiApertureInterval a.1 → ℂ) =ᵐ[volume]
      fun t => -suzukiRawScrewDerivativeConvolution a f (t : ℝ) :=
  (memLp_neg_suzukiRawScrewDerivativeConvolution_restrict a f).coeFn_toLp

theorem suzukiApertureZeroExtend_adjointWitness_ae_restrict
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    suzukiApertureZeroExtend (suzukiRawScrewAdjointWitness a f) =ᵐ[
      (volume : Measure ℝ).restrict (Icc (-a.1) a.1)]
      fun x => -suzukiRawScrewDerivativeConvolution a f x := by
  change ∀ᵐ x : ℝ ∂(volume : Measure ℝ).restrict (Icc (-a.1) a.1),
    suzukiApertureZeroExtend (suzukiRawScrewAdjointWitness a f) x =
      -suzukiRawScrewDerivativeConvolution a f x
  rw [ae_restrict_iff_subtype measurableSet_Icc]
  filter_upwards [suzukiApertureRepresentative_ae (suzukiRawScrewAdjointWitness a f),
    suzukiRawScrewAdjointWitness_coeFn a f] with x hrep hwitness
  rw [suzukiApertureZeroExtend_apply, hrep, hwitness]

/-- The reverse primitive of the `L²` witness is exactly the raw screw convolution minus its
right-endpoint constant. -/
theorem suzukiApertureUpperPrefix_adjointWitness
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1)
    (t : SuzukiApertureInterval a.1) :
    suzukiApertureUpperPrefix a.1 (suzukiRawScrewAdjointWitness a f) t =
      ∫ u : SuzukiApertureInterval a.1,
        ((GaloisForLFunctions.RHTower.suzukiSourceScrew
              ((t : ℝ) - (u : ℝ)) -
            GaloisForLFunctions.RHTower.suzukiSourceScrew
              (a.1 - (u : ℝ)) : ℝ) : ℂ) * f u ∂volume := by
  rw [suzukiApertureUpperPrefix_eq_intervalIntegral]
  have hzero := suzukiApertureZeroExtend_adjointWitness_ae_restrict a f
  have hzeroGlobal : ∀ᵐ x : ℝ ∂volume,
      x ∈ Icc (-a.1) a.1 →
        suzukiApertureZeroExtend (suzukiRawScrewAdjointWitness a f) x =
          -suzukiRawScrewDerivativeConvolution a f x :=
    (ae_restrict_iff' measurableSet_Icc).mp hzero
  calc
    (∫ x in (t : ℝ)..a.1,
        suzukiApertureZeroExtend (suzukiRawScrewAdjointWitness a f) x) =
      ∫ x in (t : ℝ)..a.1, -suzukiRawScrewDerivativeConvolution a f x := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hzeroGlobal] with x hx
        intro hxt
        rw [uIoc_of_le t.property.2] at hxt
        exact hx ⟨le_trans t.property.1 hxt.1.le, hxt.2⟩
    _ = _ := intervalIntegral_neg_suzukiRawScrewDerivativeConvolution a f t


end RHTower

end
