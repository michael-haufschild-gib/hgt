import GaloisForLFunctions.RHTower.SuzukiScrewWeilIdentity
import GaloisForLFunctions.RHTower.KernelOperatorPolarization
import GaloisForLFunctions.RHTower.TraceNormBound
import GaloisForLFunctions.RHTower.XiDivisorHilbertCarrier
import GaloisForLFunctions.RHTower.TraceClassCyclicity

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct
open RHTower

/-!
# Suzuki's trace-class screw-kernel operator

This module formalizes Theorem 1.5 of Suzuki (2022) for the literal kernel in equation (1.9)
and the literal bounded-aperture operator in equation (1.10). The proof factors that operator
through the multiplicity-exact Hilbert divisor carrier: both synthesis maps are Hilbert--Schmidt,
so their cross-space composition is trace class. Absolute reciprocal-square convergence proves
that this factorization agrees almost everywhere with Suzuki's integral formula.
-/

noncomputable section

namespace RHTower


def suzukiDivisorFeatureCoord (t : ℝ) (q : XiZeroCopy) : ℂ :=
  (Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1) / xiSpectralPoint q

theorem norm_suzukiDivisorFeatureCoord_le (t : ℝ) (q : XiZeroCopy) :
    ‖suzukiDivisorFeatureCoord t q‖ ≤
      (1 + Real.exp (|t| / 2)) / ‖xiSpectralPoint q‖ := by
  have hstrip : |(I * xiSpectralPoint q).re| ≤ (1 / 2 : ℝ) :=
    le_of_lt (abs_re_I_mul_xiSpectralPoint_le_half q)
  have hre : (I * xiSpectralPoint q * (t : ℂ)).re ≤ |t| / 2 := by
    rw [Complex.mul_re]
    simp only [ofReal_re, ofReal_im, mul_zero, sub_zero]
    calc
      (I * xiSpectralPoint q).re * t ≤
          |(I * xiSpectralPoint q).re * t| := le_abs_self _
      _ = |(I * xiSpectralPoint q).re| * |t| := abs_mul _ _
      _ ≤ (1 / 2) * |t| := by gcongr
      _ = |t| / 2 := by ring
  rw [suzukiDivisorFeatureCoord, norm_div]
  calc
    ‖Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1‖ /
          ‖xiSpectralPoint q‖ ≤
        (‖Complex.exp (I * xiSpectralPoint q * (t : ℂ))‖ + ‖(1 : ℂ)‖) /
          ‖xiSpectralPoint q‖ := by
      gcongr
      exact norm_sub_le _ _
    _ = (Real.exp (I * xiSpectralPoint q * (t : ℂ)).re + 1) /
          ‖xiSpectralPoint q‖ := by
      rw [Complex.norm_exp, norm_one]
    _ ≤ (1 + Real.exp (|t| / 2)) / ‖xiSpectralPoint q‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      linarith [Real.exp_le_exp.mpr hre]

theorem memlp_suzukiDivisorFeatureCoord (t : ℝ) : Memℓp (suzukiDivisorFeatureCoord t) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  apply Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_)
    (xiSpectralPoint_inv_sq_summable.mul_left
      ((1 + Real.exp (|t| / 2)) ^ 2))
  rw [show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, Real.rpow_two]
  have h := norm_suzukiDivisorFeatureCoord_le t q
  have hq : 0 < ‖xiSpectralPoint q‖ :=
    norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  calc
    ‖suzukiDivisorFeatureCoord t q‖ ^ 2 ≤
        ((1 + Real.exp (|t| / 2)) / ‖xiSpectralPoint q‖) ^ 2 := by gcongr
    _ = (1 + Real.exp (|t| / 2)) ^ 2 *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by field_simp

def suzukiDivisorFeature (t : ℝ) : XiDivisorL2 :=
  ⟨suzukiDivisorFeatureCoord t, memlp_suzukiDivisorFeatureCoord t⟩

@[simp] theorem suzukiDivisorFeature_apply (t : ℝ) (q : XiZeroCopy) :
    suzukiDivisorFeature t q = suzukiDivisorFeatureCoord t q := rfl

theorem continuous_suzukiDivisorFeature : Continuous suzukiDivisorFeature := by
  rw [continuous_iff_continuousAt]
  intro t
  let A : ℝ := |t| + 1
  let C : ℝ := 1 + Real.exp (A / 2)
  let S : ℝ → ℝ := fun s => ∑' q : XiZeroCopy,
    ‖suzukiDivisorFeatureCoord s q - suzukiDivisorFeatureCoord t q‖ ^ 2
  have hA : 0 < A := by
    dsimp [A]
    linarith [abs_nonneg t]
  have htA : -A < t ∧ t < A := by
    dsimp [A]
    constructor <;> linarith [le_abs_self t, neg_abs_le t]
  have hcoord (q : XiZeroCopy) : Continuous fun s : ℝ =>
      ‖suzukiDivisorFeatureCoord s q - suzukiDivisorFeatureCoord t q‖ ^ 2 := by
    unfold suzukiDivisorFeatureCoord
    fun_prop
  have hbound (q : XiZeroCopy) (s : ℝ) (hs : s ∈ Icc (-A) A) :
      ‖‖suzukiDivisorFeatureCoord s q - suzukiDivisorFeatureCoord t q‖ ^ 2‖ ≤
        (2 * C) ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
    have habss : |s| ≤ A := (abs_le).2 hs
    have habst : |t| ≤ A := by
      dsimp [A]
      linarith
    have hsC : ‖suzukiDivisorFeatureCoord s q‖ ≤ C / ‖xiSpectralPoint q‖ := by
      calc
        ‖suzukiDivisorFeatureCoord s q‖ ≤
            (1 + Real.exp (|s| / 2)) / ‖xiSpectralPoint q‖ :=
          norm_suzukiDivisorFeatureCoord_le s q
        _ ≤ C / ‖xiSpectralPoint q‖ := by
          apply div_le_div_of_nonneg_right _ (norm_nonneg _)
          dsimp [C]
          gcongr
    have htC : ‖suzukiDivisorFeatureCoord t q‖ ≤ C / ‖xiSpectralPoint q‖ := by
      calc
        ‖suzukiDivisorFeatureCoord t q‖ ≤
            (1 + Real.exp (|t| / 2)) / ‖xiSpectralPoint q‖ :=
          norm_suzukiDivisorFeatureCoord_le t q
        _ ≤ C / ‖xiSpectralPoint q‖ := by
          apply div_le_div_of_nonneg_right _ (norm_nonneg _)
          dsimp [C]
          gcongr
    have hdiff : ‖suzukiDivisorFeatureCoord s q - suzukiDivisorFeatureCoord t q‖ ≤
        2 * C / ‖xiSpectralPoint q‖ := by
      calc
        ‖suzukiDivisorFeatureCoord s q - suzukiDivisorFeatureCoord t q‖ ≤
            ‖suzukiDivisorFeatureCoord s q‖ + ‖suzukiDivisorFeatureCoord t q‖ := norm_sub_le _ _
        _ ≤ C / ‖xiSpectralPoint q‖ + C / ‖xiSpectralPoint q‖ :=
          add_le_add hsC htC
        _ = 2 * C / ‖xiSpectralPoint q‖ := by ring
    have hq : 0 < ‖xiSpectralPoint q‖ :=
      norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc
      ‖suzukiDivisorFeatureCoord s q - suzukiDivisorFeatureCoord t q‖ ^ 2 ≤
          (2 * C / ‖xiSpectralPoint q‖) ^ 2 := by gcongr
      _ = (2 * C) ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by field_simp
  have hsum : Summable (fun q : XiZeroCopy =>
      (2 * C) ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2)) :=
    xiSpectralPoint_inv_sq_summable.mul_left ((2 * C) ^ 2)
  have hSOn : ContinuousOn S (Icc (-A) A) := by
    apply continuousOn_tsum (fun q => (hcoord q).continuousOn) hsum
    intro q s hs
    exact hbound q s hs
  have hS : ContinuousAt S t :=
    hSOn.continuousAt (Icc_mem_nhds htA.1 htA.2)
  have hS0 : S t = 0 := by
    simp [S]
  have hsqrt : Tendsto (fun s => Real.sqrt (S s)) (nhds t) (nhds 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hS.tendsto
    rw [hS0, Real.sqrt_zero] at h
    exact h
  show Tendsto suzukiDivisorFeature (nhds t) (nhds (suzukiDivisorFeature t))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply hsqrt.congr'
  filter_upwards with s
  symm
  rw [← Real.sqrt_sq (norm_nonneg (suzukiDivisorFeature s - suzukiDivisorFeature t))]
  congr 1
  dsimp [S]
  rw [HilbertSchmidt.lp_norm_sq_eq]
  apply tsum_congr
  intro q
  rw [lp.coeFn_sub]
  rfl

def suzukiLeftFunctional (t : ℝ) : XiDivisorL2 →L[ℂ] ℂ :=
  InnerProductSpace.toDual ℂ XiDivisorL2 (star (suzukiDivisorFeature t))

def suzukiRightFunctional (u : ℝ) : XiDivisorL2 →L[ℂ] ℂ :=
  InnerProductSpace.toDual ℂ XiDivisorL2 (suzukiDivisorFeature (-u))

theorem suzukiLeftFunctional_apply (t : ℝ) (c : XiDivisorL2) :
    suzukiLeftFunctional t c =
      ∑' q : XiZeroCopy, suzukiDivisorFeatureCoord t q * c q := by
  rw [suzukiLeftFunctional]
  change inner ℂ (star (suzukiDivisorFeature t)) c = _
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro q
  simp only [lp.star_apply, suzukiDivisorFeature_apply, RCLike.inner_apply]
  simp [mul_comm]

theorem suzukiRightFunctional_apply (u : ℝ) (c : XiDivisorL2) :
    suzukiRightFunctional u c =
      ∑' q : XiZeroCopy,
        (starRingEnd ℂ) (suzukiDivisorFeatureCoord (-u) q) * c q := by
  rw [suzukiRightFunctional]
  change inner ℂ (suzukiDivisorFeature (-u)) c = _
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro q
  simp only [suzukiDivisorFeature_apply, RCLike.inner_apply]
  simp [mul_comm]

theorem continuous_suzukiLeftFunctional : Continuous suzukiLeftFunctional := by
  unfold suzukiLeftFunctional
  exact (InnerProductSpace.toDual ℂ XiDivisorL2).continuous.comp
    ((continuous_star : Continuous (star : XiDivisorL2 → XiDivisorL2)).comp
      continuous_suzukiDivisorFeature)

theorem continuous_suzukiRightFunctional : Continuous suzukiRightFunctional := by
  unfold suzukiRightFunctional
  exact (InnerProductSpace.toDual ℂ XiDivisorL2).continuous.comp
    (continuous_suzukiDivisorFeature.comp continuous_neg)

abbrev SuzukiApertureInterval (a : ℝ) := ClosedInterval (-a) a

attribute [local instance] Measure.Subtype.measureSpace

abbrev SuzukiApertureIntervalL2 (a : ℝ) : Type :=
  Lp ℂ 2 (volume : Measure (SuzukiApertureInterval a))

def suzukiLeftFunctionalContinuous (a : ℝ) :
    C(SuzukiApertureInterval a, XiDivisorL2 →L[ℂ] ℂ) where
  toFun t := suzukiLeftFunctional t
  continuous_toFun := continuous_suzukiLeftFunctional.comp continuous_subtype_val

def suzukiRightFunctionalContinuous (a : ℝ) :
    C(SuzukiApertureInterval a, XiDivisorL2 →L[ℂ] ℂ) where
  toFun u := suzukiRightFunctional u
  continuous_toFun := continuous_suzukiRightFunctional.comp continuous_subtype_val

def suzukiLeftFunctionalField (a : ℝ) :
    Lp (XiDivisorL2 →L[ℂ] ℂ) 2
      (volume : Measure (SuzukiApertureInterval a)) :=
  ContinuousMap.toLp 2 (volume : Measure (SuzukiApertureInterval a)) ℂ
    (suzukiLeftFunctionalContinuous a)

def suzukiRightFunctionalField (a : ℝ) :
    Lp (XiDivisorL2 →L[ℂ] ℂ) 2
      (volume : Measure (SuzukiApertureInterval a)) :=
  ContinuousMap.toLp 2 (volume : Measure (SuzukiApertureInterval a)) ℂ
    (suzukiRightFunctionalContinuous a)

def suzukiLeftSynthesis (a : ℝ) :
    XiDivisorL2 →L[ℂ] SuzukiApertureIntervalL2 a :=
  kernelOperator (volume : Measure (SuzukiApertureInterval a))
    (suzukiLeftFunctionalField a)

def suzukiRightSynthesis (a : ℝ) :
    XiDivisorL2 →L[ℂ] SuzukiApertureIntervalL2 a :=
  kernelOperator (volume : Measure (SuzukiApertureInterval a))
    (suzukiRightFunctionalField a)

def suzukiScrewIntegralOperator (a : ℝ) : SuzukiApertureIntervalL2 a →L[ℂ] SuzukiApertureIntervalL2 a :=
  suzukiLeftSynthesis a ∘L ContinuousLinearMap.adjoint (suzukiRightSynthesis a)

theorem suzukiLeftSynthesis_coeFn (a : ℝ) (c : XiDivisorL2) :
    (suzukiLeftSynthesis a c : SuzukiApertureInterval a → ℂ) =ᵐ[volume]
      fun t => suzukiLeftFunctional t c := by
  filter_upwards [
    (evalBilinear (𝕜 := ℂ) (E := XiDivisorL2)).coeFn_holder
      (r := (2 : ENNReal)) (suzukiLeftFunctionalField a)
      (Lp.const ∞ (volume : Measure (SuzukiApertureInterval a)) c),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure (SuzukiApertureInterval a)))
      (suzukiLeftFunctionalContinuous a),
    Lp.coeFn_const (p := ∞) (volume : Measure (SuzukiApertureInterval a)) c
  ] with t hholder hfield hconst
  rw [suzukiLeftSynthesis, kernelOperator, kernelOperatorMap_apply,
    hholder, suzukiLeftFunctionalField, hfield, hconst]
  rfl

theorem suzukiRightSynthesis_coeFn (a : ℝ) (c : XiDivisorL2) :
    (suzukiRightSynthesis a c : SuzukiApertureInterval a → ℂ) =ᵐ[volume]
      fun u => suzukiRightFunctional u c := by
  filter_upwards [
    (evalBilinear (𝕜 := ℂ) (E := XiDivisorL2)).coeFn_holder
      (r := (2 : ENNReal)) (suzukiRightFunctionalField a)
      (Lp.const ∞ (volume : Measure (SuzukiApertureInterval a)) c),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure (SuzukiApertureInterval a)))
      (suzukiRightFunctionalContinuous a),
    Lp.coeFn_const (p := ∞) (volume : Measure (SuzukiApertureInterval a)) c
  ] with u hholder hfield hconst
  rw [suzukiRightSynthesis, kernelOperator, kernelOperatorMap_apply,
    hholder, suzukiRightFunctionalField, hfield, hconst]
  rfl

theorem suzukiLeftFunctional_single (t : ℝ) (q : XiZeroCopy) :
    suzukiLeftFunctional t (lp.single 2 q (1 : ℂ)) = suzukiDivisorFeatureCoord t q := by
  rw [suzukiLeftFunctional]
  change inner ℂ (star (suzukiDivisorFeature t)) (lp.single 2 q (1 : ℂ)) = _
  rw [lp.inner_single_right]
  simp [suzukiDivisorFeature_apply]

theorem suzukiRightFunctional_single (u : ℝ) (q : XiZeroCopy) :
    suzukiRightFunctional u (lp.single 2 q (1 : ℂ)) =
      (starRingEnd ℂ) (suzukiDivisorFeatureCoord (-u) q) := by
  rw [suzukiRightFunctional]
  change inner ℂ (suzukiDivisorFeature (-u)) (lp.single 2 q (1 : ℂ)) = _
  rw [lp.inner_single_right]
  simp [suzukiDivisorFeature_apply]

theorem adjoint_suzukiRightSynthesis_apply
    (a : ℝ) (f : SuzukiApertureIntervalL2 a) (q : XiZeroCopy) :
    (ContinuousLinearMap.adjoint (suzukiRightSynthesis a) f) q =
      ∫ u : SuzukiApertureInterval a, suzukiDivisorFeatureCoord (-(u : ℝ)) q * f u ∂volume := by
  have h := ContinuousLinearMap.adjoint_inner_right (suzukiRightSynthesis a)
    (lp.single 2 q (1 : ℂ)) f
  rw [lp.inner_single_left, MeasureTheory.L2.inner_def] at h
  have hleft : inner ℂ (1 : ℂ)
      ((ContinuousLinearMap.adjoint (suzukiRightSynthesis a) f) q) =
      (ContinuousLinearMap.adjoint (suzukiRightSynthesis a) f) q := by
    simp
  rw [hleft] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [suzukiRightSynthesis_coeFn a (lp.single 2 q (1 : ℂ))] with u hu
  rw [hu, suzukiRightFunctional_single]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_star]
  ring

theorem suzukiScrewIntegralOperator_isTraceClass (a : ℝ) :
    (suzukiScrewIntegralOperator a).IsTraceClass := by
  rw [suzukiScrewIntegralOperator]
  exact (memSchattenClass_one_comp
    (isHilbertSchmidt_kernelOperator _ _)
    (isHilbertSchmidt_kernelOperator _ _).adjoint).one_isTraceClass

theorem suzukiDivisorFeatureCoord_mul_eq_kernelTerm (t u : ℝ) (q : XiZeroCopy) :
    suzukiDivisorFeatureCoord t q * suzukiDivisorFeatureCoord (-u) q =
      xiScrewKernelExponentialTerm t u q := by
  have hq : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  rw [suzukiDivisorFeatureCoord, suzukiDivisorFeatureCoord, xiScrewKernelExponentialTerm]
  have hneg :
      Complex.exp (I * xiSpectralPoint q * ((-u : ℝ) : ℂ)) =
        Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) := by
    congr 1
    push_cast
    ring
  rw [hneg]
  field_simp [hq]

theorem suzukiKernelTerm_mul_integrable
    {a : ℝ} (ha : 0 ≤ a) (f : SuzukiApertureIntervalL2 a)
    (t : SuzukiApertureInterval a) (q : XiZeroCopy) :
    Integrable (fun u : SuzukiApertureInterval a =>
      xiScrewKernelExponentialTerm (t : ℝ) (u : ℝ) q * f u) := by
  have hfint : Integrable (fun u : SuzukiApertureInterval a => f u) :=
    (Lp.memLp f).integrable (by norm_num)
  apply hfint.bdd_mul
  · unfold xiScrewKernelExponentialTerm
    fun_prop
  · filter_upwards with u
    exact norm_xiScrewKernelExponentialTerm_le_of_mem_Icc
      ha t.property u.property q

theorem suzukiKernelTerm_integral_norm_summable
    {a : ℝ} (ha : 0 ≤ a) (f : SuzukiApertureIntervalL2 a)
    (t : SuzukiApertureInterval a) :
    Summable (fun q : XiZeroCopy => ∫ u : SuzukiApertureInterval a,
      ‖xiScrewKernelExponentialTerm (t : ℝ) (u : ℝ) q * f u‖ ∂volume) := by
  have hfint : Integrable (fun u : SuzukiApertureInterval a => f u) :=
    (Lp.memLp f).integrable (by norm_num)
  let C : ℝ := (Real.exp (a / 2) + 1) ^ 2
  apply Summable.of_nonneg_of_le (fun q => integral_nonneg fun _ => norm_nonneg _)
    (fun q => ?_) (xiSpectralPoint_inv_sq_summable.mul_left
      (C * ∫ u : SuzukiApertureInterval a, ‖f u‖ ∂volume))
  calc
    (∫ u : SuzukiApertureInterval a,
        ‖xiScrewKernelExponentialTerm (t : ℝ) (u : ℝ) q * f u‖ ∂volume) ≤
      ∫ u : SuzukiApertureInterval a,
        (C * (1 / ‖xiSpectralPoint q‖ ^ 2)) * ‖f u‖ ∂volume := by
          apply integral_mono_ae
          · exact (suzukiKernelTerm_mul_integrable ha f t q).norm
          · exact hfint.norm.const_mul _
          · filter_upwards with u
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right
              (norm_xiScrewKernelExponentialTerm_le_of_mem_Icc
                ha t.property u.property q) (norm_nonneg _)
    _ = (C * (1 / ‖xiSpectralPoint q‖ ^ 2)) *
        ∫ u : SuzukiApertureInterval a, ‖f u‖ ∂volume := by
          rw [integral_const_mul]
    _ = (C * ∫ u : SuzukiApertureInterval a, ‖f u‖ ∂volume) *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring

theorem suzukiKernelTerm_tsum_integral
    {a : ℝ} (ha : 0 ≤ a) (f : SuzukiApertureIntervalL2 a)
    (t : SuzukiApertureInterval a) :
    (∑' q : XiZeroCopy, ∫ u : SuzukiApertureInterval a,
      xiScrewKernelExponentialTerm (t : ℝ) (u : ℝ) q * f u ∂volume) =
      ∫ u : SuzukiApertureInterval a,
        suzukiScrewKernel (t : ℝ) (u : ℝ) * f u ∂volume := by
  rw [integral_tsum_of_summable_integral_norm
    (suzukiKernelTerm_mul_integrable ha f t)
    (suzukiKernelTerm_integral_norm_summable ha f t)]
  apply integral_congr_ae
  filter_upwards with u
  rw [suzukiScrewKernel_eq_tsum_exponential, tsum_mul_right]

theorem suzukiScrewIntegralOperator_coeFn
    {a : ℝ} (ha : 0 ≤ a) (f : SuzukiApertureIntervalL2 a) :
    (suzukiScrewIntegralOperator a f : SuzukiApertureInterval a → ℂ) =ᵐ[volume]
      fun t => ∫ u : SuzukiApertureInterval a,
        suzukiScrewKernel (t : ℝ) (u : ℝ) * f u ∂volume := by
  change
    (suzukiLeftSynthesis a
        (ContinuousLinearMap.adjoint (suzukiRightSynthesis a) f) :
      SuzukiApertureInterval a → ℂ) =ᵐ[volume] _
  filter_upwards [suzukiLeftSynthesis_coeFn a
    (ContinuousLinearMap.adjoint (suzukiRightSynthesis a) f)] with t ht
  rw [ht, suzukiLeftFunctional_apply]
  calc
    (∑' q : XiZeroCopy, suzukiDivisorFeatureCoord (t : ℝ) q *
        (ContinuousLinearMap.adjoint (suzukiRightSynthesis a) f) q) =
      ∑' q : XiZeroCopy, suzukiDivisorFeatureCoord (t : ℝ) q *
        (∫ u : SuzukiApertureInterval a, suzukiDivisorFeatureCoord (-(u : ℝ)) q * f u ∂volume) := by
          apply tsum_congr
          intro q
          rw [adjoint_suzukiRightSynthesis_apply]
    _ = ∑' q : XiZeroCopy, ∫ u : SuzukiApertureInterval a,
        xiScrewKernelExponentialTerm (t : ℝ) (u : ℝ) q * f u ∂volume := by
          apply tsum_congr
          intro q
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with u
          rw [← mul_assoc, suzukiDivisorFeatureCoord_mul_eq_kernelTerm]
    _ = ∫ u : SuzukiApertureInterval a,
        suzukiScrewKernel (t : ℝ) (u : ℝ) * f u ∂volume :=
      suzukiKernelTerm_tsum_integral ha f t

/-- **Suzuki (2022), Theorem 1.5.** For every positive aperture, the literal integral
operator with kernel `G_g(t,u)` from equations (1.9)--(1.10) is trace class on
`L²([-a,a])`. This statement is unconditional: no Riemann-hypothesis assumption enters. -/
theorem suzuki_theorem_one_five {a : ℝ} (_ha : 0 < a) :
    (suzukiScrewIntegralOperator a).IsTraceClass :=
  suzukiScrewIntegralOperator_isTraceClass a

/-- Pointwise realization certifying that the operator in Suzuki's Theorem 1.5 is his
literal equation (1.10), not merely an abstract trace-class proxy. -/
theorem suzuki_theorem_one_five_kernel_formula {a : ℝ} (ha : 0 < a)
    (f : SuzukiApertureIntervalL2 a) :
    (suzukiScrewIntegralOperator a f : SuzukiApertureInterval a → ℂ) =ᵐ[volume]
      fun t => ∫ u : SuzukiApertureInterval a,
        suzukiScrewKernel (t : ℝ) (u : ℝ) * f u ∂volume :=
  suzukiScrewIntegralOperator_coeFn ha.le f

end RHTower
