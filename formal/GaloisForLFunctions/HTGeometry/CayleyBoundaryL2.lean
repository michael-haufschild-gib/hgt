import GaloisForLFunctions.HTGeometry.CircleFourierDensityUniqueness
import GaloisForLFunctions.HTGeometry.HardyDiskLineMultiplierTransport
import GaloisForLFunctions.HTGeometry.ProjectiveLabelNullPreimage
import GaloisForLFunctions.HTGeometry.WeightedDensityL2
import GaloisForLFunctions.HTGeometry.SummableCircleFourierDensity
import GaloisForLFunctions.HTGeometry.InfiniteSupportCayleyGram

/-!
# Exact circle-to-line Cayley boundary isometry

The standard Cauchy probability measure on the real line pushes forward under
`x ↦ (x - i)/(x + i)` to normalized circle Haar measure.  Multiplying its pullback by the
positive square-root density and the analytic unimodular phase gives the classical Hardy
half-density

`f ↦ π⁻¹ᐒ² (x + i)⁻¹ f((x - i)/(x + i))`.

The construction is an exact linear isometry on `L²`, and it intertwines every bounded measurable
circle multiplier with the literal pulled-back multiplier on the real line.
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal lp InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Lebesgue density of the standard Cauchy probability measure. -/
def standardCauchyWeight (x : ℝ) : ℝ :=
  1 / (Real.pi * (1 + x ^ 2))

theorem measurable_standardCauchyWeight : Measurable standardCauchyWeight := by
  unfold standardCauchyWeight
  fun_prop

theorem standardCauchyWeight_pos (x : ℝ) : 0 < standardCauchyWeight x := by
  unfold standardCauchyWeight
  positivity

/-- The standard Cauchy probability is the explicit positive-density Lebesgue measure. -/
theorem standardCauchyMeasure_eq_withDensity :
    ProbabilityTheory.cauchyMeasure 0 1 =
      (volume : Measure ℝ).withDensity (realDensity standardCauchyWeight) := by
  rw [ProbabilityTheory.cauchyMeasure_of_scale_ne_zero 0 (γ := 1) (by norm_num)]
  congr 1
  funext x
  rw [ProbabilityTheory.cauchyPDF, realDensity]
  congr 1
  simp only [ProbabilityTheory.cauchyPDFReal, NNReal.coe_one, sub_zero,
    one_pow, mul_one]
  rw [standardCauchyWeight]
  field_simp
  ring

local instance : CompleteSpace UpperHardyL2 :=
  RHTower.isClosed_hardyL2.completeSpace_coe

def cayleyBaseFeature : UpperHardyL2 :=
  lowerCauchyFeatureAt I (by simp)

def cayleyHardyShift : UpperHardyL2 →L[ℂ] UpperHardyL2 :=
  upperHardyInnerBlaschke I (by simp)

theorem coe_cayleyBaseFeature :
    ((((cayleyBaseFeature : UpperHardyL2) : RealLineL2) : ℝ → ℂ))
      =ᵐ[volume] fun x => (((x : ℝ) : ℂ) + I)⁻¹ := by
  simpa [cayleyBaseFeature] using
    (coe_lowerCauchyFeatureAt (w := I) (by simp))

theorem coe_cayleyHardyShift_pow (n : ℕ) :
    (((((cayleyHardyShift ^ n) cayleyBaseFeature : UpperHardyL2) :
        RealLineL2) : ℝ → ℂ)) =ᵐ[volume]
      fun x => realCayley x ^ n * (((x : ℝ) : ℂ) + I)⁻¹ := by
  induction n with
  | zero =>
      simpa using coe_cayleyBaseFeature
  | succ n ih =>
      rw [pow_succ']
      change ((((cayleyHardyShift
        ((cayleyHardyShift ^ n) cayleyBaseFeature) : UpperHardyL2) :
          RealLineL2) : ℝ → ℂ)) =ᵐ[volume] _
      filter_upwards [RHTower.coeFn_blaschkeMulInv I
          ((((cayleyHardyShift ^ n) cayleyBaseFeature : UpperHardyL2) :
            RealLineL2)), ih] with x hmul hn
      rw [show ((cayleyHardyShift
          ((cayleyHardyShift ^ n) cayleyBaseFeature) : UpperHardyL2) :
            RealLineL2) x =
          RHTower.blaschkeMulInv I
            ((((cayleyHardyShift ^ n) cayleyBaseFeature : UpperHardyL2) :
              RealLineL2)) x from rfl,
        hmul, hn, RHTower.blaschkeSymbolInv]
      rw [show (starRingEnd ℂ) I = -I by simp]
      rw [sub_neg_eq_add]
      change realCayley x *
          (realCayley x ^ n * ((x : ℂ) + I)⁻¹) = _
      rw [pow_succ']
      ring

theorem inner_cayleyBaseFeature_shift_pow_succ (n : ℕ) :
    inner ℂ cayleyBaseFeature
      ((cayleyHardyShift ^ (n + 1)) cayleyBaseFeature) = 0 := by
  rw [pow_succ']
  change upperHardyCauchyEval I (by simp)
      (upperHardyInnerBlaschke I (by simp)
        ((cayleyHardyShift ^ n) cayleyBaseFeature)) = 0
  let p : UpperHalfPlanePoint := ⟨I, by simp⟩
  have h := upperHardyCauchyEval_upperHardyInnerBlaschke p p
    ((cayleyHardyShift ^ n) cayleyBaseFeature)
  change upperHardyCauchyEval I (by simp)
      (upperHardyInnerBlaschke I (by simp)
        ((cayleyHardyShift ^ n) cayleyBaseFeature)) = _ at h
  rw [h]
  simp [upperHalfPlaneBlaschkeFactor]

theorem integral_realCayley_pow_div_one_add_sq (n : ℕ) :
    (∫ x : ℝ, realCayley x ^ (n + 1) / (1 + x ^ 2)) = 0 := by
  have hinner := inner_cayleyBaseFeature_shift_pow_succ n
  change inner ℂ (lowerCauchyFeatureAt I (by simp))
      ((cayleyHardyShift ^ (n + 1)) cayleyBaseFeature) = 0 at hinner
  rw [inner_lowerCauchyFeatureAt] at hinner
  have hcoe := coe_cayleyHardyShift_pow (n + 1)
  have hintegral : (∫ x : ℝ,
      (((((cayleyHardyShift ^ (n + 1)) cayleyBaseFeature : UpperHardyL2) :
        RealLineL2) : ℝ → ℂ) x /
          (((x : ℝ) : ℂ) - I))) =
      (∫ x : ℝ, realCayley x ^ (n + 1) / (1 + x ^ 2)) := by
    apply integral_congr_ae
    filter_upwards [hcoe] with x hx
    rw [hx]
    have hp : ((x : ℂ) + I) ≠ 0 := real_add_I_ne_zero x
    have hm : ((x : ℂ) - I) ≠ 0 := by
      intro hz
      have him := congrArg Complex.im hz
      norm_num at him
    have hfactor : ((x : ℂ) + I) * ((x : ℂ) - I) =
        1 + (x : ℂ) ^ 2 := by
      apply Complex.ext
      · norm_num [pow_two]
        ring
      · norm_num [pow_two]
    have hrc : (1 : ℂ) + (x : ℂ) ^ 2 ≠ 0 := by
      rw [← hfactor]
      exact mul_ne_zero hp hm
    field_simp [hp, hm, hrc]
    rw [mul_assoc, hfactor]
  rw [hintegral] at hinner
  exact hinner

/-- Every positive Cayley moment of the standard Cauchy law vanishes. -/
theorem integral_realCayley_pow_standardCauchy (n : ℕ) :
    (∫ x : ℝ, realCayley x ^ n
        ∂ProbabilityTheory.cauchyMeasure 0 1) =
      if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [standardCauchyMeasure_eq_withDensity,
      integral_withDensity_eq_integral_toReal_smul₀
        (measurable_realDensity measurable_standardCauchyWeight).aemeasurable
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [if_neg (Nat.succ_ne_zero m)]
    change (∫ x : ℝ,
      ((realDensity standardCauchyWeight x).toReal : ℝ) •
        realCayley x ^ (m + 1)) = 0
    simp only [realDensity, ENNReal.toReal_ofReal,
      (standardCauchyWeight_pos _).le]
    simp_rw [Complex.real_smul]
    rw [show (fun x : ℝ => standardCauchyWeight x * realCayley x ^ (m + 1)) =
        fun x => (Real.pi : ℂ)⁻¹ *
          (realCayley x ^ (m + 1) / (1 + x ^ 2)) by
      funext x
      rw [standardCauchyWeight]
      push_cast
      rw [one_div, mul_inv_rev]
      ring]
    rw [integral_const_mul, integral_realCayley_pow_div_one_add_sq, mul_zero]

/-- The real Cayley transform sends the standard Cauchy law exactly to normalized circle Haar. -/
theorem map_circleCayley_standardCauchy :
    Measure.map circleCayley (ProbabilityTheory.cauchyMeasure 0 1) =
      circleLebesgue := by
  letI : IsProbabilityMeasure
      (Measure.map circleCayley (ProbabilityTheory.cauchyMeasure 0 1)) :=
    Measure.isProbabilityMeasure_map
      continuous_circleCayley.measurable.aemeasurable
  apply circle_measure_eq_of_forall_zpow_integral_eq
  intro k
  have hcontinuous : Continuous (fun z : Circle => (z : ℂ) ^ k) := by
    cases k with
    | ofNat n => exact continuous_subtype_val.pow n
    | negSucc n =>
        rw [show (fun z : Circle => (z : ℂ) ^ (Int.negSucc n)) =
            fun z : Circle => ((starRingEnd ℂ) (z : ℂ)) ^ (n + 1) by
          funext z
          rw [zpow_negSucc, ← inv_pow,
            ← Complex.inv_eq_conj (Circle.norm_coe z)]]
        exact Complex.continuous_conj.comp continuous_subtype_val |>.pow (n + 1)
  rw [integral_map continuous_circleCayley.measurable.aemeasurable
    hcontinuous.aestronglyMeasurable,
    integral_circleLebesgue_coe_zpow]
  simp only [circleCayley_coe]
  rw [← cayleyMomentZ_eq_integral_zpow]
  cases k with
  | ofNat n =>
      rw [cayleyMomentZ, cayleyMoment]
      simpa using integral_realCayley_pow_standardCauchy n
  | negSucc n =>
      rw [cayleyMomentZ, cayleyMoment, integral_realCayley_pow_standardCauchy]
      simp

theorem circleCayley_measurePreserving :
    MeasurePreserving circleCayley
      (ProbabilityTheory.cauchyMeasure 0 1) circleLebesgue :=
  ⟨continuous_circleCayley.measurable, map_circleCayley_standardCauchy⟩

theorem circleCayley_weighted_measurePreserving :
    MeasurePreserving circleCayley
      ((volume : Measure ℝ).withDensity (realDensity standardCauchyWeight))
      circleLebesgue := by
  refine ⟨continuous_circleCayley.measurable, ?_⟩
  rw [← standardCauchyMeasure_eq_withDensity]
  exact map_circleCayley_standardCauchy

/-- Pullback by the Cayley map into the standard-Cauchy weighted line. -/
def circleCayleyWeightedPullback :
    Lp ℂ 2 circleLebesgue →ₗᵢ[ℂ]
      WeightedL2 (μ := (volume : Measure ℝ)) standardCauchyWeight :=
  Lp.compMeasurePreservingₗᵢ ℂ circleCayley
    circleCayley_weighted_measurePreserving

theorem circleCayleyWeightedPullback_ae (f : Lp ℂ 2 circleLebesgue) :
    circleCayleyWeightedPullback f =ᵐ[volume]
      fun x => f (circleCayley x) := by
  exact (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
    standardCauchyWeight_pos).mp
      (Lp.coeFn_compMeasurePreserving f circleCayley_weighted_measurePreserving)

/-- Unimodular analytic half-density phase for the upper-half-plane Cayley transform. -/
def cayleyHardyPhase (x : ℝ) : ℂ :=
  (Real.sqrt (1 + x ^ 2) : ℂ) * (((x : ℝ) : ℂ) + I)⁻¹

theorem continuous_cayleyHardyPhase : Continuous cayleyHardyPhase := by
  unfold cayleyHardyPhase
  have hnum : Continuous (fun x : ℝ => (Real.sqrt (1 + x ^ 2) : ℂ)) := by
    fun_prop
  have hden : Continuous (fun x : ℝ => (((x : ℝ) : ℂ) + I)⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · exact fun x => real_add_I_ne_zero x
  exact hnum.mul hden

@[simp] theorem norm_cayleyHardyPhase (x : ℝ) :
    ‖cayleyHardyPhase x‖ = 1 := by
  unfold cayleyHardyPhase
  rw [norm_mul, norm_inv]
  have hpos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_def]
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, I_re, add_zero,
    Complex.add_im, Complex.ofReal_im, I_im, zero_add]
  have hsqrt : Real.sqrt (x * x + 1 * 1) = Real.sqrt (1 + x ^ 2) := by
    congr 1
    ring
  rw [hsqrt]
  exact mul_inv_cancel₀ hpos.ne'

theorem cayleyHardyPhase_mul_sqrtWeight (x : ℝ) :
    cayleyHardyPhase x * sqrtWeight standardCauchyWeight x =
      (Real.sqrt Real.pi : ℂ)⁻¹ * (((x : ℝ) : ℂ) + I)⁻¹ := by
  have hA : 0 ≤ 1 + x ^ 2 := by positivity
  have hden : Real.pi * (1 + x ^ 2) ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero (by positivity)
  have hreal : Real.sqrt (1 + x ^ 2) *
      Real.sqrt (1 / (Real.pi * (1 + x ^ 2))) =
        (Real.sqrt Real.pi)⁻¹ := by
    rw [← Real.sqrt_mul hA]
    have hmul : (1 + x ^ 2) * (1 / (Real.pi * (1 + x ^ 2))) =
        Real.pi⁻¹ := by
      field_simp [hden]
    rw [hmul, Real.sqrt_inv]
  unfold cayleyHardyPhase sqrtWeight standardCauchyWeight
  calc
    ((Real.sqrt (1 + x ^ 2) : ℂ) * (((x : ℝ) : ℂ) + I)⁻¹) *
        (Real.sqrt (1 / (Real.pi * (1 + x ^ 2))) : ℂ) =
      ((Real.sqrt (1 + x ^ 2) *
        Real.sqrt (1 / (Real.pi * (1 + x ^ 2))) : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) + I)⁻¹ := by push_cast; ring
    _ = (Real.sqrt Real.pi : ℂ)⁻¹ * (((x : ℝ) : ℂ) + I)⁻¹ := by
      rw [hreal]
      push_cast
      rfl

/-- Cayley pullback followed by the positive density and analytic phase factors. -/
def circleLineCayleyIsometry :
    Lp ℂ 2 circleLebesgue →ₗᵢ[ℂ] RealLineL2 :=
  (RHTower.unimodularMulUnitary cayleyHardyPhase
      continuous_cayleyHardyPhase.aestronglyMeasurable norm_cayleyHardyPhase).toLinearIsometry.comp
    ((weightedDensityUnitary standardCauchyWeight measurable_standardCauchyWeight
      standardCauchyWeight_pos).toLinearIsometry.comp circleCayleyWeightedPullback)

theorem circleLineCayleyIsometry_ae (f : Lp ℂ 2 circleLebesgue) :
    circleLineCayleyIsometry f =ᵐ[volume] fun x =>
      cayleyHardyPhase x * sqrtWeight standardCauchyWeight x *
        f (circleCayley x) := by
  filter_upwards [
    RHTower.unimodularMulUnitary_ae cayleyHardyPhase
      continuous_cayleyHardyPhase.aestronglyMeasurable norm_cayleyHardyPhase
      ((weightedDensityUnitary standardCauchyWeight measurable_standardCauchyWeight
        standardCauchyWeight_pos)
        (circleCayleyWeightedPullback f)),
    densityMul_ae standardCauchyWeight measurable_standardCauchyWeight
      standardCauchyWeight_pos (circleCayleyWeightedPullback f),
    circleCayleyWeightedPullback_ae f] with x hphase hdensity hpull
  rw [show circleLineCayleyIsometry f x =
      RHTower.unimodularMulUnitary cayleyHardyPhase
        continuous_cayleyHardyPhase.aestronglyMeasurable norm_cayleyHardyPhase
        ((weightedDensityUnitary standardCauchyWeight measurable_standardCauchyWeight
          standardCauchyWeight_pos) (circleCayleyWeightedPullback f)) x from rfl,
    hphase]
  change cayleyHardyPhase x *
      densityMul standardCauchyWeight measurable_standardCauchyWeight
        standardCauchyWeight_pos (circleCayleyWeightedPullback f) x = _
  rw [hdensity, hpull]
  ring

/-- Pointwise classical half-density formula for the Cayley isometry. -/
theorem circleLineCayleyIsometry_ae_explicit (f : Lp ℂ 2 circleLebesgue) :
    circleLineCayleyIsometry f =ᵐ[volume] fun x =>
      (Real.sqrt Real.pi : ℂ)⁻¹ * (((x : ℝ) : ℂ) + I)⁻¹ *
        f (circleCayley x) := by
  filter_upwards [circleLineCayleyIsometry_ae f] with x hx
  rw [hx, cayleyHardyPhase_mul_sqrtWeight]

/-- Exact conjugation of bounded circle multipliers by the Cayley half-density isometry. -/
theorem circleLineCayleyIsometry_mul
    {φ : Circle → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ z, ‖φ z‖ ≤ C) (f : Lp ℂ 2 circleLebesgue) :
    circleLineCayleyIsometry
        (lpBoundedMulCLM (p := 2) (μ := circleLebesgue) hφ hC0 hC f) =
      lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
        (hφ.comp continuous_circleCayley.measurable) hC0
        (fun x => hC (circleCayley x)) (circleLineCayleyIsometry f) := by
  apply Lp.ext
  have hmulCircle := lpBoundedMulCLM_coeFn
    (p := 2) (μ := circleLebesgue) hφ hC0 hC f
  have hmulCircleCompWeighted := hmulCircle.comp_tendsto
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hmulCircleComp :
      (fun x => (lpBoundedMulCLM (p := 2) (μ := circleLebesgue)
          hφ hC0 hC f) (circleCayley x)) =ᵐ[volume]
        fun x => φ (circleCayley x) * f (circleCayley x) :=
    (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
      standardCauchyWeight_pos).mp hmulCircleCompWeighted
  filter_upwards [
    circleLineCayleyIsometry_ae_explicit
      (lpBoundedMulCLM (p := 2) (μ := circleLebesgue) hφ hC0 hC f),
    circleLineCayleyIsometry_ae_explicit f,
    hmulCircleComp,
    lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
      (hφ.comp continuous_circleCayley.measurable) hC0
      (fun x => hC (circleCayley x)) (circleLineCayleyIsometry f)]
      with x hleft hbase hcircle hright
  rw [hleft, hright, hcircle, hbase]
  simp only [Function.comp_apply]
  ring

end

end GaloisForLFunctions.HTGeometry
