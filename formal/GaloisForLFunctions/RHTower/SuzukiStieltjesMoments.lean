import GaloisForLFunctions.RHTower.SuzukiScrewGrowthBound
import GaloisForLFunctions.RHTower.SuzukiScrewSmoothTestCriterion
import GaloisForLFunctions.HTGeometry.HardyStieltjesDeterminacy
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Suzuki's literal Stieltjes moments

This module formalizes the moment sequence displayed in Suzuki (2022), Theorem 1.8:

`mu_n = ∫_0^∞ (1/4) exp (-t/2) Psi(t) t^n dt`.

The prime--Lerch growth theorem gives unconditional absolute integrability of every moment and a
Hardy square-root exponential window.  No positivity or RH assumption enters these analytic
facts.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Polynomial powers remain integrable against square-root exponential decay on `(0,∞)`. -/
theorem integrableOn_pow_mul_exp_neg_sqrt (n : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-c * Real.sqrt t)) (Ioi 0) := by
  rw [← integrableOn_Ioi_comp_rpow_iff
    (fun t : ℝ => t ^ n * Real.exp (-c * Real.sqrt t))
    (p := (2 : ℝ)) (by norm_num)]
  have hbase := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (2 * n + 1 : ℝ)) (b := c)
    (by nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity] :
      (-1 : ℝ) < (2 * n + 1 : ℝ))
    (by norm_num) hc
  apply IntegrableOn.congr_fun (hbase.const_mul 2) _ measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := hx
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp only [smul_eq_mul]
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    Real.rpow_two, Real.sqrt_sq_eq_abs, abs_of_pos hx0]
  have hexp : 2 * (n : ℝ) + 1 = ((2 * n + 1 : ℕ) : ℝ) := by norm_num
  rw [hexp, Real.rpow_natCast]
  ring

/-- Literal density in Suzuki's Theorem 1.8, before restricting to the positive half-line. -/
def suzukiStieltjesDensity (t : ℝ) : ℝ :=
  (1 / 4 : ℝ) * Real.exp (-t / 2) * suzukiPsi t

/-- Literal moment sequence in Suzuki's Theorem 1.8. -/
def suzukiStieltjesMoment (n : ℕ) : ℝ :=
  ∫ t : ℝ in Ioi 0, suzukiStieltjesDensity t * t ^ n

theorem continuous_suzukiStieltjesDensity : Continuous suzukiStieltjesDensity := by
  unfold suzukiStieltjesDensity
  exact (continuous_const.mul
    (Real.continuous_exp.comp (continuous_id.neg.div_const 2))).mul continuous_suzukiPsi

/-- Every literal Suzuki moment is absolutely integrable, unconditionally. -/
theorem integrableOn_suzukiStieltjesDensity_mul_pow (n : ℕ) :
    IntegrableOn (fun t : ℝ => suzukiStieltjesDensity t * t ^ n) (Ioi 0) := by
  obtain ⟨c, M, hc, hM, hbound⟩ := exists_abs_suzukiPsi_le_exp_half_sub_sqrt
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hbound
  let T : ℝ := max 1 T₀
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) (le_max_left 1 T₀)
  have hboundT : ∀ t ∈ Ioi T,
      |suzukiPsi t| ≤ M * Real.exp (t / 2 - c * Real.sqrt t) := by
    intro t ht
    exact hT₀ t ((le_max_right 1 T₀).trans ht.le)
  have hcont : Continuous (fun t : ℝ => suzukiStieltjesDensity t * t ^ n) :=
    continuous_suzukiStieltjesDensity.mul (continuous_id.pow n)
  have hcompact : IntegrableOn
      (fun t : ℝ => suzukiStieltjesDensity t * t ^ n) (Ioc 0 T) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmajor : IntegrableOn
      (fun t : ℝ => (M / 4) * (t ^ n * Real.exp (-c * Real.sqrt t))) (Ioi T) :=
    ((integrableOn_pow_mul_exp_neg_sqrt n hc).mono_set
      (Ioi_subset_Ioi hT.le)).const_mul (M / 4)
  have htail : IntegrableOn
      (fun t : ℝ => suzukiStieltjesDensity t * t ^ n) (Ioi T) := by
    apply Integrable.mono' hmajor hcont.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hT.trans ht
    have hscale : 0 ≤ (1 / 4 : ℝ) * Real.exp (-t / 2) * t ^ n := by positivity
    have hmul := mul_le_mul_of_nonneg_left (hboundT t ht) hscale
    rw [Real.norm_eq_abs, suzukiStieltjesDensity, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4),
      abs_of_pos (Real.exp_pos _), abs_of_pos (pow_pos ht0 n)]
    calc
      1 / 4 * Real.exp (-t / 2) * |suzukiPsi t| * t ^ n
          ≤ (1 / 4 * Real.exp (-t / 2) * t ^ n) *
            (M * Real.exp (t / 2 - c * Real.sqrt t)) := by
            simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = M / 4 * t ^ n *
          (Real.exp (-t / 2) * Real.exp (t / 2 - c * Real.sqrt t)) := by ring
      _ = M / 4 * (t ^ n * Real.exp (-c * Real.sqrt t)) := by
        rw [← Real.exp_add]
        rw [show -t / 2 + (t / 2 - c * Real.sqrt t) =
          -c * Real.sqrt t by ring]
        ring
  rw [← Ioc_union_Ioi_eq_Ioi hT.le]
  exact hcompact.union htail

theorem suzukiStieltjesMoment_integrable (n : ℕ) :
    IntegrableOn (fun t : ℝ => suzukiStieltjesDensity t * t ^ n) (Ioi 0) :=
  integrableOn_suzukiStieltjesDensity_mul_pow n

/-- Suzuki's literal signed density has the Hardy square-root exponential moment needed for
Stieltjes determinacy.  The absolute value makes this unconditional. -/
theorem exists_integrableOn_exp_sqrt_mul_abs_suzukiStieltjesDensity :
    ∃ d : ℝ, 0 < d ∧ IntegrableOn
      (fun t : ℝ => Real.exp (d * Real.sqrt t) * |suzukiStieltjesDensity t|) (Ioi 0) := by
  obtain ⟨c, M, hc, hM, hbound⟩ := exists_abs_suzukiPsi_le_exp_half_sub_sqrt
  let d : ℝ := c / 2
  have hd : 0 < d := div_pos hc (by norm_num)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hbound
  let T : ℝ := max 1 T₀
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) (le_max_left 1 T₀)
  have hboundT : ∀ t ∈ Ioi T,
      |suzukiPsi t| ≤ M * Real.exp (t / 2 - c * Real.sqrt t) := by
    intro t ht
    exact hT₀ t ((le_max_right 1 T₀).trans ht.le)
  let F : ℝ → ℝ := fun t =>
    Real.exp (d * Real.sqrt t) * |suzukiStieltjesDensity t|
  have hFcont : Continuous F := by
    dsimp only [F]
    exact (Real.continuous_exp.comp
      (continuous_const.mul Real.continuous_sqrt)).mul
        continuous_suzukiStieltjesDensity.abs
  have hcompact : IntegrableOn F (Ioc 0 T) :=
    hFcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmajor : IntegrableOn
      (fun t : ℝ => (M / 4) * Real.exp (-d * Real.sqrt t)) (Ioi T) := by
    have h := ((integrableOn_pow_mul_exp_neg_sqrt 0 hd).mono_set
      (Ioi_subset_Ioi hT.le)).const_mul (M / 4)
    change Integrable
      (fun t : ℝ => (M / 4) * Real.exp (-d * Real.sqrt t))
      (volume.restrict (Ioi T))
    simpa only [pow_zero, one_mul] using h
  have htail : IntegrableOn F (Ioi T) := by
    apply Integrable.mono' hmajor hFcont.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hT.trans ht
    have hscale : 0 ≤ Real.exp (d * Real.sqrt t) *
        ((1 / 4 : ℝ) * Real.exp (-t / 2)) := by positivity
    have hmul := mul_le_mul_of_nonneg_left (hboundT t ht) hscale
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.exp_nonneg _) (abs_nonneg _))]
    rw [suzukiStieltjesDensity]
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4),
      abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (d * Real.sqrt t) * (1 / 4 * Real.exp (-t / 2) *
          |suzukiPsi t|)
          ≤ (Real.exp (d * Real.sqrt t) *
              (1 / 4 * Real.exp (-t / 2))) *
            (M * Real.exp (t / 2 - c * Real.sqrt t)) := by
            simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = M / 4 * (Real.exp (d * Real.sqrt t) * Real.exp (-t / 2) *
          Real.exp (t / 2 - c * Real.sqrt t)) := by ring
      _ = M / 4 * Real.exp
          (d * Real.sqrt t + (-t / 2) + (t / 2 - c * Real.sqrt t)) := by
        rw [Real.exp_add, Real.exp_add]
      _ = M / 4 * Real.exp (-d * Real.sqrt t) := by
        dsimp only [d]
        congr 1
        ring
  refine ⟨d, hd, ?_⟩
  rw [← Ioc_union_Ioi_eq_Ioi hT.le]
  exact hcompact.union htail

/-! ## Positive and negative parts of the literal signed density -/

/-- Lebesgue measure restricted to Suzuki's source half-line. -/
def suzukiStieltjesBaseMeasure : Measure ℝ :=
  volume.restrict (Ioi 0)

/-- Positive-part measure of Suzuki's literal signed density. -/
def suzukiStieltjesPositiveMeasure : Measure ℝ :=
  suzukiStieltjesBaseMeasure.withDensity
    (fun t => ENNReal.ofReal (suzukiStieltjesDensity t))

/-- Negative-part measure of Suzuki's literal signed density. -/
def suzukiStieltjesNegativeMeasure : Measure ℝ :=
  suzukiStieltjesBaseMeasure.withDensity
    (fun t => ENNReal.ofReal (-suzukiStieltjesDensity t))

theorem integrable_suzukiStieltjesDensity_base :
    Integrable suzukiStieltjesDensity suzukiStieltjesBaseMeasure := by
  change IntegrableOn suzukiStieltjesDensity (Ioi 0)
  simpa only [pow_zero, mul_one] using suzukiStieltjesMoment_integrable 0

instance suzukiStieltjesPositiveMeasure.instIsFiniteMeasure :
    IsFiniteMeasure suzukiStieltjesPositiveMeasure := by
  unfold suzukiStieltjesPositiveMeasure
  exact isFiniteMeasure_withDensity_ofReal
    integrable_suzukiStieltjesDensity_base.hasFiniteIntegral

instance suzukiStieltjesNegativeMeasure.instIsFiniteMeasure :
    IsFiniteMeasure suzukiStieltjesNegativeMeasure := by
  unfold suzukiStieltjesNegativeMeasure
  exact isFiniteMeasure_withDensity_ofReal
    integrable_suzukiStieltjesDensity_base.neg.hasFiniteIntegral

theorem suzukiStieltjesPositiveMeasure_support :
    ∀ᵐ t ∂suzukiStieltjesPositiveMeasure, 0 ≤ t := by
  unfold suzukiStieltjesPositiveMeasure
  apply (ae_withDensity_iff
    continuous_suzukiStieltjesDensity.measurable.ennreal_ofReal).2
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact fun _ => ht.le

theorem suzukiStieltjesNegativeMeasure_support :
    ∀ᵐ t ∂suzukiStieltjesNegativeMeasure, 0 ≤ t := by
  unfold suzukiStieltjesNegativeMeasure
  apply (ae_withDensity_iff
    (continuous_suzukiStieltjesDensity.neg.measurable.ennreal_ofReal)).2
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact fun _ => ht.le

theorem integrable_pow_suzukiStieltjesPositiveMeasure (n : ℕ) :
    Integrable (fun t : ℝ => t ^ n) suzukiStieltjesPositiveMeasure := by
  unfold suzukiStieltjesPositiveMeasure
  rw [integrable_withDensity_iff_integrable_smul₀'
    continuous_suzukiStieltjesDensity.measurable.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal', smul_eq_mul]
  have hraw : Integrable (fun t : ℝ => suzukiStieltjesDensity t * t ^ n)
      suzukiStieltjesBaseMeasure := suzukiStieltjesMoment_integrable n
  apply Integrable.mono' hraw.norm
    ((continuous_suzukiStieltjesDensity.max continuous_const).mul
      (continuous_id.pow n)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    change |max (suzukiStieltjesDensity t) 0 * t ^ n| ≤
      |suzukiStieltjesDensity t * t ^ n|
    rw [abs_mul, abs_mul]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg (t ^ n))
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _))

theorem integrable_pow_suzukiStieltjesNegativeMeasure (n : ℕ) :
    Integrable (fun t : ℝ => t ^ n) suzukiStieltjesNegativeMeasure := by
  unfold suzukiStieltjesNegativeMeasure
  change Integrable (fun t : ℝ => t ^ n)
    (suzukiStieltjesBaseMeasure.withDensity
      (fun t => ENNReal.ofReal ((-suzukiStieltjesDensity) t)))
  rw [integrable_withDensity_iff_integrable_smul₀'
    continuous_suzukiStieltjesDensity.measurable.neg.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal', smul_eq_mul]
  have hraw : Integrable (fun t : ℝ => suzukiStieltjesDensity t * t ^ n)
      suzukiStieltjesBaseMeasure := suzukiStieltjesMoment_integrable n
  apply Integrable.mono' hraw.norm
    ((continuous_suzukiStieltjesDensity.neg.max continuous_const).mul
      (continuous_id.pow n)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    change |max (-suzukiStieltjesDensity t) 0 * t ^ n| ≤
      |suzukiStieltjesDensity t * t ^ n|
    rw [abs_mul, abs_mul]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg (t ^ n))
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _))

/-- Positive part minus negative part recovers Suzuki's literal signed moment. -/
theorem integral_pow_positive_sub_negative_eq_suzukiStieltjesMoment (n : ℕ) :
    (∫ t : ℝ, t ^ n ∂suzukiStieltjesPositiveMeasure) -
      (∫ t : ℝ, t ^ n ∂suzukiStieltjesNegativeMeasure) =
        suzukiStieltjesMoment n := by
  have hposBase : Integrable
      (fun t : ℝ => max (suzukiStieltjesDensity t) 0 * t ^ n)
      suzukiStieltjesBaseMeasure := by
    have h := integrable_pow_suzukiStieltjesPositiveMeasure n
    unfold suzukiStieltjesPositiveMeasure at h
    rw [integrable_withDensity_iff_integrable_smul₀'
      continuous_suzukiStieltjesDensity.measurable.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h
    simpa only [ENNReal.toReal_ofReal', smul_eq_mul] using h
  have hnegBase : Integrable
      (fun t : ℝ => max (-suzukiStieltjesDensity t) 0 * t ^ n)
      suzukiStieltjesBaseMeasure := by
    have h := integrable_pow_suzukiStieltjesNegativeMeasure n
    unfold suzukiStieltjesNegativeMeasure at h
    change Integrable (fun t : ℝ => t ^ n)
      (suzukiStieltjesBaseMeasure.withDensity
        (fun t => ENNReal.ofReal ((-suzukiStieltjesDensity) t))) at h
    rw [integrable_withDensity_iff_integrable_smul₀'
      continuous_suzukiStieltjesDensity.measurable.neg.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h
    simpa only [ENNReal.toReal_ofReal', Pi.neg_apply, smul_eq_mul] using h
  unfold suzukiStieltjesPositiveMeasure suzukiStieltjesNegativeMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀
    continuous_suzukiStieltjesDensity.measurable.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  change (∫ t : ℝ, max (suzukiStieltjesDensity t) 0 * t ^ n
      ∂suzukiStieltjesBaseMeasure) -
    (∫ t : ℝ, t ^ n ∂suzukiStieltjesBaseMeasure.withDensity
      (fun t => ENNReal.ofReal ((-suzukiStieltjesDensity) t))) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (continuous_suzukiStieltjesDensity.neg.measurable.ennreal_ofReal.aemeasurable)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal', smul_eq_mul]
  have hnegBase' : Integrable
      (fun t : ℝ => max ((-suzukiStieltjesDensity) t) 0 * t ^ n)
      suzukiStieltjesBaseMeasure := by
    simpa only [Pi.neg_apply] using hnegBase
  rw [← integral_sub hposBase hnegBase']
  unfold suzukiStieltjesMoment suzukiStieltjesBaseMeasure
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    change max (suzukiStieltjesDensity t) 0 * t ^ n -
      max (-suzukiStieltjesDensity t) 0 * t ^ n =
        suzukiStieltjesDensity t * t ^ n
    rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self])

/-- Both Jordan parts inherit Suzuki's Hardy window. -/
theorem exists_hardy_suzukiStieltjesPositiveMeasure :
    ∃ d : ℝ, 0 < d ∧ Integrable
      (fun t : ℝ => Real.exp (d * Real.sqrt t))
      suzukiStieltjesPositiveMeasure := by
  obtain ⟨d, hd, hAbs⟩ :=
    exists_integrableOn_exp_sqrt_mul_abs_suzukiStieltjesDensity
  refine ⟨d, hd, ?_⟩
  unfold suzukiStieltjesPositiveMeasure
  rw [integrable_withDensity_iff_integrable_smul₀'
    continuous_suzukiStieltjesDensity.measurable.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal', smul_eq_mul]
  apply Integrable.mono' hAbs
    ((continuous_suzukiStieltjesDensity.max continuous_const).mul
      (Real.continuous_exp.comp
        (continuous_const.mul Real.continuous_sqrt))).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    change |max (suzukiStieltjesDensity t) 0 * Real.exp (d * Real.sqrt t)| ≤
      Real.exp (d * Real.sqrt t) * |suzukiStieltjesDensity t|
    rw [abs_mul, abs_of_nonneg (le_max_right _ _),
      abs_of_pos (Real.exp_pos _)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (max_le (le_abs_self (suzukiStieltjesDensity t)) (abs_nonneg _))
      (Real.exp_nonneg (d * Real.sqrt t)))

theorem exists_hardy_suzukiStieltjesNegativeMeasure :
    ∃ d : ℝ, 0 < d ∧ Integrable
      (fun t : ℝ => Real.exp (d * Real.sqrt t))
      suzukiStieltjesNegativeMeasure := by
  obtain ⟨d, hd, hAbs⟩ :=
    exists_integrableOn_exp_sqrt_mul_abs_suzukiStieltjesDensity
  refine ⟨d, hd, ?_⟩
  unfold suzukiStieltjesNegativeMeasure
  change Integrable (fun t : ℝ => Real.exp (d * Real.sqrt t))
    (suzukiStieltjesBaseMeasure.withDensity
      (fun t => ENNReal.ofReal ((-suzukiStieltjesDensity) t)))
  rw [integrable_withDensity_iff_integrable_smul₀'
    continuous_suzukiStieltjesDensity.measurable.neg.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal', smul_eq_mul]
  apply Integrable.mono' hAbs
    ((continuous_suzukiStieltjesDensity.neg.max continuous_const).mul
      (Real.continuous_exp.comp
        (continuous_const.mul Real.continuous_sqrt))).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    change |max (-suzukiStieltjesDensity t) 0 * Real.exp (d * Real.sqrt t)| ≤
      Real.exp (d * Real.sqrt t) * |suzukiStieltjesDensity t|
    rw [abs_mul, abs_of_nonneg (le_max_right _ _),
      abs_of_pos (Real.exp_pos _)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (max_le (neg_le_abs (suzukiStieltjesDensity t)) (abs_nonneg _))
      (Real.exp_nonneg (d * Real.sqrt t)))

end RHTower
