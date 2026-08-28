import GaloisForLFunctions.RHTower.ThetaCarrierHassePacket
import GaloisForLFunctions.RHTower.ThetaCuspFourierLaplace
import GaloisForLFunctions.HTGeometry.ConstitutiveThetaHasseKMSExecutionBalance
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

open MeasureTheory Set Filter Real
open GaloisForLFunctions.HTGeometry
open InformationTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry
noncomputable def thetaTiltStatisticMoment (g : ℝ → ℝ) (a : ℝ) (k : ℕ) : ℝ :=
  ∫ x : ℝ, g x * x ^ k * Real.exp (a * x) * RHTower.thetaCuspFullSource x

noncomputable def thetaTiltStatisticMean (g : ℝ → ℝ) (a : ℝ) : ℝ :=
  thetaTiltStatisticMoment g a 0 / RHTower.thetaTiltMoment a 0

noncomputable def thetaTiltStatisticCovariance (g : ℝ → ℝ) (a : ℝ) : ℝ :=
  thetaTiltStatisticMoment g a 1 / RHTower.thetaTiltMoment a 0 -
    thetaTiltStatisticMean g a * RHTower.thetaTiltMean a

theorem integrable_thetaTiltStatisticIntegrand {g : ℝ → ℝ}
    (hgcont : Continuous g) {C : ℝ} (hg : ∀ x, ‖g x‖ ≤ C)
    {a : ℝ} (ha : |a| ≤ 1) (k : ℕ) :
    Integrable (fun x : ℝ =>
      g x * x ^ k * Real.exp (a * x) * RHTower.thetaCuspFullSource x) := by
  have hC : 0 ≤ C := le_trans (norm_nonneg (g 0)) (hg 0)
  have hmaj : Integrable (fun x : ℝ => C * RHTower.thetaTiltBound k x) :=
    (RHTower.integrable_thetaTiltBound k).const_mul C
  refine hmaj.mono
    (((hgcont.mul (continuous_id.pow k)).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
        RHTower.contDiff_thetaCuspFullSource.continuous).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hbase := RHTower.norm_thetaTiltIntegrand_le ha k x
  have hbound : 0 ≤ RHTower.thetaTiltBound k x := by
    unfold RHTower.thetaTiltBound
    exact add_nonneg
      (mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
        (RHTower.thetaCuspFullSource_pos_all _).le)
      (mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
        (RHTower.thetaCuspFullSource_pos_all _).le)
  calc
    ‖g x * x ^ k * Real.exp (a * x) * RHTower.thetaCuspFullSource x‖ =
        ‖g x‖ * ‖x ^ k * Real.exp (a * x) * RHTower.thetaCuspFullSource x‖ := by
          simp only [norm_mul]
          ring
    _ ≤ C * RHTower.thetaTiltBound k x :=
      mul_le_mul (hg x) hbase (norm_nonneg _) hC
    _ = ‖C * RHTower.thetaTiltBound k x‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC hbound)]

theorem hasDerivAt_thetaTiltStatisticMoment {g : ℝ → ℝ}
    (hgcont : Continuous g) {C : ℝ} (hg : ∀ x, ‖g x‖ ≤ C)
    {a : ℝ} (ha : |a| < 1) (k : ℕ) :
    HasDerivAt (fun t : ℝ => thetaTiltStatisticMoment g t k)
      (thetaTiltStatisticMoment g a (k + 1)) a := by
  set ε : ℝ := (1 - |a|) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hball : ∀ t ∈ Metric.ball a ε, |t| ≤ 1 := by
    intro t ht
    have hta : |t - a| < ε := by simpa [Real.dist_eq] using ht
    have habs : |t| - |a| ≤ |t - a| := abs_sub_abs_le_abs_sub t a
    linarith [habs, hta, hεpos]
  have hC : 0 ≤ C := le_trans (norm_nonneg (g 0)) (hg 0)
  have hmeas : ∀ᶠ t in nhds a, AEStronglyMeasurable
      (fun x : ℝ => g x * x ^ k * Real.exp (t * x) * RHTower.thetaCuspFullSource x) volume :=
    Filter.Eventually.of_forall fun t =>
      (((hgcont.mul (continuous_id.pow k)).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
          RHTower.contDiff_thetaCuspFullSource.continuous).aestronglyMeasurable
  have hint := integrable_thetaTiltStatisticIntegrand hgcont hg ha.le k
  have hmeas' : AEStronglyMeasurable
      (fun x : ℝ => g x * x ^ (k + 1) * Real.exp (a * x) *
        RHTower.thetaCuspFullSource x) volume :=
    (((hgcont.mul (continuous_id.pow (k + 1))).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
        RHTower.contDiff_thetaCuspFullSource.continuous).aestronglyMeasurable
  have hbound : ∀ᵐ x : ℝ, ∀ t ∈ Metric.ball a ε,
      ‖g x * x ^ (k + 1) * Real.exp (t * x) * RHTower.thetaCuspFullSource x‖ ≤
        C * RHTower.thetaTiltBound (k + 1) x := by
    filter_upwards with x t ht
    have hbase := RHTower.norm_thetaTiltIntegrand_le (hball t ht) (k + 1) x
    calc
      ‖g x * x ^ (k + 1) * Real.exp (t * x) * RHTower.thetaCuspFullSource x‖ =
          ‖g x‖ * ‖x ^ (k + 1) * Real.exp (t * x) * RHTower.thetaCuspFullSource x‖ := by
            simp only [norm_mul]
            ring
      _ ≤ C * RHTower.thetaTiltBound (k + 1) x :=
        mul_le_mul (hg x) hbase (norm_nonneg _) hC
  have hdiff : ∀ᵐ x : ℝ, ∀ t ∈ Metric.ball a ε,
      HasDerivAt
        (fun t : ℝ => g x * x ^ k * Real.exp (t * x) * RHTower.thetaCuspFullSource x)
        (g x * x ^ (k + 1) * Real.exp (t * x) * RHTower.thetaCuspFullSource x) t := by
    filter_upwards with x t ht
    have hlin : HasDerivAt (fun u : ℝ => u * x) x t := by
      simpa using (hasDerivAt_id t).mul_const x
    have hexp : HasDerivAt (fun u : ℝ => Real.exp (u * x)) (Real.exp (t * x) * x) t :=
      hlin.exp
    have h := (((hexp.const_mul (g x * x ^ k))).mul_const
      (RHTower.thetaCuspFullSource x))
    apply h.congr_deriv
    rw [pow_succ]
    ring
  have hnhds : Metric.ball a ε ∈ nhds a := Metric.ball_mem_nhds a hεpos
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => g x * x ^ k * Real.exp (t * x) * RHTower.thetaCuspFullSource x)
    (F' := fun t x => g x * x ^ (k + 1) * Real.exp (t * x) * RHTower.thetaCuspFullSource x)
    hnhds hmeas hint hmeas' hbound
    ((RHTower.integrable_thetaTiltBound (k + 1)).const_mul C) hdiff
  exact hres.2

theorem thetaTiltStatisticMean_eq_integral {g : ℝ → ℝ} {a : ℝ} (ha : |a| ≤ 1) :
    thetaTiltStatisticMean g a = ∫ x : ℝ, g x ∂(RHTower.thetaTiltProb a) := by
  rw [RHTower.integral_thetaTiltProb ha]
  unfold thetaTiltStatisticMean thetaTiltStatisticMoment
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

theorem hasDerivAt_thetaTiltStatisticMean {g : ℝ → ℝ}
    (hgcont : Continuous g) {C : ℝ} (hg : ∀ x, ‖g x‖ ≤ C)
    {a : ℝ} (ha : |a| < 1) :
    HasDerivAt (thetaTiltStatisticMean g) (thetaTiltStatisticCovariance g a) a := by
  have hN := hasDerivAt_thetaTiltStatisticMoment hgcont hg ha 0
  have hD := RHTower.hasDerivAt_thetaTiltMoment ha 0
  have hD0 := RHTower.thetaTiltMoment_zero_pos a ha.le
  have hdiv := hN.div hD hD0.ne'
  refine hdiv.congr_deriv ?_
  unfold thetaTiltStatisticCovariance thetaTiltStatisticMean RHTower.thetaTiltMean
  field_simp

theorem integral_pairDifference_eq_two_mul_covariance
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    (hg : Integrable g μ) (hx : Integrable (fun x : ℝ => x) μ)
    (hgx : Integrable (fun x : ℝ => g x * x) μ) :
    (∫ p : ℝ × ℝ, (g p.1 - g p.2) * (p.1 - p.2) ∂(μ.prod μ)) =
      2 * ((∫ x : ℝ, g x * x ∂μ) - (∫ x : ℝ, g x ∂μ) * ∫ x : ℝ, x ∂μ) := by
  let A : ℝ × ℝ → ℝ := fun p => (g p.1 * p.1) * 1
  let B : ℝ × ℝ → ℝ := fun p => g p.1 * p.2
  let C : ℝ × ℝ → ℝ := fun p => p.1 * g p.2
  let D : ℝ × ℝ → ℝ := fun p => 1 * (g p.2 * p.2)
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const 1
  have hA : Integrable A (μ.prod μ) := hgx.mul_prod h1
  have hB : Integrable B (μ.prod μ) := hg.mul_prod hx
  have hC : Integrable C (μ.prod μ) := hx.mul_prod hg
  have hD : Integrable D (μ.prod μ) := h1.mul_prod hgx
  have heq : (fun p : ℝ × ℝ => (g p.1 - g p.2) * (p.1 - p.2)) =
      fun p => (A p - B p) - C p + D p := by
    funext p
    simp only [A, B, C, D]
    ring
  rw [heq]
  calc
    (∫ p, A p - B p - C p + D p ∂(μ.prod μ)) =
        (∫ p, A p - B p - C p ∂(μ.prod μ)) +
          ∫ p, D p ∂(μ.prod μ) :=
      integral_add ((hA.sub hB).sub hC) hD
    _ = ((∫ p, A p ∂(μ.prod μ)) - (∫ p, B p ∂(μ.prod μ)) -
          ∫ p, C p ∂(μ.prod μ)) + ∫ p, D p ∂(μ.prod μ) := by
      congr 1
      calc
        (∫ p, A p - B p - C p ∂(μ.prod μ)) =
            (∫ p, A p - B p ∂(μ.prod μ)) - ∫ p, C p ∂(μ.prod μ) :=
          integral_sub (hA.sub hB) hC
        _ = ((∫ p, A p ∂(μ.prod μ)) - (∫ p, B p ∂(μ.prod μ))) -
            ∫ p, C p ∂(μ.prod μ) := by
          rw [integral_sub hA hB]
    _ = 2 * ((∫ x : ℝ, g x * x ∂μ) -
          (∫ x : ℝ, g x ∂μ) * ∫ x : ℝ, x ∂μ) := by
      rw [show (∫ p, A p ∂(μ.prod μ)) =
      (∫ x, g x * x ∂μ) * ∫ _ : ℝ, 1 ∂μ by
        exact MeasureTheory.integral_prod_mul (fun x => g x * x) (fun _ : ℝ => 1),
        show (∫ p, B p ∂(μ.prod μ)) =
      (∫ x, g x ∂μ) * ∫ x, x ∂μ by
        exact MeasureTheory.integral_prod_mul g (fun x : ℝ => x),
        show (∫ p, C p ∂(μ.prod μ)) =
      (∫ x, x ∂μ) * ∫ x, g x ∂μ by
        exact MeasureTheory.integral_prod_mul (fun x : ℝ => x) g,
        show (∫ p, D p ∂(μ.prod μ)) =
      (∫ _ : ℝ, 1 ∂μ) * ∫ x, g x * x ∂μ by
        exact MeasureTheory.integral_prod_mul (fun _ : ℝ => 1) (fun x => g x * x)]
      simp
      ring

theorem thetaTiltProb_Icc_pos {a u v : ℝ} (ha : |a| ≤ 1) (huv : u < v) :
    0 < RHTower.thetaTiltProb a (Set.Icc u v) := by
  rw [pos_iff_ne_zero]
  intro hzero
  rw [RHTower.thetaTiltProb_eq_withDensity ha] at hzero
  have hpos : ∀ᵐ x : ℝ ∂volume,
      ENNReal.ofReal
        (Real.exp (a * x) * RHTower.thetaCuspFullSource x /
          RHTower.thetaTiltMoment a 0) ≠ 0 := by
    filter_upwards with x
    apply ne_of_gt
    rw [ENNReal.ofReal_pos]
    exact div_pos
      (mul_pos (Real.exp_pos _) (RHTower.thetaCuspFullSource_pos x))
      (RHTower.thetaTiltMoment_zero_pos a ha)
  have hvol := (measure_withDensity_eq_zero_iff volume
    (RHTower.measurable_thetaTiltProbDensity a) hpos (Set.Icc u v)).mp hzero
  rw [Real.volume_Icc, ENNReal.ofReal_eq_zero] at hvol
  linarith

theorem covariance_pos_of_strictMono
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    (hmono : StrictMono g) (hg : Integrable g μ)
    (hx : Integrable (fun x : ℝ => x) μ)
    (hgx : Integrable (fun x : ℝ => g x * x) μ)
    (hpos : 0 < μ (Set.Icc (1 : ℝ) 2))
    (hneg : 0 < μ (Set.Icc (-2 : ℝ) (-1))) :
    0 < (∫ x : ℝ, g x * x ∂μ) - (∫ x : ℝ, g x ∂μ) * ∫ x : ℝ, x ∂μ := by
  let H : ℝ × ℝ → ℝ := fun p => (g p.1 - g p.2) * (p.1 - p.2)
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const 1
  have hA : Integrable (fun p : ℝ × ℝ => (g p.1 * p.1) * 1) (μ.prod μ) :=
    hgx.mul_prod h1
  have hB : Integrable (fun p : ℝ × ℝ => g p.1 * p.2) (μ.prod μ) :=
    hg.mul_prod hx
  have hC : Integrable (fun p : ℝ × ℝ => p.1 * g p.2) (μ.prod μ) :=
    hx.mul_prod hg
  have hD : Integrable (fun p : ℝ × ℝ => 1 * (g p.2 * p.2)) (μ.prod μ) :=
    h1.mul_prod hgx
  have hH : Integrable H (μ.prod μ) := by
    have heq : H = fun p =>
        (((g p.1 * p.1) * 1 - g p.1 * p.2) - p.1 * g p.2) +
          1 * (g p.2 * p.2) := by
      funext p
      simp only [H]
      ring
    rw [heq]
    exact (hA.sub hB |>.sub hC).add hD
  have hHnonneg : ∀ p, 0 ≤ H p := by
    rintro ⟨x, y⟩
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (hmono.monotone hlt.le)) (sub_nonpos.mpr hlt.le)
    · subst y
      simp [H]
    · exact mul_nonneg (sub_nonneg.mpr (hmono.monotone hgt.le)) (sub_nonneg.mpr hgt.le)
  have hrect : Set.Icc (1 : ℝ) 2 ×ˢ Set.Icc (-2 : ℝ) (-1) ⊆ Function.support H := by
    rintro ⟨x, y⟩ ⟨hxI, hyI⟩
    have hyx : y < x := by linarith [hxI.1, hyI.2]
    have hgxy : g y < g x := hmono hyx
    change H (x, y) ≠ 0
    exact ne_of_gt (mul_pos (sub_pos.mpr hgxy) (sub_pos.mpr hyx))
  have hrectpos : 0 < (μ.prod μ) (Set.Icc (1 : ℝ) 2 ×ˢ Set.Icc (-2 : ℝ) (-1)) := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_pos hpos.ne' hneg.ne'
  have hsupp : 0 < (μ.prod μ) (Function.support H) :=
    lt_of_lt_of_le hrectpos (measure_mono hrect)
  have hint : 0 < ∫ p, H p ∂(μ.prod μ) := by
    rw [integral_pos_iff_support_of_nonneg hHnonneg hH]
    exact hsupp
  rw [show (∫ p, H p ∂(μ.prod μ)) =
      2 * ((∫ x : ℝ, g x * x ∂μ) - (∫ x : ℝ, g x ∂μ) * ∫ x : ℝ, x ∂μ) by
    exact integral_pairDifference_eq_two_mul_covariance hg hx hgx] at hint
  nlinarith

theorem thetaTiltStatisticCovariance_eq_integral {g : ℝ → ℝ} {a : ℝ}
    (ha : |a| ≤ 1) :
    thetaTiltStatisticCovariance g a =
      (∫ x : ℝ, g x * x ∂(RHTower.thetaTiltProb a)) -
        (∫ x : ℝ, g x ∂(RHTower.thetaTiltProb a)) *
          ∫ x : ℝ, x ∂(RHTower.thetaTiltProb a) := by
  have hfirst : thetaTiltStatisticMoment g a 1 / RHTower.thetaTiltMoment a 0 =
      ∫ x : ℝ, g x * x ∂(RHTower.thetaTiltProb a) := by
    rw [RHTower.integral_thetaTiltProb ha]
    unfold thetaTiltStatisticMoment
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [thetaTiltStatisticCovariance, hfirst,
    thetaTiltStatisticMean_eq_integral ha, RHTower.integral_id_thetaTiltProb ha]

theorem thetaTiltStatisticCovariance_pos {g : ℝ → ℝ}
    (hmono : StrictMono g) (hgcont : Continuous g) {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C)
    {a : ℝ} (ha : |a| ≤ 1) : 0 < thetaTiltStatisticCovariance g a := by
  letI := RHTower.thetaTiltProb_isProbabilityMeasure ha
  have hgi : Integrable g (RHTower.thetaTiltProb a) := by
    apply RHTower.integrable_thetaTiltProb ha
    simpa [pow_zero] using integrable_thetaTiltStatisticIntegrand hgcont hgC ha 0
  have hxi := RHTower.integrable_id_thetaTiltProb ha
  have hgxi : Integrable (fun x : ℝ => g x * x) (RHTower.thetaTiltProb a) := by
    apply RHTower.integrable_thetaTiltProb ha
    simpa [pow_one] using integrable_thetaTiltStatisticIntegrand hgcont hgC ha 1
  rw [thetaTiltStatisticCovariance_eq_integral ha]
  exact covariance_pos_of_strictMono hmono hgi hxi hgxi
    (thetaTiltProb_Icc_pos ha (by norm_num))
    (thetaTiltProb_Icc_pos ha (by norm_num))

/-! ## Continuous theta averages of the two execution observables -/

noncomputable def thetaHasseExecutionTVStatistic (x : ℝ) : ℝ :=
  geometricExecutionTV (thetaHasseRatio x)

noncomputable def thetaHasseExecutionEntropyStatistic (x : ℝ) : ℝ :=
  geometricExecutionEntropy (thetaHasseRatio x)

noncomputable def thetaHasseExecutionTVAverage (a : ℝ) : ℝ :=
  thetaTiltStatisticMean thetaHasseExecutionTVStatistic a

noncomputable def thetaHasseExecutionEntropyAverage (a : ℝ) : ℝ :=
  thetaTiltStatisticMean thetaHasseExecutionEntropyStatistic a

theorem thetaHasseExecutionTVStatistic_bounds (x : ℝ) :
    0 < thetaHasseExecutionTVStatistic x ∧
      thetaHasseExecutionTVStatistic x < 2 / 3 := by
  have hq0 := thetaHasseRatio_pos x
  have hq1 := thetaHasseRatio_lt_half x
  constructor
  · rw [thetaHasseExecutionTVStatistic, geometricExecutionTV]
    positivity
  · rw [thetaHasseExecutionTVStatistic, geometricExecutionTV]
    have hden : 0 < 1 + thetaHasseRatio x := by linarith
    rw [div_lt_iff₀ hden]
    nlinarith

theorem geometricExecutionEntropy_half :
    geometricExecutionEntropy (1 / 2) = 2 * Real.log 2 := by
  rw [geometricExecutionEntropy]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  simp only [div_self (by norm_num : (1 / 2 : ℝ) ≠ 0), one_mul]
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  simp
  ring

theorem thetaHasseExecutionEntropyStatistic_bounds (x : ℝ) :
    0 < thetaHasseExecutionEntropyStatistic x ∧
      thetaHasseExecutionEntropyStatistic x < 2 * Real.log 2 := by
  have hq0 := thetaHasseRatio_pos x
  have hqhalf := thetaHasseRatio_lt_half x
  have hq1 : thetaHasseRatio x < 1 := lt_trans hqhalf (by norm_num)
  constructor
  · rw [thetaHasseExecutionEntropyStatistic, geometricExecutionEntropy]
    have hlog1 : Real.log (1 - thetaHasseRatio x) < 0 :=
      Real.log_neg (by linarith) (by linarith)
    have hlogq : Real.log (thetaHasseRatio x) < 0 := Real.log_neg hq0 hq1
    have hfrac : 0 < thetaHasseRatio x / (1 - thetaHasseRatio x) := by positivity
    nlinarith [mul_neg_of_pos_of_neg hfrac hlogq]
  · have hmono := strictMonoOn_geometricExecutionEntropy
      (show thetaHasseRatio x ∈ Set.Ioo (0 : ℝ) 1 from ⟨hq0, hq1⟩)
      (show (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 by norm_num) hqhalf
    rw [geometricExecutionEntropy_half] at hmono
    exact hmono

theorem continuous_thetaHasseRatio : Continuous thetaHasseRatio := by
  have hexp : Continuous (fun x : ℝ => Real.exp x) := Real.continuous_exp
  have hneg : Continuous (fun x : ℝ => -Real.exp x) := hexp.neg
  have houter : Continuous (fun x : ℝ => Real.exp (-Real.exp x)) :=
    Real.continuous_exp.comp hneg
  unfold thetaHasseRatio
  exact (continuous_const.sub houter).div_const 2

theorem continuous_thetaHasseExecutionTVStatistic :
    Continuous thetaHasseExecutionTVStatistic := by
  unfold thetaHasseExecutionTVStatistic geometricExecutionTV
  exact (continuous_const.mul continuous_thetaHasseRatio).div
    (continuous_const.add continuous_thetaHasseRatio)
    (fun x => by linarith [thetaHasseRatio_pos x])

theorem continuous_thetaHasseExecutionEntropyStatistic :
    Continuous thetaHasseExecutionEntropyStatistic := by
  unfold thetaHasseExecutionEntropyStatistic geometricExecutionEntropy
  have hlog1 : Continuous (fun x : ℝ => Real.log (1 - thetaHasseRatio x)) :=
    (continuous_const.sub continuous_thetaHasseRatio).log
      (fun x => show 1 - thetaHasseRatio x ≠ 0 from by
        linarith [thetaHasseRatio_lt_half x])
  have hlogq : Continuous (fun x : ℝ => Real.log (thetaHasseRatio x)) :=
    continuous_thetaHasseRatio.log (fun x => (thetaHasseRatio_pos x).ne')
  have hfrac : Continuous (fun x : ℝ => thetaHasseRatio x / (1 - thetaHasseRatio x)) :=
    continuous_thetaHasseRatio.div (continuous_const.sub continuous_thetaHasseRatio)
      (fun x => by linarith [thetaHasseRatio_lt_half x])
  exact hlog1.neg.sub (hfrac.mul hlogq)

theorem norm_thetaHasseExecutionTVStatistic_le (x : ℝ) :
    ‖thetaHasseExecutionTVStatistic x‖ ≤ (2 / 3 : ℝ) := by
  rw [Real.norm_eq_abs, abs_of_pos (thetaHasseExecutionTVStatistic_bounds x).1]
  exact (thetaHasseExecutionTVStatistic_bounds x).2.le

theorem norm_thetaHasseExecutionEntropyStatistic_le (x : ℝ) :
    ‖thetaHasseExecutionEntropyStatistic x‖ ≤ 2 * Real.log 2 := by
  rw [Real.norm_eq_abs, abs_of_pos (thetaHasseExecutionEntropyStatistic_bounds x).1]
  exact (thetaHasseExecutionEntropyStatistic_bounds x).2.le

theorem thetaHasseExecutionTVAverage_eq_integral {a : ℝ} (ha : |a| ≤ 1) :
    thetaHasseExecutionTVAverage a =
      ∫ x : ℝ, thetaHasseExecutionTVStatistic x ∂(RHTower.thetaTiltProb a) :=
  thetaTiltStatisticMean_eq_integral ha

theorem thetaHasseExecutionEntropyAverage_eq_integral {a : ℝ} (ha : |a| ≤ 1) :
    thetaHasseExecutionEntropyAverage a =
      ∫ x : ℝ, thetaHasseExecutionEntropyStatistic x ∂(RHTower.thetaTiltProb a) :=
  thetaTiltStatisticMean_eq_integral ha

theorem hasDerivAt_thetaHasseExecutionTVAverage {a : ℝ} (ha : |a| < 1) :
    HasDerivAt thetaHasseExecutionTVAverage
      (thetaTiltStatisticCovariance thetaHasseExecutionTVStatistic a) a :=
  hasDerivAt_thetaTiltStatisticMean continuous_thetaHasseExecutionTVStatistic
    norm_thetaHasseExecutionTVStatistic_le ha

theorem hasDerivAt_thetaHasseExecutionEntropyAverage {a : ℝ} (ha : |a| < 1) :
    HasDerivAt thetaHasseExecutionEntropyAverage
      (thetaTiltStatisticCovariance thetaHasseExecutionEntropyStatistic a) a :=
  hasDerivAt_thetaTiltStatisticMean continuous_thetaHasseExecutionEntropyStatistic
    norm_thetaHasseExecutionEntropyStatistic_le ha

theorem thetaHasseExecutionTVAverage_covariance_pos {a : ℝ} (ha : |a| ≤ 1) :
    0 < thetaTiltStatisticCovariance thetaHasseExecutionTVStatistic a :=
  thetaTiltStatisticCovariance_pos strictMono_thetaHasseExecutionTV
    continuous_thetaHasseExecutionTVStatistic norm_thetaHasseExecutionTVStatistic_le ha

theorem thetaHasseExecutionEntropyAverage_covariance_pos {a : ℝ} (ha : |a| ≤ 1) :
    0 < thetaTiltStatisticCovariance thetaHasseExecutionEntropyStatistic a :=
  thetaTiltStatisticCovariance_pos strictMono_thetaHasseExecutionEntropy
    continuous_thetaHasseExecutionEntropyStatistic norm_thetaHasseExecutionEntropyStatistic_le ha

noncomputable def thetaTiltStatisticReflectionGap (g : ℝ → ℝ) (a : ℝ) : ℝ :=
  thetaTiltStatisticMean g a - thetaTiltStatisticMean g (-a)

noncomputable def thetaHasseExecutionTVReflectionGap (a : ℝ) : ℝ :=
  thetaTiltStatisticReflectionGap thetaHasseExecutionTVStatistic a

noncomputable def thetaHasseExecutionEntropyReflectionGap (a : ℝ) : ℝ :=
  thetaTiltStatisticReflectionGap thetaHasseExecutionEntropyStatistic a

theorem thetaTiltStatisticReflectionGap_neg (g : ℝ → ℝ) (a : ℝ) :
    thetaTiltStatisticReflectionGap g (-a) = -thetaTiltStatisticReflectionGap g a := by
  rw [thetaTiltStatisticReflectionGap, thetaTiltStatisticReflectionGap]
  simp only [neg_neg]
  ring

theorem hasDerivAt_thetaTiltStatisticReflectionGap {g : ℝ → ℝ}
    (hgcont : Continuous g) {C : ℝ} (hg : ∀ x, ‖g x‖ ≤ C)
    {a : ℝ} (ha : |a| < 1) :
    HasDerivAt (thetaTiltStatisticReflectionGap g)
      (thetaTiltStatisticCovariance g a + thetaTiltStatisticCovariance g (-a)) a := by
  have hpos := hasDerivAt_thetaTiltStatisticMean hgcont hg ha
  have hneg := hasDerivAt_thetaTiltStatisticMean hgcont hg (by simpa using ha : |-a| < 1)
  have hcomp := hneg.comp a (hasDerivAt_neg a)
  have hsub := hpos.sub hcomp
  refine hsub.congr_deriv ?_
  ring

theorem hasDerivAt_thetaHasseExecutionTVReflectionGap {a : ℝ} (ha : |a| < 1) :
    HasDerivAt thetaHasseExecutionTVReflectionGap
      (thetaTiltStatisticCovariance thetaHasseExecutionTVStatistic a +
        thetaTiltStatisticCovariance thetaHasseExecutionTVStatistic (-a)) a :=
  hasDerivAt_thetaTiltStatisticReflectionGap continuous_thetaHasseExecutionTVStatistic
    norm_thetaHasseExecutionTVStatistic_le ha

theorem hasDerivAt_thetaHasseExecutionEntropyReflectionGap {a : ℝ} (ha : |a| < 1) :
    HasDerivAt thetaHasseExecutionEntropyReflectionGap
      (thetaTiltStatisticCovariance thetaHasseExecutionEntropyStatistic a +
        thetaTiltStatisticCovariance thetaHasseExecutionEntropyStatistic (-a)) a :=
  hasDerivAt_thetaTiltStatisticReflectionGap continuous_thetaHasseExecutionEntropyStatistic
    norm_thetaHasseExecutionEntropyStatistic_le ha

theorem strictMonoOn_thetaHasseExecutionTVReflectionGap :
    StrictMonoOn thetaHasseExecutionTVReflectionGap (Set.Ioo (-1 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (D := Set.Ioo (-1 : ℝ) 1) (convex_Ioo _ _)
  · intro a ha
    exact (hasDerivAt_thetaHasseExecutionTVReflectionGap (by simpa [abs_lt] using ha)).continuousAt.continuousWithinAt
  · intro a ha
    rw [interior_Ioo] at ha
    rw [(hasDerivAt_thetaHasseExecutionTVReflectionGap (by simpa [abs_lt] using ha)).deriv]
    have hpa := thetaHasseExecutionTVAverage_covariance_pos
      (show |a| ≤ 1 from (by rw [abs_le]; exact ⟨ha.1.le, ha.2.le⟩))
    have hpna := thetaHasseExecutionTVAverage_covariance_pos
      (show |-a| ≤ 1 from by simpa using (show |a| ≤ 1 from by
        rw [abs_le]; exact ⟨ha.1.le, ha.2.le⟩))
    linarith

theorem strictMonoOn_thetaHasseExecutionEntropyReflectionGap :
    StrictMonoOn thetaHasseExecutionEntropyReflectionGap (Set.Ioo (-1 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (D := Set.Ioo (-1 : ℝ) 1) (convex_Ioo _ _)
  · intro a ha
    exact (hasDerivAt_thetaHasseExecutionEntropyReflectionGap (by simpa [abs_lt] using ha)).continuousAt.continuousWithinAt
  · intro a ha
    rw [interior_Ioo] at ha
    rw [(hasDerivAt_thetaHasseExecutionEntropyReflectionGap (by simpa [abs_lt] using ha)).deriv]
    have hpa := thetaHasseExecutionEntropyAverage_covariance_pos
      (show |a| ≤ 1 from (by rw [abs_le]; exact ⟨ha.1.le, ha.2.le⟩))
    have hpna := thetaHasseExecutionEntropyAverage_covariance_pos
      (show |-a| ≤ 1 from by simpa using (show |a| ≤ 1 from by
        rw [abs_le]; exact ⟨ha.1.le, ha.2.le⟩))
    linarith

theorem thetaHasseExecutionTVReflectionGap_eq_zero_iff {a : ℝ} (ha : |a| < 1) :
    thetaHasseExecutionTVReflectionGap a = 0 ↔ a = 0 := by
  constructor
  · intro hz
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hlt := strictMonoOn_thetaHasseExecutionTVReflectionGap
        (show a ∈ Set.Ioo (-1 : ℝ) 1 by simpa [abs_lt] using ha)
        (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num) hneg
      simp [thetaHasseExecutionTVReflectionGap, thetaTiltStatisticReflectionGap] at hlt
      rw [thetaHasseExecutionTVReflectionGap, thetaTiltStatisticReflectionGap] at hz
      linarith
    · have hlt := strictMonoOn_thetaHasseExecutionTVReflectionGap
        (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)
        (show a ∈ Set.Ioo (-1 : ℝ) 1 by simpa [abs_lt] using ha) hpos
      simp [thetaHasseExecutionTVReflectionGap, thetaTiltStatisticReflectionGap] at hlt
      rw [thetaHasseExecutionTVReflectionGap, thetaTiltStatisticReflectionGap] at hz
      linarith
  · rintro rfl
    simp [thetaHasseExecutionTVReflectionGap, thetaTiltStatisticReflectionGap]

theorem thetaHasseExecutionEntropyReflectionGap_eq_zero_iff {a : ℝ} (ha : |a| < 1) :
    thetaHasseExecutionEntropyReflectionGap a = 0 ↔ a = 0 := by
  constructor
  · intro hz
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hlt := strictMonoOn_thetaHasseExecutionEntropyReflectionGap
        (show a ∈ Set.Ioo (-1 : ℝ) 1 by simpa [abs_lt] using ha)
        (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num) hneg
      simp [thetaHasseExecutionEntropyReflectionGap, thetaTiltStatisticReflectionGap] at hlt
      rw [thetaHasseExecutionEntropyReflectionGap, thetaTiltStatisticReflectionGap] at hz
      linarith
    · have hlt := strictMonoOn_thetaHasseExecutionEntropyReflectionGap
        (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)
        (show a ∈ Set.Ioo (-1 : ℝ) 1 by simpa [abs_lt] using ha) hpos
      simp [thetaHasseExecutionEntropyReflectionGap, thetaTiltStatisticReflectionGap] at hlt
      rw [thetaHasseExecutionEntropyReflectionGap, thetaTiltStatisticReflectionGap] at hz
      linarith
  · rintro rfl
    simp [thetaHasseExecutionEntropyReflectionGap, thetaTiltStatisticReflectionGap]

noncomputable def reflectionGapHomeomorph (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Set.Ioo (-1 : ℝ) 1))
    (hmono : StrictMonoOn f (Set.Ioo (-1 : ℝ) 1)) :
    {a : ℝ // a ∈ Set.Ioo (-1 : ℝ) 1} ≃ₜ
      Set.range (fun a : {a : ℝ // a ∈ Set.Ioo (-1 : ℝ) 1} => f a) := by
  let F : {a : ℝ // a ∈ Set.Ioo (-1 : ℝ) 1} → ℝ := fun a => f a
  have hFmono : StrictMono F := by
    intro a b hab
    exact hmono a.property b.property hab
  have hFrange : Set.OrdConnected (Set.range F) := by
    have hpre : IsPreconnected (f '' Set.Ioo (-1 : ℝ) 1) :=
      isPreconnected_Ioo.image f hcont
    rw [show Set.range F = f '' Set.Ioo (-1 : ℝ) 1 by ext y; simp [F]]
    exact hpre.ordConnected
  exact (hFmono.isEmbedding_of_ordConnected hFrange).toHomeomorph

noncomputable def thetaHasseExecutionTVReflectionHomeomorph :
    {a : ℝ // a ∈ Set.Ioo (-1 : ℝ) 1} ≃ₜ
      Set.range (fun a : {a : ℝ // a ∈ Set.Ioo (-1 : ℝ) 1} =>
        thetaHasseExecutionTVReflectionGap a) :=
  reflectionGapHomeomorph thetaHasseExecutionTVReflectionGap
    (fun a ha => (hasDerivAt_thetaHasseExecutionTVReflectionGap
      (by simpa [abs_lt] using ha)).continuousAt.continuousWithinAt)
    strictMonoOn_thetaHasseExecutionTVReflectionGap

noncomputable def thetaHasseExecutionEntropyReflectionHomeomorph :
    {a : ℝ // a ∈ Set.Ioo (-1 : ℝ) 1} ≃ₜ
      Set.range (fun a : {a : ℝ // a ∈ Set.Ioo (-1 : ℝ) 1} =>
        thetaHasseExecutionEntropyReflectionGap a) :=
  reflectionGapHomeomorph thetaHasseExecutionEntropyReflectionGap
    (fun a ha => (hasDerivAt_thetaHasseExecutionEntropyReflectionGap
      (by simpa [abs_lt] using ha)).continuousAt.continuousWithinAt)
    strictMonoOn_thetaHasseExecutionEntropyReflectionGap

theorem thetaHasseExecutionTVReflectionHomeomorph_isProperMap :
    IsProperMap thetaHasseExecutionTVReflectionHomeomorph :=
  thetaHasseExecutionTVReflectionHomeomorph.isProperMap

theorem thetaHasseExecutionEntropyReflectionHomeomorph_isProperMap :
    IsProperMap thetaHasseExecutionEntropyReflectionHomeomorph :=
  thetaHasseExecutionEntropyReflectionHomeomorph.isProperMap

/-! ## Continuous covariance, Popoviciu, and Fisher response -/

noncomputable def probabilityMean (μ : Measure ℝ) (f : ℝ → ℝ) : ℝ := ∫ x, f x ∂μ

noncomputable def probabilityVariance (μ : Measure ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ x, (f x - probabilityMean μ f) ^ 2 ∂μ

noncomputable def probabilityCovariance (μ : Measure ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ x, (f x - probabilityMean μ f) * (g x - probabilityMean μ g) ∂μ

theorem integrable_probabilityCentered_sq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    Integrable (fun x => (f x - probabilityMean μ f) ^ 2) μ := by
  have heq : (fun x => (f x - probabilityMean μ f) ^ 2) =
      fun x => f x ^ 2 - (2 * probabilityMean μ f) * f x +
        (probabilityMean μ f) ^ 2 := by
    funext x
    ring
  rw [heq]
  exact (hf2.sub (hf.const_mul _)).add (integrable_const _)

theorem probabilityCovariance_eq_raw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f g : ℝ → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    probabilityCovariance μ f g =
      (∫ x, f x * g x ∂μ) - (∫ x, f x ∂μ) * ∫ x, g x ∂μ := by
  let mf : ℝ := probabilityMean μ f
  let mg : ℝ := probabilityMean μ g
  have hmf : Integrable (fun x => mf * g x) μ := hg.const_mul mf
  have hmg : Integrable (fun x => mg * f x) μ := hf.const_mul mg
  have hc : Integrable (fun _ : ℝ => mf * mg) μ := integrable_const _
  have heq : (fun x => (f x - mf) * (g x - mg)) =
      fun x => ((f x * g x - mf * g x) - mg * f x) + mf * mg := by
    funext x
    ring
  rw [probabilityCovariance]
  change (∫ x, (f x - mf) * (g x - mg) ∂μ) = _
  rw [heq]
  calc
    (∫ x, ((f x * g x - mf * g x) - mg * f x) + mf * mg ∂μ) =
        (∫ x, (f x * g x - mf * g x) - mg * f x ∂μ) +
          ∫ _ : ℝ, mf * mg ∂μ :=
      integral_add ((hfg.sub hmf).sub hmg) hc
    _ = ((∫ x, f x * g x - mf * g x ∂μ) - ∫ x, mg * f x ∂μ) +
          ∫ _ : ℝ, mf * mg ∂μ := by
      congr 1
      exact integral_sub (hfg.sub hmf) hmg
    _ = (((∫ x, f x * g x ∂μ) - ∫ x, mf * g x ∂μ) -
          ∫ x, mg * f x ∂μ) + ∫ _ : ℝ, mf * mg ∂μ := by
      congr 1
      congr 1
      exact integral_sub hfg hmf
    _ = (∫ x, f x * g x ∂μ) - (∫ x, f x ∂μ) * ∫ x, g x ∂μ := by
      rw [integral_const_mul, integral_const_mul]
      simp only [integral_const, probReal_univ, one_smul]
      unfold mf mg probabilityMean
      ring

theorem probabilityVariance_eq_raw {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    probabilityVariance μ f = (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
  have hff : Integrable (fun x => f x * f x) μ := by simpa [pow_two] using hf2
  calc
    probabilityVariance μ f = probabilityCovariance μ f f := by
      unfold probabilityVariance probabilityCovariance
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    _ = (∫ x, f x * f x ∂μ) - (∫ x, f x ∂μ) * ∫ x, f x ∂μ :=
      probabilityCovariance_eq_raw hf hf hff
    _ = (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
      congr 1
      · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        ring
      · ring

theorem probabilityCovariance_sq_le_variance_mul_variance
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {f g : ℝ → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) :
    probabilityCovariance μ f g ^ 2 ≤
      probabilityVariance μ f * probabilityVariance μ g := by
  have hfc := hf.sub (integrable_const (probabilityMean μ f))
  have hgc := hg.sub (integrable_const (probabilityMean μ g))
  have hfcsq := integrable_probabilityCentered_sq hf hf2
  have hgcsq := integrable_probabilityCentered_sq hg hg2
  unfold probabilityCovariance probabilityVariance
  exact sq_integral_mul_le hfc.aestronglyMeasurable hgc.aestronglyMeasurable hfcsq hgcsq

theorem probabilityVariance_le_quarter_range_sq
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    {l u : ℝ} (hl : ∀ x, l ≤ f x) (hu : ∀ x, f x ≤ u) :
    probabilityVariance μ f ≤ (u - l) ^ 2 / 4 := by
  have haff : Integrable (fun x => (l + u) * f x - l * u) μ :=
    (hf.const_mul (l + u)).sub (integrable_const (l * u))
  have hsecond : (∫ x, f x ^ 2 ∂μ) ≤ ∫ x, (l + u) * f x - l * u ∂μ := by
    apply integral_mono hf2 haff
    intro x
    have hprod : 0 ≤ (f x - l) * (u - f x) :=
      mul_nonneg (sub_nonneg.mpr (hl x)) (sub_nonneg.mpr (hu x))
    nlinarith
  have hmeanLower : l ≤ ∫ x, f x ∂μ := by
    have h := integral_mono (integrable_const l) hf (fun x => hl x)
    simpa using h
  have hmeanUpper : (∫ x, f x ∂μ) ≤ u := by
    have h := integral_mono hf (integrable_const u) (fun x => hu x)
    simpa using h
  rw [probabilityVariance_eq_raw hf hf2]
  have hsecond' : (∫ x, f x ^ 2 ∂μ) ≤
      (l + u) * (∫ x, f x ∂μ) - l * u := by
    calc
      (∫ x, f x ^ 2 ∂μ) ≤ ∫ x, (l + u) * f x - l * u ∂μ := hsecond
      _ = (l + u) * (∫ x, f x ∂μ) - l * u := by
        rw [integral_sub (hf.const_mul (l + u)) (integrable_const (l * u)),
          integral_const_mul]
        simp
  nlinarith [sq_nonneg (2 * (∫ x, f x ∂μ) - l - u)]

theorem integrable_thetaHasseExecutionTVStatistic {a : ℝ} (ha : |a| ≤ 1) :
    Integrable thetaHasseExecutionTVStatistic (RHTower.thetaTiltProb a) := by
  apply RHTower.integrable_thetaTiltProb ha
  simpa using integrable_thetaTiltStatisticIntegrand
    continuous_thetaHasseExecutionTVStatistic norm_thetaHasseExecutionTVStatistic_le ha 0

theorem integrable_thetaHasseExecutionEntropyStatistic {a : ℝ} (ha : |a| ≤ 1) :
    Integrable thetaHasseExecutionEntropyStatistic (RHTower.thetaTiltProb a) := by
  apply RHTower.integrable_thetaTiltProb ha
  simpa using integrable_thetaTiltStatisticIntegrand
    continuous_thetaHasseExecutionEntropyStatistic norm_thetaHasseExecutionEntropyStatistic_le ha 0

theorem integrable_sq_thetaHasseExecutionTVStatistic {a : ℝ} (ha : |a| ≤ 1) :
    Integrable (fun x => thetaHasseExecutionTVStatistic x ^ 2)
      (RHTower.thetaTiltProb a) := by
  letI := RHTower.thetaTiltProb_isProbabilityMeasure ha
  apply Integrable.of_bound
    (continuous_thetaHasseExecutionTVStatistic.pow 2).aestronglyMeasurable
    ((2 / 3 : ℝ) ^ 2)
  filter_upwards with x
  change ‖thetaHasseExecutionTVStatistic x ^ 2‖ ≤ (2 / 3 : ℝ) ^ 2
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_thetaHasseExecutionTVStatistic_le x) 2

theorem integrable_sq_thetaHasseExecutionEntropyStatistic {a : ℝ} (ha : |a| ≤ 1) :
    Integrable (fun x => thetaHasseExecutionEntropyStatistic x ^ 2)
      (RHTower.thetaTiltProb a) := by
  letI := RHTower.thetaTiltProb_isProbabilityMeasure ha
  apply Integrable.of_bound
    (continuous_thetaHasseExecutionEntropyStatistic.pow 2).aestronglyMeasurable
    ((2 * Real.log 2) ^ 2)
  filter_upwards with x
  change ‖thetaHasseExecutionEntropyStatistic x ^ 2‖ ≤ (2 * Real.log 2) ^ 2
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_thetaHasseExecutionEntropyStatistic_le x) 2

theorem integrable_sq_id_thetaTiltProb {a : ℝ} (ha : |a| ≤ 1) :
    Integrable (fun x : ℝ => x ^ 2) (RHTower.thetaTiltProb a) := by
  apply RHTower.integrable_thetaTiltProb ha
  simpa using integrable_thetaTiltStatisticIntegrand
    (g := fun _ : ℝ => 1) continuous_const (C := 1) (by simp) ha 2

theorem thetaTiltStatisticCovariance_eq_probabilityCovariance {g : ℝ → ℝ}
    {a : ℝ} (ha : |a| ≤ 1) (hg : Integrable g (RHTower.thetaTiltProb a))
    (hgx : Integrable (fun x => g x * x) (RHTower.thetaTiltProb a)) :
    thetaTiltStatisticCovariance g a =
      probabilityCovariance (RHTower.thetaTiltProb a) g (fun x => x) := by
  letI := RHTower.thetaTiltProb_isProbabilityMeasure ha
  rw [thetaTiltStatisticCovariance_eq_integral ha]
  exact (probabilityCovariance_eq_raw hg (RHTower.integrable_id_thetaTiltProb ha) hgx).symm

theorem thetaTiltVariance_eq_probabilityVariance {a : ℝ} (ha : |a| ≤ 1) :
    RHTower.thetaTiltVariance a =
      probabilityVariance (RHTower.thetaTiltProb a) (fun x => x) := by
  letI := RHTower.thetaTiltProb_isProbabilityMeasure ha
  have hraw := probabilityVariance_eq_raw (RHTower.integrable_id_thetaTiltProb ha)
    (integrable_sq_id_thetaTiltProb ha)
  rw [hraw, RHTower.integral_id_thetaTiltProb ha]
  have hsecond : (∫ x : ℝ, x ^ 2 ∂(RHTower.thetaTiltProb a)) =
      RHTower.thetaTiltMoment a 2 / RHTower.thetaTiltMoment a 0 := by
    rw [RHTower.integral_thetaTiltProb ha]
    congr 1
  rw [hsecond]
  rfl

theorem thetaHasseExecutionTVVariance_le {a : ℝ} (ha : |a| ≤ 1) :
    probabilityVariance (RHTower.thetaTiltProb a) thetaHasseExecutionTVStatistic ≤ 1 / 9 := by
  letI := RHTower.thetaTiltProb_isProbabilityMeasure ha
  have h := probabilityVariance_le_quarter_range_sq
    (integrable_thetaHasseExecutionTVStatistic ha)
    (integrable_sq_thetaHasseExecutionTVStatistic ha)
    (l := 0) (u := 2 / 3)
    (fun x => (thetaHasseExecutionTVStatistic_bounds x).1.le)
    (fun x => (thetaHasseExecutionTVStatistic_bounds x).2.le)
  norm_num at h ⊢
  exact h

theorem thetaHasseExecutionEntropyVariance_le {a : ℝ} (ha : |a| ≤ 1) :
    probabilityVariance (RHTower.thetaTiltProb a)
      thetaHasseExecutionEntropyStatistic ≤ (Real.log 2) ^ 2 := by
  letI := RHTower.thetaTiltProb_isProbabilityMeasure ha
  have h := probabilityVariance_le_quarter_range_sq
    (integrable_thetaHasseExecutionEntropyStatistic ha)
    (integrable_sq_thetaHasseExecutionEntropyStatistic ha)
    (l := 0) (u := 2 * Real.log 2)
    (fun x => (thetaHasseExecutionEntropyStatistic_bounds x).1.le)
    (fun x => (thetaHasseExecutionEntropyStatistic_bounds x).2.le)
  nlinarith

theorem thetaHasseExecutionTV_fisher_response {a : ℝ} (ha : |a| < 1) :
    9 * (deriv thetaHasseExecutionTVAverage a) ^ 2 ≤ RHTower.thetaTiltVariance a := by
  have hale : |a| ≤ 1 := ha.le
  letI := RHTower.thetaTiltProb_isProbabilityMeasure hale
  have hg := integrable_thetaHasseExecutionTVStatistic hale
  have hx := RHTower.integrable_id_thetaTiltProb hale
  have hg2 := integrable_sq_thetaHasseExecutionTVStatistic hale
  have hx2 := integrable_sq_id_thetaTiltProb hale
  have hcs := probabilityCovariance_sq_le_variance_mul_variance hg hx hg2 hx2
  have hgx : Integrable (fun x => thetaHasseExecutionTVStatistic x * x)
      (RHTower.thetaTiltProb a) := by
    apply RHTower.integrable_thetaTiltProb hale
    simpa [pow_one] using integrable_thetaTiltStatisticIntegrand
      continuous_thetaHasseExecutionTVStatistic norm_thetaHasseExecutionTVStatistic_le hale 1
  rw [← thetaTiltStatisticCovariance_eq_probabilityCovariance hale hg hgx,
    ← thetaTiltVariance_eq_probabilityVariance hale] at hcs
  have hstat := thetaHasseExecutionTVVariance_le hale
  have hvar := (RHTower.thetaTiltVariance_pos hale).le
  have hprod := mul_le_mul_of_nonneg_right hstat hvar
  have hcv := le_trans hcs hprod
  rw [(hasDerivAt_thetaHasseExecutionTVAverage ha).deriv]
  nlinarith [hcv]

theorem thetaHasseExecutionEntropy_fisher_response {a : ℝ} (ha : |a| < 1) :
    (deriv thetaHasseExecutionEntropyAverage a) ^ 2 / (Real.log 2) ^ 2 ≤
      RHTower.thetaTiltVariance a := by
  have hale : |a| ≤ 1 := ha.le
  letI := RHTower.thetaTiltProb_isProbabilityMeasure hale
  have hg := integrable_thetaHasseExecutionEntropyStatistic hale
  have hx := RHTower.integrable_id_thetaTiltProb hale
  have hg2 := integrable_sq_thetaHasseExecutionEntropyStatistic hale
  have hx2 := integrable_sq_id_thetaTiltProb hale
  have hcs := probabilityCovariance_sq_le_variance_mul_variance hg hx hg2 hx2
  have hgx : Integrable (fun x => thetaHasseExecutionEntropyStatistic x * x)
      (RHTower.thetaTiltProb a) := by
    apply RHTower.integrable_thetaTiltProb hale
    simpa [pow_one] using integrable_thetaTiltStatisticIntegrand
      continuous_thetaHasseExecutionEntropyStatistic
      norm_thetaHasseExecutionEntropyStatistic_le hale 1
  rw [← thetaTiltStatisticCovariance_eq_probabilityCovariance hale hg hgx,
    ← thetaTiltVariance_eq_probabilityVariance hale] at hcs
  have hstat := thetaHasseExecutionEntropyVariance_le hale
  have hvar := (RHTower.thetaTiltVariance_pos hale).le
  have hprod := mul_le_mul_of_nonneg_right hstat hvar
  have hcv := le_trans hcs hprod
  rw [(hasDerivAt_thetaHasseExecutionEntropyAverage ha).deriv]
  rw [div_le_iff₀ (sq_pos_of_pos (Real.log_pos (by norm_num)))]
  nlinarith [hcv]

/-! ## Exact reflected half-line coordinate -/

theorem integral_thetaTiltStatistic_reflectionGap_eq_sinh_Ioi
    {g : ℝ → ℝ} (hgcont : Continuous g) {C : ℝ} (hg : ∀ x, ‖g x‖ ≤ C)
    {a : ℝ} (ha : |a| ≤ 1) :
    (∫ x : ℝ, g x * Real.exp (a * x) * RHTower.thetaCuspFullSource x) -
        (∫ x : ℝ, g x * Real.exp ((-a) * x) * RHTower.thetaCuspFullSource x) =
      2 * ∫ x : ℝ in Set.Ioi 0,
        (g x - g (-x)) * Real.sinh (a * x) * RHTower.thetaCuspFullSource x := by
  let P : ℝ → ℝ := fun x =>
    g x * Real.exp (a * x) * RHTower.thetaCuspFullSource x
  let Pneg : ℝ → ℝ := fun x =>
    g x * Real.exp ((-a) * x) * RHTower.thetaCuspFullSource x
  let Q : ℝ → ℝ := fun x =>
    g (-x) * Real.exp (a * x) * RHTower.thetaCuspFullSource x
  let J : ℝ → ℝ := fun x => P x - Q x
  let H : ℝ → ℝ := fun x =>
    (g x - g (-x)) * Real.sinh (a * x) * RHTower.thetaCuspFullSource x
  have hP : Integrable P := by
    simpa [P] using integrable_thetaTiltStatisticIntegrand hgcont hg ha 0
  have hPneg : Integrable Pneg := by
    simpa [Pneg] using integrable_thetaTiltStatisticIntegrand
      (a := -a) hgcont hg (by simpa using ha) 0
  have hQ : Integrable Q := by
    have href := hPneg.comp_neg
    simpa [Pneg, Q, RHTower.thetaCuspFullSource_neg] using href
  have hreflect : (∫ x, Pneg x) = ∫ x, Q x := by
    calc
      (∫ x, Pneg x) = ∫ x, Pneg (-x) :=
        (MeasureTheory.integral_neg_eq_self Pneg volume).symm
      _ = ∫ x, Q x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp [Pneg, Q, RHTower.thetaCuspFullSource_neg]
  have hJ : Integrable J := hP.sub hQ
  have hJneg : Integrable (fun x => J (-x)) := hJ.comp_neg
  have haverage : (fun x => (J x + J (-x)) / 2) = H := by
    funext x
    simp only [J, P, Q, H, RHTower.thetaCuspFullSource_neg, neg_neg]
    rw [Real.sinh_eq]
    ring_nf
  have hH : Integrable H := by
    rw [← haverage]
    exact (hJ.add hJneg).div_const 2
  have hint_JH : (∫ x, J x) = ∫ x, H x := by
    rw [← haverage, integral_div, MeasureTheory.integral_add hJ hJneg,
      MeasureTheory.integral_neg_eq_self J volume]
    ring
  have hHeven (x : ℝ) : H (-x) = H x := by
    simp only [H, neg_neg, RHTower.thetaCuspFullSource_neg]
    rw [show a * (-x) = -(a * x) by ring, Real.sinh_neg]
    ring
  let K : ℝ → ℝ := (Set.Ioi (0 : ℝ)).indicator H
  have hK : Integrable K := hH.indicator measurableSet_Ioi
  have hKneg : Integrable (fun x => K (-x)) := hK.comp_neg
  have hHK : H = fun x => K x + K (-x) := by
    funext x
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · have hnx : 0 < -x := by linarith
      rw [show K x = 0 by simp [K, not_lt.mpr hx.le],
        show K (-x) = H (-x) by simp [K, hnx], zero_add, hHeven]
    · simp [K, H]
    · have hnmem : -x ∉ Set.Ioi (0 : ℝ) := by simp [hx.le]
      rw [show K x = H x by simp [K, hx],
        show K (-x) = 0 by simp [K, hnmem], add_zero]
  have hint_HK : (∫ x, H x) = 2 * ∫ x, K x := by
    rw [hHK, MeasureTheory.integral_add hK hKneg,
      MeasureTheory.integral_neg_eq_self K volume]
    ring
  have hKset : (∫ x, K x) = ∫ x in Set.Ioi (0 : ℝ), H x :=
    MeasureTheory.integral_indicator measurableSet_Ioi
  have hPJ : (∫ x, P x) - ∫ x, Pneg x = ∫ x, J x := by
    rw [hreflect, integral_sub hP hQ]
  calc
    (∫ x, P x) - ∫ x, Pneg x = ∫ x, J x := hPJ
    _ = ∫ x, H x := hint_JH
    _ = 2 * ∫ x, K x := hint_HK
    _ = 2 * ∫ x in Set.Ioi (0 : ℝ), H x := by rw [hKset]
    _ = 2 * ∫ x : ℝ in Set.Ioi 0,
        (g x - g (-x)) * Real.sinh (a * x) * RHTower.thetaCuspFullSource x := rfl

theorem thetaTiltStatisticReflectionGap_eq_sinh_Ioi
    {g : ℝ → ℝ} (hgcont : Continuous g) {C : ℝ} (hg : ∀ x, ‖g x‖ ≤ C)
    {a : ℝ} (ha : |a| ≤ 1) :
    thetaTiltStatisticReflectionGap g a =
      2 / RHTower.thetaTiltMoment a 0 *
        ∫ x : ℝ in Set.Ioi 0,
          (g x - g (-x)) * Real.sinh (a * x) * RHTower.thetaCuspFullSource x := by
  rw [thetaTiltStatisticReflectionGap]
  unfold thetaTiltStatisticMean thetaTiltStatisticMoment
  rw [RHTower.thetaTiltMoment_zero_neg]
  rw [← sub_div]
  simp only [pow_zero, mul_one]
  rw [integral_thetaTiltStatistic_reflectionGap_eq_sinh_Ioi hgcont hg ha]
  ring

theorem thetaHasseExecutionTVReflectionGap_eq_sinh_Ioi {a : ℝ} (ha : |a| ≤ 1) :
    thetaHasseExecutionTVReflectionGap a =
      2 / RHTower.thetaTiltMoment a 0 *
        ∫ x : ℝ in Set.Ioi 0,
          (thetaHasseExecutionTVStatistic x - thetaHasseExecutionTVStatistic (-x)) *
            Real.sinh (a * x) * RHTower.thetaCuspFullSource x :=
  thetaTiltStatisticReflectionGap_eq_sinh_Ioi
    continuous_thetaHasseExecutionTVStatistic norm_thetaHasseExecutionTVStatistic_le ha

theorem thetaHasseExecutionEntropyReflectionGap_eq_sinh_Ioi {a : ℝ} (ha : |a| ≤ 1) :
    thetaHasseExecutionEntropyReflectionGap a =
      2 / RHTower.thetaTiltMoment a 0 *
        ∫ x : ℝ in Set.Ioi 0,
          (thetaHasseExecutionEntropyStatistic x -
            thetaHasseExecutionEntropyStatistic (-x)) *
            Real.sinh (a * x) * RHTower.thetaCuspFullSource x :=
  thetaTiltStatisticReflectionGap_eq_sinh_Ioi
    continuous_thetaHasseExecutionEntropyStatistic
    norm_thetaHasseExecutionEntropyStatistic_le ha

/-! ## Common-recovery and Fourier/Xi composition -/

theorem thetaCarrierPacket_fst {a : ℝ} (ha : |a| ≤ 1) :
    (RHTower.thetaCarrierPacket a).fst = RHTower.thetaTiltProb a := by
  letI := RHTower.thetaTiltProb_isProbabilityMeasure ha
  rw [RHTower.thetaCarrierPacket]
  exact splitFormation_recovers_observer
    (RHTower.thetaTiltProb a) RHTower.thetaHasseProfile.kernel

theorem thetaHasseExecutionTVAverage_eq_thetaCarrierPacket_fst_integral
    {a : ℝ} (ha : |a| ≤ 1) :
    thetaHasseExecutionTVAverage a =
      ∫ x : ℝ, thetaHasseExecutionTVStatistic x ∂(RHTower.thetaCarrierPacket a).fst := by
  rw [thetaCarrierPacket_fst ha]
  exact thetaHasseExecutionTVAverage_eq_integral ha

theorem thetaHasseExecutionEntropyAverage_eq_thetaCarrierPacket_fst_integral
    {a : ℝ} (ha : |a| ≤ 1) :
    thetaHasseExecutionEntropyAverage a =
      ∫ x : ℝ, thetaHasseExecutionEntropyStatistic x ∂(RHTower.thetaCarrierPacket a).fst := by
  rw [thetaCarrierPacket_fst ha]
  exact thetaHasseExecutionEntropyAverage_eq_integral ha

theorem thetaHasseContinuous_commonRecovery_composition
    {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    (RHTower.thetaCarrierPacket a).fst = RHTower.thetaTiltProb a ∧
    formationLiftKernel RHTower.thetaHasseProfile.kernel (fun x : ℝ => -x) measurable_neg
        ∘ₘ RHTower.thetaCarrierPacket a = RHTower.thetaCarrierPacket (-a) ∧
    klDiv (RHTower.thetaCarrierPacket a) (RHTower.thetaCarrierPacket b) =
        klDiv (RHTower.thetaTiltProb a) (RHTower.thetaTiltProb b) ∧
    klDiv
        (formationLiftKernel RHTower.thetaHasseProfile.kernel (fun x : ℝ => -x) measurable_neg
          ∘ₘ RHTower.thetaCarrierPacket a)
        (formationLiftKernel RHTower.thetaHasseProfile.kernel (fun x : ℝ => -x) measurable_neg
          ∘ₘ RHTower.thetaCarrierPacket b) =
        klDiv (RHTower.thetaCarrierPacket a) (RHTower.thetaCarrierPacket b) ∧
    thetaHasseExecutionTVAverage a =
        ∫ x : ℝ, thetaHasseExecutionTVStatistic x ∂(RHTower.thetaCarrierPacket a).fst ∧
    thetaHasseExecutionEntropyAverage a =
        ∫ x : ℝ, thetaHasseExecutionEntropyStatistic x ∂(RHTower.thetaCarrierPacket a).fst := by
  exact ⟨thetaCarrierPacket_fst ha,
    RHTower.thetaCarrierPacket_reflect ha,
    RHTower.klDiv_thetaCarrierPacket ha hb,
    RHTower.klDiv_thetaCarrierPacket_lift_isometry ha hb,
    thetaHasseExecutionTVAverage_eq_thetaCarrierPacket_fst_integral ha,
    thetaHasseExecutionEntropyAverage_eq_thetaCarrierPacket_fst_integral ha⟩

noncomputable def thetaTiltCharacteristic (a t : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) ∂(RHTower.thetaTiltProb a)

theorem integral_thetaTiltProb_complex {a : ℝ} (ha : |a| ≤ 1) (f : ℝ → ℂ) :
    ∫ x : ℝ, f x ∂(RHTower.thetaTiltProb a) =
      (∫ x : ℝ, f x *
        ((Real.exp (a * x) * RHTower.thetaCuspFullSource x : ℝ) : ℂ)) /
          (RHTower.thetaTiltMoment a 0 : ℂ) := by
  rw [RHTower.thetaTiltProb_eq_withDensity ha,
    integral_withDensity_eq_integral_toReal_smul
      (RHTower.measurable_thetaTiltProbDensity a)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [RHTower.thetaTiltDensityToReal ha]
  rw [← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change (((Real.exp (a * x) * RHTower.thetaCuspFullSource x /
      RHTower.thetaTiltMoment a 0 : ℝ) : ℂ) * f x) =
    f x * ((Real.exp (a * x) * RHTower.thetaCuspFullSource x : ℝ) : ℂ) /
      (RHTower.thetaTiltMoment a 0 : ℂ)
  push_cast
  ring

theorem integral_thetaCharacteristic_numerator_eq_XiC
    {a : ℝ} (ha : |a| < 1) (t : ℝ) :
    (∫ x : ℝ, Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) *
        ((Real.exp (a * x) * RHTower.thetaCuspFullSource x : ℝ) : ℂ)) =
      RHTower.XiC ((t : ℂ) + (a : ℂ) * Complex.I) := by
  have hw : ((t : ℂ) + (a : ℂ) * Complex.I) ∈
      RHTower.thetaCuspFourierLaplaceStrip := by
    simp only [RHTower.thetaCuspFourierLaplaceStrip, Set.mem_setOf_eq,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_add, mul_one]
    simpa using abs_lt.mp ha
  rw [← RHTower.thetaCuspFourierLaplace_eq_XiC_on_strip hw,
    RHTower.thetaCuspFourierLaplace]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  rw [RHTower.thetaCuspFourierLaplaceIntegrand]
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  have hIa : -Complex.I * ((a : ℂ) * Complex.I) = (a : ℂ) := by
    rw [show -Complex.I * ((a : ℂ) * Complex.I) =
      -(Complex.I * Complex.I) * (a : ℂ) by ring, Complex.I_mul_I]
    ring
  symm
  calc
    -Complex.I * ((t : ℂ) + (a : ℂ) * Complex.I) * (x : ℂ) =
        -Complex.I * (t : ℂ) * (x : ℂ) +
          (-Complex.I * ((a : ℂ) * Complex.I)) * (x : ℂ) := by ring
    _ = -Complex.I * (t : ℂ) * (x : ℂ) + (a : ℂ) * (x : ℂ) := by rw [hIa]

theorem thetaTiltCharacteristic_eq_XiC {a : ℝ} (ha : |a| < 1) (t : ℝ) :
    thetaTiltCharacteristic a t =
      RHTower.XiC ((t : ℂ) + (a : ℂ) * Complex.I) /
        RHTower.XiC (Complex.I * (a : ℂ)) := by
  rw [thetaTiltCharacteristic, integral_thetaTiltProb_complex ha.le,
    integral_thetaCharacteristic_numerator_eq_XiC ha t,
    RHTower.thetaTiltMoment_zero_eq_XiC]

/-! ## Four-organ conservation and central selection capstones -/

theorem thetaHasseExecutionTVAverage_eq_integral_one_sub_purity
    {a : ℝ} (ha : |a| ≤ 1) :
    thetaHasseExecutionTVAverage a =
      ∫ x : ℝ, 1 - ∑' n : ℕ, geometricLayerMass (thetaHasseRatio x) n ^ 2
        ∂(RHTower.thetaTiltProb a) := by
  rw [thetaHasseExecutionTVAverage_eq_integral ha]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact geometricExecutionTV_eq_one_sub_purity
    (thetaHasseRatio_pos x).le (lt_trans (thetaHasseRatio_lt_half x) (by norm_num))

theorem thetaHasseExecutionEntropyAverage_eq_integral_layerShannon
    {a : ℝ} (ha : |a| ≤ 1) :
    thetaHasseExecutionEntropyAverage a =
      ∫ x : ℝ, ∑' n : ℕ, geometricLayerShannonTerm (thetaHasseRatio x) n
        ∂(RHTower.thetaTiltProb a) := by
  rw [thetaHasseExecutionEntropyAverage_eq_integral ha]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact (tsum_geometricLayerShannonTerm (thetaHasseRatio_pos x)
    (lt_trans (thetaHasseRatio_lt_half x) (by norm_num))).symm

theorem thetaHasseExecutionTV_balance_forces_central_sigma
    {σ : ℝ} (hσ : |1 / 2 - σ| < 1)
    (hbalance : thetaHasseExecutionTVAverage (1 / 2 - σ) =
      thetaHasseExecutionTVAverage (-(1 / 2 - σ))) : σ = 1 / 2 := by
  have hgap : thetaHasseExecutionTVReflectionGap (1 / 2 - σ) = 0 := by
    rw [thetaHasseExecutionTVReflectionGap, thetaTiltStatisticReflectionGap]
    exact sub_eq_zero.mpr hbalance
  have hcenter := (thetaHasseExecutionTVReflectionGap_eq_zero_iff hσ).mp hgap
  linarith

theorem thetaHasseExecutionEntropy_balance_forces_central_sigma
    {σ : ℝ} (hσ : |1 / 2 - σ| < 1)
    (hbalance : thetaHasseExecutionEntropyAverage (1 / 2 - σ) =
      thetaHasseExecutionEntropyAverage (-(1 / 2 - σ))) : σ = 1 / 2 := by
  have hgap : thetaHasseExecutionEntropyReflectionGap (1 / 2 - σ) = 0 := by
    rw [thetaHasseExecutionEntropyReflectionGap, thetaTiltStatisticReflectionGap]
    exact sub_eq_zero.mpr hbalance
  have hcenter := (thetaHasseExecutionEntropyReflectionGap_eq_zero_iff hσ).mp hgap
  linarith

end GaloisForLFunctions.HTGeometry
