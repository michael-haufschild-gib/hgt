import GaloisForLFunctions.RHTower.CCMFirstClockHalfWaveReflection
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Apex-superlevel majorization and its atomic obstruction

This module lifts the exact first-clock half-wave balance to amplitude measures.  Layer-cake
integration proves that universal superlevel dominance would imply RH.  The final declarations
test that stronger candidate against the source's discrete prime-power geometry.
-/

open MeasureTheory
open Set
open scoped BigOperators
open Finset

noncomputable section

namespace RHTower

def ccmFirstClockAlignedAmplitude (L : ℝ) (k : ℕ) : ℝ :=
  max (Real.sin ((2 * Real.pi / L) * Real.log k)) 0

def ccmFirstClockCounterAmplitude (L : ℝ) (k : ℕ) : ℝ :=
  max (-Real.sin ((2 * Real.pi / L) * Real.log k)) 0

def ccmFirstClockAlignedMeasure (L : ℝ) : Measure ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
    ENNReal.ofReal (criticalMellinAtomWeight k) •
      Measure.dirac (ccmFirstClockAlignedAmplitude L k)

def ccmFirstClockCounterMeasure (L : ℝ) : Measure ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
    ENNReal.ofReal (criticalMellinAtomWeight k) •
      Measure.dirac (ccmFirstClockCounterAmplitude L k)

theorem ccmFirstClock_integral_finsetWeightedDirac
    (s : Finset ℕ) (w x : ℕ → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) :
    ∫ y : ℝ, y ∂(∑ k ∈ s,
      ENNReal.ofReal (w k) • Measure.dirac (x k)) =
      ∑ k ∈ s, w k * x k := by
  have hint :
      ∀ k ∈ s,
        Integrable (fun y : ℝ => y)
          (ENNReal.ofReal (w k) • Measure.dirac (x k)) := by
    intro k _hk
    exact (integrable_dirac (by simp)).smul_measure (by simp)
  rw [integral_finsetSum_measure hint]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (hw k hk), smul_eq_mul]

theorem ccmFirstClock_integral_finsetWeightedDirac_function
    (s : Finset ℕ) (w x : ℕ → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (f : ℝ → ℝ) :
    ∫ y : ℝ, f y ∂(∑ k ∈ s,
      ENNReal.ofReal (w k) • Measure.dirac (x k)) =
      ∑ k ∈ s, w k * f (x k) := by
  have hint :
      ∀ k ∈ s,
        Integrable f
          (ENNReal.ofReal (w k) • Measure.dirac (x k)) := by
    intro k _hk
    exact (integrable_dirac (by simp)).smul_measure (by simp)
  rw [integral_finsetSum_measure hint]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (hw k hk), smul_eq_mul]

theorem ccmFirstClockAlignedMeasure_moment (L : ℝ) :
    ∫ x : ℝ, x ∂ccmFirstClockAlignedMeasure L =
      ccmFirstClockPrimeAlignedMass L (2 * Real.pi / L) := by
  rw [ccmFirstClockAlignedMeasure,
    ccmFirstClock_integral_finsetWeightedDirac _ _ _
      (fun k _hk => criticalMellinAtomWeight_nonneg k)]
  rfl

theorem ccmFirstClockCounterMeasure_moment (L : ℝ) :
    ∫ x : ℝ, x ∂ccmFirstClockCounterMeasure L =
      ccmFirstClockPrimeCounterMass L (2 * Real.pi / L) := by
  rw [ccmFirstClockCounterMeasure,
    ccmFirstClock_integral_finsetWeightedDirac _ _ _
      (fun k _hk => criticalMellinAtomWeight_nonneg k)]
  rfl

def ccmFirstClockHalfWaveAmplitude (L h : ℝ) : ℝ :=
  max (Real.sin ((2 * Real.pi / L) * h)) 0

def ccmFirstClockContinuousBaseMeasure (L : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioc 0 (L / 2))).withDensity
    (fun h => ENNReal.ofReal (ccmFirstClockContinuousReflectionGap L h))

def ccmFirstClockContinuousAmplitudeMeasure (L : ℝ) : Measure ℝ :=
  Measure.map (ccmFirstClockHalfWaveAmplitude L) (ccmFirstClockContinuousBaseMeasure L)

lemma ccmFirstClockHalfWaveAmplitude_measurable (L : ℝ) :
    Measurable (ccmFirstClockHalfWaveAmplitude L) := by
  unfold ccmFirstClockHalfWaveAmplitude
  measurability

lemma ccmFirstClockContinuousReflectionGap_measurable (L : ℝ) :
    Measurable (ccmFirstClockContinuousReflectionGap L) := by
  unfold ccmFirstClockContinuousReflectionGap
    ccmFirstClockContinuousSourceDensity
    ccmPublishedArchimedeanDensity
  measurability

lemma ccmFirstClockHalfWaveAmplitude_eq_sin
    {L h : ℝ} (hL : 0 < L) (hh : h ∈ Set.Ioc 0 (L / 2)) :
    ccmFirstClockHalfWaveAmplitude L h =
      Real.sin ((2 * Real.pi / L) * h) := by
  have hfreq : 0 < 2 * Real.pi / L := div_pos (by positivity) hL
  have hphase0 : 0 ≤ (2 * Real.pi / L) * h :=
    mul_nonneg hfreq.le hh.1.le
  have hhalf : (2 * Real.pi / L) * (L / 2) = Real.pi := by
    field_simp
  have hphasePi : (2 * Real.pi / L) * h ≤ Real.pi := by
    calc
      (2 * Real.pi / L) * h ≤ (2 * Real.pi / L) * (L / 2) :=
        mul_le_mul_of_nonneg_left hh.2 hfreq.le
      _ = Real.pi := hhalf
  rw [ccmFirstClockHalfWaveAmplitude,
    max_eq_left (Real.sin_nonneg_of_nonneg_of_le_pi hphase0 hphasePi)]

theorem ccmFirstClockContinuousAmplitudeMeasure_moment
    {L : ℝ} (hL : 0 < L) :
    ∫ x : ℝ, x ∂ccmFirstClockContinuousAmplitudeMeasure L =
      ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) := by
  rw [ccmFirstClockContinuousAmplitudeMeasure,
    integral_map
      (ccmFirstClockHalfWaveAmplitude_measurable L).aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x)
        (Measure.map (ccmFirstClockHalfWaveAmplitude L) (ccmFirstClockContinuousBaseMeasure L)))]
  rw [ccmFirstClockContinuousBaseMeasure,
    integral_withDensity_eq_integral_toReal_smul
      ((ccmFirstClockContinuousReflectionGap_measurable L).ennreal_ofReal)
      (by simp) (ccmFirstClockHalfWaveAmplitude L)]
  rw [ccmFirstClockContinuousHalfWaveBudget,
    intervalIntegral.integral_of_le (by linarith : 0 ≤ L / 2)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
  have hgap :=
    (ccmFirstClockContinuousReflectionGap_pos hL hh.1)
  rw [ENNReal.toReal_ofReal hgap.le,
    ccmFirstClockHalfWaveAmplitude_eq_sin hL hh]
  simp only [smul_eq_mul]
  ring

def ccmFirstClockApexObservable (x : ℝ) : ℝ := max x 0

lemma ccmFirstClockApexObservable_measurable :
    Measurable ccmFirstClockApexObservable := by
  unfold ccmFirstClockApexObservable
  measurability

lemma ccmFirstClockApexObservable_nonneg (x : ℝ) :
    0 ≤ ccmFirstClockApexObservable x :=
  le_max_right _ _

theorem ccmFirstClockAlignedMeasure_apexMoment (L : ℝ) :
    ∫ x : ℝ, ccmFirstClockApexObservable x ∂ccmFirstClockAlignedMeasure L =
      ccmFirstClockPrimeAlignedMass L (2 * Real.pi / L) := by
  rw [ccmFirstClockAlignedMeasure,
    ccmFirstClock_integral_finsetWeightedDirac_function _ _ _
      (fun k _hk => criticalMellinAtomWeight_nonneg k)]
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [ccmFirstClockApexObservable, ccmFirstClockAlignedAmplitude]
  rw [max_eq_left (le_max_right _ _)]

theorem ccmFirstClockCounterMeasure_apexMoment (L : ℝ) :
    ∫ x : ℝ, ccmFirstClockApexObservable x ∂ccmFirstClockCounterMeasure L =
      ccmFirstClockPrimeCounterMass L (2 * Real.pi / L) := by
  rw [ccmFirstClockCounterMeasure,
    ccmFirstClock_integral_finsetWeightedDirac_function _ _ _
      (fun k _hk => criticalMellinAtomWeight_nonneg k)]
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [ccmFirstClockApexObservable, ccmFirstClockCounterAmplitude]
  rw [max_eq_left (le_max_right _ _)]

lemma ccmFirstClockContinuousAmplitude_integrable
    {L : ℝ} (hL : 0 < L) :
    Integrable (ccmFirstClockHalfWaveAmplitude L) (ccmFirstClockContinuousBaseMeasure L) := by
  have hperiod : (2 * Real.pi / L) * L = 2 * Real.pi := by
    field_simp
  have hi :=
    intervalIntegrable_ccmFirstClockContinuousHalfWave hL hperiod
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by linarith : 0 ≤ L / 2)] at hi
  rw [ccmFirstClockContinuousBaseMeasure,
    integrable_withDensity_iff
      ((ccmFirstClockContinuousReflectionGap_measurable L).ennreal_ofReal)
      (by simp)]
  refine hi.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
  have hgap :=
    ccmFirstClockContinuousReflectionGap_pos hL hh.1
  rw [ENNReal.toReal_ofReal hgap.le,
    ccmFirstClockHalfWaveAmplitude_eq_sin hL hh]

theorem ccmFirstClockContinuousAmplitudeMeasure_apexMoment
    {L : ℝ} (hL : 0 < L) :
    ∫ x : ℝ, ccmFirstClockApexObservable x ∂ccmFirstClockContinuousAmplitudeMeasure L =
      ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) := by
  rw [ccmFirstClockContinuousAmplitudeMeasure,
    integral_map
      (ccmFirstClockHalfWaveAmplitude_measurable L).aemeasurable
      ccmFirstClockApexObservable_measurable.aestronglyMeasurable]
  have happ :
      (fun h => ccmFirstClockApexObservable (ccmFirstClockHalfWaveAmplitude L h)) =
        ccmFirstClockHalfWaveAmplitude L := by
    funext h
    exact max_eq_left (le_max_right _ _)
  rw [happ]
  have hm := ccmFirstClockContinuousAmplitudeMeasure_moment hL
  rw [ccmFirstClockContinuousAmplitudeMeasure,
    integral_map
      (ccmFirstClockHalfWaveAmplitude_measurable L).aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x)
        (Measure.map (ccmFirstClockHalfWaveAmplitude L) (ccmFirstClockContinuousBaseMeasure L)))] at hm
  exact hm

lemma ccmFirstClockAlignedMeasure_apexIntegrable (L : ℝ) :
    Integrable ccmFirstClockApexObservable (ccmFirstClockAlignedMeasure L) := by
  rw [ccmFirstClockAlignedMeasure, integrable_finsetSum_measure]
  intro k _hk
  exact (integrable_dirac (by simp [ccmFirstClockApexObservable])).smul_measure (by simp)

lemma ccmFirstClockCounterMeasure_apexIntegrable (L : ℝ) :
    Integrable ccmFirstClockApexObservable (ccmFirstClockCounterMeasure L) := by
  rw [ccmFirstClockCounterMeasure, integrable_finsetSum_measure]
  intro k _hk
  exact (integrable_dirac (by simp [ccmFirstClockApexObservable])).smul_measure (by simp)

lemma ccmFirstClockContinuousAmplitudeMeasure_apexIntegrable
    {L : ℝ} (hL : 0 < L) :
    Integrable ccmFirstClockApexObservable (ccmFirstClockContinuousAmplitudeMeasure L) := by
  rw [ccmFirstClockContinuousAmplitudeMeasure,
    integrable_map_measure
      ccmFirstClockApexObservable_measurable.aestronglyMeasurable
      (ccmFirstClockHalfWaveAmplitude_measurable L).aemeasurable]
  refine (ccmFirstClockContinuousAmplitude_integrable hL).congr ?_
  filter_upwards [] with h
  exact (max_eq_left (le_max_right _ _)).symm

def ccmFirstClockGoodApexMeasure (L : ℝ) : Measure ℝ :=
  ccmFirstClockContinuousAmplitudeMeasure L + ccmFirstClockAlignedMeasure L

def ccmFirstClockBadApexMeasure (L : ℝ) : Measure ℝ :=
  ccmFirstClockCounterMeasure L

theorem ccmFirstClockGoodApexMeasure_moment
    {L : ℝ} (hL : 0 < L) :
    ∫ x : ℝ, ccmFirstClockApexObservable x ∂ccmFirstClockGoodApexMeasure L =
      ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) +
        ccmFirstClockPrimeAlignedMass L (2 * Real.pi / L) := by
  rw [ccmFirstClockGoodApexMeasure,
    integral_add_measure
      (ccmFirstClockContinuousAmplitudeMeasure_apexIntegrable hL)
      (ccmFirstClockAlignedMeasure_apexIntegrable L),
    ccmFirstClockContinuousAmplitudeMeasure_apexMoment hL,
    ccmFirstClockAlignedMeasure_apexMoment]

theorem ccmFirstClockBadApexMeasure_moment (L : ℝ) :
    ∫ x : ℝ, ccmFirstClockApexObservable x ∂ccmFirstClockBadApexMeasure L =
      ccmFirstClockPrimeCounterMass L (2 * Real.pi / L) := by
  exact ccmFirstClockCounterMeasure_apexMoment L

lemma ccmFirstClockGoodApexMeasure_integrable
    {L : ℝ} (hL : 0 < L) :
    Integrable ccmFirstClockApexObservable (ccmFirstClockGoodApexMeasure L) := by
  exact (ccmFirstClockContinuousAmplitudeMeasure_apexIntegrable hL).add_measure
    (ccmFirstClockAlignedMeasure_apexIntegrable L)

lemma ccmFirstClockBadApexMeasure_integrable (L : ℝ) :
    Integrable ccmFirstClockApexObservable (ccmFirstClockBadApexMeasure L) :=
  ccmFirstClockCounterMeasure_apexIntegrable L

theorem ccmFirstClock_lintegral_ofReal_le_of_superlevel_dominance
    {μ ν : Measure ℝ} {f : ℝ → ℝ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf : Measurable f)
    (htail : ∀ t : ℝ, 0 < t →
      μ {x | t ≤ f x} ≤ ν {x | t ≤ f x}) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
  rw [lintegral_eq_lintegral_meas_le μ
      (Filter.Eventually.of_forall hf0) hf.aemeasurable,
    lintegral_eq_lintegral_meas_le ν
      (Filter.Eventually.of_forall hf0) hf.aemeasurable]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact htail t ht

def CCMFirstClockApexSuperlevelMajorization : Prop :=
  ∀ L : ℝ, Real.pi / 2 ≤ L →
    ∀ t : ℝ, 0 < t →
      ccmFirstClockBadApexMeasure L {x | t ≤ ccmFirstClockApexObservable x} ≤
        ccmFirstClockGoodApexMeasure L {x | t ≤ ccmFirstClockApexObservable x}

theorem ccmFirstClockApexSuperlevelMajorization_implies_halfWaveDominance
    (hmajor : CCMFirstClockApexSuperlevelMajorization) :
    CCMFirstClockPrimeHalfWaveDominance := by
  intro L hL
  have hLpos : 0 < L :=
    lt_of_lt_of_le (by positivity : 0 < Real.pi / 2) hL
  have hperiod : (2 * Real.pi / L) * L = 2 * Real.pi := by
    field_simp
  have hlin :=
    ccmFirstClock_lintegral_ofReal_le_of_superlevel_dominance
      ccmFirstClockApexObservable_nonneg ccmFirstClockApexObservable_measurable
      (hmajor L hL)
  have hbadOfReal :=
    ofReal_integral_eq_lintegral_ofReal
      (ccmFirstClockBadApexMeasure_integrable L)
      (Filter.Eventually.of_forall ccmFirstClockApexObservable_nonneg)
  have hgoodOfReal :=
    ofReal_integral_eq_lintegral_ofReal
      (ccmFirstClockGoodApexMeasure_integrable hLpos)
      (Filter.Eventually.of_forall ccmFirstClockApexObservable_nonneg)
  rw [← hbadOfReal, ← hgoodOfReal,
    ccmFirstClockBadApexMeasure_moment,
    ccmFirstClockGoodApexMeasure_moment hLpos] at hlin
  exact
    (ENNReal.ofReal_le_ofReal_iff
      (add_nonneg
        (ccmFirstClockContinuousHalfWaveBudget_pos hLpos hperiod).le
        (ccmFirstClockPrimeAlignedMass_nonneg L (2 * Real.pi / L)))).1 hlin

theorem ccmFirstClockApexSuperlevelMajorization_implies_rh
    (hmajor : CCMFirstClockApexSuperlevelMajorization) :
    RiemannHypothesis :=
  ccmFirstClockPrimeHalfWaveDominance_iff_rh.mp
    (ccmFirstClockApexSuperlevelMajorization_implies_halfWaveDominance hmajor)

/-- Aperture at which the `k = 4` prime-power atom sits exactly at the negative sine apex. -/
def ccmFirstClockNegativeApexLength : ℝ :=
  (8 / 3 : ℝ) * Real.log 2

lemma ccmFirstClockNegativeApexLength_pos :
    0 < ccmFirstClockNegativeApexLength := by
  unfold ccmFirstClockNegativeApexLength
  exact mul_pos (by norm_num) (Real.log_pos (by norm_num))

lemma ccmFirstClockNegativeApexLength_ge_pi_div_two :
    Real.pi / 2 ≤ ccmFirstClockNegativeApexLength := by
  have hlog := Real.log_two_gt_d9
  have hpi := Real.pi_lt_d2
  unfold ccmFirstClockNegativeApexLength
  norm_num at hlog hpi ⊢
  linarith

lemma real_sin_eq_one_of_nonneg_of_le_two_pi
    {x : ℝ} (hx0 : 0 ≤ x) (hx2pi : x ≤ 2 * Real.pi)
    (hsin : Real.sin x = 1) :
    x = Real.pi / 2 := by
  rcases Real.sin_eq_one_iff.mp hsin with ⟨n, hn⟩
  have hnzero : n = 0 := by
    by_contra hne
    have hcases : n ≤ -1 ∨ 1 ≤ n := by omega
    rcases hcases with hnneg | hnpos
    · have hnneg' : (n : ℝ) ≤ -1 := by exact_mod_cast hnneg
      nlinarith [Real.pi_pos]
    · have hnpos' : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      nlinarith [Real.pi_pos]
  subst n
  norm_num at hn
  exact hn.symm

lemma ccmFirstClockNegativeApex_phase_four :
    (2 * Real.pi / ccmFirstClockNegativeApexLength) * Real.log 4 =
      3 * Real.pi / 2 := by
  have hlog2ne : Real.log 2 ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hlog4]
  unfold ccmFirstClockNegativeApexLength
  field_simp
  ring

lemma ccmFirstClockCounterAmplitude_four_negativeApex :
    ccmFirstClockCounterAmplitude ccmFirstClockNegativeApexLength 4 = 1 := by
  rw [ccmFirstClockCounterAmplitude]
  change
    max (-Real.sin ((2 * Real.pi / ccmFirstClockNegativeApexLength) *
      Real.log (4 : ℝ))) 0 = 1
  rw [ccmFirstClockNegativeApex_phase_four]
  have hangle :
      3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
  rw [hangle, Real.sin_add, Real.sin_pi, Real.cos_pi,
    Real.sin_pi_div_two, Real.cos_pi_div_two]
  norm_num

def ccmFirstClockClosedApexSet : Set ℝ :=
  {x | 1 ≤ ccmFirstClockApexObservable x}

lemma ccmFirstClockClosedApexSet_measurable :
    MeasurableSet ccmFirstClockClosedApexSet := by
  unfold ccmFirstClockClosedApexSet
  exact measurableSet_le measurable_const ccmFirstClockApexObservable_measurable

lemma four_mem_ccmFirstClockNegativeApex_cutoff :
    4 ∈ Finset.Icc 2
      ⌊Real.exp ccmFirstClockNegativeApexLength⌋₊ := by
  rw [Finset.mem_Icc]
  constructor
  · norm_num
  · apply (Nat.le_floor_iff
      (Real.exp_pos ccmFirstClockNegativeApexLength).le).mpr
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
      ring
    have hlog4lt :
        Real.log 4 < ccmFirstClockNegativeApexLength := by
      rw [hlog4]
      unfold ccmFirstClockNegativeApexLength
      nlinarith
    calc
      (4 : ℝ) = Real.exp (Real.log 4) := by
        rw [Real.exp_log (by norm_num)]
      _ ≤ Real.exp ccmFirstClockNegativeApexLength :=
        (Real.exp_le_exp.mpr hlog4lt.le)

lemma criticalMellinAtomWeight_four_pos :
    0 < criticalMellinAtomWeight 4 := by
  rw [criticalMellinAtomWeight]
  apply mul_pos
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · exact ArithmeticFunction.vonMangoldt_pos_iff.mpr
      ⟨2, 2, Nat.prime_two.prime, by norm_num, by norm_num⟩

lemma ccmFirstClockBadApexMeasure_closedApex_pos :
    0 <
      ccmFirstClockBadApexMeasure ccmFirstClockNegativeApexLength
        ccmFirstClockClosedApexSet := by
  rw [ccmFirstClockBadApexMeasure, ccmFirstClockCounterMeasure]
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  refine lt_of_lt_of_le ?_
    (Finset.single_le_sum
      (fun k _hk => Measure.zero_le _ _)
      four_mem_ccmFirstClockNegativeApex_cutoff)
  ·
    rw [Measure.smul_apply,
      Measure.dirac_apply_of_mem]
    · simpa using ENNReal.ofReal_pos.mpr criticalMellinAtomWeight_four_pos
    · change 1 ≤ ccmFirstClockApexObservable
        (ccmFirstClockCounterAmplitude ccmFirstClockNegativeApexLength 4)
      rw [ccmFirstClockCounterAmplitude_four_negativeApex]
      norm_num [ccmFirstClockApexObservable]

lemma ccmFirstClockAlignedAmplitude_lt_one_at_negativeApex
    {k : ℕ}
    (hk : k ∈ Finset.Icc 2
      ⌊Real.exp ccmFirstClockNegativeApexLength⌋₊) :
    ccmFirstClockAlignedAmplitude ccmFirstClockNegativeApexLength k < 1 := by
  have hLpos := ccmFirstClockNegativeApexLength_pos
  have hfreqpos :
      0 < 2 * Real.pi / ccmFirstClockNegativeApexLength :=
    div_pos (by positivity) hLpos
  have hkpos : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (Finset.mem_Icc.mp hk).1)
  have hkexp :
      (k : ℝ) ≤ Real.exp ccmFirstClockNegativeApexLength :=
    (Nat.le_floor_iff
      (Real.exp_pos ccmFirstClockNegativeApexLength).le).mp
      (Finset.mem_Icc.mp hk).2
  have hlogle :
      Real.log (k : ℝ) ≤ ccmFirstClockNegativeApexLength :=
    (Real.log_le_iff_le_exp hkpos).mpr hkexp
  let phase :=
    (2 * Real.pi / ccmFirstClockNegativeApexLength) *
      Real.log (k : ℝ)
  have hphase0 : 0 ≤ phase := by
    exact mul_nonneg hfreqpos.le (Real.log_natCast_nonneg k)
  have hperiod :
      (2 * Real.pi / ccmFirstClockNegativeApexLength) *
        ccmFirstClockNegativeApexLength = 2 * Real.pi := by
    field_simp [hLpos.ne']
  have hphase2pi : phase ≤ 2 * Real.pi := by
    calc
      phase ≤
          (2 * Real.pi / ccmFirstClockNegativeApexLength) *
            ccmFirstClockNegativeApexLength :=
        mul_le_mul_of_nonneg_left hlogle hfreqpos.le
      _ = 2 * Real.pi := hperiod
  have hampLe :
      ccmFirstClockAlignedAmplitude ccmFirstClockNegativeApexLength k ≤ 1 := by
    rw [ccmFirstClockAlignedAmplitude]
    exact max_le (Real.sin_le_one phase) zero_le_one
  refine lt_of_le_of_ne hampLe ?_
  intro hampOne
  have hsinNonneg : 0 ≤ Real.sin phase := by
    by_contra hneg
    have hzero :
        ccmFirstClockAlignedAmplitude ccmFirstClockNegativeApexLength k = 0 := by
      rw [ccmFirstClockAlignedAmplitude, max_eq_right (le_of_not_ge hneg)]
    linarith
  have hsinOne : Real.sin phase = 1 := by
    rw [ccmFirstClockAlignedAmplitude, max_eq_left hsinNonneg] at hampOne
    exact hampOne
  have hphase :
      phase = Real.pi / 2 :=
    real_sin_eq_one_of_nonneg_of_le_two_pi hphase0 hphase2pi hsinOne
  have hLne : ccmFirstClockNegativeApexLength ≠ 0 := hLpos.ne'
  dsimp [phase] at hphase
  field_simp [hLne] at hphase
  have hcancel :
      2 * Real.log (k : ℝ) =
        ccmFirstClockNegativeApexLength / 2 := by
    apply (mul_left_cancel₀ Real.pi_ne_zero)
    nlinarith
  have hlogEq :
      Real.log (k : ℝ) = (2 / 3 : ℝ) * Real.log 2 := by
    unfold ccmFirstClockNegativeApexLength at hcancel
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hlogCube :
      Real.log ((k : ℝ) ^ 3) = Real.log 4 := by
    rw [Real.log_pow, hlogEq, hlog4]
    norm_num
    ring
  have hcube : (k : ℝ) ^ 3 = 4 := by
    have hexp := congrArg Real.exp hlogCube
    rw [Real.exp_log (by positivity : 0 < (k : ℝ) ^ 3),
      Real.exp_log (by norm_num : (0 : ℝ) < 4)] at hexp
    exact hexp
  have hkge : (2 : ℝ) ≤ k := by
    exact_mod_cast (Finset.mem_Icc.mp hk).1
  have hcubedge : (2 : ℝ) ^ 3 ≤ (k : ℝ) ^ 3 := by
    gcongr
  norm_num at hcubedge
  linarith

lemma ccmFirstClockAlignedMeasure_closedApex_eq_zero :
    ccmFirstClockAlignedMeasure ccmFirstClockNegativeApexLength
      ccmFirstClockClosedApexSet = 0 := by
  rw [ccmFirstClockAlignedMeasure]
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  have hnotmem :
      ccmFirstClockAlignedAmplitude ccmFirstClockNegativeApexLength k ∉
        ccmFirstClockClosedApexSet := by
    change ¬1 ≤ ccmFirstClockApexObservable
      (ccmFirstClockAlignedAmplitude ccmFirstClockNegativeApexLength k)
    rw [ccmFirstClockApexObservable,
      max_eq_left (by
        exact le_max_right
          (Real.sin ((2 * Real.pi / ccmFirstClockNegativeApexLength) *
            Real.log k)) 0)]
    exact not_le_of_gt
      (ccmFirstClockAlignedAmplitude_lt_one_at_negativeApex hk)
  rw [Measure.smul_apply, Measure.dirac_apply]
  simp [hnotmem]

lemma ccmFirstClockHalfWaveAmplitude_apex_unique
    {L h : ℝ} (hL : 0 < L) (hh : h ∈ Set.Ioc 0 (L / 2))
    (hapex : 1 ≤
      ccmFirstClockApexObservable (ccmFirstClockHalfWaveAmplitude L h)) :
    h = L / 4 := by
  have hampNonneg : 0 ≤ ccmFirstClockHalfWaveAmplitude L h :=
    le_max_right _ _
  have hampLe : ccmFirstClockHalfWaveAmplitude L h ≤ 1 := by
    rw [ccmFirstClockHalfWaveAmplitude]
    exact max_le (Real.sin_le_one _) zero_le_one
  have hampOne : ccmFirstClockHalfWaveAmplitude L h = 1 := by
    rw [ccmFirstClockApexObservable,
      max_eq_left hampNonneg] at hapex
    exact le_antisymm hampLe hapex
  have hsinOne :
      Real.sin ((2 * Real.pi / L) * h) = 1 := by
    rw [ccmFirstClockHalfWaveAmplitude_eq_sin hL hh] at hampOne
    exact hampOne
  have hfreq : 0 < 2 * Real.pi / L := div_pos (by positivity) hL
  have hphase0 : 0 ≤ (2 * Real.pi / L) * h :=
    mul_nonneg hfreq.le hh.1.le
  have hhalf : (2 * Real.pi / L) * (L / 2) = Real.pi := by
    field_simp [hL.ne']
  have hphasePi : (2 * Real.pi / L) * h ≤ Real.pi := by
    calc
      (2 * Real.pi / L) * h ≤ (2 * Real.pi / L) * (L / 2) :=
        mul_le_mul_of_nonneg_left hh.2 hfreq.le
      _ = Real.pi := hhalf
  have hphase :
      (2 * Real.pi / L) * h = Real.pi / 2 :=
    real_sin_eq_one_of_nonneg_of_le_two_pi hphase0
      (hphasePi.trans (by linarith [Real.pi_pos])) hsinOne
  field_simp [hL.ne'] at hphase
  have hcancel : 4 * h = L := by
    apply mul_left_cancel₀ Real.pi_ne_zero
    nlinarith
  linarith

lemma ccmFirstClockContinuousAmplitudeMeasure_closedApex_eq_zero :
    ccmFirstClockContinuousAmplitudeMeasure
        ccmFirstClockNegativeApexLength ccmFirstClockClosedApexSet = 0 := by
  rw [ccmFirstClockContinuousAmplitudeMeasure,
    Measure.map_apply
      (ccmFirstClockHalfWaveAmplitude_measurable
        ccmFirstClockNegativeApexLength)
      ccmFirstClockClosedApexSet_measurable]
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply
    (ccmFirstClockClosedApexSet_measurable.preimage
      (ccmFirstClockHalfWaveAmplitude_measurable
        ccmFirstClockNegativeApexLength))]
  apply measure_mono_null
    (t := {ccmFirstClockNegativeApexLength / 4})
  · intro h hh
    rw [Set.mem_inter_iff] at hh
    rw [Set.mem_singleton_iff]
    exact ccmFirstClockHalfWaveAmplitude_apex_unique
      ccmFirstClockNegativeApexLength_pos hh.2 hh.1
  · simp

lemma ccmFirstClockGoodApexMeasure_closedApex_eq_zero :
    ccmFirstClockGoodApexMeasure ccmFirstClockNegativeApexLength
      ccmFirstClockClosedApexSet = 0 := by
  rw [ccmFirstClockGoodApexMeasure,
    Measure.coe_add, Pi.add_apply,
    ccmFirstClockContinuousAmplitudeMeasure_closedApex_eq_zero,
    ccmFirstClockAlignedMeasure_closedApex_eq_zero,
    zero_add]

/-- The closed-superlevel law is impossible: the prime power `4` is a positive atom at the
negative apex, while the continuous and aligned sides have zero mass at the positive apex. -/
theorem not_ccmFirstClockApexSuperlevelMajorization :
    ¬CCMFirstClockApexSuperlevelMajorization := by
  intro hmajor
  have hdom :=
    hmajor ccmFirstClockNegativeApexLength
      ccmFirstClockNegativeApexLength_ge_pi_div_two 1 zero_lt_one
  change
    ccmFirstClockBadApexMeasure ccmFirstClockNegativeApexLength
        ccmFirstClockClosedApexSet ≤
      ccmFirstClockGoodApexMeasure ccmFirstClockNegativeApexLength
        ccmFirstClockClosedApexSet at hdom
  rw [ccmFirstClockGoodApexMeasure_closedApex_eq_zero] at hdom
  exact (not_le_of_gt ccmFirstClockBadApexMeasure_closedApex_pos) hdom

end RHTower
