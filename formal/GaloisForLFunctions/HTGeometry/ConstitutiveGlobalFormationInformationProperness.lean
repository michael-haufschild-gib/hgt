import Mathlib.Probability.Distributions.Bernoulli
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ClassLaw
import GaloisForLFunctions.HTGeometry.ConstitutiveTimeReversalLikelihoodCocycle
import GaloisForLFunctions.HTGeometry.ConstitutiveGlobalFormationProperness

/-!
# Full-source formation information properness

This module closes the global-information bridge for formation selection.  In the convergence
chamber, the canonical group-class law pushes forward along the least-prime, least-depth occupation
observer to an exact Bernoulli law.  Its symmetric Kullback--Leibler work is the reporter work from
`ConstitutiveGlobalFormationProperness`; two-sided data processing makes it a lower bound for the
full class-law work.  A finite bound on that full work along every source-generated scale is
therefore equivalent to neutral formation.

No Riemann-hypothesis premise or divisor specialization occurs.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal

noncomputable section

def fugacityShiftConv (θ : AbelianZetaConvergentParameters) (u : ℝ) (hu : 0 ≤ u) :
    AbelianZetaConvergentParameters where
  sigma := θ.sigma
  tau := θ.tau + u
  sigma_pos := θ.sigma_pos
  tau_nonneg := add_nonneg θ.tau_nonneg hu
  firstDepth := by linarith [θ.firstDepth]

@[simp] theorem fugacityShiftConv_toParams (θ : AbelianZetaConvergentParameters)
    (u : ℝ) (hu : 0 ≤ u) :
    (fugacityShiftConv θ u hu).toAbelianZetaParameters =
      fugacityShiftParameters θ.toAbelianZetaParameters u hu := rfl

theorem fugacityShiftParameters_zero (θ : AbelianZetaParameters) (h0 : 0 ≤ (0 : ℝ)) :
    fugacityShiftParameters θ 0 h0 = θ := by
  cases θ
  simp [fugacityShiftParameters]

theorem ae_finiteSupport (θ : AbelianZetaConvergentParameters) :
    ∀ᵐ k ∂θ.toAbelianZetaParameters.gasMeasure, (Function.support k).Finite := by
  rw [ae_iff_measure_eq measurableSet_finiteSupport.nullMeasurableSet]
  rw [measure_univ]
  exact θ.measure_finite_occupancy_eq_one

theorem classLaw_map_modeCoordinate (θ : AbelianZetaConvergentParameters)
    (m : AbelianZetaMode) :
    (classLaw θ.toAbelianZetaParameters).map (fun A => A.configuration m) =
      θ.toAbelianZetaParameters.modeLaw m := by
  rw [classLaw_eq_map θ, Measure.map_map (by fun_prop) measurable_classOf]
  rw [← Measure.infinitePi_map_eval (μ := θ.toAbelianZetaParameters.modeLaw) m]
  apply Measure.map_congr
  filter_upwards [ae_finiteSupport θ] with k hk
  exact congrFun (classOf_of_finite hk) m

def occupiedBool (n : ℕ) : Bool := decide (n ≠ 0)

theorem occupiedBool_zero : occupiedBool 0 = false := by simp [occupiedBool]

theorem occupiedBool_pos {n : ℕ} (hn : n ≠ 0) : occupiedBool n = true := by
  simp [occupiedBool, hn]

def ratioUnit (θ : AbelianZetaParameters) (m : AbelianZetaMode) : unitInterval :=
  ⟨θ.ratio m, θ.ratio_pos m |>.le, θ.ratio_lt_one m |>.le⟩

@[simp] theorem ratioUnit_coe (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    (ratioUnit θ m : ℝ) = θ.ratio m := rfl

theorem modeLaw_map_occupiedBool (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    (θ.modeLaw m).map occupiedBool = Ber(true, false, ratioUnit θ m) := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.singleton b)]
  cases b with
  | false =>
      have hpre : occupiedBool ⁻¹' {false} = {0} := by
        ext n
        simp [occupiedBool]
      rw [hpre, θ.modeLaw_zero]
      rw [bernoulliMeasure_apply_of_notMem_of_mem (ratioUnit θ m)
        (MeasurableSet.singleton false) (by simp) (by simp)]
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
  | true =>
      have hpre : occupiedBool ⁻¹' {true} = ({0}ᶜ : Set ℕ) := by
        ext n
        simp [occupiedBool]
      rw [hpre, θ.modeLaw_occupied]
      rw [bernoulliMeasure_apply_of_mem_of_notMem (ratioUnit θ m)
        (MeasurableSet.singleton true) (by simp) (by simp)]
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1

def leastModeObserver (A : AbelianZetaGroupClass) : Bool :=
  occupiedBool (A.configuration leastMode)

theorem classLaw_map_leastModeObserver (θ : AbelianZetaConvergentParameters) :
    (classLaw θ.toAbelianZetaParameters).map leastModeObserver =
      Ber(true, false, ratioUnit θ.toAbelianZetaParameters leastMode) := by
  change (classLaw θ.toAbelianZetaParameters).map
      (occupiedBool ∘ fun A => A.configuration leastMode) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [classLaw_map_modeCoordinate, modeLaw_map_occupiedBool]

def bernoulliDensity (p r : unitInterval) (b : Bool) : ℝ≥0∞ :=
  if b then ENNReal.ofReal ((p : ℝ) / (r : ℝ))
  else ENNReal.ofReal ((1 - (p : ℝ)) / (1 - (r : ℝ)))

theorem withDensity_bool_singleton (μ : Measure Bool) (f : Bool → ℝ≥0∞) (b : Bool) :
    (μ.withDensity f) {b} = f b * μ {b} := by
  rw [withDensity_apply f (MeasurableSet.singleton b), lintegral_singleton]

theorem bernoulli_eq_withDensity (p r : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) :
    Ber(true, false, p) = Ber(true, false, r).withDensity (bernoulliDensity p r) := by
  apply Measure.ext_of_singleton
  intro b
  rw [withDensity_bool_singleton]
  cases b with
  | false =>
      rw [bernoulliMeasure_apply_of_notMem_of_mem p (MeasurableSet.singleton false)
        (by simp) (by simp)]
      rw [bernoulliMeasure_apply_of_notMem_of_mem r (MeasurableSet.singleton false)
        (by simp) (by simp)]
      simp only [bernoulliDensity, Bool.false_eq_true, ↓reduceIte]
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (div_nonneg (by linarith) (by linarith))]
      congr 1
      simp only [unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
      field_simp [ne_of_gt (sub_pos.mpr hr1)]
  | true =>
      rw [bernoulliMeasure_apply_of_mem_of_notMem p (MeasurableSet.singleton true)
        (by simp) (by simp)]
      rw [bernoulliMeasure_apply_of_mem_of_notMem r (MeasurableSet.singleton true)
        (by simp) (by simp)]
      simp only [bernoulliDensity, ↓reduceIte]
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (div_nonneg hp0.le hr0.le)]
      congr 1
      simp only [unitInterval.coe_toNNReal]
      field_simp

theorem bernoulli_ac (p r : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) :
    Ber(true, false, p) ≪ Ber(true, false, r) := by
  rw [bernoulli_eq_withDensity p r hp0 hp1 hr0 hr1]
  exact withDensity_absolutelyContinuous _ _

theorem rnDeriv_bernoulli (p r : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) :
    Ber(true, false, p).rnDeriv Ber(true, false, r) =ᵐ[Ber(true, false, r)]
      bernoulliDensity p r := by
  rw [bernoulli_eq_withDensity p r hp0 hp1 hr0 hr1]
  exact Measure.rnDeriv_withDensity _ (by fun_prop)

theorem llr_bernoulli (p r : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) :
    llr Ber(true, false, p) Ber(true, false, r) =ᵐ[Ber(true, false, p)]
      fun b => if b then Real.log ((p : ℝ) / (r : ℝ))
        else Real.log ((1 - (p : ℝ)) / (1 - (r : ℝ))) := by
  have hac := bernoulli_ac p r hp0 hp1 hr0 hr1
  filter_upwards [(rnDeriv_bernoulli p r hp0 hp1 hr0 hr1).filter_mono hac.ae_le] with b hb
  rw [llr, hb]
  have hratio : 0 ≤ (p : ℝ) / (r : ℝ) := div_nonneg hp0.le hr0.le
  have hcomp : 0 ≤ (1 - (p : ℝ)) / (1 - (r : ℝ)) :=
    div_nonneg (sub_nonneg.mpr hp1.le) (sub_nonneg.mpr hr1.le)
  cases b
  · simp [bernoulliDensity, ENNReal.toReal_ofReal hcomp]
  · simp [bernoulliDensity, ENNReal.toReal_ofReal hratio]

theorem toReal_klDiv_bernoulli (p r : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) :
    (klDiv Ber(true, false, p) Ber(true, false, r)).toReal =
      (p : ℝ) * Real.log ((p : ℝ) / (r : ℝ)) +
        (1 - (p : ℝ)) * Real.log ((1 - (p : ℝ)) / (1 - (r : ℝ))) := by
  rw [toReal_klDiv_of_measure_eq (bernoulli_ac p r hp0 hp1 hr0 hr1) (by simp)]
  rw [integral_congr_ae (llr_bernoulli p r hp0 hp1 hr0 hr1)]
  rw [integral_bernoulliMeasure]
  simp only [↓reduceIte, Bool.false_eq_true, smul_eq_mul]

theorem integrable_llr_bernoulli (p r : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) :
    Integrable (llr Ber(true, false, p) Ber(true, false, r)) Ber(true, false, p) := by
  rw [integrable_congr (llr_bernoulli p r hp0 hp1 hr0 hr1)]
  exact integrable_bernoulliMeasure true false p _

theorem klDiv_bernoulli_ne_top (p r : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) :
    klDiv Ber(true, false, p) Ber(true, false, r) ≠ ⊤ :=
  klDiv_ne_top (bernoulli_ac p r hp0 hp1 hr0 hr1)
    (integrable_llr_bernoulli p r hp0 hp1 hr0 hr1)

def bernoulliJeffreysReal (p r : unitInterval) : ℝ :=
  (klDiv Ber(true, false, p) Ber(true, false, r)).toReal +
    (klDiv Ber(true, false, r) Ber(true, false, p)).toReal

theorem bernoulliJeffreysReal_formula (p r : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) :
    bernoulliJeffreysReal p r =
      ((p : ℝ) - (r : ℝ)) *
        (Real.log ((p : ℝ) / (r : ℝ)) +
          Real.log ((1 - (r : ℝ)) / (1 - (p : ℝ)))) := by
  rw [bernoulliJeffreysReal,
    toReal_klDiv_bernoulli p r hp0 hp1 hr0 hr1,
    toReal_klDiv_bernoulli r p hr0 hr1 hp0 hp1]
  rw [Real.log_div hp0.ne' hr0.ne', Real.log_div hr0.ne' hp0.ne',
    Real.log_div (sub_pos.mpr hp1).ne' (sub_pos.mpr hr1).ne',
    Real.log_div (sub_pos.mpr hr1).ne' (sub_pos.mpr hp1).ne']
  ring

theorem log_ratio_fugacityShift (θ : AbelianZetaParameters) (u : ℝ) (hu : 0 ≤ u) :
    Real.log (θ.ratio leastMode /
      (fugacityShiftParameters θ u hu).ratio leastMode) = u * Real.log 2 := by
  have hq := θ.ratio_pos leastMode
  have hs : 0 < (2 : ℝ) ^ (-u) := Real.rpow_pos_of_pos (by norm_num) _
  rw [leastMode_ratio_fugacityShift]
  rw [Real.log_div hq.ne' (mul_pos hq hs).ne', Real.log_mul hq.ne' hs.ne',
    Real.log_rpow (by norm_num)]
  ring

theorem bernoulliJeffreysReal_fugacityShift (θ : AbelianZetaParameters)
    (u : ℝ) (hu : 0 ≤ u) :
    bernoulliJeffreysReal (ratioUnit θ leastMode)
      (ratioUnit (fugacityShiftParameters θ u hu) leastMode) =
        reporterWork (θ.ratio leastMode) u := by
  have hq0 := θ.ratio_pos leastMode
  have hq1 := θ.ratio_lt_one leastMode
  have hr0 := (fugacityShiftParameters θ u hu).ratio_pos leastMode
  have hr1 := (fugacityShiftParameters θ u hu).ratio_lt_one leastMode
  rw [bernoulliJeffreysReal_formula _ _ hq0 hq1 hr0 hr1]
  simp only [ratioUnit_coe]
  rw [log_ratio_fugacityShift θ u hu]
  rw [leastMode_ratio_fugacityShift]
  rfl

def bernoulliJeffreys (p r : unitInterval) : ℝ≥0∞ :=
  klDiv Ber(true, false, p) Ber(true, false, r) +
    klDiv Ber(true, false, r) Ber(true, false, p)

theorem bernoulliJeffreys_toReal (p r : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) :
    (bernoulliJeffreys p r).toReal = bernoulliJeffreysReal p r := by
  rw [bernoulliJeffreys, ENNReal.toReal_add
    (klDiv_bernoulli_ne_top p r hp0 hp1 hr0 hr1)
    (klDiv_bernoulli_ne_top r p hr0 hr1 hp0 hp1)]
  rfl

theorem bernoulliJeffreys_toReal_fugacityShift (θ : AbelianZetaParameters)
    (u : ℝ) (hu : 0 ≤ u) :
    (bernoulliJeffreys (ratioUnit θ leastMode)
      (ratioUnit (fugacityShiftParameters θ u hu) leastMode)).toReal =
        reporterWork (θ.ratio leastMode) u := by
  rw [bernoulliJeffreys_toReal _ _
    (θ.ratio_pos leastMode) (θ.ratio_lt_one leastMode)
    ((fugacityShiftParameters θ u hu).ratio_pos leastMode)
    ((fugacityShiftParameters θ u hu).ratio_lt_one leastMode)]
  exact bernoulliJeffreysReal_fugacityShift θ u hu

def fullFormationJeffreys (θ : AbelianZetaConvergentParameters)
    (u : ℝ) (hu : 0 ≤ u) : ℝ≥0∞ :=
  klDiv (classLaw θ.toAbelianZetaParameters)
      (classLaw (fugacityShiftConv θ u hu).toAbelianZetaParameters) +
    klDiv (classLaw (fugacityShiftConv θ u hu).toAbelianZetaParameters)
      (classLaw θ.toAbelianZetaParameters)

theorem reporterJeffreys_le_fullFormationJeffreys
    (θ : AbelianZetaConvergentParameters) (u : ℝ) (hu : 0 ≤ u) :
    bernoulliJeffreys (ratioUnit θ.toAbelianZetaParameters leastMode)
        (ratioUnit (fugacityShiftParameters θ.toAbelianZetaParameters u hu) leastMode) ≤
      fullFormationJeffreys θ u hu := by
  let P := classLaw θ.toAbelianZetaParameters
  let Q := classLaw (fugacityShiftConv θ u hu).toAbelianZetaParameters
  have hP := classLaw_map_leastModeObserver θ
  have hQ := classLaw_map_leastModeObserver (fugacityShiftConv θ u hu)
  simp only [fugacityShiftConv_toParams] at hQ
  rw [bernoulliJeffreys, fullFormationJeffreys, ← hP, ← hQ]
  exact add_le_add
    (klDiv_map_le P Q (q := leastModeObserver) (by fun_prop))
    (klDiv_map_le Q P (q := leastModeObserver) (by fun_prop))

def BoundedFullFormationWork (θ : AbelianZetaConvergentParameters) (d u : ℝ)
    (hd0 : 0 ≤ d) (hu : 0 ≤ u) : Prop :=
  ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n : ℕ,
    fullFormationJeffreys θ (d ^ n * u)
      (mul_nonneg (pow_nonneg hd0 n) hu) ≤ C

theorem boundedFullFormationWork_iff (θ : AbelianZetaConvergentParameters)
    {d u : ℝ} (hd : 1 < d) (hu : 0 ≤ u) :
    BoundedFullFormationWork θ d u (by linarith) hu ↔ u = 0 := by
  constructor
  · rintro ⟨C, hCtop, hC⟩
    apply (leastMode_boundedScaleWork_iff θ.toAbelianZetaParameters hd hu).mp
    refine ⟨C.toReal, fun n => ?_⟩
    have hdn : 0 ≤ d ^ n * u := mul_nonneg (pow_nonneg (by linarith) n) hu
    have hle := reporterJeffreys_le_fullFormationJeffreys θ (d ^ n * u) hdn
    have hreal := ENNReal.toReal_mono hCtop (hle.trans (hC n))
    rwa [bernoulliJeffreys_toReal_fugacityShift] at hreal
  · rintro rfl
    refine ⟨0, ENNReal.zero_ne_top, fun n => ?_⟩
    have hshift := fugacityShiftParameters_zero θ.toAbelianZetaParameters
      (by norm_num : 0 ≤ (0 : ℝ))
    simp [fullFormationJeffreys, hshift]

end

end GaloisForLFunctions.HTGeometry
