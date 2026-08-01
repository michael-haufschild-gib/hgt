import GaloisForLFunctions.HTGeometry.JuliaDefectLevyKhintchine
import GaloisForLFunctions.HTGeometry.CharacteristicEquilibriumDefect

/-!
# Positive definiteness of the Julia equilibrium defect

The Julia compression Lévy density is normalized to a symmetric jump law.  Its compound-Poisson
law has characteristic function equal to the Julia compression square and exact variance `3 / 2`.
The center-mixed Julia kernel is therefore its normalized second-order characteristic defect, so
the universal equilibrium-defect law proves positive definiteness from source data.
-/

open MeasureTheory Set
open scoped ENNReal

namespace HTGeometry

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Finite jump intensity in the Julia compression Lévy law. -/
def juliaCompressionJumpRate : ℝ :=
  (3 / 2 : ℝ) * Real.log 2

theorem juliaCompressionJumpRate_pos : 0 < juliaCompressionJumpRate := by
  unfold juliaCompressionJumpRate
  positivity

/-- Symmetric normalized jump density associated with the Julia compression exponent. -/
def juliaCompressionJumpDensity (x : ℝ) : ℝ :=
  juliaCompressionLevyDensity |x| / (2 * juliaCompressionJumpRate)

theorem juliaCompressionJumpDensity_nonneg (x : ℝ) :
    0 ≤ juliaCompressionJumpDensity x := by
  by_cases hx : x = 0
  · subst x
    simp [juliaCompressionJumpDensity, juliaCompressionLevyDensity]
  · exact (div_pos (juliaCompressionLevyDensity_pos (abs_pos.mpr hx))
      (mul_pos (by norm_num) juliaCompressionJumpRate_pos)).le

theorem integrable_juliaCompressionJumpDensity :
    Integrable juliaCompressionJumpDensity := by
  have hpos : IntegrableOn
      (fun x : ℝ => juliaCompressionJumpDensity |x|) (Set.Ioi 0) := by
    have hscaled := integrableOn_juliaCompressionLevyDensity.const_mul
      (2 * juliaCompressionJumpRate)⁻¹
    refine Integrable.congr hscaled ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 0 < x at hx
    simp [juliaCompressionJumpDensity, abs_of_pos hx, div_eq_mul_inv, mul_comm]
  have hneg : IntegrableOn
      (fun x : ℝ => juliaCompressionJumpDensity |x|) (Set.Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let e : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [e.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos
  have hfull : Integrable (fun x : ℝ => juliaCompressionJumpDensity |x|) := by
    have hu : IntegrableOn (fun x : ℝ => juliaCompressionJumpDensity |x|) Set.univ := by
      simpa only [Set.Iic_union_Ioi] using hneg.union hpos
    simpa only [IntegrableOn, Measure.restrict_univ] using hu
  exact hfull.congr (Filter.Eventually.of_forall fun x => by
    simp [juliaCompressionJumpDensity])

theorem integral_juliaCompressionJumpDensity :
    ∫ x : ℝ, juliaCompressionJumpDensity x = 1 := by
  rw [show (fun x : ℝ => juliaCompressionJumpDensity x) =
      fun x => juliaCompressionJumpDensity |x| by
    funext x
    simp [juliaCompressionJumpDensity]]
  rw [integral_comp_abs]
  rw [show (∫ x : ℝ in Set.Ioi 0, juliaCompressionJumpDensity x) =
      (2 * juliaCompressionJumpRate)⁻¹ *
        ∫ x : ℝ in Set.Ioi 0, juliaCompressionLevyDensity x by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change 0 < x at hx
    simp only [juliaCompressionJumpDensity, abs_of_pos hx]
    rw [div_eq_mul_inv]
    ring]
  rw [juliaCompressionLevyDensity_mass]
  unfold juliaCompressionJumpRate
  field_simp [Real.log_ne_zero_of_pos_of_ne_one
    (by norm_num : (0 : ℝ) < 2) (by norm_num)]

def juliaCompressionJumpDensityNNReal (x : ℝ) : NNReal :=
  ⟨juliaCompressionJumpDensity x, juliaCompressionJumpDensity_nonneg x⟩

theorem measurable_juliaCompressionJumpDensityNNReal :
    Measurable juliaCompressionJumpDensityNNReal := by
  apply Measurable.subtype_mk
  unfold juliaCompressionJumpDensity juliaCompressionLevyDensity
  fun_prop

def juliaCompressionJumpMeasure : Measure ℝ :=
  volume.withDensity fun x => (juliaCompressionJumpDensityNNReal x : ℝ≥0∞)

theorem isProbabilityMeasure_juliaCompressionJumpMeasure :
    IsProbabilityMeasure juliaCompressionJumpMeasure := by
  constructor
  rw [juliaCompressionJumpMeasure,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [show (fun x : ℝ => (juliaCompressionJumpDensityNNReal x : ℝ≥0∞)) =
      fun x => ENNReal.ofReal (juliaCompressionJumpDensity x) by
    funext x
    exact (ENNReal.ofReal_eq_coe_nnreal
      (juliaCompressionJumpDensity_nonneg x)).symm]
  rw [← ofReal_integral_eq_lintegral_ofReal
    integrable_juliaCompressionJumpDensity
    (Filter.Eventually.of_forall juliaCompressionJumpDensity_nonneg)]
  rw [integral_juliaCompressionJumpDensity]
  norm_num

def juliaCompressionJumpProbabilityMeasure : ProbabilityMeasure ℝ :=
  ⟨juliaCompressionJumpMeasure,
    isProbabilityMeasure_juliaCompressionJumpMeasure⟩

private theorem integrable_juliaCompressionJumpCharacteristic (y : ℝ) :
    Integrable (fun x : ℝ =>
      (juliaCompressionJumpDensity x : ℂ) *
        Complex.exp (((y * x : ℝ) : ℂ) * Complex.I)) := by
  have hdmeas : Measurable juliaCompressionJumpDensity := by
    unfold juliaCompressionJumpDensity juliaCompressionLevyDensity
    measurability
  refine integrable_juliaCompressionJumpDensity.mono'
    ((Complex.measurable_ofReal.comp hdmeas).mul (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards with x
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (juliaCompressionJumpDensity_nonneg x)]

private theorem integral_eq_integral_Ioi_add_reflect
    {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ x : ℝ, f x) = ∫ x : ℝ in Set.Ioi 0, (f x + f (-x)) := by
  have hsplit := integral_add_compl (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi hf
  simp only [compl_Ioi] at hsplit
  have hneg : (∫ x : ℝ in Set.Iic 0, f x) = ∫ x : ℝ in Set.Ioi 0, f (-x) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi 0 f).symm
  rw [← hsplit, hneg, ← integral_add hf.integrableOn hf.comp_neg.integrableOn]

theorem charFun_juliaCompressionJumpProbabilityMeasure (y : ℝ) :
    charFun (juliaCompressionJumpProbabilityMeasure : Measure ℝ) y =
      ((juliaCompressionJumpRate⁻¹ *
        ∫ t : ℝ in Set.Ioi 0,
          Real.cos (t * y) * juliaCompressionLevyDensity t : ℝ) : ℂ) := by
  rw [charFun_apply_real]
  unfold juliaCompressionJumpProbabilityMeasure
  simp only [ProbabilityMeasure.coe_mk]
  rw [juliaCompressionJumpMeasure,
    integral_withDensity_eq_integral_smul
      measurable_juliaCompressionJumpDensityNNReal]
  rw [show (fun x : ℝ => juliaCompressionJumpDensityNNReal x •
        Complex.exp ((y : ℂ) * (x : ℂ) * Complex.I)) =
      fun x : ℝ => (juliaCompressionJumpDensity x : ℂ) *
        Complex.exp (((y * x : ℝ) : ℂ) * Complex.I) by
    funext x
    change (juliaCompressionJumpDensity x : ℂ) *
      Complex.exp ((y : ℂ) * (x : ℂ) * Complex.I) = _
    congr 2
    push_cast
    rfl]
  rw [integral_eq_integral_Ioi_add_reflect
    (integrable_juliaCompressionJumpCharacteristic y)]
  rw [show (∫ x : ℝ in Set.Ioi 0,
      ((juliaCompressionJumpDensity x : ℂ) *
          Complex.exp (((y * x : ℝ) : ℂ) * Complex.I) +
        (juliaCompressionJumpDensity (-x) : ℂ) *
          Complex.exp (((y * -x : ℝ) : ℂ) * Complex.I))) =
      ∫ x : ℝ in Set.Ioi 0,
        ((juliaCompressionJumpRate⁻¹ *
          (Real.cos (x * y) * juliaCompressionLevyDensity x) : ℝ) : ℂ) by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change 0 < x at hx
    have heven : juliaCompressionJumpDensity (-x) =
        juliaCompressionJumpDensity x := by
      simp [juliaCompressionJumpDensity]
    dsimp only
    rw [heven]
    simp only [juliaCompressionJumpDensity, abs_of_pos hx]
    rw [show (((y * x : ℝ) : ℂ) * Complex.I) =
        ((y * x : ℝ) : ℂ) * Complex.I by rfl,
      show (((y * -x : ℝ) : ℂ) * Complex.I) =
        ((-(y * x) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring]
  rw [← integral_const_mul]
  have hcosInt : IntegrableOn
      (fun t : ℝ => Real.cos (t * y) * juliaCompressionLevyDensity t)
      (Set.Ioi 0) :=
    integrableOn_juliaCompressionLevyDensity.bdd_mul
      ((Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs]
        exact Real.abs_cos_le_one _)
  exact Complex.ofRealCLM.integral_comp_comm
    (hcosInt.const_mul juliaCompressionJumpRate⁻¹)

theorem charFun_juliaCompressionJumpProbabilityMeasure_sub_one (y : ℝ) :
    (juliaCompressionJumpRate : ℂ) *
        (charFun (juliaCompressionJumpProbabilityMeasure : Measure ℝ) y - 1) =
      ((- ∫ t : ℝ in Set.Ioi 0,
        (1 - Real.cos (t * y)) * juliaCompressionLevyDensity t : ℝ) : ℂ) := by
  rw [charFun_juliaCompressionJumpProbabilityMeasure]
  have hrate : juliaCompressionJumpRate ≠ 0 := juliaCompressionJumpRate_pos.ne'
  have hcosInt : IntegrableOn
      (fun t : ℝ => Real.cos (t * y) * juliaCompressionLevyDensity t)
      (Set.Ioi 0) :=
    integrableOn_juliaCompressionLevyDensity.bdd_mul
      ((Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs]
        exact Real.abs_cos_le_one _)
  have hsplit :
      (∫ t : ℝ in Set.Ioi 0,
        (1 - Real.cos (t * y)) * juliaCompressionLevyDensity t) =
      (∫ t : ℝ in Set.Ioi 0, juliaCompressionLevyDensity t) -
        ∫ t : ℝ in Set.Ioi 0,
          Real.cos (t * y) * juliaCompressionLevyDensity t := by
    rw [← integral_sub integrableOn_juliaCompressionLevyDensity hcosInt]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring
  rw [hsplit, juliaCompressionLevyDensity_mass]
  rw [show (∫ t : ℝ in Set.Ioi 0,
      Real.cos (t * y) * juliaCompressionLevyDensity t) =
      ∫ t : ℝ in Set.Ioi 0,
        Real.cos (y * t) * juliaCompressionLevyDensity t by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [mul_comm t y]]
  rw [show juliaCompressionJumpRate = (3 / 2 : ℝ) * Real.log 2 by rfl]
  change ((juliaCompressionJumpRate : ℂ) *
      (((juliaCompressionJumpRate⁻¹ * _ : ℝ) : ℂ) - 1)) = _
  unfold juliaCompressionJumpRate
  push_cast
  have hlog : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hlogC : (Real.log 2 : ℂ) ≠ 0 := by exact_mod_cast hlog
  field_simp [hrate, hlog, hlogC]
  ring

