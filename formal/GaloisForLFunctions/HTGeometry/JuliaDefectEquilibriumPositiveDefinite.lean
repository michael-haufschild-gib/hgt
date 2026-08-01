import GaloisForLFunctions.HTGeometry.JuliaDefectLevyKhintchine
import GaloisForLFunctions.HTGeometry.CharacteristicEquilibriumDefect
import GaloisForLFunctions.HTGeometry.ConvolutionAtomBounds

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

theorem integrableOn_sq_mul_juliaCompressionLevyDensity :
    IntegrableOn (fun t : ℝ => t ^ 2 * juliaCompressionLevyDensity t)
      (Set.Ioi 0) := by
  have h2 : IntegrableOn
      (fun t : ℝ => t / Real.sinh (Real.pi * t / 4)) (Set.Ioi 0) := by
    convert integrableOn_t_div_sinh (a := (2 : ℝ)) (by norm_num) using 1 <;>
      norm_num
  have hh : IntegrableOn
      (fun t : ℝ => t / Real.sinh (Real.pi * t)) (Set.Ioi 0) := by
    convert integrableOn_t_div_sinh (a := (1 / 2 : ℝ)) (by norm_num) using 1 <;>
      norm_num
  have hlin := (h2.const_mul (1 / 2 : ℝ)).sub (hh.const_mul (2 : ℝ))
  refine hlin.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : t ≠ 0 := ht.ne'
  have hs4 : Real.sinh (Real.pi * t / 4) ≠ 0 :=
    (Real.sinh_pos_iff.mpr
      (div_pos (mul_pos Real.pi_pos ht) (by norm_num))).ne'
  have hs1 : Real.sinh (Real.pi * t) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)).ne'
  unfold juliaCompressionLevyDensity
  change (1 / 2 : ℝ) * (t / Real.sinh (Real.pi * t / 4)) -
      2 * (t / Real.sinh (Real.pi * t)) =
    t ^ 2 * (1 / (2 * t * Real.sinh (Real.pi * t / 4)) -
      2 / (t * Real.sinh (Real.pi * t)))
  field_simp [ht0, hs4, hs1]

/-- Exact positive-half-line quadratic mass of the Julia compression Lévy law. -/
theorem integral_Ioi_sq_mul_juliaCompressionLevyDensity :
    (∫ t : ℝ in Set.Ioi 0, t ^ 2 * juliaCompressionLevyDensity t) = 3 / 2 := by
  have h2 : (∫ t : ℝ in Set.Ioi 0,
      t / Real.sinh (Real.pi * t / 4)) = 4 := by
    convert integral_t_cos_div_sinh
      (a := (2 : ℝ)) (y := (0 : ℝ)) (by norm_num) using 1 <;> norm_num
  have hh : (∫ t : ℝ in Set.Ioi 0,
      t / Real.sinh (Real.pi * t)) = 1 / 4 := by
    convert integral_t_cos_div_sinh
      (a := (1 / 2 : ℝ)) (y := (0 : ℝ)) (by norm_num) using 1 <;> norm_num
  have hi2 : IntegrableOn
      (fun t : ℝ => t / Real.sinh (Real.pi * t / 4)) (Set.Ioi 0) := by
    convert integrableOn_t_div_sinh (a := (2 : ℝ)) (by norm_num) using 1 <;>
      norm_num
  have hih : IntegrableOn
      (fun t : ℝ => t / Real.sinh (Real.pi * t)) (Set.Ioi 0) := by
    convert integrableOn_t_div_sinh (a := (1 / 2 : ℝ)) (by norm_num) using 1 <;>
      norm_num
  rw [show (∫ t : ℝ in Set.Ioi 0,
      t ^ 2 * juliaCompressionLevyDensity t) =
      (1 / 2 : ℝ) * (∫ t : ℝ in Set.Ioi 0,
          t / Real.sinh (Real.pi * t / 4)) -
        2 * (∫ t : ℝ in Set.Ioi 0,
          t / Real.sinh (Real.pi * t)) by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub (hi2.const_mul (1 / 2)) (hih.const_mul 2)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : t ≠ 0 := ht.ne'
    have hs4 : Real.sinh (Real.pi * t / 4) ≠ 0 :=
      (Real.sinh_pos_iff.mpr
        (div_pos (mul_pos Real.pi_pos ht) (by norm_num))).ne'
    have hs1 : Real.sinh (Real.pi * t) ≠ 0 :=
      (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)).ne'
    unfold juliaCompressionLevyDensity
    field_simp [ht0, hs4, hs1]]
  rw [h2, hh]
  norm_num

theorem integrable_sq_mul_juliaCompressionJumpDensity :
    Integrable (fun x : ℝ => x ^ 2 * juliaCompressionJumpDensity x) := by
  have hpos : IntegrableOn
      (fun x : ℝ => x ^ 2 * juliaCompressionJumpDensity |x|) (Set.Ioi 0) := by
    have hscaled := integrableOn_sq_mul_juliaCompressionLevyDensity.const_mul
      (2 * juliaCompressionJumpRate)⁻¹
    refine hscaled.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 0 < x at hx
    simp only [juliaCompressionJumpDensity, abs_of_pos hx]
    rw [div_eq_mul_inv]
    ring
  have hneg : IntegrableOn
      (fun x : ℝ => x ^ 2 * juliaCompressionJumpDensity |x|) (Set.Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let e : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [e.integrableOn_map_iff]
    simp_rw [Function.comp_def, neg_sq, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos
  have hfull : Integrable
      (fun x : ℝ => x ^ 2 * juliaCompressionJumpDensity |x|) := by
    have hu : IntegrableOn
        (fun x : ℝ => x ^ 2 * juliaCompressionJumpDensity |x|) Set.univ := by
      simpa only [Set.Iic_union_Ioi] using hneg.union hpos
    simpa only [IntegrableOn, Measure.restrict_univ] using hu
  exact hfull.congr (Filter.Eventually.of_forall fun x => by
    simp [juliaCompressionJumpDensity])

theorem integral_sq_mul_juliaCompressionJumpDensity :
    (∫ x : ℝ, x ^ 2 * juliaCompressionJumpDensity x) =
      (3 / 2 : ℝ) / juliaCompressionJumpRate := by
  rw [show (fun x : ℝ => x ^ 2 * juliaCompressionJumpDensity x) =
      fun x => (fun z : ℝ => z ^ 2 * juliaCompressionJumpDensity z) |x| by
    funext x
    simp [juliaCompressionJumpDensity, sq_abs]]
  calc
    (∫ x : ℝ,
        (fun z : ℝ => z ^ 2 * juliaCompressionJumpDensity z) |x|) =
        2 * ∫ x : ℝ in Set.Ioi 0,
          x ^ 2 * juliaCompressionJumpDensity x :=
      integral_comp_abs (f := fun z : ℝ => z ^ 2 * juliaCompressionJumpDensity z)
    _ = 2 * ((2 * juliaCompressionJumpRate)⁻¹ *
        ∫ x : ℝ in Set.Ioi 0,
          x ^ 2 * juliaCompressionLevyDensity x) := by
      congr 1
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change 0 < x at hx
      simp only [juliaCompressionJumpDensity, abs_of_pos hx]
      rw [div_eq_mul_inv]
      ring
    _ = (3 / 2 : ℝ) / juliaCompressionJumpRate := by
      rw [integral_Ioi_sq_mul_juliaCompressionLevyDensity]
      field_simp [juliaCompressionJumpRate_pos.ne']

theorem integrable_sq_juliaCompressionJumpProbabilityMeasure :
    Integrable (fun x : ℝ => x ^ 2)
      (juliaCompressionJumpProbabilityMeasure : Measure ℝ) := by
  unfold juliaCompressionJumpProbabilityMeasure
  simp only [ProbabilityMeasure.coe_mk]
  rw [juliaCompressionJumpMeasure,
    integrable_withDensity_iff_integrable_coe_smul
      measurable_juliaCompressionJumpDensityNNReal]
  change Integrable (fun x : ℝ => juliaCompressionJumpDensity x * x ^ 2)
  simpa only [mul_comm] using integrable_sq_mul_juliaCompressionJumpDensity

theorem integral_sq_juliaCompressionJumpProbabilityMeasure :
    (∫ x : ℝ, x ^ 2
      ∂(juliaCompressionJumpProbabilityMeasure : Measure ℝ)) =
      (3 / 2 : ℝ) / juliaCompressionJumpRate := by
  unfold juliaCompressionJumpProbabilityMeasure
  simp only [ProbabilityMeasure.coe_mk]
  rw [juliaCompressionJumpMeasure,
    integral_withDensity_eq_integral_smul
      measurable_juliaCompressionJumpDensityNNReal]
  rw [show (fun x : ℝ => juliaCompressionJumpDensityNNReal x • x ^ 2) =
      fun x : ℝ => x ^ 2 * juliaCompressionJumpDensity x by
    funext x
    change juliaCompressionJumpDensity x * x ^ 2 = _
    ring]
  exact integral_sq_mul_juliaCompressionJumpDensity

theorem integral_id_juliaCompressionJumpProbabilityMeasure :
    (∫ x : ℝ, x
      ∂(juliaCompressionJumpProbabilityMeasure : Measure ℝ)) = 0 := by
  unfold juliaCompressionJumpProbabilityMeasure
  simp only [ProbabilityMeasure.coe_mk]
  rw [juliaCompressionJumpMeasure,
    integral_withDensity_eq_integral_smul
      measurable_juliaCompressionJumpDensityNNReal]
  change (∫ x : ℝ, juliaCompressionJumpDensity x * x) = 0
  have hodd : (fun x : ℝ => juliaCompressionJumpDensity (-x) * (-x)) =
      fun x : ℝ => -(juliaCompressionJumpDensity x * x) := by
    funext x
    simp [juliaCompressionJumpDensity]
  have hneg := MeasureTheory.integral_neg_eq_self
    (fun x : ℝ => juliaCompressionJumpDensity x * x) volume
  rw [hodd, MeasureTheory.integral_neg] at hneg
  linarith

theorem memLp_id_juliaCompressionJumpProbabilityMeasure :
    MemLp id 2 (juliaCompressionJumpProbabilityMeasure : Measure ℝ) := by
  exact (memLp_two_iff_integrable_sq (by fun_prop)).2
    integrable_sq_juliaCompressionJumpProbabilityMeasure

/-- Compound-Poisson equilibrium measure generated by the Julia compression Lévy source. -/
def juliaCompressionEquilibriumProbabilityMeasure : ProbabilityMeasure ℝ :=
  ⟨compoundPoisson juliaCompressionJumpRate
      (juliaCompressionJumpProbabilityMeasure : Measure ℝ),
    isProbabilityMeasure_compoundPoisson
      juliaCompressionJumpRate juliaCompressionJumpRate_pos.le
      (juliaCompressionJumpProbabilityMeasure : Measure ℝ)⟩

theorem juliaCompressionSquareProfile_pos (y : ℝ) :
    0 < juliaCompressionSquareProfile y := by
  rw [juliaCompressionSquareProfile_eq_cosh_ratio]
  exact div_pos (sq_pos_of_pos (Real.cosh_pos _))
    (Real.sqrt_pos.mpr (Real.cosh_pos _))

/-- The source compound-Poisson law has the Julia compression square as characteristic
function. -/
theorem charFun_juliaCompressionEquilibriumProbabilityMeasure (y : ℝ) :
    charFun (juliaCompressionEquilibriumProbabilityMeasure : Measure ℝ) y =
      (juliaCompressionSquareProfile y : ℂ) := by
  unfold juliaCompressionEquilibriumProbabilityMeasure
  simp only [ProbabilityMeasure.coe_mk]
  rw [charFun_compoundPoisson juliaCompressionJumpRate
    juliaCompressionJumpRate_pos.le
    (juliaCompressionJumpProbabilityMeasure : Measure ℝ) y]
  rw [charFun_juliaCompressionJumpProbabilityMeasure_sub_one]
  rw [← neg_log_juliaCompressionSquareProfile_eq_integral]
  push_cast
  rw [neg_neg, ← Complex.ofReal_exp,
    Real.exp_log (juliaCompressionSquareProfile_pos y)]

/-- The zero-jump Poisson sector is the exact atom at the origin. -/
theorem juliaCompressionEquilibriumProbabilityMeasure_zero_mass_exp :
    (juliaCompressionEquilibriumProbabilityMeasure : Measure ℝ) {0} =
      ENNReal.ofReal (Real.exp (-juliaCompressionJumpRate)) := by
  change (compoundPoisson juliaCompressionJumpRate
      (juliaCompressionJumpProbabilityMeasure : Measure ℝ)) {0} = _
  rw [compoundPoisson, convPowMixture_singleton, tsum_eq_single 0]
  · simp [convPow]
  · intro n hn
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    letI : NullSingletonClass juliaCompressionJumpMeasure := by
      rw [juliaCompressionJumpMeasure]
      infer_instance
    letI : NullSingletonClass
        (juliaCompressionJumpProbabilityMeasure : Measure ℝ) := by
      change NullSingletonClass juliaCompressionJumpMeasure
      infer_instance
    letI : NullSingletonClass
        (convPow (juliaCompressionJumpProbabilityMeasure : Measure ℝ) n) :=
      nullSingletonClass_convPow
        (juliaCompressionJumpProbabilityMeasure : Measure ℝ) hnpos
    rw [measure_singleton, mul_zero]

theorem exp_neg_juliaCompressionJumpRate :
    Real.exp (-juliaCompressionJumpRate) =
      1 / (2 * Real.sqrt 2) := by
  have hsqrt : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.exp_log (Real.sqrt_pos.mpr (by norm_num))]
  rw [juliaCompressionJumpRate,
    show -((3 / 2 : ℝ) * Real.log 2) =
      -(Real.log 2 + Real.log 2 / 2) by ring,
    Real.exp_neg, Real.exp_add,
    Real.exp_log (by norm_num : (0 : ℝ) < 2), hsqrt]
  ring

/-- Exact boundary atom of the Julia compression compound-Poisson law. -/
theorem juliaCompressionEquilibriumProbabilityMeasure_zero_mass :
    (juliaCompressionEquilibriumProbabilityMeasure : Measure ℝ) {0} =
      ENNReal.ofReal (1 / (2 * Real.sqrt 2)) := by
  rw [juliaCompressionEquilibriumProbabilityMeasure_zero_mass_exp,
    exp_neg_juliaCompressionJumpRate]

theorem integrable_sq_juliaCompressionEquilibriumProbabilityMeasure :
    Integrable (fun x : ℝ => x ^ 2)
      (juliaCompressionEquilibriumProbabilityMeasure : Measure ℝ) := by
  have h := compoundPoisson_centered_secondMoment
    juliaCompressionJumpRate juliaCompressionJumpRate_pos.le
    (juliaCompressionJumpProbabilityMeasure : Measure ℝ)
    memLp_id_juliaCompressionJumpProbabilityMeasure
    integral_id_juliaCompressionJumpProbabilityMeasure
  exact h.1

/-- Exact variance of the source measure underlying the Julia center-mixed kernel. -/
theorem integral_sq_juliaCompressionEquilibriumProbabilityMeasure :
    (∫ x : ℝ, x ^ 2
      ∂(juliaCompressionEquilibriumProbabilityMeasure : Measure ℝ)) = 3 / 2 := by
  have h := (compoundPoisson_centered_secondMoment
    juliaCompressionJumpRate juliaCompressionJumpRate_pos.le
    (juliaCompressionJumpProbabilityMeasure : Measure ℝ)
    memLp_id_juliaCompressionJumpProbabilityMeasure
    integral_id_juliaCompressionJumpProbabilityMeasure).2
  rw [integral_sq_juliaCompressionJumpProbabilityMeasure] at h
  rw [show (∫ x : ℝ, x ^ 2
      ∂(juliaCompressionEquilibriumProbabilityMeasure : Measure ℝ)) =
      ∫ x : ℝ, x ^ 2 ∂compoundPoisson juliaCompressionJumpRate
        (juliaCompressionJumpProbabilityMeasure : Measure ℝ) by rfl]
  rw [h]
  field_simp [juliaCompressionJumpRate_pos.ne']

theorem normalizedCharacteristicDefect_juliaCompressionEquilibriumProbabilityMeasure
    (y : ℝ) :
    normalizedCharacteristicDefect
        (juliaCompressionEquilibriumProbabilityMeasure : Measure ℝ) (3 / 2) y =
      juliaDefectAttenuationKernel y := by
  by_cases hy : y = 0
  · subst y
    simp [normalizedCharacteristicDefect]
  · rw [normalizedCharacteristicDefect, if_neg hy,
      juliaDefectAttenuationKernel_eq_profile hy, juliaDefectAttenuationProfile,
      juliaDefectSquareProfile_eq_one_sub_compression,
      charFun_juliaCompressionEquilibriumProbabilityMeasure]
    simp only [Complex.ofReal_re]
    field_simp [hy]
    ring

/-- Square-biased Julia compression law, with density `(2 / 3) x²` relative to the source
compound-Poisson law. -/
def juliaCompressionSquareBiasedProbabilityMeasure : ProbabilityMeasure ℝ :=
  squareBiasedProbabilityMeasure
    (juliaCompressionEquilibriumProbabilityMeasure : Measure ℝ)
    (m := (3 / 2 : ℝ)) (by norm_num)
    integrable_sq_juliaCompressionEquilibriumProbabilityMeasure
    integral_sq_juliaCompressionEquilibriumProbabilityMeasure

/-- Literal `(2 / 3) x²` density formula for the square-biased Julia compression law. -/
theorem juliaCompressionSquareBiasedProbabilityMeasure_toMeasure :
    (juliaCompressionSquareBiasedProbabilityMeasure : Measure ℝ) =
      (juliaCompressionEquilibriumProbabilityMeasure : Measure ℝ).withDensity
        (fun x => (((2 / 3 : ℝ) * x ^ 2).toNNReal : ℝ≥0∞)) := by
  rw [juliaCompressionSquareBiasedProbabilityMeasure,
    squareBiasedProbabilityMeasure]
  simp only [ProbabilityMeasure.coe_mk, squareBiasedMeasure]
  congr 1
  funext x
  congr 2
  ring

/-- First form of the Julia equilibrium identity: square-biased sinc-square expectation. -/
theorem integral_sinc_sq_juliaCompressionSquareBiasedProbabilityMeasure
    (y : ℝ) :
    (∫ x : ℝ, Real.sinc (x / 2 * y) ^ 2
      ∂(juliaCompressionSquareBiasedProbabilityMeasure : Measure ℝ)) =
      juliaDefectAttenuationKernel y := by
  rw [juliaCompressionSquareBiasedProbabilityMeasure,
    squareBiasedProbabilityMeasure]
  simp only [ProbabilityMeasure.coe_mk]
  rw [squareBiasedMeasure,
    integral_withDensity_eq_integral_smul (by fun_prop)]
  rw [show (fun x : ℝ => (x ^ 2 / (3 / 2 : ℝ)).toNNReal •
      Real.sinc (x / 2 * y) ^ 2) =
      fun x => x ^ 2 / (3 / 2 : ℝ) * Real.sinc (x / 2 * y) ^ 2 by
    funext x
    rw [show (x ^ 2 / (3 / 2 : ℝ)).toNNReal =
        ⟨x ^ 2 / (3 / 2 : ℝ), by positivity⟩ by
      exact Real.toNNReal_of_nonneg (by positivity)]
    rfl]
  rw [integral_squareBias_sinc_sq_eq_normalizedCharacteristicDefect
    (juliaCompressionEquilibriumProbabilityMeasure : Measure ℝ)
    (m := (3 / 2 : ℝ)) (by norm_num)
    integrable_sq_juliaCompressionEquilibriumProbabilityMeasure
    integral_sq_juliaCompressionEquilibriumProbabilityMeasure]
  exact normalizedCharacteristicDefect_juliaCompressionEquilibriumProbabilityMeasure y

/-- Julia attenuation as an actual equilibrium-clock probability law. -/
def juliaDefectEquilibriumClockProbabilityMeasure : ProbabilityMeasure ℝ :=
  equilibriumClockProbabilityMeasure
    (juliaCompressionEquilibriumProbabilityMeasure : Measure ℝ)
    (m := (3 / 2 : ℝ)) (by norm_num)
    integrable_sq_juliaCompressionEquilibriumProbabilityMeasure
    integral_sq_juliaCompressionEquilibriumProbabilityMeasure

/-- Second form of the Julia equilibrium identity: the corrected attenuation kernel is a
characteristic function. -/
theorem charFun_juliaDefectEquilibriumClockProbabilityMeasure (y : ℝ) :
    charFun (juliaDefectEquilibriumClockProbabilityMeasure : Measure ℝ) y =
      (juliaDefectAttenuationKernel y : ℂ) := by
  rw [juliaDefectEquilibriumClockProbabilityMeasure,
    charFun_equilibriumClockProbabilityMeasure]
  exact_mod_cast
    normalizedCharacteristicDefect_juliaCompressionEquilibriumProbabilityMeasure y

/-- Explicit law of `X̂ (U - V)`, where `X̂` is square-biased Julia compression and `U,V` are
independent uniforms on `[-1/2,1/2]`. -/
def juliaDefectEquilibriumDifferenceProbabilityMeasure : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    (juliaCompressionSquareBiasedProbabilityMeasure.prod
      centeredUniformDifferenceProbabilityMeasure)
    (f := fun p : ℝ × ℝ => p.1 * p.2) (by fun_prop)

/-- The explicit independent-difference construction is the generic triangular equilibrium
clock. -/
theorem juliaDefectEquilibriumDifferenceProbabilityMeasure_eq_clock :
    juliaDefectEquilibriumDifferenceProbabilityMeasure =
      juliaDefectEquilibriumClockProbabilityMeasure := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [juliaDefectEquilibriumDifferenceProbabilityMeasure,
    juliaDefectEquilibriumClockProbabilityMeasure,
    equilibriumClockProbabilityMeasure]
  simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_prod]
  rw [centeredUniformDifferenceProbabilityMeasure_eq_triangular]
  unfold juliaCompressionSquareBiasedProbabilityMeasure
  rfl

/-- Exact characteristic identity for the paper's independent `X̂ (U - V)` construction. -/
theorem charFun_juliaDefectEquilibriumDifferenceProbabilityMeasure (y : ℝ) :
    charFun (juliaDefectEquilibriumDifferenceProbabilityMeasure : Measure ℝ) y =
      (juliaDefectAttenuationKernel y : ℂ) := by
  rw [juliaDefectEquilibriumDifferenceProbabilityMeasure_eq_clock,
    charFun_juliaDefectEquilibriumClockProbabilityMeasure]

/-- **Julia equilibrium Gram law from source data.**  The theta-specific center-mixed Julia
kernel is positive definite on every finite real configuration. -/
theorem positiveDefiniteOnReal_juliaDefectAttenuationKernel :
    PositiveDefiniteOnReal (fun y => (juliaDefectAttenuationKernel y : ℂ)) := by
  have hpd := positiveDefiniteOnReal_normalizedCharacteristicDefect
    (juliaCompressionEquilibriumProbabilityMeasure : Measure ℝ)
    (m := (3 / 2 : ℝ)) (by norm_num)
    integrable_sq_juliaCompressionEquilibriumProbabilityMeasure
    integral_sq_juliaCompressionEquilibriumProbabilityMeasure
  simpa only [normalizedCharacteristicDefect_juliaCompressionEquilibriumProbabilityMeasure]
    using hpd

end

end HTGeometry
