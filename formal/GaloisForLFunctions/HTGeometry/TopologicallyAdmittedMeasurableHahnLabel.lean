import GaloisForLFunctions.HTGeometry.PosteriorContrastProjection
import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedHahnLabel
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

open MeasureTheory
open Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {X : Type u} [MeasurableSpace X]

/-- Signed current carried by a binary measurable experiment. -/
def measurableSignedCurrent (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] : SignedMeasure X :=
  Q.toSignedMeasure - P.toSignedMeasure

/-- Canonical dominating law for the signed current. -/
def currentControl (P Q : Measure X) : Measure X := P + Q

/-- The signed current is absolutely continuous with respect to the sum law. -/
theorem measurableSignedCurrent_absolutelyContinuous
    (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    measurableSignedCurrent P Q ≪ᵥ (currentControl P Q).toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.sub
  · apply VectorMeasure.AbsolutelyContinuous.mk
    intro s hs hzero
    rw [currentControl, Measure.toENNRealVectorMeasure_apply_measurable hs] at hzero
    have hQ : Q s = 0 :=
      (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)) hzero
    rw [Measure.toSignedMeasure_apply_measurable hs, measureReal_def, hQ]
    simp
  · apply VectorMeasure.AbsolutelyContinuous.mk
    intro s hs hzero
    rw [currentControl, Measure.toENNRealVectorMeasure_apply_measurable hs] at hzero
    have hP : P s = 0 :=
      (Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)) hzero
    rw [Measure.toSignedMeasure_apply_measurable hs, measureReal_def, hP]
    simp

/-- Canonical real Radon--Nikodym density of the signed current. -/
def measurableHahnDensity (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] : X → ℝ :=
  (measurableSignedCurrent P Q).rnDeriv (currentControl P Q)

theorem measurable_measurableHahnDensity (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    Measurable (measurableHahnDensity P Q) := by
  unfold measurableHahnDensity
  fun_prop

theorem integrable_measurableHahnDensity (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    Integrable (measurableHahnDensity P Q) (currentControl P Q) := by
  exact SignedMeasure.integrable_rnDeriv _ _

/-- Radon--Nikodym reconstruction of the signed current. -/
theorem currentControl_withDensity_measurableHahnDensity
    (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    (currentControl P Q).withDensityᵥ (measurableHahnDensity P Q) =
      measurableSignedCurrent P Q := by
  letI : IsFiniteMeasure (currentControl P Q) := by
    unfold currentControl
    infer_instance
  exact SignedMeasure.withDensityᵥ_rnDeriv_eq _ _
    (measurableSignedCurrent_absolutelyContinuous P Q)

/-- The weighted `L¹` law is literally variation of the signed current. -/
theorem variation_measurableSignedCurrent_eq
    (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    (measurableSignedCurrent P Q).variation =
      (currentControl P Q).withDensity
        (fun x => ‖measurableHahnDensity P Q x‖ₑ) := by
  rw [← currentControl_withDensity_measurableHahnDensity P Q]
  exact Measure.variation_withDensityᵥ
    (integrable_measurableHahnDensity P Q)

/-- Probability-normalized total variation, expressed in source RN coordinates. -/
def measurableHahnTV (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] : ℝ :=
  (1 / 2 : ℝ) * ∫ x, |measurableHahnDensity P Q x| ∂(currentControl P Q)

/-- The RN-coordinate definition equals half the signed-current variation mass. -/
theorem measurableHahnTV_eq_half_variation
    (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    measurableHahnTV P Q =
      (1 / 2 : ℝ) * ((measurableSignedCurrent P Q).variation Set.univ).toReal := by
  rw [measurableHahnTV, variation_measurableSignedCurrent_eq,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  congr 1
  simpa only [Real.norm_eq_abs] using
    (integral_norm_eq_lintegral_enorm
      (integrable_measurableHahnDensity P Q).aestronglyMeasurable)

/-- Measurability of the fixed representative of the Hahn sign. -/
theorem measurable_hahnSign : Measurable hahnSign := by
  unfold hahnSign
  exact Measurable.ite (measurableSet_le measurable_const measurable_id)
    measurable_const measurable_const

/-- Canonical measurable Hahn label of a binary experiment. -/
def measurableHahnLabel (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] : X → ℝ :=
  fun x => hahnSign (measurableHahnDensity P Q x)

theorem measurable_measurableHahnLabel (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    Measurable (measurableHahnLabel P Q) :=
  measurable_hahnSign.comp (measurable_measurableHahnDensity P Q)

/-- Current extracted by a measurable soft label. -/
def measurableDecisionCurrent (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (g : SoftLabel X) : ℝ :=
  (1 / 2 : ℝ) *
    ∫ x, (g x : ℝ) * measurableHahnDensity P Q x ∂(currentControl P Q)

/-- Weighted approximation error to the canonical measurable Hahn label. -/
def measurableHahnLabelError (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (g : SoftLabel X) : ℝ :=
  ∫ x, |(g x : ℝ) - measurableHahnLabel P Q x| *
    |measurableHahnDensity P Q x| ∂(currentControl P Q)

theorem integrable_abs_measurableHahnDensity
    (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    Integrable (fun x => |measurableHahnDensity P Q x|) (currentControl P Q) := by
  simpa only [Real.norm_eq_abs] using
    (integrable_measurableHahnDensity P Q).norm

theorem integrable_softLabel_mul_measurableHahnDensity
    (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (g : SoftLabel X) (hg : Measurable fun x => ((g x : Set.Icc (-1 : ℝ) 1) : ℝ)) :
    Integrable (fun x => (g x : ℝ) * measurableHahnDensity P Q x)
      (currentControl P Q) := by
  refine (integrable_measurableHahnDensity P Q).norm.mono'
    (hg.mul (measurable_measurableHahnDensity P Q)).aestronglyMeasurable ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, abs_mul]
  calc
    |(g x : ℝ)| * |measurableHahnDensity P Q x| ≤
        1 * |measurableHahnDensity P Q x| := by
      gcongr
      exact (abs_le.mpr (g x).2)
    _ = |measurableHahnDensity P Q x| := one_mul _

/-- Exact measurable Hahn law: decision deficit is weighted `L¹` label error. -/
theorem measurableHahnTV_sub_decisionCurrent_eq_labelError
    (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (g : SoftLabel X) (hg : Measurable fun x => ((g x : Set.Icc (-1 : ℝ) 1) : ℝ)) :
    measurableHahnTV P Q - measurableDecisionCurrent P Q g =
      (1 / 2 : ℝ) * measurableHahnLabelError P Q g := by
  rw [measurableHahnTV, measurableDecisionCurrent, measurableHahnLabelError,
    ← mul_sub, ← integral_sub
      (integrable_abs_measurableHahnDensity P Q)
      (integrable_softLabel_mul_measurableHahnDensity P Q g hg)]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [measurableHahnLabel]
  have hpoint := hahn_regret_pointwise (measurableHahnDensity P Q x) (g x)
  linarith

end

end GaloisForLFunctions.HTGeometry
