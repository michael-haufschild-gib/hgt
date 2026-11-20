import GaloisForLFunctions.goldbach.LiLiu.Mellin.VerticalLine
import GaloisForLFunctions.goldbach.LiLiu.Boundary.BoundaryTest
import GaloisForLFunctions.HTGeometry.TranslationFrameOperators

/-! # Positive arc length on both boundaries of the arithmetic strip

The left-edge test extends by zero to the second boundary. Its squared
norm in the two-edge space is exactly its squared norm on the line.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

@[simp] theorem mellinLine_re (a t : ℝ) : (mellinLine a t).re = a := by simp [mellinLine]
@[simp] theorem mellinLine_im (a t : ℝ) : (mellinLine a t).im = t := by simp [mellinLine]

theorem mellinLine_continuous (a : ℝ) : Continuous (mellinLine a) := by unfold mellinLine; fun_prop

def boundaryMeasure (a b : ℝ) : Measure ℂ :=
  Measure.map (mellinLine a) volume + Measure.map (mellinLine b) volume

instance (a b : ℝ) : SFinite (boundaryMeasure a b) := by unfold boundaryMeasure; infer_instance

theorem boundaryMeasure_ae_edges (a b : ℝ) :
    ∀ᵐ z ∂boundaryMeasure a b, z.re = a ∨ z.re = b := by
  have hm : MeasurableSet {z : ℂ | z.re=a ∨ z.re=b} :=
    (measurableSet_eq_fun continuous_re.measurable measurable_const).union
      (measurableSet_eq_fun continuous_re.measurable measurable_const)
  rw [boundaryMeasure,ae_add_measure_iff,ae_map_iff (mellinLine_continuous a).measurable.aemeasurable hm,
    ae_map_iff (mellinLine_continuous b).measurable.aemeasurable hm]
  exact ⟨Eventually.of_forall (fun t => Or.inl (mellinLine_re _ _)),
    Eventually.of_forall (fun t => Or.inr (mellinLine_re _ _))⟩

theorem integrable_boundaryMeasure_iff {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {f : ℂ → E} (hf : Measurable f) (a b : ℝ) :
    Integrable f (boundaryMeasure a b) ↔ Integrable (fun t => f (mellinLine a t)) ∧
      Integrable (fun t => f (mellinLine b t)) := by
  rw [boundaryMeasure,integrable_add_measure,
    integrable_map_measure hf.aestronglyMeasurable (mellinLine_continuous a).measurable.aemeasurable,
    integrable_map_measure hf.aestronglyMeasurable (mellinLine_continuous b).measurable.aemeasurable]
  rfl

theorem integral_boundaryMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {f : ℂ → E}
    (hf : Measurable f) {a b : ℝ} (hi : Integrable f (boundaryMeasure a b)) :
    (∫ z, f z ∂boundaryMeasure a b) =
      (∫ t : ℝ, f (mellinLine a t)) + ∫ t : ℝ, f (mellinLine b t) := by
  obtain ⟨h₁,h₂⟩ := integrable_add_measure.mp hi
  rw [boundaryMeasure,integral_add_measure h₁ h₂,integral_map (mellinLine_continuous a).measurable.aemeasurable
    hf.aestronglyMeasurable,integral_map (mellinLine_continuous b).measurable.aemeasurable hf.aestronglyMeasurable]

def leftLift (a : ℝ) (f : ℝ → ℂ) (z : ℂ) := if z.re=a then f z.im else 0

theorem leftLift_measurable {f : ℝ → ℂ} (hf : Measurable f) (a : ℝ) : Measurable (leftLift a f) :=
  (hf.comp continuous_im.measurable).ite (measurableSet_eq_fun continuous_re.measurable measurable_const)
    measurable_const

theorem leftLift_memLp {a b : ℝ} (hab : a < b) {f : ℝ → ℂ} (hf : Measurable f) (hi : MemLp f 2 volume) :
    MemLp (leftLift a f) 2 (boundaryMeasure a b) := by
  have hm := leftLift_measurable hf a
  rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable,
    integrable_boundaryMeasure_iff (hm.norm.pow_const 2) a b]
  simpa [leftLift,hab.ne']
    using And.intro ((memLp_two_iff_integrable_sq_norm hi.1).mp hi) (integrable_zero ℝ ℝ volume)

theorem leftLift_norm_sq {a b : ℝ} (hab : a < b) {f : ℝ → ℂ} (hf : Measurable f) (hi : MemLp f 2 volume) :
    ‖(leftLift_memLp hab hf hi).toLp (leftLift a f)‖^2 = ‖hi.toLp f‖^2 := by
  have H := leftLift_memLp hab hf hi
  rw [HTGeometry.norm_sq_toLp_eq_integral H,HTGeometry.norm_sq_toLp_eq_integral hi,
    integral_boundaryMeasure ((leftLift_measurable hf a).norm.pow_const 2)
      ((memLp_two_iff_integrable_sq_norm H.1).mp H)]
  simp [leftLift,hab.ne']

def clippedPoint (a b : ℝ) (z : ℂ) : ℂ := mellinLine (max a (min b z.re)) z.im

theorem clippedPoint_continuous (a b : ℝ) : Continuous (clippedPoint a b) := by
  unfold clippedPoint mellinLine
  fun_prop

theorem clippedPoint_re {a b : ℝ} (hab : a ≤ b) (z : ℂ) : (clippedPoint a b z).re ∈ Icc a b := by
  simp only [clippedPoint,mellinLine_re]
  exact ⟨le_max_left ..,max_le hab (min_le_left ..)⟩

@[simp] theorem clippedPoint_im (a b : ℝ) (z : ℂ) : (clippedPoint a b z).im = z.im := mellinLine_im ..

theorem clippedPoint_eq {a b : ℝ} {z : ℂ} (hz : z.re ∈ Icc a b) : clippedPoint a b z=z := by
  simp [clippedPoint,mellinLine,min_eq_right hz.2,max_eq_right hz.1,re_add_im]

#print axioms leftLift_norm_sq
end
end GaloisForLFunctions.Goldbach.LiLiu
