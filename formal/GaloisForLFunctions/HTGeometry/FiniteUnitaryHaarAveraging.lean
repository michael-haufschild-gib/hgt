import GaloisForLFunctions.HTGeometry.FiniteUnitaryHaarTopology
import Mathlib.MeasureTheory.Group.Convolution

/-!
# Haar averaging on finite unitary groups

The normalized `U(d)` Haar law averages every finite local coordinate measure
into a scalar multiple of Haar measure.  This is the measure bridge for the
exponential-coordinate atlas used before determinant normalization.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Averaging a measure by normalized finite-unitary Haar on the right. -/
theorem finiteUnitaryHaar_left_convolution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure (Matrix.unitaryGroup ι ℂ)) :
    ν ∗ₘ finiteUnitaryHaar ι =
      (ν Set.univ) • finiteUnitaryHaar ι := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_mconv hf]
  simp_rw [← MeasureTheory.lintegral_map hf (measurable_const_mul _),
    map_mul_left_eq_self]
  rw [lintegral_const]
  symm
  simpa only [smul_eq_mul, mul_comm] using
    (MeasureTheory.lintegral_smul_measure (μ := finiteUnitaryHaar ι)
      (f := f) (c := ν Set.univ))

/-- Averaging normalized finite-unitary Haar by an `SFinite` measure on the
left. -/
theorem finiteUnitaryHaar_right_convolution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure (Matrix.unitaryGroup ι ℂ)) [SFinite ν] :
    finiteUnitaryHaar ι ∗ₘ ν =
      (ν Set.univ) • finiteUnitaryHaar ι := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_mconv hf]
  have hmeas : Measurable
      (Function.uncurry fun x y : Matrix.unitaryGroup ι ℂ => f (x * y)) := by
    change Measurable (fun p : Matrix.unitaryGroup ι ℂ ×
      Matrix.unitaryGroup ι ℂ => f (p.1 * p.2))
    exact hf.comp measurable_mul
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  simp_rw [← MeasureTheory.lintegral_map hf (measurable_mul_const _),
    map_mul_right_eq_self]
  rw [lintegral_const]
  symm
  simpa only [smul_eq_mul, mul_comm] using
    (MeasureTheory.lintegral_smul_measure (μ := finiteUnitaryHaar ι)
      (f := f) (c := ν Set.univ))

end

end GaloisForLFunctions.HTGeometry
