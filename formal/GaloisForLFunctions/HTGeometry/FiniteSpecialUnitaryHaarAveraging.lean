import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryHaarTopology
import Mathlib.MeasureTheory.Group.Convolution

/-!
# Haar averaging on finite special-unitary groups

Convolving normalized `SU(n)` Haar measure with an arbitrary measure averages
that measure to its total mass times Haar.  This is the measure-theoretic
engine for transferring a local coordinate null-set statement to Haar-nullity.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Averaging any measure by normalized finite-special-unitary Haar measure on
the right gives its total mass times Haar. -/
theorem finiteSpecialUnitaryHaar_left_convolution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure (Matrix.specialUnitaryGroup ι ℂ)) :
    ν ∗ₘ finiteSpecialUnitaryHaar ι =
      (ν Set.univ) • finiteSpecialUnitaryHaar ι := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_mconv hf]
  simp_rw [← MeasureTheory.lintegral_map hf (measurable_const_mul _),
    map_mul_left_eq_self]
  rw [lintegral_const]
  symm
  simpa only [smul_eq_mul, mul_comm] using
    (MeasureTheory.lintegral_smul_measure (μ := finiteSpecialUnitaryHaar ι)
      (f := f) (c := ν Set.univ))

/-- Averaging any measure by normalized finite-special-unitary Haar measure on
the left gives its total mass times Haar. -/
theorem finiteSpecialUnitaryHaar_right_convolution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure (Matrix.specialUnitaryGroup ι ℂ)) [SFinite ν] :
    finiteSpecialUnitaryHaar ι ∗ₘ ν =
      (ν Set.univ) • finiteSpecialUnitaryHaar ι := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_mconv hf]
  have hmeas : Measurable
      (Function.uncurry fun x y : Matrix.specialUnitaryGroup ι ℂ => f (x * y)) := by
    change Measurable (fun p : Matrix.specialUnitaryGroup ι ℂ ×
      Matrix.specialUnitaryGroup ι ℂ => f (p.1 * p.2))
    exact hf.comp measurable_mul
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  simp_rw [← MeasureTheory.lintegral_map hf (measurable_mul_const _),
    map_mul_right_eq_self]
  rw [lintegral_const]
  symm
  simpa only [smul_eq_mul, mul_comm] using
    (MeasureTheory.lintegral_smul_measure (μ := finiteSpecialUnitaryHaar ι)
      (f := f) (c := ν Set.univ))

end

end GaloisForLFunctions.HTGeometry
