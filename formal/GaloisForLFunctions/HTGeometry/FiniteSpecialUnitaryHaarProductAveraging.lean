import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryHaarProductTopology
import Mathlib.MeasureTheory.Group.Convolution

/-!
# Haar averaging on independent finite special-unitary gate tuples

The architecture-level independent gate law obeys the same two convolution
identities as a single normalized Haar gate.  It is therefore suitable for a
Haar-null transfer on the complete gate-assignment space.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Averaging any gate-tuple measure by independent Haar gates on the right
gives its total mass times the independent Haar law. -/
theorem finiteSpecialUnitaryHaarProduct_left_convolution
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (ν : Measure (κ → Matrix.specialUnitaryGroup ι ℂ)) :
    ν ∗ₘ finiteSpecialUnitaryHaarProduct κ ι =
      (ν Set.univ) • finiteSpecialUnitaryHaarProduct κ ι := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_mconv hf]
  simp_rw [← MeasureTheory.lintegral_map hf (measurable_const_mul _),
    map_mul_left_eq_self]
  rw [lintegral_const]
  symm
  simpa only [smul_eq_mul, mul_comm] using
    (MeasureTheory.lintegral_smul_measure
      (μ := finiteSpecialUnitaryHaarProduct κ ι) (f := f) (c := ν Set.univ))

/-- Averaging independent Haar gates by an `SFinite` gate-tuple measure on
the left gives its total mass times the independent Haar law. -/
theorem finiteSpecialUnitaryHaarProduct_right_convolution
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (ν : Measure (κ → Matrix.specialUnitaryGroup ι ℂ)) [SFinite ν] :
    finiteSpecialUnitaryHaarProduct κ ι ∗ₘ ν =
      (ν Set.univ) • finiteSpecialUnitaryHaarProduct κ ι := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_mconv hf]
  have hmeas : Measurable
      (Function.uncurry fun x y : κ → Matrix.specialUnitaryGroup ι ℂ => f (x * y)) := by
    change Measurable (fun p : (κ → Matrix.specialUnitaryGroup ι ℂ) ×
      (κ → Matrix.specialUnitaryGroup ι ℂ) => f (p.1 * p.2))
    exact hf.comp measurable_mul
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  simp_rw [← MeasureTheory.lintegral_map hf (measurable_mul_const _),
    map_mul_right_eq_self]
  rw [lintegral_const]
  symm
  simpa only [smul_eq_mul, mul_comm] using
    (MeasureTheory.lintegral_smul_measure
      (μ := finiteSpecialUnitaryHaarProduct κ ι) (f := f) (c := ν Set.univ))

end

end GaloisForLFunctions.HTGeometry
