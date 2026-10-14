import GaloisForLFunctions.HTGeometry.PaperHalfLineCayley
import GaloisForLFunctions.HTGeometry.OperatorReferenceObservation

/-! # Two reference profiles identify the full signed source tail -/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory
private abbrev H := Lp ℂ 2 halfLineMeasure

theorem paperHalfLineCayley_same_norm (F G : C(ℝ, ℝ)) (T : ℝ) (x : H) :
    ‖paperHalfLineCayley F T x‖ = ‖paperHalfLineCayley G T x‖ :=
  (paperHalfLineCayley_norm_map F T x).trans (paperHalfLineCayley_norm_map G T x).symm

theorem paperHalfLineCayley_eq_iff_tail (F G : C(ℝ, ℝ)) (T : ℝ) :
    paperHalfLineCayley F T = paperHalfLineCayley G T ↔ ∀ t ≥ T, F t = G t := by
  constructor
  · intro h
    apply (paperHalfLineCayley_compact_difference_iff F G T).mp
    rw [h, sub_self]
    exact isCompactOperator_zero
  · intro h
    apply sub_eq_zero.mp
    exact (paperHalfLine_compact_iff_zero (paperHalfLineCayley_difference_coeFn F G T)).mp
      ((paperHalfLineCayley_compact_difference_iff F G T).mpr h)

theorem paperHalfLineCayley_reference_eq_iff_tail (F G : C(ℝ, ℝ)) (T : ℝ) :
    ((∀ x, operatorReferenceNorm (paperHalfLineCayley F T) 1 x =
        operatorReferenceNorm (paperHalfLineCayley G T) 1 x) ∧
      (∀ x, operatorReferenceNorm (paperHalfLineCayley F T) Complex.I x =
        operatorReferenceNorm (paperHalfLineCayley G T) Complex.I x)) ↔
      ∀ t ≥ T, F t = G t := by
  rw [operatorReferenceNorm_pair_eq_iff _ _ (paperHalfLineCayley_same_norm F G T),
    paperHalfLineCayley_eq_iff_tail]

end
end GaloisForLFunctions.HTGeometry
