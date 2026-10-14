import GaloisForLFunctions.RHTower.PaperLagCayleyGreenBoundary
import GaloisForLFunctions.RHTower.PaperLagCayleyCurvatureSeparation
import GaloisForLFunctions.HTGeometry.CayleyReferenceReconstruction

/-! # Reference recovery of the actual integer-lag source

Two singleton reference responses recover every signed curvature coefficient
and the complete lag with its original affine charges. They distinguish the
literal source and arithmetic model at every coordinate of an explicit tail,
although the bare observations agree and their difference has zero ideal cost.
-/

namespace RHTower.PaperLagCayley
noncomputable section
open GaloisForLFunctions.HTGeometry IntegerLagCurvature

theorem source_reference_reconstruction (n : ℕ) :
    lpReferenceSource sourceOperator n = source n :=
  lpReferenceSource_eq sourceOperator source sourceOperator_apply n

theorem arithmetic_reference_reconstruction (n : ℕ) :
    lpReferenceSource arithmeticOperator n = arithmetic n :=
  lpReferenceSource_eq arithmeticOperator arithmetic arithmeticOperator_apply n

theorem source_reference_curvature (n : ℕ) :
    lpReferenceSource sourceOperator n / (n + 3 : ℝ) = scaledCurvature n := by
  rw [source_reference_reconstruction, source]
  have hn : (n : ℝ) + 3 ≠ 0 := by positivity
  field_simp

def lagFromReferences (T : Space →L[ℂ] Space) (N : ℕ) : ℝ :=
  (affineBase + N * affineSlope + ∑ n ∈ Finset.range N,
    ((N : ℝ) - n) * (lpReferenceSource T n / (n + 3 : ℝ))) /
      Real.sqrt (N + 3 : ℝ)

theorem lagFromReferences_source (N : ℕ) :
    lagFromReferences sourceOperator N = integerLag (N + 3) := by
  rw [← lagFromPhases_source N]
  simp only [lagFromReferences, lagFromPhases, greenFromPhases,
    source_reference_reconstruction, source_from_phase]

theorem source_arithmetic_same_bare_observations (x : Space) :
    ‖sourceOperator x‖ = ‖arithmeticOperator x‖ :=
  (ContinuousLinearMap.norm_map_of_mem_unitary sourceOperator_unitary x).trans
    (ContinuousLinearMap.norm_map_of_mem_unitary arithmeticOperator_unitary x).symm

theorem source_arithmetic_same_solid_observations (x : Space) :
    lpSolidObservation sourceOperator x = lpSolidObservation arithmeticOperator x := by
  rw [lpSolidObservation_eq_norm_of_coordinate_mul _ _ sourceOperator_apply,
    lpSolidObservation_eq_norm_of_coordinate_mul _ _ arithmeticOperator_apply]
  exact source_arithmetic_same_bare_observations x

theorem source_arithmetic_reference_singleton_distinguishes (n : ℕ) :
    operatorReferenceNorm sourceOperator 1 (lp.single 2 (n + 9) (1 : ℂ)) ≠
        operatorReferenceNorm arithmeticOperator 1 (lp.single 2 (n + 9) (1 : ℂ)) ∨
      operatorReferenceNorm sourceOperator Complex.I (lp.single 2 (n + 9) (1 : ℂ)) ≠
        operatorReferenceNorm arithmeticOperator Complex.I (lp.single 2 (n + 9) (1 : ℂ)) := by
  classical
  by_contra h
  push Not at h
  apply phase_tail_ne_arithmetic n
  calc
    _ = lpReferencePhase sourceOperator (n + 9) :=
      (lpReferencePhase_eq_circle _ phase sourceOperator_apply _).symm
    _ = lpReferencePhase arithmeticOperator (n + 9) := by
      simp only [lpReferencePhase, h.1, h.2]
    _ = _ := lpReferencePhase_eq_circle _ arithmeticPhase arithmeticOperator_apply _

theorem source_arithmetic_reference_difference_tail_le (n : ℕ) (z : ℂ) :
    |operatorReferenceNorm sourceOperator z (lp.single 2 (n + 9) (1 : ℂ)) -
      operatorReferenceNorm arithmeticOperator z (lp.single 2 (n + 9) (1 : ℂ))| ≤
        1 / (3 * (n + 12 : ℝ) * (n + 11)) := by
  rw [operatorReferenceNorm_coordinate_single _ _ sourceOperator_apply,
    operatorReferenceNorm_coordinate_single _ _ arithmeticOperator_apply]
  calc
    _ ≤ ‖((phase (n + 9) : ℂ) - z) - ((arithmeticPhase (n + 9) : ℂ) - z)‖ :=
      abs_norm_sub_norm_le _ _
    _ = ‖(phase (n + 9) : ℂ) - arithmeticPhase (n + 9)‖ := by congr 1; abel
    _ ≤ _ := phase_discrepancy_tail_le n

theorem source_arithmetic_discrepancy_cost :
    compactOperatorTraceCost Space (sourceOperator - arithmeticOperator) = 0 := by
  rw [compactOperatorTraceCost_eq, if_pos sourceOperator_sub_arithmetic_compact]

end
end RHTower.PaperLagCayley
