import GaloisForLFunctions.HTGeometry.KerrNewmanEinsteinMaxwellAlgebra
import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovBridge

/-!
# Belinski--Zakharov nilpotent residue as an Einstein--Maxwell rank-one endomorphism

The canonical BZ nilpotent residue is the existing Einstein--Maxwell rank-one endomorphism on
the two-Killing plane: take its second coordinate and return that multiple of the residue vector.
Its contraction vanishes, so the generic rank-one square law specializes to nilpotence. This is
common algebraic structure only, not a physical stress-tensor identification.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

/-- The coordinate functional selecting the second two-Killing component. -/
def belinskiZakharovNilpotentCoordinateFunctional :
    (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.proj 1

/-- The BZ residue vector has zero contraction with its coordinate functional. -/
theorem belinskiZakharovNilpotentCoordinateFunctional_vector
    (residue : ℝ) :
    belinskiZakharovNilpotentCoordinateFunctional ![residue, 0] = 0 := by
  simp [belinskiZakharovNilpotentCoordinateFunctional]

/-- BZ nilpotent-residue action is exactly the canonical Einstein--Maxwell rank-one action. -/
theorem belinskiZakharovNilpotentResidue_mulVec_eq_einsteinMaxwellRankOne
    (residue : ℝ) (x : Fin 2 → ℝ) :
    belinskiZakharovNilpotentResidue residue *ᵥ x =
      einsteinMaxwellRankOneEndomorphism
        belinskiZakharovNilpotentCoordinateFunctional ![residue, 0] x := by
  ext i
  fin_cases i <;>
    simp [belinskiZakharovNilpotentResidue, Matrix.mulVec,
      einsteinMaxwellRankOneEndomorphism,
      belinskiZakharovNilpotentCoordinateFunctional, dotProduct, Fin.sum_univ_two]
  all_goals ring

/-- The generic Einstein--Maxwell rank-one square law gives zero for the BZ specialization. -/
theorem belinskiZakharovNilpotentEinsteinMaxwellRankOne_sq
    (residue : ℝ) :
    einsteinMaxwellRankOneEndomorphism
        belinskiZakharovNilpotentCoordinateFunctional ![residue, 0] *
      einsteinMaxwellRankOneEndomorphism
        belinskiZakharovNilpotentCoordinateFunctional ![residue, 0] = 0 := by
  rw [einsteinMaxwellRankOneEndomorphism_sq]
  simp [belinskiZakharovNilpotentCoordinateFunctional]

end GaloisForLFunctions.HTGeometry
