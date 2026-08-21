import GaloisForLFunctions.HTGeometry.KerrNewmanBZDressedCoordinateEinsteinBridge
import GaloisForLFunctions.HTGeometry.KerrNewmanEinsteinMaxwellAlgebra

/-!
# Einstein--Maxwell obstruction on the flat BZ Kerr--Newman lift

The constant BZ lift has identically zero coordinate Einstein tensor.  Transport the canonical
Maxwell stress by the same constant frame congruence.  Then its transverse principal entries have
opposite signs, whereas a cosmological term has equal transverse entries.  Thus the full
coordinate Einstein equation on this flat lift has only the zero cosmological and zero Maxwell
member.

This is a consistency/obstruction result for the concrete flat lift, not an Einstein--Maxwell
calculation for curved Kerr--Newman.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

/-- Canonical Maxwell stress transported by the same constant frame change as the flat BZ lift. -/
noncomputable def kerrNewmanFlatBZDressedCanonicalMaxwellStress
    (parameter electric magnetic : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  belinskiZakharovKillingLift parameter * kerrNewmanCanonicalMaxwellStress electric magnetic *
    Matrix.transpose (belinskiZakharovKillingLift parameter)

/-- At zero dressing, the transported source is the canonical Maxwell stress itself. -/
theorem kerrNewmanFlatBZDressedCanonicalMaxwellStress_zero
    (electric magnetic : ℝ) :
    kerrNewmanFlatBZDressedCanonicalMaxwellStress 0 electric magnetic =
      kerrNewmanCanonicalMaxwellStress electric magnetic := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kerrNewmanFlatBZDressedCanonicalMaxwellStress, belinskiZakharovKillingLift,
      kerrNewmanCanonicalMaxwellStress, Matrix.transpose_apply, Matrix.mul_apply,
      Fin.sum_univ_four]

/-- **Flat BZ Einstein--Maxwell obstruction.**  A constant BZ-flat Kerr--Newman lift satisfies
the coordinate Einstein equation with its transported canonical Maxwell source exactly when the
cosmological, electric, and magnetic amplitudes all vanish. -/
theorem kerrNewmanFlatBZDressed_coordinateEinsteinMaxwell_iff_trivial
    (parameter cosmological electric magnetic : ℝ) (x : Fin 4 → ℝ) :
    coordinateEinsteinTensor (kerrNewmanFlatBZDressedSmoothMetric parameter) x +
        cosmological • (kerrNewmanFlatBZDressedSmoothMetric parameter).metric x =
      kerrNewmanFlatBZDressedCanonicalMaxwellStress parameter electric magnetic ↔
      cosmological = 0 ∧ electric = 0 ∧ magnetic = 0 := by
  constructor
  · intro h
    rw [kerrNewmanFlatBZDressed_coordinateEinsteinTensor_zero] at h
    have h11 := congrFun (congrFun h 1) 1
    have h22 := congrFun (congrFun h 2) 2
    simp [kerrNewmanFlatBZDressedSmoothMetric,
      kerrNewmanFlatBZDressedCanonicalMaxwellStress, belinskiZakharovKillingLift,
      kerrNewmanFlatBZDressedMetric, kerrNewmanCanonicalMaxwellStress,
      kerrNewmanCanonicalMaxwellStressMagnitude, Matrix.transpose_apply, Matrix.mul_apply,
      Fin.sum_univ_four] at h11 h22
    have hsum : electric ^ 2 + magnetic ^ 2 = 0 := by
      nlinarith [h11, h22]
    have helectricSq : electric ^ 2 = 0 := by
      nlinarith [sq_nonneg magnetic]
    have hmagneticSq : magnetic ^ 2 = 0 := by
      nlinarith [sq_nonneg electric]
    refine ⟨?_, (sq_eq_zero_iff).mp helectricSq, (sq_eq_zero_iff).mp hmagneticSq⟩
    nlinarith [h11, hsum]
  · rintro ⟨rfl, rfl, rfl⟩
    rw [kerrNewmanFlatBZDressed_coordinateEinsteinTensor_zero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kerrNewmanFlatBZDressedCanonicalMaxwellStress,
        kerrNewmanCanonicalMaxwellStress, kerrNewmanCanonicalMaxwellStressMagnitude,
        belinskiZakharovKillingLift, Matrix.transpose_apply, Matrix.mul_apply,
        Fin.sum_univ_four]

end GaloisForLFunctions.HTGeometry
