import GaloisForLFunctions.HTGeometry.SymmetricChiralShapeLogDeriv
import GaloisForLFunctions.RHTower.HardyZ

/-!
# Time-one Gamma--Meixner chiral factor is the inverse Hardy reflection phase

The time-one Gamma--Meixner intensity on the critical line is, up to its positive scalar
normalization, the symmetric product of the two completed archimedean Gamma orientations. Its
completed chiral quotient is exactly the inverse zeta functional-equation cocycle, and hence the
inverse square of the corpus's globally oriented Hardy phase.

Together with `SymmetricChiralShapeLogDeriv`, this identifies the shape derivative of the positive
Gamma--Meixner family as a branch-free source for the Hardy phase velocity. No Xi zero or RH
hypothesis enters these identities.
-/

noncomputable section

namespace RHTower

open Complex GaloisForLFunctions.HTGeometry

/-- Completed symmetric time-one Gamma--Meixner factor on the critical line. -/
def gammaMeixnerTimeOneCompletedSymmetric (tau : ℝ) : ℂ :=
  Complex.Gammaℝ (linePt tau) * Complex.Gammaℝ (1 - linePt tau)

/-- Completed pole-oriented time-one chiral quotient. -/
def gammaMeixnerTimeOneCompletedChiral (tau : ℝ) : ℂ :=
  Complex.Gammaℝ (linePt tau) / Complex.Gammaℝ (1 - linePt tau)

/-- Symmetric time-one factor is exactly the squared norm of the completed Gamma orientation. -/
theorem gammaMeixnerTimeOneCompletedSymmetric_eq_normSq (tau : ℝ) :
    gammaMeixnerTimeOneCompletedSymmetric tau =
      (‖Complex.Gammaℝ (linePt tau)‖ : ℂ) ^ 2 := by
  unfold gammaMeixnerTimeOneCompletedSymmetric
  rw [← conj_linePt, Gammaℝ_conj, Complex.mul_conj']

/-- Completed chiral factor is the multiplicative inverse of the zeta reflection cocycle. -/
theorem gammaMeixnerTimeOneCompletedChiral_mul_zetaChi (tau : ℝ) :
    gammaMeixnerTimeOneCompletedChiral tau * zetaChi (linePt tau) = 1 := by
  have hG : Complex.Gammaℝ (linePt tau) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (linePt_re_pos tau)
  have hGc : Complex.Gammaℝ (1 - linePt tau) ≠ 0 := by
    rw [← conj_linePt, Gammaℝ_conj]
    exact (map_ne_zero (starRingEnd ℂ)).mpr hG
  unfold gammaMeixnerTimeOneCompletedChiral zetaChi
  field_simp

/-- The same chiral factor is the inverse square of the canonical continuous Hardy phase. -/
theorem gammaMeixnerTimeOneCompletedChiral_mul_gammaHardyPhase_sq (tau : ℝ) :
    gammaMeixnerTimeOneCompletedChiral tau *
        (gammaHardyPhase tau * gammaHardyPhase tau) = 1 := by
  rw [gammaHardyPhase_sq, gammaMeixnerTimeOneCompletedChiral_mul_zetaChi]

end RHTower
