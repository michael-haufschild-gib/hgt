import GaloisForLFunctions.HTGeometry.ExactCompletedC5SeamSlopeChamberNoGo
import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveSl2

/-!
# Exact completed C5 lowest-weight anomaly

The source `sl₂` lowering field was a candidate dimension reduction for the remaining compact C5
incidence problem.  In adapted coordinates it is `-∂/∂b`, so annihilation of completed C5
orientation would remove the clock coordinate and reduce the sign problem to `(r,k)`.

This module kills that route structurally.  At the zero-scale algebraic seam the physical source
field equals `sl₂F`.  Completed C5 orientation vanishes there, but its covariant Lie law and the
nonzero constant term of the fixed-action C5 charge force a strictly positive lowering derivative.
The surviving exact anomaly identifies the obstruction: the compact proof must retain clock
dynamics or replace it with an invariant carrying the same C5 charge.
-/

open Complex Real

namespace HTGeometry

noncomputable section

private abbrev c5ZeroSeamState : ModularThetaSourcePositiveState → ℂ :=
  modularThetaSourcePositiveSeamState 0

/-- Completed C5 orientation vanishes at the zero-scale algebraic seam. -/
theorem eval_modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial_zero_eq_zero :
    MvPolynomial.eval c5ZeroSeamState
      modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial = 0 := by
  rw [← modularThetaSourcePositiveChart_c5ExactCompletedSeamOrientationPolynomial]
  have hchart := eval_modularThetaSourcePositiveChartPullback_seam (0 : ℝ)
    modularThetaLyapunovC5ExactCompletedSeamOrientationPolynomial
  norm_num only [zero_pow] at hchart
  rw [hchart]
  rw [← eval_modularThetaGeneralLyapunovPullback_seam,
    modularThetaGeneralLyapunov_c5ExactCompletedSeamOrientationPolynomial,
    eval_modularThetaODENormalizedC5ExactCompletedSeamOrientationPolynomial_seam]

/-- Exact zero-scale seam value of corrected C5 slope. -/
theorem eval_modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial_zero_eq :
    MvPolynomial.eval c5ZeroSeamState
        modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial =
      (-3 / 8 : ℂ) ^ (6 : ℕ) * modularThetaC5FixedActionSeamPolynomial 0 := by
  rw [← modularThetaSourcePositiveChart_c5ExactCompletedSeamSlopePolynomial]
  have hchart := eval_modularThetaSourcePositiveChartPullback_seam (0 : ℝ)
    modularThetaLyapunovC5ExactCompletedSeamSlopePolynomial
  norm_num only [zero_pow] at hchart
  rw [hchart]
  rw [← eval_modularThetaGeneralLyapunovPullback_seam,
    modularThetaGeneralLyapunov_c5ExactCompletedSeamSlopePolynomial,
    eval_modularThetaODENormalizedC5ExactCompletedSeamSlopePolynomial_seam,
    eval_modularThetaODENormalizedC5FixedActionSeamPolynomial_seam,
    eval_modularThetaODENormalizedSourceJet_zero]
  norm_num [modularThetaODESeamState]

/-- Corrected C5 slope does not vanish at the zero-scale seam. -/
theorem eval_modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial_zero_ne_zero :
    MvPolynomial.eval c5ZeroSeamState
      modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial ≠ 0 := by
  rw [eval_modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial_zero_eq]
  norm_num [modularThetaC5FixedActionSeamPolynomial]

/-- Exact physical-field derivative forced by the zero-scale C5 charge. -/
theorem eval_modularThetaSourcePositiveLie_c5ExactCompletedSeamOrientation_zero_eq :
    MvPolynomial.eval c5ZeroSeamState
        (modularThetaSourcePositiveLie
          modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial) =
      (-3 / 8 : ℂ) ^ (5 : ℕ) * modularThetaC5FixedActionSeamPolynomial 0 := by
  have horientation :=
    eval_modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial_zero_eq_zero
  have hslope :=
    eval_modularThetaSourcePositiveC5ExactCompletedSeamSlopePolynomial_zero_eq
  have hid := congrArg (MvPolynomial.eval c5ZeroSeamState)
    modularThetaSourcePositive_c5ExactCompletedSeamOrientation_covariantLie
  simp only [map_mul, map_add, map_sub, MvPolynomial.eval_C,
    MvPolynomial.eval_X] at hid
  rw [horientation, hslope] at hid
  norm_num [c5ZeroSeamState, modularThetaSourcePositiveSeamState,
    modularThetaSourcePositiveNormalizedSourceJet] at hid
  linear_combination (-8 / 3 : ℂ) * hid

/-- At the zero-scale seam, the physical source derivative and `sl₂F` derivative agree on every
polynomial observable. -/
theorem eval_modularThetaSourcePositiveLie_zero_eq_sl2F
    (P : ModularThetaSourcePositivePolynomial) :
    MvPolynomial.eval c5ZeroSeamState (modularThetaSourcePositiveLie P) =
      MvPolynomial.eval c5ZeroSeamState
        (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F P) := by
  unfold modularThetaSourcePositiveLie modularThetaSourcePositiveFieldLie
  simp only [map_sum, map_mul]
  have huniv : (Finset.univ : Finset ModularThetaSourcePositiveState) =
      {.U, .B, .Q} := by
    ext i
    cases i <;> simp
  rw [huniv]
  simp [c5ZeroSeamState, modularThetaSourcePositiveSeamState,
    modularThetaSourcePositiveVectorField, modularThetaSourcePositiveSl2F,
    modularThetaSourcePositiveLoweringField]
  norm_num

/-- Positive survivor of the failed reduction: the completed C5 orientation carries a strictly
positive, explicitly fixed `sl₂F` anomaly at the zero-scale seam. -/
theorem eval_modularThetaSourcePositiveFieldLie_sl2F_c5ExactCompletedSeamOrientation_zero_pos :
    0 < (MvPolynomial.eval c5ZeroSeamState
      (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F
        modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial)).re := by
  rw [← eval_modularThetaSourcePositiveLie_zero_eq_sl2F,
    eval_modularThetaSourcePositiveLie_c5ExactCompletedSeamOrientation_zero_eq]
  norm_num [modularThetaC5FixedActionSeamPolynomial]

/-- **Lowest-weight reduction no-go.** Completed C5 orientation is not annihilated by `sl₂F`.
Consequently its adapted form genuinely depends on clock coordinate `b`; the compact C5 incidence
burden cannot be reduced to the two invariants `(r,k)` by lowest-weight factorization. -/
theorem modularThetaSourcePositiveC5ExactCompletedSeamOrientation_not_lowestWeight :
    modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F
      modularThetaSourcePositiveC5ExactCompletedSeamOrientationPolynomial ≠ 0 := by
  intro hzero
  have heval := congrArg (MvPolynomial.eval c5ZeroSeamState) hzero
  have hpos :=
    eval_modularThetaSourcePositiveFieldLie_sl2F_c5ExactCompletedSeamOrientation_zero_pos
  rw [heval] at hpos
  simp at hpos

end

end HTGeometry
