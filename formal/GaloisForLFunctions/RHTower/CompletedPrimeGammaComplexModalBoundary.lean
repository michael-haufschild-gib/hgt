import GaloisForLFunctions.HTGeometry.FiniteModalHankelRank
import GaloisForLFunctions.RHTower.CompletedPrimeGammaMovingComplexHankel

/-!
# Complex modal boundary for the moving completed prime--Gamma source

Finite quasinormal-mode and damped-oscillator models become finite complex modal sequences after
sampling.  The moving completed-source Hankel determinant therefore supplies an exact admission
test: a nonzero determinant in size `d+1` excludes every exact `d`-mode model.

At the functional-equation center, RH makes every leading real source determinant strictly
positive.  Its complex scalar extension is nonzero, so under RH the completed-source moment clock
escapes every fixed finite complex modal model.  This is a constraint on observed values, not an
identification of the source with a black hole or a claim about spacetime evolution.
-/

namespace RHTower

noncomputable section

/-- The moving completed-source moment sequence has complex modal width at most `d`. -/
def CompletedMovingComplexModalWidthAtMost (d : ℕ) (sigma : ℂ) : Prop :=
  HTGeometry.FiniteModalWidthAtMost d (completedMovingComplexMoment sigma)

/-- The moving completed-source complex matrix is the generic algebraic Hankel matrix. -/
theorem completedMovingComplexHankelMatrix_eq_algebraicHankelMatrix
    (n : ℕ) (sigma : ℂ) :
    completedMovingComplexHankelMatrix n sigma =
      HTGeometry.algebraicHankelMatrix (completedMovingComplexMoment sigma) n := rfl

/-- A finite complex modal presentation forces the corresponding moving determinant to vanish. -/
theorem completedMovingComplexHankelDet_eq_zero_of_modalWidthAtMost
    {d : ℕ} {sigma : ℂ}
    (h : CompletedMovingComplexModalWidthAtMost d sigma) :
    completedMovingComplexHankelDet (d + 1) sigma = 0 := by
  rw [completedMovingComplexHankelDet,
    completedMovingComplexHankelMatrix_eq_algebraicHankelMatrix]
  exact HTGeometry.det_algebraicHankelMatrix_succ_eq_zero_of_finiteModalWidthAtMost h

/-- A nonzero moving determinant excludes every exact complex modal model of that width. -/
theorem not_completedMovingComplexModalWidthAtMost_of_det_ne_zero
    {d : ℕ} {sigma : ℂ}
    (hdet : completedMovingComplexHankelDet (d + 1) sigma ≠ 0) :
    ¬ CompletedMovingComplexModalWidthAtMost d sigma := by
  intro h
  exact hdet (completedMovingComplexHankelDet_eq_zero_of_modalWidthAtMost h)

/-- **RH complex modal boundary.**  Under RH, the completed source at the center escapes every
fixed finite complex modal model. -/
theorem not_completedMovingComplexModalWidthAtMost_one_half_of_riemannHypothesis
    (hRH : RiemannHypothesis) (d : ℕ) :
    ¬ CompletedMovingComplexModalWidthAtMost d (1 / 2) := by
  apply not_completedMovingComplexModalWidthAtMost_of_det_ne_zero
  rw [completedMovingComplexHankelDet_one_half]
  exact_mod_cast ne_of_gt
    (by
      rw [primeArchSourceMomentHankelMatrix_eq_xiCentralMomentHankelMatrix]
      exact det_xiCentralMomentHankelMatrix_pos_of_riemannHypothesis hRH (d + 1))

end

end RHTower
