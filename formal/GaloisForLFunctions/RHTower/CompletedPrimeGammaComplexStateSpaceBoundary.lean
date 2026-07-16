import GaloisForLFunctions.HTGeometry.FiniteFieldStateSpaceHankelRank
import GaloisForLFunctions.HTGeometry.LinearRecurrenceStateSpace
import GaloisForLFunctions.RHTower.CompletedPrimeGammaComplexModalBoundary

/-!
# Complex state-space boundary for the moving completed prime--Gamma source

The field-generic state-space Hankel theorem permits arbitrary finite complex transfer matrices,
including nonnormal and nondiagonalizable/Jordan responses.  Applied to the moving completed-source
moments, it turns a single nonzero complex Hankel determinant into an exclusion of every local
finite-coordinate approximation with that fixed complex hidden dimension.

At the functional-equation center, RH supplies nonvanishing in every size.  The result therefore
strictly strengthens the diagonal complex-modal boundary while remaining a constraint theorem, not
an RH proof or a claim that the source is a black hole.
-/

namespace RHTower

noncomputable section

/-- Exact finite complex state-space realization of the moving completed-source moments. -/
def CompletedMovingComplexStateSpaceDimensionAtMost (d : ℕ) (sigma : ℂ) : Prop :=
  HTGeometry.AlgebraicStateSpaceDimensionAtMost d (completedMovingComplexMoment sigma)

/-- Local finite-coordinate closure by complex state-space models of one fixed dimension. -/
def CompletedMovingComplexFixedStateSpaceDimensionLocalClosure
    (d : ℕ) (sigma : ℂ) : Prop :=
  HTGeometry.FixedAlgebraicStateSpaceDimensionLocalClosure d
    (completedMovingComplexMoment sigma)

/-- A finite complex modal model is a diagonal complex state-space realization. -/
theorem completedMovingComplexStateSpaceDimensionAtMost_of_modalWidthAtMost
    {d : ℕ} {sigma : ℂ}
    (h : CompletedMovingComplexModalWidthAtMost d sigma) :
    CompletedMovingComplexStateSpaceDimensionAtMost d sigma :=
  HTGeometry.algebraicStateSpaceDimensionAtMost_of_finiteModalWidthAtMost h

/-- Exact state-space realization implies fixed-dimensional local closure. -/
theorem completedMovingComplexFixedStateSpaceDimensionLocalClosure_of_dimensionAtMost
    {d : ℕ} {sigma : ℂ}
    (h : CompletedMovingComplexStateSpaceDimensionAtMost d sigma) :
    CompletedMovingComplexFixedStateSpaceDimensionLocalClosure d sigma :=
  HTGeometry.fixedAlgebraicStateSpaceDimensionLocalClosure_of_dimensionAtMost h

/-- A positive finite-order recurrence for the moving completed-source values supplies its
canonical companion-matrix realization of the same dimension. -/
theorem completedMovingComplexStateSpaceDimensionAtMost_of_linearRecurrence
    {sigma : ℂ} (E : LinearRecurrence ℂ)
    (hsolution : E.IsSolution (completedMovingComplexMoment sigma))
    (horder : E.order ≠ 0) :
    CompletedMovingComplexStateSpaceDimensionAtMost E.order sigma :=
  HTGeometry.algebraicStateSpaceDimensionAtMost_of_linearRecurrence
    E hsolution horder

/-- Fixed complex state dimension forces the corresponding moving determinant to vanish. -/
theorem completedMovingComplexHankelDet_eq_zero_of_fixedStateSpaceDimensionLocalClosure
    {d : ℕ} {sigma : ℂ}
    (h : CompletedMovingComplexFixedStateSpaceDimensionLocalClosure d sigma) :
    completedMovingComplexHankelDet (d + 1) sigma = 0 := by
  rw [completedMovingComplexHankelDet,
    completedMovingComplexHankelMatrix_eq_algebraicHankelMatrix]
  exact HTGeometry.det_algebraicHankelMatrix_succ_eq_zero_of_fixedStateSpaceDimensionLocalClosure h

/-- One nonzero moving determinant excludes every locally approximating complex state-space model
of the corresponding fixed dimension. -/
theorem not_completedMovingComplexFixedStateSpaceDimensionLocalClosure_of_det_ne_zero
    {d : ℕ} {sigma : ℂ}
    (hdet : completedMovingComplexHankelDet (d + 1) sigma ≠ 0) :
    ¬ CompletedMovingComplexFixedStateSpaceDimensionLocalClosure d sigma := by
  intro h
  exact hdet
    (completedMovingComplexHankelDet_eq_zero_of_fixedStateSpaceDimensionLocalClosure h)

/-- **RH complex hidden-dimension boundary.**  Under RH, no uniformly bounded complex state-space
family can locally reproduce all completed-source moment blocks at the center. -/
theorem not_completedMovingComplexFixedStateSpaceDimensionLocalClosure_one_half_of_riemannHypothesis
    (hRH : RiemannHypothesis) (d : ℕ) :
    ¬ CompletedMovingComplexFixedStateSpaceDimensionLocalClosure d (1 / 2) := by
  apply not_completedMovingComplexFixedStateSpaceDimensionLocalClosure_of_det_ne_zero
  rw [completedMovingComplexHankelDet_one_half]
  exact_mod_cast ne_of_gt
    (by
      rw [primeArchSourceMomentHankelMatrix_eq_xiCentralMomentHankelMatrix]
      exact det_xiCentralMomentHankelMatrix_pos_of_riemannHypothesis hRH (d + 1))

/-- **RH finite-recurrence boundary.**  Under RH, the completed moving source at the center obeys
no positive finite-order complex linear recurrence. -/
theorem not_completedMovingComplexLinearRecurrence_one_half_of_riemannHypothesis
    (hRH : RiemannHypothesis) (E : LinearRecurrence ℂ) (horder : E.order ≠ 0) :
    ¬ E.IsSolution (completedMovingComplexMoment (1 / 2)) := by
  intro hsolution
  apply not_completedMovingComplexFixedStateSpaceDimensionLocalClosure_one_half_of_riemannHypothesis
    hRH E.order
  apply completedMovingComplexFixedStateSpaceDimensionLocalClosure_of_dimensionAtMost
  exact completedMovingComplexStateSpaceDimensionAtMost_of_linearRecurrence
    E hsolution horder

end

end RHTower
