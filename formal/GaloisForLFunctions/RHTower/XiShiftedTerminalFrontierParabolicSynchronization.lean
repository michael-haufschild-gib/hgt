import GaloisForLFunctions.RHTower.XiShiftedParabolicDegreeHorizon
import GaloisForLFunctions.RHTower.XiShiftedHankelStrictFrontierCurvatureRenewal

/-!
# Canonical shifted-Xi frontiers are intrinsically parabolic

Fixed-degree far-right positivity does not control a changing degree--mass schedule.  The corpus
parabolic degree horizon is stronger: above one explicit quadratic mass threshold it makes every
vector in the degree-matched shifted-Xi Hankel form strictly positive.

This module connects that theorem to canonical terminal frontiers.  Every occupied degree-`n`
frontier lies below `K (n+2)^2`; every actual strict successor lies strictly below
`K (n+3)^2`.  Consequently false RH can only generate its cofinal source-adaptive strict-frontier
phase inside the intrinsic parabolic cone `sqrt mass = O(degree)`.  Arbitrarily delayed positive
schedules from fixed-degree recession are therefore not canonical-frontier countermodels.
-/

open Matrix Set

namespace RHTower

noncomputable section

/-- Above the corpus parabolic horizon, the complete degree-matched shifted-Xi moment block is
positive definite. -/
theorem xiShiftedMomentHankelMatrix_posDef_of_parabolicDegreeHorizon
    (n : ℕ) {y : ℝ}
    (hy : routeUParabolicDegreeHorizon * (((n + 2 : ℕ) : ℝ) ^ 2) ≤ y) :
    (xiShiftedMomentHankelMatrix y (n + 2)).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨xiShiftedMomentHankelMatrix_isHermitian y (n + 2), ?_⟩
  intro c hc
  rw [star_trivial]
  change 0 < xiShiftedMomentHankelQuadratic y (n + 2) c
  rw [xiShiftedMomentHankelQuadratic_eq]
  exact xiShiftedReciprocalHankelQuadratic_pos_of_parabolic (n + 1) c hc hy

/-- Every actual degree-`n` failure occurs strictly before its quadratic parabolic horizon. -/
theorem lt_parabolicDegreeHorizon_of_mem_xiShiftedHigherBlockFailureSet
    (n : ℕ) {y : ℝ} (hy : y ∈ xiShiftedHigherBlockFailureSet n) :
    y < routeUParabolicDegreeHorizon * (((n + 2 : ℕ) : ℝ) ^ 2) := by
  by_contra hnot
  have hbound : routeUParabolicDegreeHorizon * (((n + 2 : ℕ) : ℝ) ^ 2) ≤ y :=
    le_of_not_gt hnot
  exact hy.2 (xiShiftedMomentHankelMatrix_posDef_of_parabolicDegreeHorizon n hbound)

/-- **Canonical frontier upper synchronization.**  Taking the supremum of the actual failure set
preserves the corpus quadratic mass bound. -/
theorem xiShiftedHigherBlockTerminalFrontier_le_parabolicDegreeHorizon
    (n : ℕ) (hne : (xiShiftedHigherBlockFailureSet n).Nonempty) :
    xiShiftedHigherBlockTerminalFrontier n ≤
      routeUParabolicDegreeHorizon * (((n + 2 : ℕ) : ℝ) ^ 2) := by
  apply csSup_le hne
  intro y hy
  exact (lt_parabolicDegreeHorizon_of_mem_xiShiftedHigherBlockFailureSet n hy).le

/-- Square-root source coordinate of every occupied canonical frontier grows at most linearly in
admission degree. -/
theorem sqrt_xiShiftedHigherBlockTerminalFrontier_le_linearDegreeHorizon
    (n : ℕ) (hne : (xiShiftedHigherBlockFailureSet n).Nonempty) :
    Real.sqrt (xiShiftedHigherBlockTerminalFrontier n) ≤
      Real.sqrt routeUParabolicDegreeHorizon * ((n + 2 : ℕ) : ℝ) := by
  have hbound := xiShiftedHigherBlockTerminalFrontier_le_parabolicDegreeHorizon n hne
  obtain ⟨y, hy⟩ := hne
  have hfront0 : 0 ≤ xiShiftedHigherBlockTerminalFrontier n :=
    hy.1.trans (le_xiShiftedHigherBlockTerminalFrontier_of_mem hy)
  have hK0 : 0 ≤ routeUParabolicDegreeHorizon :=
    routeUParabolicDegreeHorizon_pos.le
  have hfrontSq := Real.sq_sqrt hfront0
  have hKSq := Real.sq_sqrt hK0
  have hsqrtFront0 := Real.sqrt_nonneg (xiShiftedHigherBlockTerminalFrontier n)
  have hsqrtK0 := Real.sqrt_nonneg routeUParabolicDegreeHorizon
  have hn0 : 0 ≤ ((n + 2 : ℕ) : ℝ) := by positivity
  have hprodSq :
      (Real.sqrt routeUParabolicDegreeHorizon * ((n + 2 : ℕ) : ℝ)) ^ 2 =
        routeUParabolicDegreeHorizon * ((n + 2 : ℕ) : ℝ) ^ 2 := by
    rw [mul_pow, hKSq]
  by_contra hnot
  have hlt :
      Real.sqrt routeUParabolicDegreeHorizon * ((n + 2 : ℕ) : ℝ) <
        Real.sqrt (xiShiftedHigherBlockTerminalFrontier n) := lt_of_not_ge hnot
  have hmul : 0 <
      (Real.sqrt (xiShiftedHigherBlockTerminalFrontier n) -
          Real.sqrt routeUParabolicDegreeHorizon * ((n + 2 : ℕ) : ℝ)) *
        (Real.sqrt (xiShiftedHigherBlockTerminalFrontier n) +
          Real.sqrt routeUParabolicDegreeHorizon * ((n + 2 : ℕ) : ℝ)) := by
    apply mul_pos
    · linarith
    · exact add_pos_of_nonneg_of_pos hsqrtFront0
        (mul_pos (Real.sqrt_pos.2 routeUParabolicDegreeHorizon_pos)
          (by positivity))
  nlinarith

/-- At an actual strict step, frontier attainment upgrades the general non-strict supremum bound
to a strict parabolic inequality. -/
theorem xiShiftedHigherBlockTerminalFrontier_succ_lt_parabolicDegreeHorizon
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    xiShiftedHigherBlockTerminalFrontier (n + 1) <
      routeUParabolicDegreeHorizon * (((n + 3 : ℕ) : ℝ) ^ 2) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_effective hne hstrict
  dsimp only at hface
  obtain ⟨v, hv⟩ := hne
  have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
  have hy0 : 0 ≤ y := hv.1.trans (hvle.trans hstrict.le)
  exact lt_parabolicDegreeHorizon_of_mem_xiShiftedHigherBlockFailureSet
    (n + 1) ⟨hy0, hface.2⟩

/-- **False-RH parabolic synchronization.**  The cofinal source-adaptive strict-frontier phase
forced by false RH cannot choose an arbitrarily delayed mass schedule: every rung lies inside the
same explicit parabolic degree cone. -/
theorem exists_cofinal_sourceAdaptive_parabolicFrontierCertificate_of_not_riemannHypothesis
    (hnot : ¬ RiemannHypothesis) (A : ℝ) :
    ∃ n : ℕ,
      (xiShiftedHigherBlockFailureSet n).Nonempty ∧
      A < xiShiftedHigherBlockTerminalFrontier n ∧
      xiShiftedHigherBlockTerminalFrontier n <
        xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
      xiShiftedHigherBlockTerminalFrontier (n + 1) <
        routeUParabolicDegreeHorizon * (((n + 3 : ℕ) : ℝ) ^ 2) := by
  obtain ⟨n, hne, hA, hstrict, _⟩ :=
    exists_cofinal_sourceAdaptive_frontierCertificate_of_not_riemannHypothesis hnot A
  exact ⟨n, hne, hA, hstrict,
    xiShiftedHigherBlockTerminalFrontier_succ_lt_parabolicDegreeHorizon hne hstrict⟩

end

end RHTower
