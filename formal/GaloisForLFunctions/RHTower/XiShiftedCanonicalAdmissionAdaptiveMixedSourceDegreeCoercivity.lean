import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveMixedSourceAction

/-!
# Adaptive mixed source action coerces degree transport

The exact degree--mass plaquette says adjacent cumulative flux differs by two Jacobi diagonals.
This module proves that same connector is not free: newborn literal adaptive mixed/completed
`P^sharp` source action strictly pays its square.

The coefficient `3/2` is sharp for the visible pair because newborn dissipation contains
`2 alpha_n^(2 : ℕ) + alpha_(n+1)^(2 : ℕ)`.  Its exact reserve is a sum of a weighted diagonal square, all
earlier diagonal energy, and positive Jacobi edges.  Thus the producer supplies a genuine
discrete--continuous Dirichlet law before reflection aggregation, not another orientation map or
fixed linear reporter.
-/

open Matrix
open scoped BigOperators

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

/-- Exact algebraic reserve behind adjacent-degree source coercivity. -/
theorem three_halves_mul_cumulativeJacobiDissipation_sub_adjacentAlpha_sq_eq_reserve
    (y : ℝ) (n : ℕ) :
    let s := fun k => (xiShiftedReciprocalMoment y k).re
    (3 / 2 : ℝ) * xiShiftedCanonicalAdmissionCumulativeJacobiDissipation y (n + 1) -
        (HTGeometry.monicOrthoAlpha s n +
          HTGeometry.monicOrthoAlpha s (n + 1)) ^ (2 : ℕ) =
      3 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ)) +
        (1 / 2 : ℝ) *
          (2 * HTGeometry.monicOrthoAlpha s n -
            HTGeometry.monicOrthoAlpha s (n + 1)) ^ (2 : ℕ) +
        6 * (∑ j ∈ Finset.range (n + 1), HTGeometry.monicOrthoBeta s j) +
        3 * (n + 2 : ℝ) *
          (HTGeometry.monicOrthoBeta s (n + 1) +
            HTGeometry.monicOrthoBeta s (n + 2)) := by
  dsimp only
  rw [xiShiftedCanonicalAdmissionCumulativeJacobiDissipation,
    Finset.sum_range_succ]
  push_cast
  ring

/-- **Source-first degree coercivity.**  Squared adjacent-degree flux is strictly paid by newborn
adaptive mixed/completed arithmetic source action. -/
theorem xiShiftedCanonicalAdmissionCumulativeJacobiFlux_degreeEdge_sq_lt_sourceAction_succ
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef) :
    (xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ (2 : ℕ)) (n + 1) -
        xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ (2 : ℕ)) n) ^ (2 : ℕ) <
      (3 / 2 : ℝ) *
        xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w (n + 1) := by
  let s := xiShiftedRealMomentSequence w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have haction :=
    xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction_eq_cumulativeJacobiDissipation
      hw (by omega : 0 < n + 1) hH
  have hedge := xiShiftedCanonicalAdmissionCumulativeJacobiFlux_succ_sub_eq_adjacentAlpha
    hn hH
  have hreserve :=
    three_halves_mul_cumulativeJacobiDissipation_sub_adjacentAlpha_sq_eq_reserve
      (w ^ (2 : ℕ)) n
  have hbeta : 0 < HTGeometry.monicOrthoBeta s (n + 1) :=
    HTGeometry.monicOrthoBeta_pos_below hbelow (by omega) (by omega)
  have hsumAlpha : 0 ≤
      ∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ) := by
    apply Finset.sum_nonneg
    intro j _
    exact sq_nonneg _
  have hsumBeta : 0 ≤
      ∑ j ∈ Finset.range (n + 1), HTGeometry.monicOrthoBeta s j := by
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below hbelow (by omega) (by
        have := Finset.mem_range.mp hj
        omega)).le
  have hbeta2 : 0 ≤ HTGeometry.monicOrthoBeta s (n + 2) :=
    (HTGeometry.monicOrthoBeta_pos_below hbelow (by omega) (by omega)).le
  have hreservePos : 0 <
      (3 / 2 : ℝ) *
          xiShiftedCanonicalAdmissionCumulativeJacobiDissipation (w ^ (2 : ℕ)) (n + 1) -
        (HTGeometry.monicOrthoAlpha s n +
          HTGeometry.monicOrthoAlpha s (n + 1)) ^ (2 : ℕ) := by
    change 0 < (3 / 2 : ℝ) *
          xiShiftedCanonicalAdmissionCumulativeJacobiDissipation (w ^ (2 : ℕ)) (n + 1) -
        (HTGeometry.monicOrthoAlpha
            (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n +
          HTGeometry.monicOrthoAlpha
            (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 1)) ^ (2 : ℕ)
    rw [hreserve]
    have hsquare : 0 ≤
        (2 * HTGeometry.monicOrthoAlpha s n -
          HTGeometry.monicOrthoAlpha s (n + 1)) ^ (2 : ℕ) := sq_nonneg _
    have hterminal : 0 <
        3 * (n + 2 : ℝ) *
          (HTGeometry.monicOrthoBeta s (n + 1) +
            HTGeometry.monicOrthoBeta s (n + 2)) := by positivity
    have hfirst : 0 ≤
        3 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ)) :=
      mul_nonneg (by norm_num) hsumAlpha
    have hsecond : 0 ≤ (1 / 2 : ℝ) *
        (2 * HTGeometry.monicOrthoAlpha s n -
          HTGeometry.monicOrthoAlpha s (n + 1)) ^ (2 : ℕ) :=
      mul_nonneg (by norm_num) hsquare
    have hthird : 0 ≤
        6 * (∑ j ∈ Finset.range (n + 1), HTGeometry.monicOrthoBeta s j) :=
      mul_nonneg (by norm_num) hsumBeta
    exact add_pos_of_nonneg_of_pos
      (add_nonneg (add_nonneg hfirst hsecond) hthird) hterminal
  rw [hedge, haction]
  exact sub_pos.mp hreservePos

/-- Derivative form: newborn literal source descent is the exact continuous capital paying its
adjacent discrete degree edge. -/
theorem xiShiftedCanonicalAdmissionCumulativeJacobiFlux_degreeEdge_sq_lt_neg_deriv_succ
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef) :
    (xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ (2 : ℕ)) (n + 1) -
        xiShiftedCanonicalAdmissionCumulativeJacobiFlux (w ^ (2 : ℕ)) n) ^ (2 : ℕ) <
      -(3 / 2 : ℝ) *
        deriv (fun y => xiShiftedCanonicalAdmissionCumulativeJacobiFlux y (n + 1))
          (w ^ (2 : ℕ)) := by
  have hsource :=
    xiShiftedCanonicalAdmissionCumulativeJacobiFlux_degreeEdge_sq_lt_sourceAction_succ
      hw hn hH
  have hflow :=
    hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_neg_sourceAction
      hw (by omega : 0 < n + 1) hH
  rw [hflow.deriv]
  linarith

end
end XiShiftedCanonicalAdmission
end RHTower
