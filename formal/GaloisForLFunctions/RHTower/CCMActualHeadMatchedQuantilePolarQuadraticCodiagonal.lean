import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarAdjacentCodiagonal

/-!
# Quadratic debt of the literal matched--quantile codiagonal

The adjacent matched--quantile codiagonal already conserves total polar mass and its
endpoint-renormalized first moment is the signed completed-error readout.  This module computes
the next mass-coordinate mode without changing the cells or taking absolute values.

For each equal-mass matched/quantile pair, translation by its literal displacement contributes a
signed linear charge and an unavoidable nonnegative quadratic debt.  Substituting the exact
completed-error displacement identifies both terms on the actual prime--polar source.  Thus any
future nonlocal cancellation law must pay this displayed debt with the same signed node-error
charge; it cannot erase it through cellwise positivity.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

open Finset MeasureTheory

private theorem intervalIntegral_sq_sub_translate_sq
    (a b d : ℝ) :
    (∫ y in a..b, y ^ (2 : ℕ)) - (∫ y in (a + d)..(b + d), y ^ (2 : ℕ)) =
      -d * (b - a) * (a + b + d) := by
  let P : ℝ → ℝ := fun y => y ^ (3 : ℕ) / 3
  have hderiv (x : ℝ) : HasDerivAt P (x ^ (2 : ℕ)) x := by
    dsimp only [P]
    simpa using ((hasDerivAt_id x).pow 3).div_const (3 : ℝ)
  have hint (x y : ℝ) : IntervalIntegrable (fun z : ℝ => z ^ (2 : ℕ)) volume x y :=
    (by fun_prop : Continuous fun z : ℝ => z ^ (2 : ℕ)).intervalIntegrable _ _
  have hab : (∫ y in a..b, y ^ (2 : ℕ)) = P b - P a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) (hint a b)
  have habd : (∫ y in (a + d)..(b + d), y ^ (2 : ℕ)) =
      P (b + d) - P (a + d) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      (hint (a + d) (b + d))
  rw [hab, habd]
  dsimp only [P]
  ring

private theorem sum_quantile_cells_sq_eq_interval (K : ℕ) :
    (∑ n ∈ Finset.range (K + 1),
      ∫ y in ccmActualHeadQuantilePolarCoordinate (n + 2)..
          ccmActualHeadQuantilePolarCoordinate (n + 3), y ^ (2 : ℕ)) =
      ∫ y in ccmActualHeadQuantilePolarCoordinate 2..
          ccmActualHeadQuantilePolarCoordinate (K + 3), y ^ (2 : ℕ) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      exact intervalIntegral.integral_add_adjacent_intervals
        ((by fun_prop : Continuous fun y : ℝ => y ^ (2 : ℕ)).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun y : ℝ => y ^ (2 : ℕ)).intervalIntegrable _ _)

/-- Signed first-order displacement charge carried by the quadratic codiagonal mode. -/
def ccmActualHeadMatchedPolarQuadraticCodiagonalLinearCharge (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1),
    ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) *
      criticalMellinAtomWeight (n + 2) *
        (ccmActualHeadMatchedPolarLowerCoordinate (n + 2) +
          ccmActualHeadMatchedPolarUpperCoordinate (n + 2))

/-- Nonnegative squared-displacement debt forced by equal-mass cell translation. -/
def ccmActualHeadMatchedPolarQuadraticCodiagonalDebt (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1),
    ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) ^ (2 : ℕ) *
      criticalMellinAtomWeight (n + 2)

theorem ccmActualHeadMatchedPolarQuadraticCodiagonalDebt_nonneg (K : ℕ) :
    0 ≤ ccmActualHeadMatchedPolarQuadraticCodiagonalDebt K := by
  unfold ccmActualHeadMatchedPolarQuadraticCodiagonalDebt
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (sq_nonneg _)
      (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer (n + 2))

/-- **Exact quadratic codiagonal law.**  The second mass-coordinate mode of the literal
matched--quantile coverage seam is its signed displacement charge minus the full squared
translation debt.  No source term is discarded. -/
theorem ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_sq :
    ∀ K : ℕ,
      ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K (fun y : ℝ => y ^ (2 : ℕ)) =
        -ccmActualHeadMatchedPolarQuadraticCodiagonalLinearCharge K -
          ccmActualHeadMatchedPolarQuadraticCodiagonalDebt K := by
  intro K
  rw [ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_eq_cells_sub_quantile]
  · rw [← sum_quantile_cells_sq_eq_interval K, ← Finset.sum_sub_distrib]
    unfold ccmActualHeadMatchedPolarQuadraticCodiagonalLinearCharge
      ccmActualHeadMatchedPolarQuadraticCodiagonalDebt
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    let a := ccmActualHeadMatchedPolarLowerCoordinate (n + 2)
    let b := ccmActualHeadMatchedPolarUpperCoordinate (n + 2)
    let d := ccmActualHeadMatchedQuantilePolarDisplacement (n + 2)
    have htranslateLo :
        ccmActualHeadQuantilePolarCoordinate (n + 2) = a + d := by
      exact ccmActualHeadMatchedQuantilePolar_lower_eq_lower_add_displacement (n + 2)
    have htranslateHi :
        ccmActualHeadQuantilePolarCoordinate (n + 3) = b + d := by
      exact ccmActualHeadMatchedQuantilePolar_upper_eq_upper_add_displacement (n + 2)
    have hwidth : b - a = criticalMellinAtomWeight (n + 2) := by
      exact ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight (n + 2)
    rw [htranslateLo, htranslateHi,
      intervalIntegral_sq_sub_translate_sq a b d, hwidth]
    dsimp only [a, b, d]
    ring
  · intro x y hx hy
    exact (by fun_prop : Continuous fun z : ℝ => z ^ (2 : ℕ)).intervalIntegrable x y

/-- **Completed-source quadratic debt law.**  After retaining the literal matched upper excess,
the quadratic codiagonal mode is the signed outgoing completed-node error charge minus the
square of that same charged displacement.  This is a source identity, not a sign estimate. -/
theorem ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_sq_eq_error_charge_sub_debt
    (K : ℕ) :
    ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K (fun y : ℝ => y ^ (2 : ℕ)) =
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) *
          (ccmActualHeadOutgoingNodeError (n + 2) +
            (ccmActualHeadMatchedPolarUpperCoordinate (n + 2) -
              2 * Real.exp (Real.log (n + 2) / 2))) *
          (ccmActualHeadMatchedPolarLowerCoordinate (n + 2) +
            ccmActualHeadMatchedPolarUpperCoordinate (n + 2))) -
      ∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) *
          (ccmActualHeadOutgoingNodeError (n + 2) +
            (ccmActualHeadMatchedPolarUpperCoordinate (n + 2) -
              2 * Real.exp (Real.log (n + 2) / 2))) ^ (2 : ℕ) := by
  rw [ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_sq]
  unfold ccmActualHeadMatchedPolarQuadraticCodiagonalLinearCharge
    ccmActualHeadMatchedPolarQuadraticCodiagonalDebt
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n + 2 := by omega
  rw [ccmActualHeadMatchedQuantilePolarDisplacement_eq_neg_error_sub_upperExcess
    (n + 2) hnpos]
  norm_num [Nat.cast_add]
  ring

end RHTower
