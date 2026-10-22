import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarQuadraticCodiagonal

/-!
# Literal matched--quantile parabolic transport

The literal matched and quantile polar cells have equal critical-Mellin atom mass, but their
scalar quadratic codiagonal incurs a squared translation debt.  This file constructs the
three-component parabolic moment carrier directly on those cells.  Each individual cell is a
null rotation of its matched partner, while the polarized cross-cell identity records the
relative displacement exactly.  No positivity, boundedness, or RH consequence is asserted.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

open MeasureTheory

/-- Zeroth, first, and half-second mass moments of an oriented interval. -/
def ccmParabolicMoment (a b : ℝ) : Fin 3 → ℝ :=
  ![b - a, (b ^ (2 : ℕ) - a ^ (2 : ℕ)) / 2, (b ^ (3 : ℕ) - a ^ (3 : ℕ)) / 6]

/-- Parabolic translation on the moment carrier. -/
def ccmParabolicShift (d : ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![v 0, d * v 0 + v 1, d ^ (2 : ℕ) / 2 * v 0 + d * v 1 + v 2]

/-- Lorentz form preserved by one common parabolic translation. -/
def ccmParabolicForm (v : Fin 3 → ℝ) : ℝ :=
  2 * v 0 * v 2 - (v 1) ^ (2 : ℕ)

/-- Polarization of `ccmParabolicForm`; this is the cross-cell channel. -/
def ccmParabolicPairing (v w : Fin 3 → ℝ) : ℝ :=
  v 0 * w 2 + v 2 * w 0 - v 1 * w 1

theorem ccmParabolicShift_moment (a b d : ℝ) :
    ccmParabolicShift d (ccmParabolicMoment a b) =
      ccmParabolicMoment (a + d) (b + d) := by
  funext i
  fin_cases i <;> simp [ccmParabolicShift, ccmParabolicMoment] <;> ring

theorem ccmParabolicForm_shift (d : ℝ) (v : Fin 3 → ℝ) :
    ccmParabolicForm (ccmParabolicShift d v) = ccmParabolicForm v := by
  simp [ccmParabolicForm, ccmParabolicShift]
  ring

theorem ccmParabolicForm_moment (a b : ℝ) :
    ccmParabolicForm (ccmParabolicMoment a b) = (b - a) ^ (4 : ℕ) / 12 := by
  simp [ccmParabolicForm, ccmParabolicMoment]
  ring

theorem ccmParabolicForm_eq_pairing_self (v : Fin 3 → ℝ) :
    ccmParabolicForm v = ccmParabolicPairing v v := by
  simp [ccmParabolicForm, ccmParabolicPairing]
  ring

theorem ccmParabolicPairing_shift (d e : ℝ) (v w : Fin 3 → ℝ) :
    ccmParabolicPairing (ccmParabolicShift d v) (ccmParabolicShift e w) =
      ccmParabolicPairing v w +
        (e - d) * (v 0 * w 1 - v 1 * w 0) +
          (e - d) ^ (2 : ℕ) / 2 * (v 0 * w 0) := by
  simp [ccmParabolicPairing, ccmParabolicShift]
  ring

/-- Three source moments of one literal matched polar cell. -/
def ccmActualHeadMatchedParabolicMoment (n : ℕ) : Fin 3 → ℝ :=
  ccmParabolicMoment
    (ccmActualHeadMatchedPolarLowerCoordinate n)
    (ccmActualHeadMatchedPolarUpperCoordinate n)

/-- Three source moments of the equal-mass literal quantile cell. -/
def ccmActualHeadQuantileParabolicMoment (n : ℕ) : Fin 3 → ℝ :=
  ccmParabolicMoment
    (ccmActualHeadQuantilePolarCoordinate n)
    (ccmActualHeadQuantilePolarCoordinate (n + 1))

theorem ccmActualHeadQuantileParabolicMoment_eq_shift_matched (n : ℕ) :
    ccmActualHeadQuantileParabolicMoment n =
      ccmParabolicShift (ccmActualHeadMatchedQuantilePolarDisplacement n)
        (ccmActualHeadMatchedParabolicMoment n) := by
  rw [ccmActualHeadQuantileParabolicMoment,
    ccmActualHeadMatchedParabolicMoment,
    ccmParabolicShift_moment,
    ccmActualHeadMatchedQuantilePolar_lower_eq_lower_add_displacement n,
    ccmActualHeadMatchedQuantilePolar_upper_eq_upper_add_displacement n]

theorem ccmActualHeadMatchedParabolicMoment_zero (n : ℕ) :
    ccmActualHeadMatchedParabolicMoment n 0 = criticalMellinAtomWeight n := by
  simp [ccmActualHeadMatchedParabolicMoment, ccmParabolicMoment,
    ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight]

theorem ccmActualHeadQuantileParabolicMoment_zero (n : ℕ) :
    ccmActualHeadQuantileParabolicMoment n 0 = criticalMellinAtomWeight n := by
  simp [ccmActualHeadQuantileParabolicMoment, ccmParabolicMoment,
    ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight]

theorem ccmActualHeadQuantileParabolicForm_eq_matched (n : ℕ) :
    ccmParabolicForm (ccmActualHeadQuantileParabolicMoment n) =
      ccmParabolicForm (ccmActualHeadMatchedParabolicMoment n) := by
  rw [ccmActualHeadQuantileParabolicMoment_eq_shift_matched,
    ccmParabolicForm_shift]

theorem ccmParabolicMoment_one_eq_intervalIntegral_id (a b : ℝ) :
    ccmParabolicMoment a b 1 = ∫ y in a..b, y := by
  rw [integral_id]
  simp [ccmParabolicMoment]

theorem ccmParabolicMoment_two_eq_half_intervalIntegral_sq (a b : ℝ) :
    ccmParabolicMoment a b 2 = (∫ y in a..b, y ^ (2 : ℕ)) / 2 := by
  let P : ℝ → ℝ := fun y => y ^ (3 : ℕ) / 3
  have hderiv (x : ℝ) : HasDerivAt P (x ^ (2 : ℕ)) x := by
    dsimp only [P]
    simpa using ((hasDerivAt_id x).pow 3).div_const (3 : ℝ)
  have hint (x y : ℝ) : IntervalIntegrable (fun z : ℝ => z ^ (2 : ℕ)) volume x y :=
    (by fun_prop : Continuous fun z : ℝ => z ^ (2 : ℕ)).intervalIntegrable _ _
  have hab : (∫ y in a..b, y ^ (2 : ℕ)) = P b - P a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) (hint a b)
  rw [hab]
  simp [ccmParabolicMoment, P]
  ring

theorem ccmActualHeadMatchedQuantilePolar_sum_sq (K : ℕ) :
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

/-- Finite literal matched-minus-quantile source vector before scalarization. -/
def ccmActualHeadMatchedQuantileParabolicCodiagonal (K : ℕ) : Fin 3 → ℝ :=
  (∑ n ∈ Finset.range (K + 1),
    ccmActualHeadMatchedParabolicMoment (n + 2)) -
  ∑ n ∈ Finset.range (K + 1),
    ccmActualHeadQuantileParabolicMoment (n + 2)

theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_zero (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCodiagonal K 0 = 0 := by
  simp only [ccmActualHeadMatchedQuantileParabolicCodiagonal,
    Finset.sum_apply, Pi.sub_apply]
  simp_rw [ccmActualHeadMatchedParabolicMoment_zero,
    ccmActualHeadQuantileParabolicMoment_zero]
  simp

theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_one_eq_profile (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCodiagonal K 1 =
      ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K (fun y : ℝ => y) := by
  simp only [ccmActualHeadMatchedQuantileParabolicCodiagonal,
    Finset.sum_apply, Pi.sub_apply]
  simp_rw [ccmActualHeadMatchedParabolicMoment,
    ccmActualHeadQuantileParabolicMoment,
    ccmParabolicMoment_one_eq_intervalIntegral_id]
  rw [ccmActualHeadMatchedQuantilePolar_sum_massCoordinate]
  symm
  apply ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_eq_cells_sub_quantile
  intro x y hx hy
  exact continuous_id.intervalIntegrable x y

theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_two_eq_half_profile (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCodiagonal K 2 =
      ccmActualHeadMatchedPolarAdjacentCodiagonalProfile K (fun y : ℝ => y ^ (2 : ℕ)) / 2 := by
  simp only [ccmActualHeadMatchedQuantileParabolicCodiagonal,
    Finset.sum_apply, Pi.sub_apply]
  simp_rw [ccmActualHeadMatchedParabolicMoment,
    ccmActualHeadQuantileParabolicMoment,
    ccmParabolicMoment_two_eq_half_intervalIntegral_sq]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [← Finset.sum_div, ← Finset.sum_div, ← sub_div,
    ccmActualHeadMatchedQuantilePolar_sum_sq]
  rw [← ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_eq_cells_sub_quantile K
    (fun y : ℝ => y ^ (2 : ℕ))]
  intro x y hx hy
  exact (by fun_prop : Continuous fun z : ℝ => z ^ (2 : ℕ)).intervalIntegrable x y

/-- The literal second parabolic source coordinate retains both completed linear charge and
its full squared displacement term. -/
theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_two_eq_error_charge_sub_debt
    (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCodiagonal K 2 =
      ((∑ n ∈ Finset.range (K + 1),
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
                2 * Real.exp (Real.log (n + 2) / 2))) ^ (2 : ℕ)) / 2 := by
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_two_eq_half_profile,
    ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_sq_eq_error_charge_sub_debt]

theorem ccmActualHeadQuantileParabolicPairing_transport (m n : ℕ) :
    ccmParabolicPairing
        (ccmActualHeadQuantileParabolicMoment m)
        (ccmActualHeadQuantileParabolicMoment n) =
      ccmParabolicPairing
          (ccmActualHeadMatchedParabolicMoment m)
          (ccmActualHeadMatchedParabolicMoment n) +
        (ccmActualHeadMatchedQuantilePolarDisplacement n -
            ccmActualHeadMatchedQuantilePolarDisplacement m) *
          (ccmActualHeadMatchedParabolicMoment m 0 *
              ccmActualHeadMatchedParabolicMoment n 1 -
            ccmActualHeadMatchedParabolicMoment m 1 *
              ccmActualHeadMatchedParabolicMoment n 0) +
        (ccmActualHeadMatchedQuantilePolarDisplacement n -
            ccmActualHeadMatchedQuantilePolarDisplacement m) ^ (2 : ℕ) / 2 *
          (criticalMellinAtomWeight m * criticalMellinAtomWeight n) := by
  rw [ccmActualHeadQuantileParabolicMoment_eq_shift_matched,
    ccmActualHeadQuantileParabolicMoment_eq_shift_matched,
    ccmParabolicPairing_shift,
    ccmActualHeadMatchedParabolicMoment_zero,
    ccmActualHeadMatchedParabolicMoment_zero]

def ccmActualHeadMatchedParabolicDiagonalForm (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1),
    ccmParabolicForm (ccmActualHeadMatchedParabolicMoment (n + 2))

def ccmActualHeadQuantileParabolicDiagonalForm (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1),
    ccmParabolicForm (ccmActualHeadQuantileParabolicMoment (n + 2))

/-- Any block-diagonal parabolic form is exactly blind to matched--quantile displacement. -/
theorem ccmActualHeadQuantileParabolicDiagonalForm_eq_matched (K : ℕ) :
    ccmActualHeadQuantileParabolicDiagonalForm K =
      ccmActualHeadMatchedParabolicDiagonalForm K := by
  unfold ccmActualHeadQuantileParabolicDiagonalForm
    ccmActualHeadMatchedParabolicDiagonalForm
  apply Finset.sum_congr rfl
  intro n hn
  exact ccmActualHeadQuantileParabolicForm_eq_matched (n + 2)

end RHTower
