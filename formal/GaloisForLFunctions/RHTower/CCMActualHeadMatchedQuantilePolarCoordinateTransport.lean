import GaloisForLFunctions.RHTower.CCMActualHeadMatchedBoundaryCoverageSeam

/-!
# Rigid matched-to-quantile transport in exponential polar coordinate

The local mass-matched cell and the monotone quantile cell attached to one critical Mellin atom
look unrelated in logarithmic height. In the canonical polar mass coordinate

`Y(h) = 2 exp(h / 2)`,

both are intervals of exactly the same length `criticalMellinAtomWeight n`. Their comparison is
therefore one rigid translation. This module identifies that translation exactly.

For a positive integer `n`, let `R_n` be the outgoing completed critical-Mellin error at `log n`.
The matched-to-quantile displacement `delta_n` satisfies

`delta_n = -R_n - matchedUpperExcess_n`,

where the local upper excess lies in `[0, criticalMellinAtomWeight n]`. Hence

`-R_n - criticalMellinAtomWeight n <= delta_n <= -R_n`.

This converts the matched coverage problem into a rigid-transport problem controlled by the
cumulative completed error up to one local atom. It makes no sign or RH claim.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- Lower endpoint of a matched symmetric cell in exponential polar mass coordinate. -/
def ccmActualHeadMatchedPolarLowerCoordinate (n : ℕ) : ℝ :=
  2 * Real.exp
    ((Real.log n - ccmActualHeadMatchedPrimePolarRadius n) / 2)

/-- Upper endpoint of a matched symmetric cell in exponential polar mass coordinate. -/
def ccmActualHeadMatchedPolarUpperCoordinate (n : ℕ) : ℝ :=
  2 * Real.exp
    ((Real.log n + ccmActualHeadMatchedPrimePolarRadius n) / 2)

/-- Monotone quantile boundary in exponential polar mass coordinate. -/
def ccmActualHeadQuantilePolarCoordinate (N : ℕ) : ℝ :=
  2 * Real.exp (ccmOutgoingPrimeQuantileBoundary N / 2)

/-- Rigid translation carrying the matched cell to its equal-mass quantile cell. -/
def ccmActualHeadMatchedQuantilePolarDisplacement (n : ℕ) : ℝ :=
  ccmActualHeadQuantilePolarCoordinate n -
    ccmActualHeadMatchedPolarLowerCoordinate n

/-- Completed critical-Mellin error after removal of the incoming Gamma tail. -/
def ccmActualHeadOutgoingNodeError (n : ℕ) : ℝ :=
  criticalMellinCompletedError (Real.log n) -
    2 * (1 - Real.exp (-(Real.log n / 2)))

theorem ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative (N : ℕ) :
    ccmActualHeadQuantilePolarCoordinate N =
      2 + ccmOutgoingPrimeCumulative N := by
  unfold ccmActualHeadQuantilePolarCoordinate
  rw [exp_half_ccmOutgoingPrimeQuantileBoundary]
  ring

/-- Every quantile cell has coordinate length exactly equal to its critical Mellin atom. -/
theorem ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight (n : ℕ) :
    ccmActualHeadQuantilePolarCoordinate (n + 1) -
        ccmActualHeadQuantilePolarCoordinate n =
      criticalMellinAtomWeight n := by
  rw [ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative,
    ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative,
    ccmOutgoingPrimeCumulative_succ]
  ring

/-- Every symmetric matched cell has the same coordinate length as its quantile cell. -/
theorem ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight (n : ℕ) :
    ccmActualHeadMatchedPolarUpperCoordinate n -
        ccmActualHeadMatchedPolarLowerCoordinate n =
      criticalMellinAtomWeight n := by
  have hmass := integral_exp_half_matchedPrimePolarCell_eq_atomWeight n
  rw [intervalIntegral_exp_half_eq] at hmass
  simpa only [ccmActualHeadMatchedPolarUpperCoordinate,
    ccmActualHeadMatchedPolarLowerCoordinate] using hmass

/-- Equal coordinate lengths force lower- and upper-endpoint displacement to agree exactly. -/
theorem ccmActualHeadMatchedQuantilePolarDisplacement_eq_upper (n : ℕ) :
    ccmActualHeadMatchedQuantilePolarDisplacement n =
      ccmActualHeadQuantilePolarCoordinate (n + 1) -
        ccmActualHeadMatchedPolarUpperCoordinate n := by
  unfold ccmActualHeadMatchedQuantilePolarDisplacement
  have hq := ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight n
  have hm := ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight n
  linarith

/-- Matched endpoints retain the arithmetic center as their geometric mean. -/
theorem ccmActualHeadMatchedPolarLower_mul_upper (n : ℕ) (hn : 0 < n) :
    ccmActualHeadMatchedPolarLowerCoordinate n *
        ccmActualHeadMatchedPolarUpperCoordinate n =
      4 * n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold ccmActualHeadMatchedPolarLowerCoordinate
    ccmActualHeadMatchedPolarUpperCoordinate
  calc
    2 * Real.exp ((Real.log n - ccmActualHeadMatchedPrimePolarRadius n) / 2) *
          (2 * Real.exp
            ((Real.log n + ccmActualHeadMatchedPrimePolarRadius n) / 2)) =
        4 * (Real.exp
            ((Real.log n - ccmActualHeadMatchedPrimePolarRadius n) / 2) *
          Real.exp
            ((Real.log n + ccmActualHeadMatchedPrimePolarRadius n) / 2)) := by ring
    _ = 4 * Real.exp
        ((Real.log n - ccmActualHeadMatchedPrimePolarRadius n) / 2 +
          (Real.log n + ccmActualHeadMatchedPrimePolarRadius n) / 2) := by
      rw [Real.exp_add]
    _ = 4 * Real.exp (Real.log n) := by
      congr 2
      ring
    _ = 4 * n := by rw [Real.exp_log hnpos]

/-- The arithmetic center lies between the two matched endpoints. -/
theorem ccmActualHeadMatchedPolarCenter_mem (n : ℕ) :
    ccmActualHeadMatchedPolarLowerCoordinate n ≤
        2 * Real.exp (Real.log n / 2) ∧
      2 * Real.exp (Real.log n / 2) ≤
        ccmActualHeadMatchedPolarUpperCoordinate n := by
  have hρ := ccmActualHeadMatchedPrimePolarRadius_nonneg n
  constructor
  · unfold ccmActualHeadMatchedPolarLowerCoordinate
    gcongr
    linarith
  · unfold ccmActualHeadMatchedPolarUpperCoordinate
    gcongr
    linarith

/-- The local matched upper half-cell excess is between zero and one full atom weight. -/
theorem ccmActualHeadMatchedPolarUpperExcess_mem_atomWeight (n : ℕ) :
    0 ≤ ccmActualHeadMatchedPolarUpperCoordinate n -
        2 * Real.exp (Real.log n / 2) ∧
      ccmActualHeadMatchedPolarUpperCoordinate n -
          2 * Real.exp (Real.log n / 2) ≤
        criticalMellinAtomWeight n := by
  have hcenter := ccmActualHeadMatchedPolarCenter_mem n
  have hwidth := ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight n
  constructor <;> linarith

/-- Exact cumulative-error displacement of the upper quantile boundary from the arithmetic
center. -/
theorem two_exp_log_half_sub_quantile_succ_eq_outgoingNodeError
    (n : ℕ) (hn : 0 < n) :
    2 * Real.exp (Real.log n / 2) -
        ccmActualHeadQuantilePolarCoordinate (n + 1) =
      ccmActualHeadOutgoingNodeError n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hexp : Real.exp (Real.log n) = (n : ℝ) := Real.exp_log hnpos
  have hterminal :=
    quantileTerminalMass_eq_completedError_sub_threshold (Real.log n)
  simp only [hexp, Nat.floor_natCast] at hterminal
  rw [ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative]
  unfold ccmActualHeadOutgoingNodeError
  exact hterminal

/-- **Rigid matched-to-quantile transport law.** In exponential polar mass coordinate, the cell
translation is the negative outgoing completed error minus the local matched upper excess. -/
theorem ccmActualHeadMatchedQuantilePolarDisplacement_eq_neg_error_sub_upperExcess
    (n : ℕ) (hn : 0 < n) :
    ccmActualHeadMatchedQuantilePolarDisplacement n =
      -ccmActualHeadOutgoingNodeError n -
        (ccmActualHeadMatchedPolarUpperCoordinate n -
          2 * Real.exp (Real.log n / 2)) := by
  have hrigid := ccmActualHeadMatchedQuantilePolarDisplacement_eq_upper n
  have herror :=
    two_exp_log_half_sub_quantile_succ_eq_outgoingNodeError n hn
  linarith

/-- **One-atom completed-error corridor.** Rigid cell displacement differs from negative outgoing
completed error by a quantity between zero and exactly one critical Mellin atom. -/
theorem ccmActualHeadMatchedQuantilePolarDisplacement_mem_errorCorridor
    (n : ℕ) (hn : 0 < n) :
    -ccmActualHeadOutgoingNodeError n - criticalMellinAtomWeight n ≤
        ccmActualHeadMatchedQuantilePolarDisplacement n ∧
      ccmActualHeadMatchedQuantilePolarDisplacement n ≤
        -ccmActualHeadOutgoingNodeError n := by
  have hid :=
    ccmActualHeadMatchedQuantilePolarDisplacement_eq_neg_error_sub_upperExcess n hn
  have hexcess := ccmActualHeadMatchedPolarUpperExcess_mem_atomWeight n
  constructor <;> linarith

/-- Nonnegative outgoing error shifts the entire quantile cell weakly left of the matched cell. -/
theorem ccmActualHeadQuantilePolarCell_le_matchedPolarCell_of_outgoingNodeError_nonneg
    (n : ℕ) (hn : 0 < n) (herror : 0 ≤ ccmActualHeadOutgoingNodeError n) :
    ccmActualHeadQuantilePolarCoordinate n ≤
        ccmActualHeadMatchedPolarLowerCoordinate n ∧
      ccmActualHeadQuantilePolarCoordinate (n + 1) ≤
        ccmActualHeadMatchedPolarUpperCoordinate n := by
  have hcorridor :=
    ccmActualHeadMatchedQuantilePolarDisplacement_mem_errorCorridor n hn
  have hδ : ccmActualHeadMatchedQuantilePolarDisplacement n ≤ 0 := by linarith
  rw [ccmActualHeadMatchedQuantilePolarDisplacement_eq_upper] at hδ
  constructor
  · unfold ccmActualHeadMatchedQuantilePolarDisplacement at hcorridor
    linarith
  · linarith

/-- Error at most minus one atom shifts the entire matched cell weakly left of the quantile cell. -/
theorem ccmActualHeadMatchedPolarCell_le_quantilePolarCell_of_outgoingNodeError_le_neg_weight
    (n : ℕ) (hn : 0 < n)
    (herror : ccmActualHeadOutgoingNodeError n ≤ -criticalMellinAtomWeight n) :
    ccmActualHeadMatchedPolarLowerCoordinate n ≤
        ccmActualHeadQuantilePolarCoordinate n ∧
      ccmActualHeadMatchedPolarUpperCoordinate n ≤
        ccmActualHeadQuantilePolarCoordinate (n + 1) := by
  have hcorridor :=
    ccmActualHeadMatchedQuantilePolarDisplacement_mem_errorCorridor n hn
  have hδ : 0 ≤ ccmActualHeadMatchedQuantilePolarDisplacement n := by linarith
  have hδupper := hδ
  rw [ccmActualHeadMatchedQuantilePolarDisplacement_eq_upper] at hδupper
  constructor
  · unfold ccmActualHeadMatchedQuantilePolarDisplacement at hδ
    linarith
  · linarith

end RHTower
