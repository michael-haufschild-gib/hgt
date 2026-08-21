import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarCoordinateTransport
import GaloisForLFunctions.RHTower.CCMCompletedErrorVariationEnergyGate

/-!
# Dyadic relative displacement of matched prime cells

The sharp dyadic completed-error variation is not an independent analytic quantity.  At an
integer `n >= 2`, compare the signed matched-to-quantile displacement at `n` with that at the
coarsened index `floor (n / 2)`.  The difference recovers the signed dyadic prime-window error,
up to the two local upper-cell excesses and one explicit, nonnegative floor reserve.

Consequently the positive dyadic prime-window excess is bounded by the positive part of this
oriented relative displacement, one atom weight, and that exact reserve.  This is a source
reduction only: it proves neither a sign nor a summability bound for the relative displacement.
-/

open scoped BigOperators
open Finset ArithmeticFunction

noncomputable section

namespace RHTower

/-- Exact polar-coordinate reserve caused by replacing the real half-index by `floor (n / 2)`. -/
def dyadicRoundingReserve (n : ℕ) : ℝ :=
  2 * (Real.exp ((Real.log n - Real.log 2) / 2) -
    Real.exp (Real.log ((n / 2 : ℕ) : ℝ) / 2))

/-- Oriented displacement of a matched prime cell under one dyadic coarsening step. -/
def dyadicRelativeDisplacement (n : ℕ) : ℝ :=
  ccmActualHeadMatchedQuantilePolarDisplacement n -
    ccmActualHeadMatchedQuantilePolarDisplacement (n / 2)

/-- Local excess of the upper matched polar half-cell over its continuous endpoint. -/
def matchedUpperExcess (n : ℕ) : ℝ :=
  ccmActualHeadMatchedPolarUpperCoordinate n -
    2 * Real.exp (Real.log n / 2)

/-- At the dyadic logarithmic shift, the prime-mass floor is exactly the coarsened integer. -/
theorem criticalMellinPrimeMass_log_sub_logTwo_eq_divTwo
    {n : ℕ} (hn : 2 ≤ n) :
    criticalMellinPrimeMass (Real.log n - Real.log 2) =
      criticalMellinPrimeMass (Real.log ((n / 2 : ℕ) : ℝ)) := by
  have hnpos : 0 < n := by omega
  have hmpos : 0 < n / 2 := by omega
  have hnposR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hmposR : (0 : ℝ) < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hmpos
  have hleftReal : Real.exp (Real.log n - Real.log 2) = (n : ℝ) / 2 := by
    rw [Real.exp_sub, Real.exp_log hnposR,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hleft : ⌊Real.exp (Real.log n - Real.log 2)⌋₊ = n / 2 := by
    rw [hleftReal]
    simpa using (Nat.floor_div_eq_div (K := ℝ) n 2)
  have hright : ⌊Real.exp (Real.log ((n / 2 : ℕ) : ℝ))⌋₊ = n / 2 := by
    rw [Real.exp_log hmposR, Nat.floor_natCast]
  unfold criticalMellinPrimeMass
  rw [hleft, hright]

/-- The completed-error dyadic variation is the difference of outgoing node errors, with the
exact floor reserve and no asymptotic remainder. -/
theorem completedError_dyadic_eq_nodeError_sub_add_rounding
    {n : ℕ} (hn : 2 ≤ n) :
    criticalMellinCompletedError (Real.log n - Real.log 2) -
        criticalMellinCompletedError (Real.log n) +
        2 * (Real.sqrt 2 - 1) / Real.sqrt n =
      ccmActualHeadOutgoingNodeError (n / 2) -
        ccmActualHeadOutgoingNodeError n + dyadicRoundingReserve n := by
  have hnpos : 0 < n := by omega
  have hmpos : 0 < n / 2 := by omega
  have hprime := criticalMellinPrimeMass_log_sub_logTwo_eq_divTwo hn
  simp only [ccmActualHeadOutgoingNodeError,
    criticalMellinCompletedError_eq_polar_sub_primeMass]
  rw [hprime]
  have hlog2 : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.exp_log (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
  have hlogn : Real.exp (Real.log n / 2) = Real.sqrt n := by
    rw [← Real.log_sqrt (by exact_mod_cast hnpos.le),
      Real.exp_log (Real.sqrt_pos.mpr (by exact_mod_cast hnpos))]
  have hlogm : Real.exp (Real.log ((n / 2 : ℕ) : ℝ) / 2) =
      Real.sqrt ((n / 2 : ℕ) : ℝ) := by
    rw [← Real.log_sqrt (by exact_mod_cast hmpos.le),
      Real.exp_log (Real.sqrt_pos.mpr (by exact_mod_cast hmpos))]
  have hneglogn : Real.exp (-(Real.log n / 2)) = (Real.sqrt n)⁻¹ := by
    rw [Real.exp_neg, hlogn]
  have hneglogm : Real.exp (-(Real.log ((n / 2 : ℕ) : ℝ) / 2)) =
      (Real.sqrt ((n / 2 : ℕ) : ℝ))⁻¹ := by
    rw [Real.exp_neg, hlogm]
  have hshift : Real.exp (-((Real.log n - Real.log 2) / 2)) =
      Real.sqrt 2 * (Real.sqrt n)⁻¹ := by
    rw [show -((Real.log n - Real.log 2) / 2) =
        Real.log 2 / 2 + -(Real.log n / 2) by ring,
      Real.exp_add, hlog2, hneglogn]
  simp_rw [Real.sinh_eq]
  rw [hshift, hneglogn, hneglogm]
  dsimp only [dyadicRoundingReserve]
  change _ = _ + 2 *
    (Real.exp ((Real.log n - Real.log 2) / 2) -
      Real.exp (Real.log ((n / 2 : ℕ) : ℝ) / 2))
  ring

/-- **Dyadic transport identity.** The signed completed-error variation is precisely the
oriented dyadic displacement, corrected by adjacent local upper-cell excesses and the floor
reserve. -/
theorem completedError_dyadic_eq_relativeDisplacement_add_upperExcess_sub_add_rounding
    {n : ℕ} (hn : 2 ≤ n) :
    criticalMellinCompletedError (Real.log n - Real.log 2) -
        criticalMellinCompletedError (Real.log n) +
        2 * (Real.sqrt 2 - 1) / Real.sqrt n =
      dyadicRelativeDisplacement n + matchedUpperExcess n -
        matchedUpperExcess (n / 2) + dyadicRoundingReserve n := by
  have hnpos : 0 < n := by omega
  have hmpos : 0 < n / 2 := by omega
  have hnode := completedError_dyadic_eq_nodeError_sub_add_rounding hn
  have hdispN :=
    ccmActualHeadMatchedQuantilePolarDisplacement_eq_neg_error_sub_upperExcess n hnpos
  have hdispM :=
    ccmActualHeadMatchedQuantilePolarDisplacement_eq_neg_error_sub_upperExcess (n / 2) hmpos
  unfold dyadicRelativeDisplacement matchedUpperExcess
  linarith

/-- The dyadic floor reserve is always nonnegative. -/
theorem dyadicRoundingReserve_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ dyadicRoundingReserve n := by
  have hnpos : 0 < n := by omega
  have hmpos : 0 < n / 2 := by omega
  have hdiv : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := Nat.cast_div_le
  have hlog : Real.log ((n / 2 : ℕ) : ℝ) ≤ Real.log ((n : ℝ) / 2) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by exact_mod_cast hmpos))
      (Set.mem_Ioi.mpr (by positivity)) hdiv
  have hexp : Real.exp (Real.log ((n / 2 : ℕ) : ℝ) / 2) ≤
      Real.exp ((Real.log n - Real.log 2) / 2) := by
    apply Real.exp_le_exp.mpr
    rw [← Real.log_div (by exact_mod_cast hnpos.ne') (by norm_num : (2 : ℝ) ≠ 0)]
    linarith
  unfold dyadicRoundingReserve
  linarith

/-- **Dyadic signed-displacement reduction.** Positive prime-window excess is controlled by the
positive oriented coarsening displacement, a single local atom, and the exact floor reserve. -/
theorem dyadicWeightedPrimeWindowPositiveExcess_le_relativeDisplacement
    {n : ℕ} (hn : 2 ≤ n) :
    dyadicWeightedPrimeWindowPositiveExcess n ≤
      (dyadicRelativeDisplacement n)⁺ + criticalMellinAtomWeight n +
        dyadicRoundingReserve n := by
  have hident :=
    completedError_dyadic_eq_relativeDisplacement_add_upperExcess_sub_add_rounding hn
  have hupperN := ccmActualHeadMatchedPolarUpperExcess_mem_atomWeight n
  have hupperM := ccmActualHeadMatchedPolarUpperExcess_mem_atomWeight (n / 2)
  have hreserve := dyadicRoundingReserve_nonneg hn
  have hweight : 0 ≤ criticalMellinAtomWeight n := hupperN.1.trans hupperN.2
  have hbase :
      criticalMellinCompletedError (Real.log n - Real.log 2) -
          criticalMellinCompletedError (Real.log n) +
          2 * (Real.sqrt 2 - 1) / Real.sqrt n ≤
        dyadicRelativeDisplacement n + criticalMellinAtomWeight n +
          dyadicRoundingReserve n := by
    rw [hident]
    simp only [matchedUpperExcess]
    linarith [hupperN.1, hupperN.2, hupperM.1]
  rw [dyadicWeightedPrimeWindowPositiveExcess_eq_posPart_completedErrorBackwardDifference hn]
  change max
      (criticalMellinCompletedError (Real.log n - Real.log 2) -
          criticalMellinCompletedError (Real.log n) +
          2 * (Real.sqrt 2 - 1) / Real.sqrt n) 0 ≤
    (dyadicRelativeDisplacement n)⁺ + criticalMellinAtomWeight n +
      dyadicRoundingReserve n
  apply max_le
  · calc
      criticalMellinCompletedError (Real.log n - Real.log 2) -
          criticalMellinCompletedError (Real.log n) +
          2 * (Real.sqrt 2 - 1) / Real.sqrt n ≤
        dyadicRelativeDisplacement n + criticalMellinAtomWeight n +
          dyadicRoundingReserve n := hbase
      _ ≤ (dyadicRelativeDisplacement n)⁺ + criticalMellinAtomWeight n +
          dyadicRoundingReserve n := by
        linarith [le_posPart (dyadicRelativeDisplacement n)]
  · linarith [posPart_nonneg (dyadicRelativeDisplacement n)]

end RHTower
