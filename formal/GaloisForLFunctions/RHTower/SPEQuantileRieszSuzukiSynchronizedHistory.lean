import GaloisForLFunctions.RHTower.SPEQuantileRieszPrimePowerHistoryTransport
import GaloisForLFunctions.RHTower.SPEQuantileRieszSuzukiPrimePowerAlphabetBridge
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCofinalPrunedHistory

/-!
# Synchronized SP-E/Suzuki prime-power history

The cofinal Suzuki seam witness uses the labelled pair
`(2, n + 1), -(3, n + 1)`.  This file aligns that exact pair with the
physical SP-E admission clock: `2^(n+1)` is already retained history when
`3^(n+1)` enters.  The two labels therefore carry both a noncommutative
seam chronology and a literal current/history placement in the full SP-E
debt ledger.

This is a source synchronization result only.  It neither identifies the
resulting ordered debt channel with the signed exterior channel nor supplies
the required indefinite transport into P-G105F.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.RHTower

/-- The SP-E stage at which the Suzuki `(3, n + 1)` atom is admitted. -/
def speQuantileRieszSuzukiSynchronizedCurrentStage (n : ℕ) : ℕ :=
  3 ^ (n + 1) - 3

/-- The already-retained SP-E history index of the Suzuki `(2, n + 1)` atom. -/
def speQuantileRieszSuzukiSynchronizedHistoryIndex (n : ℕ) : ℕ :=
  2 ^ (n + 1) - 2

/-- The current stage's literal source endpoint is the labelled prime power `3^(n+1)`. -/
theorem speQuantileRieszSuzukiSynchronizedCurrentStage_add_three (n : ℕ) :
    speQuantileRieszSuzukiSynchronizedCurrentStage n + 3 = 3 ^ (n + 1) := by
  unfold speQuantileRieszSuzukiSynchronizedCurrentStage
  apply Nat.sub_add_cancel
  calc
    3 = 3 ^ (1 : ℕ) := by norm_num
    _ ≤ 3 ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)

/-- The selected history index is exactly the labelled prime power `2^(n+1)`. -/
theorem speQuantileRieszSuzukiSynchronizedHistoryIndex_add_two (n : ℕ) :
    speQuantileRieszSuzukiSynchronizedHistoryIndex n + 2 = 2 ^ (n + 1) := by
  unfold speQuantileRieszSuzukiSynchronizedHistoryIndex
  apply Nat.sub_add_cancel
  calc
    2 = 2 ^ (1 : ℕ) := by norm_num
    _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)

/-- At the literal `3^(n+1)` admission, the literal `2^(n+1)` atom belongs to retained SP-E
history.  This is the physical-time half of the synchronized two-letter source witness. -/
theorem speQuantileRieszSuzukiSynchronizedHistoryIndex_mem_currentRange (n : ℕ) :
    speQuantileRieszSuzukiSynchronizedHistoryIndex n ∈
      Finset.range (speQuantileRieszSuzukiSynchronizedCurrentStage n + 1) := by
  rw [Finset.mem_range]
  have hpow : 2 ^ (n + 1) < 3 ^ (n + 1) :=
    Nat.pow_lt_pow_left (by omega) (by omega)
  unfold speQuantileRieszSuzukiSynchronizedHistoryIndex
    speQuantileRieszSuzukiSynchronizedCurrentStage
  omega

/-- The cofinal Suzuki forward leg is precisely the already-retained `(2,n+1)` SP-E label. -/
theorem suzukiCofinalPrunedHistoryDelta_eq_synchronizedHistoryLabel (n : ℕ) :
    suzukiCofinalPrunedHistoryDelta n =
      suzukiPrimePowerStep (⟨2, Nat.prime_two⟩, n + 1) := by
  rfl

/-- The cofinal Suzuki reflected leg is precisely the newly-admitted `(3,n+1)` SP-E label. -/
theorem suzukiCofinalPrunedHistoryEta_eq_synchronizedCurrentLabel (n : ℕ) :
    suzukiCofinalPrunedHistoryEta n =
      -suzukiPrimePowerStep (⟨3, Nat.prime_three⟩, n + 1) := by
  rfl

/-- The current SP-E atom at the synchronized stage has exactly Suzuki's labelled alphabet
weight.  No label is merged or scalarized. -/
theorem criticalMellinAtomWeight_speQuantileRieszSuzukiSynchronizedCurrent_eq (n : ℕ) :
    criticalMellinAtomWeight (speQuantileRieszSuzukiSynchronizedCurrentStage n + 3) =
      suzukiPrimePowerWeight (⟨3, Nat.prime_three⟩, n + 1) := by
  rw [speQuantileRieszSuzukiSynchronizedCurrentStage_add_three]
  exact criticalMellinAtomWeight_prime_pow_eq_suzukiPrimePowerWeight
    ⟨3, Nat.prime_three⟩ (n + 1) (by omega)

/-- The exact two ordered debt interactions of the synchronized labels split from the complete
SP-E debt admission.  The remainder is retained explicitly; this is not a two-label truncation
of the strict-cross ledger. -/
theorem speQuantileRieszSynchronizedDebtAdmission_erase_add (n : ℕ) :
    (∑ m ∈ (Finset.range (speQuantileRieszSuzukiSynchronizedCurrentStage n + 1)).erase
        (speQuantileRieszSuzukiSynchronizedHistoryIndex n),
        (ccmActualHeadMatchedQuantileParabolicDisplacementDebt
            (m + 2) (speQuantileRieszSuzukiSynchronizedCurrentStage n + 3) +
          ccmActualHeadMatchedQuantileParabolicDisplacementDebt
            (speQuantileRieszSuzukiSynchronizedCurrentStage n + 3) (m + 2))) +
      (ccmActualHeadMatchedQuantileParabolicDisplacementDebt
          (2 ^ (n + 1)) (3 ^ (n + 1)) +
        ccmActualHeadMatchedQuantileParabolicDisplacementDebt
          (3 ^ (n + 1)) (2 ^ (n + 1))) =
      ∑ m ∈ Finset.range (speQuantileRieszSuzukiSynchronizedCurrentStage n + 1),
        (ccmActualHeadMatchedQuantileParabolicDisplacementDebt
            (m + 2) (speQuantileRieszSuzukiSynchronizedCurrentStage n + 3) +
          ccmActualHeadMatchedQuantileParabolicDisplacementDebt
            (speQuantileRieszSuzukiSynchronizedCurrentStage n + 3) (m + 2)) := by
  let K := speQuantileRieszSuzukiSynchronizedCurrentStage n
  let h := speQuantileRieszSuzukiSynchronizedHistoryIndex n
  let debt : ℕ → ℝ := fun m =>
    ccmActualHeadMatchedQuantileParabolicDisplacementDebt (m + 2) (K + 3) +
      ccmActualHeadMatchedQuantileParabolicDisplacementDebt (K + 3) (m + 2)
  have hmem : h ∈ Finset.range (K + 1) := by
    exact speQuantileRieszSuzukiSynchronizedHistoryIndex_mem_currentRange n
  change (∑ m ∈ (Finset.range (K + 1)).erase h, debt m) +
      (ccmActualHeadMatchedQuantileParabolicDisplacementDebt
          (2 ^ (n + 1)) (3 ^ (n + 1)) +
        ccmActualHeadMatchedQuantileParabolicDisplacementDebt
          (3 ^ (n + 1)) (2 ^ (n + 1))) =
    ∑ m ∈ Finset.range (K + 1), debt m
  rw [← speQuantileRieszSuzukiSynchronizedHistoryIndex_add_two,
    ← speQuantileRieszSuzukiSynchronizedCurrentStage_add_three]
  exact Finset.sum_erase_add _ _ hmem

/-- Above every aperture threshold there is a single exponent whose two Suzuki chronology labels
are simultaneously a literal SP-E history/current pair.  The forward/reversed readouts remain
`1` and `0`, while the physical-time membership is retained. -/
theorem exists_speQuantileRieszSuzukiSynchronizedCofinalHistory (A : ℝ) :
    ∃ n : ℕ, A < suzukiCofinalPrunedHistoryAperture n ∧
      speQuantileRieszSuzukiSynchronizedHistoryIndex n ∈
        Finset.range (speQuantileRieszSuzukiSynchronizedCurrentStage n + 1) ∧
      suzukiOrientedSupportPrunedHistoryAction (suzukiCofinalPrunedHistoryAperture n)
          [suzukiCofinalPrunedHistoryDelta n, suzukiCofinalPrunedHistoryEta n]
          (suzukiCofinalPrunedHistorySeed n) (suzukiCofinalPrunedHistoryReadout n) = 1 ∧
      suzukiOrientedSupportPrunedHistoryAction (suzukiCofinalPrunedHistoryAperture n)
          [suzukiCofinalPrunedHistoryEta n, suzukiCofinalPrunedHistoryDelta n]
          (suzukiCofinalPrunedHistorySeed n) (suzukiCofinalPrunedHistoryReadout n) = 0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * A / Real.log 10)
  refine ⟨n, ?_, speQuantileRieszSuzukiSynchronizedHistoryIndex_mem_currentRange n,
    suzukiCofinalPrunedHistory_ordered_value_asymmetry_at n⟩
  have hlog : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hmul := (div_lt_iff₀ hlog).mp hn
  have hnle : (n : ℝ) * Real.log 10 ≤ ((n + 1 : ℕ) : ℝ) * Real.log 10 := by
    gcongr
    omega
  change A < ((n + 1 : ℕ) : ℝ) * Real.log 10 / 2
  linarith

end

end RHTower
