import GaloisForLFunctions.RHTower.Sieve.HarmonicReservoirCapacity

/-!
# Fixed-token reservoir conservation

This module formalizes the exact finite core of the Route E fixed-token central-corner
reservoir conservation law.  A coordinate shift is decomposed into its positive and negative
parts.  Their maximum is exactly the largest absolute subset excursion, while their sum is exact
total variation.  Applied to source breadth, reservoir breadth, and fixed token breadth, this
gives the sharp reservoir conservation inequality and the parity-rigid reservoir-free
obstruction.
-/

namespace RHTower

open Finset

section Excursion

variable {ι : Type*} [Fintype ι]

/-- Total positive mass of a finite integer shift family. -/
def positiveShiftMass (δ : ι → ℤ) : ℤ :=
  ∑ i, max (δ i) 0

/-- Total negative mass of a finite integer shift family, recorded positively. -/
def negativeShiftMass (δ : ι → ℤ) : ℤ :=
  ∑ i, max (-δ i) 0

/-- Sharp absolute subset excursion of a finite integer shift family. -/
def subsetShiftExcursion (δ : ι → ℤ) : ℤ :=
  max (positiveShiftMass δ) (negativeShiftMass δ)

/-- Total variation of a finite integer shift family. -/
def shiftTotalVariation (δ : ι → ℤ) : ℤ :=
  ∑ i, |δ i|

private theorem self_eq_posPart_sub_negPart (z : ℤ) :
    z = max z 0 - max (-z) 0 := by
  rcases le_total 0 z with hz | hz
  · rw [max_eq_left hz, max_eq_right (neg_nonpos.mpr hz)]
    simp
  · rw [max_eq_right hz, max_eq_left (neg_nonneg.mpr hz)]
    simp

private theorem abs_eq_posPart_add_negPart (z : ℤ) :
    |z| = max z 0 + max (-z) 0 := by
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz, max_eq_left hz, max_eq_right (neg_nonpos.mpr hz)]
    simp
  · rw [abs_of_nonpos hz, max_eq_right hz, max_eq_left (neg_nonneg.mpr hz)]
    simp

/-- Every subset sum lies between minus the negative shift mass and the positive shift mass. -/
theorem subsetShiftSum_mem_interval (δ : ι → ℤ) (S : Finset ι) :
    -negativeShiftMass δ ≤ ∑ i ∈ S, δ i ∧
      ∑ i ∈ S, δ i ≤ positiveShiftMass δ := by
  constructor
  · have hpoint : ∀ i ∈ S, -max (-δ i) 0 ≤ δ i := by
      intro i hi
      omega
    have hneg :
        ∑ i ∈ S, -δ i ≤ negativeShiftMass δ := by
      calc
        ∑ i ∈ S, -δ i ≤ ∑ i ∈ S, max (-δ i) 0 :=
          Finset.sum_le_sum fun i hi => le_max_left _ _
        _ ≤ ∑ i, max (-δ i) 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg (by simp)
            (fun i hiS hi => le_max_right _ _)
        _ = negativeShiftMass δ := rfl
    rw [Finset.sum_neg_distrib] at hneg
    linarith
  · calc
      ∑ i ∈ S, δ i ≤ ∑ i ∈ S, max (δ i) 0 :=
        Finset.sum_le_sum fun i hi => le_max_left _ _
      _ ≤ ∑ i, max (δ i) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (by simp)
          (fun i hiS hi => le_max_right _ _)
      _ = positiveShiftMass δ := rfl

/-- Every absolute subset sum is bounded by the sharp excursion. -/
theorem abs_subsetShiftSum_le_excursion (δ : ι → ℤ) (S : Finset ι) :
    |∑ i ∈ S, δ i| ≤ subsetShiftExcursion δ := by
  obtain ⟨hlower, hupper⟩ := subsetShiftSum_mem_interval δ S
  rw [abs_le]
  exact ⟨(neg_le_neg (le_max_right _ _)).trans hlower,
    hupper.trans (le_max_left _ _)⟩

/-- Positive coordinates realize the full positive shift mass. -/
theorem sum_positiveShiftIndices (δ : ι → ℤ) :
    ∑ i ∈ (Finset.univ.filter fun i => 0 < δ i), δ i = positiveShiftMass δ := by
  rw [positiveShiftMass, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs with h
  · exact (max_eq_left h.le).symm
  · exact (max_eq_right (le_of_not_gt h)).symm

/-- Negative coordinates realize minus the full negative shift mass. -/
theorem sum_negativeShiftIndices (δ : ι → ℤ) :
    ∑ i ∈ (Finset.univ.filter fun i => δ i < 0), δ i = -negativeShiftMass δ := by
  rw [negativeShiftMass, Finset.sum_filter]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs with h
  · rw [max_eq_left (neg_nonneg.mpr h.le)]
    simp
  · rw [max_eq_right (neg_nonpos.mpr (le_of_not_gt h))]
    simp

/-- The excursion is attained by either all positive or all negative coordinates. -/
theorem exists_subset_abs_sum_eq_excursion (δ : ι → ℤ) :
    ∃ S : Finset ι, |∑ i ∈ S, δ i| = subsetShiftExcursion δ := by
  rcases le_total (positiveShiftMass δ) (negativeShiftMass δ) with h | h
  · refine ⟨Finset.univ.filter fun i => δ i < 0, ?_⟩
    rw [sum_negativeShiftIndices, abs_neg, abs_of_nonneg]
    · exact (max_eq_right h).symm
    · exact Finset.sum_nonneg fun i hi => le_max_right _ _
  · refine ⟨Finset.univ.filter fun i => 0 < δ i, ?_⟩
    rw [sum_positiveShiftIndices, abs_of_nonneg]
    · exact (max_eq_left h).symm
    · exact Finset.sum_nonneg fun i hi => le_max_right _ _

/-- Exact Jordan decomposition of the total signed shift. -/
theorem sum_shift_eq_positive_sub_negative (δ : ι → ℤ) :
    ∑ i, δ i = positiveShiftMass δ - negativeShiftMass δ := by
  calc
    ∑ i, δ i = ∑ i, (max (δ i) 0 - max (-δ i) 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact self_eq_posPart_sub_negPart (δ i)
    _ = positiveShiftMass δ - negativeShiftMass δ := by
      rw [Finset.sum_sub_distrib]
      rfl

/-- Exact total-variation decomposition. -/
theorem shiftTotalVariation_eq_positive_add_negative (δ : ι → ℤ) :
    shiftTotalVariation δ = positiveShiftMass δ + negativeShiftMass δ := by
  simp_rw [shiftTotalVariation, abs_eq_posPart_add_negPart, Finset.sum_add_distrib]
  rfl

/-- Total variation is at most twice the sharp subset excursion. -/
theorem shiftTotalVariation_le_two_mul_excursion (δ : ι → ℤ) :
    shiftTotalVariation δ ≤ 2 * subsetShiftExcursion δ := by
  rw [shiftTotalVariation_eq_positive_add_negative]
  unfold subsetShiftExcursion
  omega

/-- If every coordinate shift is odd, arity is bounded by total variation. -/
theorem card_le_shiftTotalVariation_of_odd (δ : ι → ℤ)
    (hodd : ∀ i, Odd (δ i)) :
    (Fintype.card ι : ℤ) ≤ shiftTotalVariation δ := by
  rw [shiftTotalVariation]
  calc
    (Fintype.card ι : ℤ) = ∑ i : ι, (1 : ℤ) := by simp
    _ ≤ ∑ i : ι, |δ i| := by
      apply Finset.sum_le_sum
      intro i hi
      have hne : δ i ≠ 0 := by
        intro hz
        simpa [hz] using hodd i
      have habs : 0 < |δ i| := abs_pos.mpr hne
      omega

/-- Parity reversal forces arity to be at most twice the sharp subset excursion. -/
theorem card_le_two_mul_excursion_of_odd (δ : ι → ℤ)
    (hodd : ∀ i, Odd (δ i)) :
    (Fintype.card ι : ℤ) ≤ 2 * subsetShiftExcursion δ :=
  le_trans (card_le_shiftTotalVariation_of_odd δ hodd)
    (shiftTotalVariation_le_two_mul_excursion δ)

end Excursion

section FixedToken

variable {ι : Type*} [Fintype ι]

/-- Exact Wold-grade shift of one fixed-token replacement coordinate. -/
def fixedTokenShift (sourceBreadth reservoirBreadth : ι → ℕ) (tokenBreadth : ℕ)
    (i : ι) : ℤ :=
  (reservoirBreadth i : ℤ) + tokenBreadth - sourceBreadth i

/-- Total source breadth, read in the integer grade group. -/
def fixedTokenSourceTotal (sourceBreadth : ι → ℕ) : ℤ :=
  ∑ i, (sourceBreadth i : ℤ)

/-- Total reservoir breadth, read in the integer grade group. -/
def fixedTokenReservoirTotal (reservoirBreadth : ι → ℕ) : ℤ :=
  ∑ i, (reservoirBreadth i : ℤ)

/-- Exact sum of all coordinate shifts. -/
theorem sum_fixedTokenShift
    (sourceBreadth reservoirBreadth : ι → ℕ) (tokenBreadth : ℕ) :
    ∑ i, fixedTokenShift sourceBreadth reservoirBreadth tokenBreadth i =
      fixedTokenReservoirTotal reservoirBreadth +
        (tokenBreadth : ℤ) * Fintype.card ι -
        fixedTokenSourceTotal sourceBreadth := by
  simp [fixedTokenShift, fixedTokenSourceTotal, fixedTokenReservoirTotal,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- **Fixed-token central-corner reservoir conservation law.**

The total reservoir breadth differs from source breadth minus fixed token breadth times arity by
at most the sharp excursion among all cube corners. -/
theorem fixedToken_reservoir_conservation
    (sourceBreadth reservoirBreadth : ι → ℕ) (tokenBreadth : ℕ) :
    |fixedTokenReservoirTotal reservoirBreadth -
        (fixedTokenSourceTotal sourceBreadth -
          (tokenBreadth : ℤ) * Fintype.card ι)| ≤
      subsetShiftExcursion
        (fixedTokenShift sourceBreadth reservoirBreadth tokenBreadth) := by
  have hfull := abs_subsetShiftSum_le_excursion
    (fixedTokenShift sourceBreadth reservoirBreadth tokenBreadth) Finset.univ
  simpa [sum_fixedTokenShift, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hfull

/-- Exact endpoint identity behind reservoir conservation. -/
theorem fixedToken_reservoir_eq_source_sub_tokens_add_signedShift
    (sourceBreadth reservoirBreadth : ι → ℕ) (tokenBreadth : ℕ) :
    fixedTokenReservoirTotal reservoirBreadth =
      fixedTokenSourceTotal sourceBreadth -
        (tokenBreadth : ℤ) * Fintype.card ι +
        positiveShiftMass
          (fixedTokenShift sourceBreadth reservoirBreadth tokenBreadth) -
        negativeShiftMass
          (fixedTokenShift sourceBreadth reservoirBreadth tokenBreadth) := by
  have hsum := sum_fixedTokenShift sourceBreadth reservoirBreadth tokenBreadth
  rw [sum_shift_eq_positive_sub_negative] at hsum
  linarith

/-- Exact parity-rigid conservation package: every odd coordinate shift contributes at least one
unit of total variation, and total variation is at most twice the largest corner excursion. -/
theorem fixedToken_parity_rigidity
    (sourceBreadth reservoirBreadth : ι → ℕ) (tokenBreadth : ℕ)
    (hodd : ∀ i, Odd (fixedTokenShift sourceBreadth reservoirBreadth tokenBreadth i)) :
    (Fintype.card ι : ℤ) ≤
      shiftTotalVariation
        (fixedTokenShift sourceBreadth reservoirBreadth tokenBreadth) ∧
    shiftTotalVariation
        (fixedTokenShift sourceBreadth reservoirBreadth tokenBreadth) ≤
      2 * subsetShiftExcursion
        (fixedTokenShift sourceBreadth reservoirBreadth tokenBreadth) := by
  exact ⟨card_le_shiftTotalVariation_of_odd _ hodd,
    shiftTotalVariation_le_two_mul_excursion _⟩

/-- Reservoir-free fixed-token dichotomy. -/
theorem reservoirFree_source_le_tokens_add_excursion
    (sourceBreadth : ι → ℕ) (tokenBreadth : ℕ) :
    fixedTokenSourceTotal sourceBreadth ≤
      (tokenBreadth : ℤ) * Fintype.card ι +
        subsetShiftExcursion
          (fixedTokenShift sourceBreadth (fun _ => 0) tokenBreadth) := by
  have h := fixedToken_reservoir_conservation
    sourceBreadth (fun _ => 0) tokenBreadth
  have habs :
      |fixedTokenSourceTotal sourceBreadth -
          (tokenBreadth : ℤ) * Fintype.card ι| ≤
        subsetShiftExcursion
          (fixedTokenShift sourceBreadth (fun _ => 0) tokenBreadth) := by
    simpa [fixedTokenReservoirTotal, abs_sub_comm] using h
  have hself :
      fixedTokenSourceTotal sourceBreadth -
          (tokenBreadth : ℤ) * Fintype.card ι ≤
        |fixedTokenSourceTotal sourceBreadth -
          (tokenBreadth : ℤ) * Fintype.card ι| :=
    le_abs_self _
  linarith

/-- **Sharp reservoir-free parity consequence.** If every fixed-token coordinate reverses
parity, then source breadth is controlled by corner excursion alone.  This eliminates arity
from the final obstruction: `d ≤ 2E` and `K ≤ r d + E` combine to give
`K ≤ (2r+1)E`. -/
theorem reservoirFree_parity_source_le_twoToken_add_one_mul_excursion
    (sourceBreadth : ι → ℕ) (tokenBreadth : ℕ)
    (hodd : ∀ i,
      Odd (fixedTokenShift sourceBreadth (fun _ => 0) tokenBreadth i)) :
    fixedTokenSourceTotal sourceBreadth ≤
      (2 * (tokenBreadth : ℤ) + 1) *
        subsetShiftExcursion
          (fixedTokenShift sourceBreadth (fun _ => 0) tokenBreadth) := by
  let δ := fixedTokenShift sourceBreadth (fun _ => 0) tokenBreadth
  have hsource :
      fixedTokenSourceTotal sourceBreadth ≤
        (tokenBreadth : ℤ) * Fintype.card ι + subsetShiftExcursion δ := by
    simpa [δ] using reservoirFree_source_le_tokens_add_excursion
      sourceBreadth tokenBreadth
  have harity :
      (Fintype.card ι : ℤ) ≤ 2 * subsetShiftExcursion δ := by
    exact card_le_two_mul_excursion_of_odd δ (by simpa [δ] using hodd)
  have hscaled :
      (tokenBreadth : ℤ) * Fintype.card ι ≤
        (tokenBreadth : ℤ) * (2 * subsetShiftExcursion δ) :=
    mul_le_mul_of_nonneg_left harity (by positivity)
  calc
    fixedTokenSourceTotal sourceBreadth ≤
        (tokenBreadth : ℤ) * Fintype.card ι + subsetShiftExcursion δ := hsource
    _ ≤ (tokenBreadth : ℤ) * (2 * subsetShiftExcursion δ) +
        subsetShiftExcursion δ := add_le_add hscaled le_rfl
    _ = (2 * (tokenBreadth : ℤ) + 1) * subsetShiftExcursion δ := by ring_nf

/-- **Finite central-scaling bridge.** If source breadth differs from reference breadth by at
most `error`, token arity costs at most `error`, and every corner excursion costs at most
`error`, then reservoir breadth differs from reference breadth by at most `3 * error`.

This is the exact epsilon-free statement underlying the paper's
`K = (1-o(1))L`, `rd = o(L)`, `E = o(L)` implication `B = (1-o(1))L`. -/
theorem fixedToken_reservoir_centralScaling_bound
    (sourceBreadth reservoirBreadth : ι → ℕ) (tokenBreadth : ℕ)
    (reference error : ℤ)
    (hsource :
      |fixedTokenSourceTotal sourceBreadth - reference| ≤ error)
    (htokens :
      (tokenBreadth : ℤ) * Fintype.card ι ≤ error)
    (hexcursion :
      subsetShiftExcursion
          (fixedTokenShift sourceBreadth reservoirBreadth tokenBreadth) ≤ error) :
    |fixedTokenReservoirTotal reservoirBreadth - reference| ≤ 3 * error := by
  let δ := fixedTokenShift sourceBreadth reservoirBreadth tokenBreadth
  have hconservation :
      |fixedTokenReservoirTotal reservoirBreadth -
          (fixedTokenSourceTotal sourceBreadth -
            (tokenBreadth : ℤ) * Fintype.card ι)| ≤ error :=
    (fixedToken_reservoir_conservation
      sourceBreadth reservoirBreadth tokenBreadth).trans hexcursion
  have htoken_nonneg :
      0 ≤ (tokenBreadth : ℤ) * Fintype.card ι := by positivity
  rw [abs_le] at hconservation hsource ⊢
  constructor <;> omega

end FixedToken

end RHTower
