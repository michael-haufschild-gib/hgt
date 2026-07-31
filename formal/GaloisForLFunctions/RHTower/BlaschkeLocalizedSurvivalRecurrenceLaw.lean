import GaloisForLFunctions.RHTower.BlaschkeLocalizedKernelLaw
import GaloisForLFunctions.RHTower.SummableLocalizedSurvivalRecurrenceLaw
import GaloisForLFunctions.RHTower.SummableWeightedHeadReduction

/-!
# Blaschke-localized countable survival recurrence

This file connects the exact Blaschke local spectral weights to the
countably infinite localized survival-recurrence interface.

For `0 < a < 1`, the tail beyond a visible head of `M` modes is exactly

`(1 - a²) * (a²)^(M - 1)`.

Consequently, every countably infinite Blaschke-localized phase packet has
a deterministic survival return whose deadline depends only on the visible
head and whose error pays that exact infinite tail.

This is an exact exponential-localization certificate. It does not assert
that a standard random Anderson Hamiltonian realizes the certificate.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Exact countable spectral tail of the Blaschke local-weight packet. -/
theorem summablePurePointSurvivalTail_blaschkeLocalizedWeight
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (M : ℕ) (hM : 1 ≤ M) :
    summablePurePointSurvivalTail (blaschkeLocalizedWeight a) M =
      (1 - a ^ 2) * (a ^ 2) ^ (M - 1) := by
  rw [summablePurePointSurvivalTail]
  calc
    (∑' j : ℕ, blaschkeLocalizedWeight a (M + j)) =
        ∑' j : ℕ, blaschkeLocalizedWeight a (j + (M - 1) + 1) := by
          apply tsum_congr
          intro j
          congr 1
          omega
    _ = (1 - a ^ 2) * (a ^ 2) ^ (M - 1) :=
      blaschkeLocalizedWeight_tail a ha0 ha1 (M - 1)

/-- Exact visible-head mass of the countable Blaschke local-weight packet. -/
theorem summableWeightedHeadMass_blaschkeLocalizedWeight
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (M : ℕ) (hM : 1 ≤ M) :
    summableWeightedHeadMass (blaschkeLocalizedWeight a) M =
      1 - (1 - a ^ 2) * (a ^ 2) ^ (M - 1) := by
  have hsplit :=
    summableWeightedHeadMass_add_tail
      (blaschkeLocalizedWeight a)
      (blaschkeLocalizedKernel_sq_summable a ha0 ha1)
      (blaschkeLocalizedWeight_tsum a ha0 ha1) M
  have htail :
      (∑' j, blaschkeLocalizedWeight a (M + j)) =
        (1 - a ^ 2) * (a ^ 2) ^ (M - 1) := by
    simpa only [summablePurePointSurvivalTail] using
      summablePurePointSurvivalTail_blaschkeLocalizedWeight
        a ha0 ha1 M hM
  rw [htail] at hsplit
  linarith

/-- Every nonempty visible head of the Blaschke packet has positive mass. -/
theorem summableWeightedHeadMass_blaschkeLocalizedWeight_pos
    (a : ℝ) (ha0 : 0 < a) (_ha1 : a < 1)
    (M : ℕ) (hM : 1 ≤ M) :
    0 < summableWeightedHeadMass (blaschkeLocalizedWeight a) M := by
  rw [summableWeightedHeadMass]
  have hzero :
      0 < blaschkeLocalizedWeight a 0 := by
    rw [blaschkeLocalizedWeight_zero]
    positivity
  have hsingle :
      blaschkeLocalizedWeight a 0 ≤
        ∑ k ∈ Finset.range M, blaschkeLocalizedWeight a k := by
    apply Finset.single_le_sum
    · intro k hk
      exact sq_nonneg (blaschkeLocalizedKernel a k)
    · simp
      omega
  exact hzero.trans_le hsingle

/--
Every countably infinite Blaschke-localized phase packet has a positive
survival return by the `M - 1` projective-gap deadline, with its complete
infinite complement paid by the exact geometric tail.
-/
theorem exists_blaschkeLocalizedSurvival_recurrence
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (omega : ℕ → ℝ) (M Q : ℕ) (hM : 1 ≤ M) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (Q + 1) ^ (M - 1) ∧
      summablePurePointSurvivalDeviation
          (blaschkeLocalizedWeight a) omega n ≤
        summableLocalizedSurvivalRecurrenceBudget
          (blaschkeLocalizedWeight a) M Q
          ((1 - a ^ 2) * (a ^ 2) ^ (M - 1)) := by
  apply exists_summableLocalizedSurvival_recurrence
    (blaschkeLocalizedWeight a) omega
      (fun k => sq_nonneg (blaschkeLocalizedKernel a k))
      (blaschkeLocalizedKernel_sq_summable a ha0 ha1)
      (blaschkeLocalizedWeight_tsum a ha0 ha1)
      M Q hM
      ((1 - a ^ 2) * (a ^ 2) ^ (M - 1))
  exact le_of_eq
    (summablePurePointSurvivalTail_blaschkeLocalizedWeight
      a ha0 ha1 M hM)

/--
At every visible-head resolution, the Blaschke-localized packet either
never exits its certified survival neighborhood or every witnessed exit
admits a strictly later return with the same exact infinite-tail budget.
-/
theorem blaschkeLocalizedSurvival_neverExits_or_postExit_return
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (omega : ℕ → ℝ) (M Q V : ℕ)
    (hM : 1 ≤ M) (hMV : M ≤ V)
    (guardTime : ℝ) (hguard : 0 < guardTime) :
    (∀ t : ℝ, 0 ≤ t →
      summablePurePointSurvivalDeviation
          (blaschkeLocalizedWeight a) omega t ≤
        summableLocalizedSurvivalRecurrenceBudget
          (blaschkeLocalizedWeight a) M Q
          ((1 - a ^ 2) * (a ^ 2) ^ (M - 1))) ∨
    ∃ exitTime : ℝ, ∃ n : ℕ,
      0 ≤ exitTime ∧
      0 < n ∧ n ≤ (Q + 1) ^ (V - 1) ∧
      summableLocalizedSurvivalRecurrenceBudget
          (blaschkeLocalizedWeight a) M Q
          ((1 - a ^ 2) * (a ^ 2) ^ (M - 1)) <
        summablePurePointSurvivalDeviation
          (blaschkeLocalizedWeight a) omega exitTime ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      summablePurePointSurvivalDeviation
          (blaschkeLocalizedWeight a) omega
          ((n : ℝ) * (exitTime + guardTime)) ≤
        summableLocalizedSurvivalRecurrenceBudget
          (blaschkeLocalizedWeight a) M Q
          ((1 - a ^ 2) * (a ^ 2) ^ (M - 1)) := by
  apply summableLocalizedSurvival_neverExits_or_postExit_return
    (blaschkeLocalizedWeight a) omega
      (fun k => sq_nonneg (blaschkeLocalizedKernel a k))
      (blaschkeLocalizedKernel_sq_summable a ha0 ha1)
      (blaschkeLocalizedWeight_tsum a ha0 ha1)
      M Q V hM hMV
      ((1 - a ^ 2) * (a ^ 2) ^ (M - 1))
      (le_of_eq
        (summablePurePointSurvivalTail_blaschkeLocalizedWeight
          a ha0 ha1 M hM))
      guardTime hguard

end RHTower
