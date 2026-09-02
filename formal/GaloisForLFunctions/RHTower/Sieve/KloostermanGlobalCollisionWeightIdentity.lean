import GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionSymmetric

/-!
# Exact weight identity for global Kloosterman collisions

The ordered unequal-modulus weight-pair energy is exactly total squared weight mass minus its
diagonal fourth moment.  Rewriting the symmetric collision receiver through this identity keeps
the diagonal saving visible, with no normalization hypothesis or cardinal relaxation.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Exact diagonal-deficit identity for ordered unequal-modulus weight-pair energy. -/
theorem kloostermanDistinctModulusWeightPairEnergy_eq_sq_sub_diagonal
    (Q : Finset ℕ) (w : ℕ → ℂ) :
    kloostermanDistinctModulusWeightPairEnergy Q w =
      (∑ q ∈ Q, ‖w q‖ ^ 2) ^ 2 - ∑ q ∈ Q, (‖w q‖ ^ 2) ^ 2 := by
  classical
  unfold kloostermanDistinctModulusWeightPairEnergy
  have hfull :
      (∑ q ∈ Q, ‖w q‖ ^ 2) ^ 2 =
        ∑ q ∈ Q, ∑ r ∈ Q, ‖w q‖ ^ 2 * ‖w r‖ ^ 2 := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
  have hdecomp :
      (∑ q ∈ Q, ∑ r ∈ Q, ‖w q‖ ^ 2 * ‖w r‖ ^ 2) =
        (∑ q ∈ Q, ∑ r ∈ Q.erase q, ‖w q‖ ^ 2 * ‖w r‖ ^ 2) +
          ∑ q ∈ Q, (‖w q‖ ^ 2) ^ 2 := by
    calc
      (∑ q ∈ Q, ∑ r ∈ Q, ‖w q‖ ^ 2 * ‖w r‖ ^ 2) =
          ∑ q ∈ Q,
            ((∑ r ∈ Q.erase q, ‖w q‖ ^ 2 * ‖w r‖ ^ 2) +
              ‖w q‖ ^ 2 * ‖w q‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [← Finset.sum_erase_add Q (fun r => ‖w q‖ ^ 2 * ‖w r‖ ^ 2) hq]
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro q hq
        ring
  rw [← hfull] at hdecomp
  linarith

/-- The symmetric global collision envelope with exact weight diagonal saving exposed. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_le_weightPair_symmetric_exact
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w B b ≤
      ((∑ q ∈ Q, ‖w q‖ ^ 2) ^ 2 -
          ∑ q ∈ Q, (‖w q‖ ^ 2) ^ 2) *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanGlobalResponsePairElementaryBudget q r B b := by
  rw [← kloostermanDistinctModulusWeightPairEnergy_eq_sq_sub_diagonal]
  exact kloostermanGlobalFrequencyCollisionEnergy_le_weightPair_symmetric Q w B b

/-- Literal-source symmetric envelope with exact weight diagonal saving exposed. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_Icc_le_weightPair_symmetric_exact
    (Q : Finset ℕ) (w : ℕ → ℂ) (N : ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w (Finset.Icc 1 N) b ≤
      ((∑ q ∈ Q, ‖w q‖ ^ 2) ^ 2 -
          ∑ q ∈ Q, (‖w q‖ ^ 2) ^ 2) *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanGlobalIntervalResponsePairElementaryBudget q r N b := by
  rw [← kloostermanDistinctModulusWeightPairEnergy_eq_sq_sub_diagonal]
  exact kloostermanGlobalFrequencyCollisionEnergy_Icc_le_weightPair_symmetric Q w N b

end

end RHTower.Sieve
