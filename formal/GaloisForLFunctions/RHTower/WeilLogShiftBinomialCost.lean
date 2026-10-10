import GaloisForLFunctions.RHTower.WeilLogShiftArithmeticBinomial
import GaloisForLFunctions.RHTower.WeilLogShiftArithmeticCost

/-! Explicit central-binomial mass in the actual Gram-test cost receivers. -/

open scoped BigOperators
noncomputable section
namespace RHTower

theorem exists_finiteWeilGram_binomial_fiber_sensitivity :
    ∃ B L : ℝ, 0 < B ∧ 1 ≤ L ∧ ∀ (r : ℕ) (s : Finset ℕ) (k : ℕ)
      (hmem : ∀ i : Fin (r + 2), k + (i : ℕ) ∈ s),
      4 * L * ((r + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) →
      (∃ w : FiniteWeilGramTest, ∀ a : ℝ,
        (∑ i, finiteWeilCanonicalMixture r k a i *
          finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) = a) ∧
      ∀ v z : Fin (r + 2) → ℝ,
        finiteWeilCanonicalMomentFiber r k v → finiteWeilCanonicalMomentFiber r k z →
        ∀ w : FiniteWeilGramTest,
          |(∑ i, v i * finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) -
            (∑ i, z i * finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩)| *
              (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r) *
                (((k + 2 : ℕ) : ℝ) ^ (r + 1) *
                  ((2 : ℝ) ^ (r + 1) / ((r + 1).choose ((r + 1) / 2) : ℝ))) ≤
                    (∑ i, |v i - z i|) * ((k + r + 3 : ℕ) : ℝ) ^ (r + 1) *
                      B * finiteWeilGramTailCost 1 w := by
  simpa only [finiteWeilArithmeticMass_eq_binomial] using
    exists_finiteWeilGram_arithmetic_fiber_sensitivity

theorem exists_finiteWeilGram_binomial_coordinate_cost :
    ∃ B L : ℝ, 0 < B ∧ 1 ≤ L ∧ ∀ (r : ℕ) (s : Finset ℕ) (k : ℕ)
      (hmem : ∀ i : Fin (r + 2), k + (i : ℕ) ∈ s),
      4 * L * ((r + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) →
      (∃ w : FiniteWeilGramTest, ∀ a : ℝ,
        (∑ i, finiteWeilCanonicalMixture r k a i *
          finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) = a) ∧
      ∀ w : FiniteWeilGramTest,
        (∀ a : ℝ, (∑ i, finiteWeilCanonicalMixture r k a i *
          finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) = a) →
        ((k + 2 : ℕ) : ℝ) ^ (r + 1) *
          ((2 : ℝ) ^ (r + 1) / ((r + 1).choose ((r + 1) / 2) : ℝ)) *
            (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r) ≤
              2 * ((k + r + 3 : ℕ) : ℝ) ^ (r + 1) * B * finiteWeilGramTailCost 1 w := by
  simpa only [finiteWeilArithmeticMass_eq_binomial] using
    exists_finiteWeilGram_arithmetic_coordinate_cost

end RHTower
