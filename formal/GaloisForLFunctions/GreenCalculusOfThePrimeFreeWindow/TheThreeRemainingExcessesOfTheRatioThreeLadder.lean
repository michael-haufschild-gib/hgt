import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFirstOverlapStepHoldsAtEveryBlockSize

/-!
# The three remaining excesses of the ratio-three ladder

The first step costs zero. The four-step budget is therefore exactly the sum
of the next three nonnegative Schur excesses, at their accumulated levels.
It vanishes precisely when each of those three steps has zero excess at
level zero. The ratios below are exact, with no rounded intermediate values.
-/

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- Exact rational milestones through the fourth ratio-squaring step. -/
theorem iteratedRatio_exact_milestones :
    iteratedRatio 0 = 103 / 50 ∧
    iteratedRatio 1 = 10609 / 5000 ∧
    iteratedRatio 2 = 112550881 / 50000000 ∧
    iteratedRatio 3 = (103 : ℝ) ^ 8 / (100 ^ 8 / 2) ∧
    iteratedRatio 4 = (103 : ℝ) ^ 16 / (100 ^ 16 / 2) := by
  norm_num [iteratedRatio_eq]

/-- The second cumulative level consists of the second excess alone. -/
theorem levelAt_two {Q : ℕ} (hQ : 2 ≤ Q) :
    levelAt Q 2 = schurStepExcess Q (10609 / 5000) 0 := by
  rw [show levelAt Q 2 = levelAt Q 1 +
    schurStepExcess Q (iteratedRatio 1) (levelAt Q 1) from rfl,
    levelAt_one hQ, zero_add, iteratedRatio_exact_milestones.2.1]

/-- The exact four-step budget, after removing the zero first term. -/
theorem levelAt_four_eq_three_excesses {Q : ℕ} (hQ : 2 ≤ Q) :
    levelAt Q 4 =
      schurStepExcess Q (10609 / 5000) 0 +
      schurStepExcess Q (112550881 / 50000000) (levelAt Q 2) +
      schurStepExcess Q ((103 : ℝ) ^ 8 / (100 ^ 8 / 2)) (levelAt Q 3) := by
  calc
    levelAt Q 4 = levelAt Q 2 +
        schurStepExcess Q (iteratedRatio 2) (levelAt Q 2) +
        schurStepExcess Q (iteratedRatio 3) (levelAt Q 3) := rfl
    _ = _ := by
      rw [iteratedRatio_exact_milestones.2.2.1,
        iteratedRatio_exact_milestones.2.2.2.1]
      conv_lhs => lhs; lhs; rw [levelAt_two hQ]

/-- Vanishing of the ratio-three budget is exactly three zero-level Schur claims. -/
theorem levelAt_four_eq_zero_iff_three_excesses {Q : ℕ} (hQ : 2 ≤ Q) :
    levelAt Q 4 = 0 ↔
      schurStepExcess Q (10609 / 5000) 0 = 0 ∧
      schurStepExcess Q (112550881 / 50000000) 0 = 0 ∧
      schurStepExcess Q ((103 : ℝ) ^ 8 / (100 ^ 8 / 2)) 0 = 0 := by
  constructor
  · intro h4
    have h2 : levelAt Q 2 = 0 :=
      le_antisymm ((levelAt_mono Q (by norm_num : 2 ≤ 4)).trans h4.le)
        (levelAt_nonneg Q 2)
    have h3 : levelAt Q 3 = 0 :=
      le_antisymm ((levelAt_mono Q (by norm_num : 3 ≤ 4)).trans h4.le)
        (levelAt_nonneg Q 3)
    have he1 : schurStepExcess Q (10609 / 5000) 0 = 0 :=
      (levelAt_two hQ).symm.trans h2
    have he2 : schurStepExcess Q (112550881 / 50000000) 0 = 0 := by
      have hrec : levelAt Q 3 = levelAt Q 2 +
          schurStepExcess Q (iteratedRatio 2) (levelAt Q 2) := rfl
      rw [h3, h2, zero_add, iteratedRatio_exact_milestones.2.2.1] at hrec
      exact hrec.symm
    refine ⟨he1, he2, ?_⟩
    have hsum := levelAt_four_eq_three_excesses hQ
    rw [h4, h2, h3, he1, he2, zero_add, zero_add] at hsum
    exact hsum.symm
  · rintro ⟨he1, he2, he3⟩
    have h2 : levelAt Q 2 = 0 := (levelAt_two hQ).trans he1
    have h3 : levelAt Q 3 = 0 := by
      show levelAt Q 2 + schurStepExcess Q (iteratedRatio 2) (levelAt Q 2) = 0
      rw [h2, iteratedRatio_exact_milestones.2.2.1, he2, add_zero]
    rw [levelAt_four_eq_three_excesses hQ, h2, h3, he1, he2, he3, add_zero, add_zero]

/-- The three explicit zero-level claims are sufficient for every ratio-three window.
This implication does not assert that the three excesses vanish. -/
theorem three_excesses_eq_zero_implies_ratio_three_index :
    (schurStepExcess 2 (10609 / 5000) 0 = 0 ∧
      schurStepExcess 2 (112550881 / 50000000) 0 = 0 ∧
      schurStepExcess 2 ((103 : ℝ) ^ 8 / (100 ^ 8 / 2)) 0 = 0) →
    ∀ Q R J : ℕ, 2 ≤ Q → 1 ≤ R → R ≤ J → J ≤ 2 * R →
      hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 := by
  intro h Q R J hQ hR hRJ hJ
  exact hermNegIndex_ratio_three_eq_one_of_levelAt_zero
    ((levelAt_four_eq_zero_iff_three_excesses le_rfl).mpr h) hQ hR hRJ hJ

#print axioms iteratedRatio_exact_milestones
#print axioms levelAt_four_eq_three_excesses
#print axioms levelAt_four_eq_zero_iff_three_excesses
#print axioms three_excesses_eq_zero_implies_ratio_three_index

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
