import GaloisForLFunctions.RHTower.WeilLogShiftGramCoordinateObstruction

/-! Exponential cost versus leakage for actual finite Weil Gram tests. -/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable section
namespace RHTower

/-- Fixed constants and a cutoff-dependent dual vector control every actual test. -/
theorem exists_finiteWeilGram_exponential_cost_leakage :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℕ, 2 ≤ K ∧ ∀ N : ℕ, 2 * K ≤ N →
      ∃ i : Finset.range N, ∃ d : Finset.range N → ℝ, ‖d‖ = 1 ∧ |d i| = 1 ∧
        (∑ j ∈ Finset.univ.erase i, |d j|) ≤ ((N / K : ℕ) : ℝ) - 1 ∧
        ∀ w : FiniteWeilGramTest,
          let y := finiteWeilGramCoefficientVector (Finset.range N) w
          ((2 : ℝ) ^ (N / K) * |y i| ≤ B * finiteWeilGramTailCost 1 w +
            (2 : ℝ) ^ (N / K) * ∑ j ∈ Finset.univ.erase i, |d j| * |y j|) ∧
          ((2 : ℝ) ^ (N / K) * |y i| ≤ B * finiteWeilGramTailCost 1 w +
            (2 : ℝ) ^ (N / K) * (((N / K : ℕ) : ℝ) - 1) *
              ‖y - Pi.single i (y i)‖) := by
  obtain ⟨B, hB, K, hK, hdual⟩ := exists_finiteWeilGram_exponential_dual_witness
  refine ⟨B, hB, K, hK, fun N hN => ?_⟩
  obtain ⟨i, d, hd, hdi, hoff, hcost⟩ := hdual N hN
  refine ⟨i, d, hd, hdi, hoff, fun w => ?_⟩
  apply finiteWeil_cost_leakage_of_pairing i d _ _ _ _ (by positivity) hdi hoff
  simpa only [finiteWeilGramCoefficientVector_pairing, mul_comm] using hcost w

/-- Unit response below half the exponential cost budget forces inverse-linear leakage. -/
theorem exists_finiteWeilGram_exponential_cost_leakage_threshold :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℕ, 2 ≤ K ∧ ∀ N : ℕ, 2 * K ≤ N →
      ∃ i : Finset.range N, ∀ w : FiniteWeilGramTest,
        let y := finiteWeilGramCoefficientVector (Finset.range N) w
        y i = 1 →
          (finiteWeilGramTailCost 1 w ≤ (2 : ℝ) ^ (N / K) / (2 * B) →
            1 / (2 * (((N / K : ℕ) : ℝ) - 1)) ≤ ‖y - Pi.single i (y i)‖) ∧
          (‖y - Pi.single i (y i)‖ ≤ 1 / (2 * (((N / K : ℕ) : ℝ) - 1)) →
            (2 : ℝ) ^ (N / K) / (2 * B) ≤ finiteWeilGramTailCost 1 w) := by
  obtain ⟨B, hB, K, hK, hleak⟩ := exists_finiteWeilGram_exponential_cost_leakage
  refine ⟨B, hB, K, hK, fun N hN => ?_⟩
  obtain ⟨i, d, _, _, _, hbound⟩ := hleak N hN
  refine ⟨i, fun w hi => ?_⟩
  have hKpos : 0 < K := by omega
  have hq : 2 ≤ N / K := (Nat.le_div_iff_mul_le hKpos).mpr hN
  have hm : 0 < ((N / K : ℕ) : ℝ) - 1 := by
    have hqreal : (2 : ℝ) ≤ ((N / K : ℕ) : ℝ) := by exact_mod_cast hq
    linarith only [hqreal]
  have hb := (hbound w).2
  rw [hi, abs_one, mul_one] at hb
  simp only [hi]
  exact finiteWeil_leakage_half_budget _ _ _ _ _ (by positivity) hB hm hb

end RHTower
