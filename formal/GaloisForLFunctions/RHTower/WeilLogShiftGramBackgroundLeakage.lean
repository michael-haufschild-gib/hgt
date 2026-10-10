import GaloisForLFunctions.RHTower.WeilLogShiftGramCoordinateObstruction
import GaloisForLFunctions.RHTower.WeilLogShiftGramExactImage

/-! Exponential cost persists after removing arbitrary logarithmic backgrounds. -/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable section
namespace RHTower

/-- A finite polynomial in the centered logarithmic coordinate. -/
def finiteWeilLogBackground (k m : ℕ) (b : Fin m → ℝ) (j : ℕ) : ℝ :=
  ∑ p, b p * finiteWeilCenteredLog k j ^ (p : ℕ)

/-- One dual witness controls every actual test after removing any logarithmic
background of degree at most `N / K - 2`. -/
theorem exists_finiteWeilGram_log_background_cost_leakage :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℕ, 2 ≤ K ∧ ∀ N : ℕ, 2 * K ≤ N →
      ∃ i : Finset.range N, ∃ d : Finset.range N → ℝ, ‖d‖ = 1 ∧ |d i| = 1 ∧
        (∑ j ∈ Finset.univ.erase i, |d j|) ≤ ((N / K : ℕ) : ℝ) - 1 ∧
        (∀ p ≤ N / K - 2, ∑ j, d j * finiteWeilCenteredLog (N - N / K) j ^ p = 0) ∧
        ∀ (w : FiniteWeilGramTest) (b : Fin (N / K - 1) → ℝ),
          let z := finiteWeilGramCoefficientVector (Finset.range N) w -
            fun j : Finset.range N => finiteWeilLogBackground (N - N / K) (N / K - 1) b j
          ((2 : ℝ) ^ (N / K) * |z i| ≤ B * finiteWeilGramTailCost 1 w +
            (2 : ℝ) ^ (N / K) * ∑ j ∈ Finset.univ.erase i, |d j| * |z j|) ∧
          ((2 : ℝ) ^ (N / K) * |z i| ≤ B * finiteWeilGramTailCost 1 w +
            (2 : ℝ) ^ (N / K) * (((N / K : ℕ) : ℝ) - 1) *
              ‖z - Pi.single i (z i)‖) := by
  obtain ⟨B, hB, K, hK, hdual⟩ := exists_finiteWeilGram_exponential_moment_dual_witness
  refine ⟨B, hB, K, hK, fun N hN => ?_⟩
  obtain ⟨i, d, hd, hdi, hoff, hm, hcost⟩ := hdual N hN
  refine ⟨i, d, hd, hdi, hoff, hm, fun w b => ?_⟩
  apply finiteWeil_cost_leakage_of_pairing i d _ _ _ _ (by positivity) hdi hoff
  have hpair := finiteWeil_pairing_sub_background d
    (finiteWeilGramCoefficientVector (Finset.range N) w)
    (fun j => finiteWeilCenteredLog (N - N / K) j) b (fun p => (p : ℕ))
    (fun p => hm p (by have := p.isLt; omega))
  change (2 : ℝ) ^ (N / K) * |∑ j,
    (finiteWeilGramCoefficientVector (Finset.range N) w j -
      ∑ p, b p * finiteWeilCenteredLog (N - N / K) j ^ (p : ℕ)) * d j| ≤ _
  rw [hpair]
  simpa only [finiteWeilGramCoefficientVector_pairing, mul_comm] using hcost w

/-- Adding any allowed background preserves the exponential cost of an isolated
anomaly. Every target in the statement is realized by an actual finite test. -/
theorem exists_finiteWeilGram_log_background_isolation_cost :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, 2 ≤ K ∧ ∀ N : ℕ, 2 * K ≤ N →
      ∃ i : Finset.range N, ∀ (b : Fin (N / K - 1) → ℝ) (a : ℝ),
        let target : Finset.range N → ℝ :=
          (fun j : Finset.range N => finiteWeilLogBackground (N - N / K) (N / K - 1) b j) +
            Pi.single i a
        (∃ w : FiniteWeilGramTest, finiteWeilGramCoefficientVector (Finset.range N) w = target) ∧
        (∀ w : FiniteWeilGramTest, finiteWeilGramCoefficientVector (Finset.range N) w = target →
          c * (2 : ℝ) ^ (N / K) * |a| ≤ finiteWeilGramTailCost 1 w) := by
  obtain ⟨B, hB, K, hK, hleak⟩ := exists_finiteWeilGram_log_background_cost_leakage
  refine ⟨B⁻¹, inv_pos.mpr hB, K, hK, fun N hN => ?_⟩
  obtain ⟨i, d, _, _, _, _, hbound⟩ := hleak N hN
  refine ⟨i, fun b a => ?_⟩
  constructor
  · exact surjective_finiteWeilGramCoefficientVector (Finset.range N) _
  · intro w hw
    have hres : finiteWeilGramCoefficientVector (Finset.range N) w -
        (fun j : Finset.range N => finiteWeilLogBackground (N - N / K) (N / K - 1) b j) =
        Pi.single i a := by
      rw [hw]
      ext j
      change (finiteWeilLogBackground (N - N / K) (N / K - 1) b j +
        (Pi.single i a : Finset.range N → ℝ) j) -
        finiteWeilLogBackground (N - N / K) (N / K - 1) b j =
        (Pi.single i a : Finset.range N → ℝ) j
      ring
    have hcost : (2 : ℝ) ^ (N / K) * |a| ≤ B * finiteWeilGramTailCost 1 w := by
      simpa only [hres, Pi.single_apply, if_true, sub_self, norm_zero, mul_zero, add_zero]
        using (hbound w b).2
    calc
      B⁻¹ * (2 : ℝ) ^ (N / K) * |a| = B⁻¹ * ((2 : ℝ) ^ (N / K) * |a|) := by ring
      _ ≤ B⁻¹ * (B * finiteWeilGramTailCost 1 w) :=
        mul_le_mul_of_nonneg_left hcost (inv_pos.mpr hB).le
      _ = finiteWeilGramTailCost 1 w := by
        rw [← mul_assoc, inv_mul_cancel₀ hB.ne', one_mul]

end RHTower
