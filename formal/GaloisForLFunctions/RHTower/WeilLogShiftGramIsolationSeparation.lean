import GaloisForLFunctions.RHTower.WeilLogShiftGramCoordinateObstruction
import GaloisForLFunctions.RHTower.WeilLogShiftGramUnitResponse
import GaloisForLFunctions.RHTower.WeilLogShiftGramUniformCost

/-! A unit response costs quadratically, while isolating one coefficient among
all cutoff coefficients can force exponential cost. Exact isolation is attainable. -/

attribute [local instance] Classical.propDecidable

noncomputable section
namespace RHTower

/-- All costs are the same native unit cost. The expensive coordinate may depend
on the cutoff, and its lower bound applies to every actual Gram test. -/
theorem exists_finiteWeilGram_coordinate_isolation_cost_separation :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ K : ℕ, 2 ≤ K ∧ ∀ N : ℕ, 2 * K ≤ N →
      ∃ i : Finset.range N,
        (∃ w : FiniteWeilGramTest,
          finiteWeilGramCoefficientVector (Finset.range N) w i = 1 ∧
            finiteWeilGramTailCost 1 w ≤ A * (N : ℝ) ^ 2) ∧
        (∃ w : FiniteWeilGramTest,
          finiteWeilGramCoefficientVector (Finset.range N) w = Pi.single i 1) ∧
        (∀ w : FiniteWeilGramTest,
          finiteWeilGramCoefficientVector (Finset.range N) w = Pi.single i 1 →
            c * (2 : ℝ) ^ (N / K) ≤ finiteWeilGramTailCost 1 w) := by
  obtain ⟨c, hc, K, hK, hbad⟩ := exists_finiteWeilGram_exponential_coordinate_obstruction
  obtain ⟨D, hD, hresponse⟩ := exists_finiteWeilGram_quadratic_unit_response
  refine ⟨c, 4 * D, hc, by positivity, K, hK, ?_⟩
  intro N hN
  obtain ⟨i, hi⟩ := hbad N hN
  refine ⟨i, ?_, ?_, hi⟩
  · obtain ⟨w, hw, hcost⟩ := hresponse (Finset.range N) i
    refine ⟨w, hw, ?_⟩
    have hiN : (i : ℕ) < N := Finset.mem_range.mp i.property
    have hindex : (((i : ℕ) + 2 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      exact_mod_cast (show (i : ℕ) + 2 ≤ 2 * N by omega)
    have hi0 : 0 ≤ (((i : ℕ) + 2 : ℕ) : ℝ) := by positivity
    have hsquare : (((i : ℕ) + 2 : ℕ) : ℝ) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by
      nlinarith only [hindex, hi0, Nat.cast_nonneg (α := ℝ) N]
    calc
      _ ≤ D * (((i : ℕ) + 2 : ℕ) : ℝ) ^ 2 := hcost
      _ ≤ D * (4 * (N : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hsquare hD.le
      _ = (4 * D) * (N : ℝ) ^ 2 := by ring
  · obtain ⟨M, x, C, _, _, hrealize⟩ :=
      exists_finiteWeilGram_distinct_fixed_node_cost_control (Finset.range N)
    obtain ⟨u, hu, _⟩ := hrealize (Pi.single i 1)
    exact ⟨⟨M, x, u, 1⟩, hu⟩

end RHTower
