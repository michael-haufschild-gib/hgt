import GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock
import GaloisForLFunctions.RHTower.CCMSubsetFidelityReadoutRigidity

/-!
# Supercritical sharpness midpoint extraction for simplex readout

Summing the primal simplex vectors gives a concrete coefficient-one reader for every dual
channel.  The resulting feature/readout product lower bound admits the large-branch counterpart of
the paper's square-root midpoint alternative.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Sum of simplex primal vectors, used as one reader for all dual channels. -/
def simplexPrimalReader : E ι := ∑ i : ι, primal ι i

theorem inner_simplexPrimalReader_dual (i : ι) :
    inner ℂ (simplexPrimalReader ι) (dual ι i) = 1 := by
  rw [simplexPrimalReader, sum_inner]
  simp [inner_primal_dual]

/-- Concrete coefficient-one uncertainty product for the simplex primal reader and all dual
channels. -/
theorem simplexPrimalReader_dual_energy_product_ge_card_sq :
    ((Fintype.card ι : ℝ) ^ (2 : ℕ)) ≤
      ‖simplexPrimalReader ι‖ ^ (2 : ℕ) * ‖∑ i : ι, dual ι i‖ ^ (2 : ℕ) := by
  simpa using
    (coefficientOneHilbertReadout_energy_product_ge_card_sq
      (Finset.univ : Finset ι) (simplexPrimalReader ι) (dual ι)
      (fun i _ ↦ inner_simplexPrimalReader_dual ι i))

/-- Large-branch midpoint alternative: either primal-reader energy or summed-dual energy reaches
the channel count. -/
theorem card_le_simplexPrimalReader_energy_or_card_le_dualSum_energy :
    (Fintype.card ι : ℝ) ≤ ‖simplexPrimalReader ι‖ ^ (2 : ℕ) ∨
      (Fintype.card ι : ℝ) ≤ ‖∑ i : ι, dual ι i‖ ^ (2 : ℕ) := by
  let c : ℝ := Fintype.card ι
  let a : ℝ := ‖simplexPrimalReader ι‖ ^ (2 : ℕ)
  let b : ℝ := ‖∑ i : ι, dual ι i‖ ^ (2 : ℕ)
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast card_pos ι
  have ha0 : 0 ≤ a := by exact sq_nonneg _
  have hb0 : 0 ≤ b := by exact sq_nonneg _
  have hproduct : c ^ (2 : ℕ) ≤ a * b := by
    exact simplexPrimalReader_dual_energy_product_ge_card_sq ι
  change c ≤ a ∨ c ≤ b
  by_contra h
  push Not at h
  have hablt : a * b < c ^ (2 : ℕ) := by
    by_cases hbzero : b = 0
    · rw [hbzero, mul_zero]
      positivity
    · have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hbzero)
      calc
        a * b < c * b := mul_lt_mul_of_pos_right h.1 hbpos
        _ < c * c := mul_lt_mul_of_pos_left h.2 hc
        _ = c ^ (2 : ℕ) := by ring
  exact (not_lt_of_ge hproduct) hablt

end RHTower
