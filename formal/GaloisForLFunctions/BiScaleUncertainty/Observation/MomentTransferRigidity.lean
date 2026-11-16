import GaloisForLFunctions.RHTower.WeilLogShiftArithmeticBinomial

/-!
# Diagonal transfers of moment annihilators

On arithmetic and logarithmic grids, the first moment-annihilator space is
a line with full support. A diagonal transfer preserves that line exactly
when all its multipliers agree. Multiplication by the arithmetic node
reveals the formerly invisible top moment one order earlier.
-/

noncomputable section
open scoped BigOperators
open RHTower

namespace GaloisForLFunctions.BiScaleUncertainty.Observation

/-- Initial moment cancellation survives precisely the constant transfers. -/
theorem arithmeticMoment_transfer_rigidity (r : ℕ) (t : Fin (r + 2) → ℝ) :
    (∀ k : Fin (r + 1), ∑ i, (t i * finiteWeilMomentWeights
      (finiteWeilArithmeticNodes r) i) * finiteWeilArithmeticNodes r i ^ k.val = 0) ↔
      ∀ i, t i = t 0 := by
  let h := finiteWeilArithmeticNodes r
  let w := finiteWeilMomentWeights h
  constructor
  · intro hm
    have hs := finiteWeilMomentWeights_span h (finiteWeilArithmeticNodes_injective r)
      (fun i => t i * w i) (fun k hk => hm ⟨k, hk⟩)
    have hi (i : Fin (r + 2)) : t i = ∑ j, (t j * w j) * h j ^ (r + 1) := by
      have he := congrFun hs i
      exact mul_right_cancel₀ (finiteWeilMomentWeights_ne_zero h
        (finiteWeilArithmeticNodes_injective r) i) he
    intro i
    exact (hi i).trans (hi 0).symm
  · intro ht k
    simp only [ht, mul_assoc, ← Finset.mul_sum]
    rw [finiteWeilMomentWeights_moment _ (finiteWeilArithmeticNodes_injective r)
      k.val (Nat.le_of_lt k.isLt), if_neg (Nat.ne_of_gt k.isLt), mul_zero]

/-- The same rigidity holds for the actual logarithmic cluster nodes. -/
theorem logClusterMoment_transfer_rigidity (r s : ℕ) (t : Fin (r + 2) → ℝ) :
    (∀ k : Fin (r + 1), ∑ i, (t i * finiteWeilMomentWeights
      (finiteWeilClusterLogNodes r s) i) * finiteWeilClusterLogNodes r s i ^ k.val = 0) ↔
      ∀ i, t i = t 0 := by
  let h := finiteWeilClusterLogNodes r s
  let w := finiteWeilMomentWeights h
  constructor
  · intro hm
    have hs := finiteWeilMomentWeights_span h (finiteWeilClusterLogNodes_injective r s)
      (fun i => t i * w i) (fun k hk => hm ⟨k, hk⟩)
    have hi (i : Fin (r + 2)) : t i = ∑ j, (t j * w j) * h j ^ (r + 1) := by
      have he := congrFun hs i
      exact mul_right_cancel₀ (finiteWeilMomentWeights_ne_zero h
        (finiteWeilClusterLogNodes_injective r s) i) he
    intro i
    exact (hi i).trans (hi 0).symm
  · intro ht k
    simp only [ht, mul_assoc, ← Finset.mul_sum]
    rw [finiteWeilMomentWeights_moment _ (finiteWeilClusterLogNodes_injective r s)
      k.val (Nat.le_of_lt k.isLt), if_neg (Nat.ne_of_gt k.isLt), mul_zero]

/-- Node multiplication moves the first surviving arithmetic moment down by one. -/
theorem arithmeticMoment_node_transfer (r : ℕ) (k : Fin (r + 1)) :
    (∑ i, (finiteWeilArithmeticNodes r i * finiteWeilMomentWeights
      (finiteWeilArithmeticNodes r) i) * finiteWeilArithmeticNodes r i ^ k.val) =
      if k.val = r then 1 else 0 := by
  have hs := finiteWeilMomentWeights_moment (finiteWeilArithmeticNodes r)
    (finiteWeilArithmeticNodes_injective r) (k.val + 1) (by have := k.isLt; omega)
  have he : r + 1 = k.val + 1 ↔ k.val = r := by omega
  rw [he] at hs
  convert hs using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]
  ring

#print axioms arithmeticMoment_transfer_rigidity
#print axioms logClusterMoment_transfer_rigidity
#print axioms arithmeticMoment_node_transfer

end GaloisForLFunctions.BiScaleUncertainty.Observation
