import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.FiniteGammaCoxLaw
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TwoTowersAddExactlyOnBoxes

/-!
# Gamma–Cox detection of vanishing two-tower profiles

The sum-of-squares grid mass encodes simultaneous vanishing of every amplitude
in a box. A single scalar detector therefore classifies complete finite profiles.
-/

open Filter Topology Finset
open scoped Classical
open GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence
noncomputable section

/-- Zero grid mass is equivalent to vanishing of the whole finite profile. -/
theorem gridMass_zero_iff (M N : ℕ) (f : ℕ → ℕ → ℝ) :
    gridMass M N f = 0 ↔ ∀ j ≤ M, ∀ k ≤ N, f j k = 0 := by
  refine ⟨eq_zero_of_gridMass_eq_zero, fun h => ?_⟩
  apply sum_eq_zero
  intro j hj
  apply sum_eq_zero
  intro k hk
  rw [h j (Nat.le_of_lt_succ (mem_range.mp hj)) k (Nat.le_of_lt_succ (mem_range.mp hk))]
  exact zero_pow two_ne_zero

/-- The grid detector tests every amplitude simultaneously through the total mass. -/
theorem cox_grid_vanishing (M N : ℕ) (f : ℕ → ℕ → ℝ) :
    Tendsto (fun K => detection K (gridMass M N f)) atTop
      (𝓝 (if ∀ j ≤ M, ∀ k ≤ N, f j k = 0 then 1 else 0)) := by
  simpa only [gridMass_zero_iff] using tendsto_detection (gridMass M N f)

/-- A finite collection of two-tower profiles is classified simultaneously. -/
theorem cox_grid_vanishing_family {ι : Type*} [Fintype ι]
    (M N : ℕ) (f : ι → ℕ → ℕ → ℝ) :
    Tendsto (fun K => (binaryLaw K (fun i => gridMass M N (f i))).real
      {b | b ≠ fun i => decide (∀ j ≤ M, ∀ k ≤ N, f i j k = 0)}) atTop (𝓝 0) := by
  simpa only [zeroPattern, gridMass_zero_iff] using
    tendsto_binaryLaw_error (fun i => gridMass M N (f i))

end
end GaloisForLFunctions.SignedArithmeticEnergyIncidence

#print axioms GaloisForLFunctions.SignedArithmeticEnergyIncidence.gridMass_zero_iff
#print axioms GaloisForLFunctions.SignedArithmeticEnergyIncidence.cox_grid_vanishing
#print axioms GaloisForLFunctions.SignedArithmeticEnergyIncidence.cox_grid_vanishing_family
