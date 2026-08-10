import GaloisForLFunctions.HTGeometry.HilbertSchmidtBlockEigenvector
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantMultiplicity

/-!
# Sign reversal for Hilbert--Schmidt kernel models
-/

namespace HilbertSchmidt

open GaloisForLFunctions.HTGeometry

variable {ι : Type*}

/-- Kernel negation agrees exactly with operator negation. -/
theorem toOperator_neg {K : ι × ι → ℂ} (hK : IsHS K) :
    toOperator (isHS_neg hK) = -toOperator hK := by
  ext f i
  show (∑' j, (-K) (i, j) * f j) = -(∑' j, K (i, j) * f j)
  rw [← tsum_neg]
  exact tsum_congr fun j => by simp

/-- Finite truncation commutes with kernel negation. -/
theorem truncKernel_neg [DecidableEq ι] (K : ι × ι → ℂ) (s : Finset ι) :
    truncKernel (-K) s = -truncKernel K s := by
  funext p
  by_cases hp : p.1 ∈ s ∧ p.2 ∈ s <;> simp [truncKernel, hp]

/-- Finite block extraction commutes with kernel negation. -/
theorem blockMatrix_neg (K : ι × ι → ℂ) (s : Finset ι) :
    blockMatrix (-K) s = -blockMatrix K s := by
  ext i j
  simp [blockMatrix]

/-- Canonically reindexed finite block extraction commutes with kernel negation. -/
theorem blockFin_neg (K : ι × ι → ℂ) (s : Finset ι) :
    blockFin (-K) s = -blockFin K s := by
  ext i j
  simp [blockFin, blockMatrix]

end HilbertSchmidt
