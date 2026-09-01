import GaloisForLFunctions.HTGeometry.ControlledPhaseChoiCutGap
import GaloisForLFunctions.HTGeometry.HaferkampTwoQubitCliffordSeeds
import GaloisForLFunctions.HTGeometry.KroneckerAmplification
import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms

/-!
# Supercritical sharpness midpoint extraction for Choi cut energy

The Boolean Hadamard amplified by a two-state identity is a concrete Kronecker unitary.  Its two
diagonal-energy factors obey the Choi cut product bound, so the paper's square-root alternative
selects a low-energy side of the cut.
-/

open scoped Matrix Kronecker

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ControlledPhaseChoiCutGap

/-- Hadamard amplified by the identity on `Bool × Unit` is unitary in the product indexing used by
the Choi cut. -/
theorem boolHadamard_kronecker_boolUnitIdentity_unitary :
    (boolHadamardMatrix ⊗ₖ (1 : Matrix (Bool × Unit) (Bool × Unit) ℂ))ᴴ *
        (boolHadamardMatrix ⊗ₖ (1 : Matrix (Bool × Unit) (Bool × Unit) ℂ)) = 1 := by
  exact (kronecker_one_mem_unitary (n := Bool × Unit)
    boolHadamardMatrix_mem_unitary).1

/-- Concrete Choi-cut diagonal-energy product bound for a Hadamard factor and identity ancilla. -/
theorem boolHadamard_boolUnitIdentity_diagonalEnergy_product_le_four :
    diagonalEnergy boolHadamardMatrix *
      diagonalEnergy (1 : Matrix (Bool × Unit) (Bool × Unit) ℂ) ≤ 4 := by
  simpa using
    (diagonalEnergy_product_le_card_of_kronecker_unitary (γ := Unit)
      boolHadamardMatrix (1 : Matrix (Bool × Unit) (Bool × Unit) ℂ)
      boolHadamard_kronecker_boolUnitIdentity_unitary)

/-- Square-root midpoint alternative: one factor of the concrete Hadamard/identity Choi cut has
diagonal energy at most two. -/
theorem boolHadamard_or_boolUnitIdentity_diagonalEnergy_le_two :
    diagonalEnergy boolHadamardMatrix ≤ 2 ∨
      diagonalEnergy (1 : Matrix (Bool × Unit) (Bool × Unit) ℂ) ≤ 2 := by
  have h := GaloisForLFunctions.HTGeometry.le_sqrt_or_le_sqrt_of_mul_le
    (δ := (4 : ℝ)) (by norm_num)
    boolHadamard_boolUnitIdentity_diagonalEnergy_product_le_four
  norm_num at h ⊢
  exact h

end GaloisForLFunctions.HTGeometry.ControlledPhaseChoiCutGap
