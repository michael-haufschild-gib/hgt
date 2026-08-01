import GaloisForLFunctions.RHTower.MaximalRealDiagonalSelfAdjoint
import GaloisForLFunctions.RHTower.DeningerBoundaryHodgeOperator

/-!
# The Kummer phase generator

The generator of the Kummer phase flow acts on the character of frequency `ℓ a` by that frequency,
so it is coordinate multiplication by the frequency function on the coefficient space.  On its
maximal square-summability domain that operator is densely defined and self-adjoint.

* `deningerPhaseGenerator` : the generator.
* `deningerPhaseGenerator_apply_basis` : it is diagonal on the characters.
* `deningerPhaseGenerator_isSelfAdjoint` : it is self-adjoint on its maximal domain.
-/

namespace RHTower

open HilbertSchmidt

noncomputable section

universe u

variable {ι : Type u} [DecidableEq ι]

/-- **The Kummer phase generator**: coordinate multiplication by the frequency, on its maximal
square-summability domain. -/
def deningerPhaseGenerator (ℓ : ι → ℝ) : DiagonalL2 ι →ₗ.[ℂ] DiagonalL2 ι :=
  maximalRealDiagonal ℓ

/-- **The generator is diagonal on the characters**: the character of frequency `ℓ i` is an
eigenvector with that eigenvalue. -/
theorem deningerPhaseGenerator_apply_basis (ℓ : ι → ℝ) (i : ι) :
    deningerPhaseGenerator ℓ ⟨lpBasis ι i, lpBasis_mem_maximalRealDiagonalDomain ℓ i⟩
      = (ℓ i : ℂ) • lpBasis ι i := by
  refine lp.ext ?_
  funext j
  show (ℓ j : ℂ) * (lpBasis ι i) j = (ℓ i : ℂ) * (lpBasis ι i) j
  by_cases hji : j = i
  · rw [hji]
  · rw [lpBasis_apply, lp.single_apply_ne _ _ _ hji]
    simp

/-- **The generator is densely defined.** -/
theorem deningerPhaseGenerator_dense (ℓ : ι → ℝ) :
    Dense ((deningerPhaseGenerator ℓ).domain : Set (DiagonalL2 ι)) :=
  maximalRealDiagonal_dense ℓ

/-- **The generator is self-adjoint on its maximal domain.** -/
theorem deningerPhaseGenerator_isSelfAdjoint (ℓ : ι → ℝ) :
    IsSelfAdjoint (deningerPhaseGenerator ℓ) :=
  maximalRealDiagonal_isSelfAdjoint ℓ

end

end RHTower
