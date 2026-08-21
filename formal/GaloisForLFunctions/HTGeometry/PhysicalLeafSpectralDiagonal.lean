/-
# The physical leaf Hamiltonian in its own spectral basis

The tensorized old basis carries the physical leaf Hamiltonian to the spectral local-extension
matrix, so composing it with any diagonalizing unitary of that matrix diagonalizes the physical
Hamiltonian itself.  This is the reconstruction step of a leaf extension, isolated from the
architecture bookkeeping and stated for arbitrary physical, spectral and leaf types.

Main results:
* `physicalLeafHamiltonian_conj_tensorIdentityBasis` — the coordinate identity.
* `physicalLeafHamiltonian_eq_spectralBasis_diagonal` — **the physical diagonalization**.
-/
import GaloisForLFunctions.HTGeometry.PhysicalObserverSpectralRealization

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {P I ρ : Type*} [Fintype P] [Fintype I] [Fintype ρ]
  [DecidableEq P] [DecidableEq I] [DecidableEq ρ]

/-- The tensorized old basis carries the physical leaf Hamiltonian to the spectral
local-extension matrix. -/
theorem physicalLeafHamiltonian_conj_tensorIdentityBasis
    (U : Matrix P I ℂ) (hUleft : Uᴴ * U = (1 : Matrix I I ℂ))
    (energy : I → ℂ) (parent : Matrix P P ℂ) (shift : ρ → ℂ) (edge : Matrix ρ ρ ℂ) :
    (tensorIdentityBasis (ρ := ρ) U)ᴴ *
        physicalLeafHamiltonian (U * Matrix.diagonal energy * Uᴴ) parent shift edge *
        tensorIdentityBasis (ρ := ρ) U
      = localExtensionMatrix energy shift (Uᴴ * parent * U) edge := by
  refine tensorIdentityBasis_coordinate_physicalLeafHamiltonian U _ parent energy shift _ edge
    hUleft ?_ rfl
  calc Uᴴ * (U * Matrix.diagonal energy * Uᴴ) * U
      = (Uᴴ * U) * Matrix.diagonal energy * (Uᴴ * U) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.diagonal energy := by rw [hUleft, Matrix.one_mul, Matrix.mul_one]

/-- **The physical leaf Hamiltonian is diagonalized by the composed spectral basis.** -/
theorem physicalLeafHamiltonian_eq_spectralBasis_diagonal
    (U : Matrix P I ℂ) (hUleft : Uᴴ * U = (1 : Matrix I I ℂ))
    (hUright : U * Uᴴ = (1 : Matrix P P ℂ))
    (energy : I → ℂ) (parent : Matrix P P ℂ) (shift : ρ → ℂ) (edge : Matrix ρ ρ ℂ)
    (W : Matrix (I × ρ) (I × ρ) ℂ) (nextEnergy : I × ρ → ℂ)
    (hdiag : localExtensionMatrix energy shift (Uᴴ * parent * U) edge
      = W * Matrix.diagonal nextEnergy * Wᴴ) :
    physicalLeafHamiltonian (U * Matrix.diagonal energy * Uᴴ) parent shift edge
      = physicalLeafSpectralBasis U W * Matrix.diagonal nextEnergy *
        (physicalLeafSpectralBasis U W)ᴴ := by
  have hT : tensorIdentityBasis (ρ := ρ) U * (tensorIdentityBasis (ρ := ρ) U)ᴴ
      = (1 : Matrix (P × ρ) (P × ρ) ℂ) := tensorIdentityBasis_mul_star_self U hUright
  have hcoord := physicalLeafHamiltonian_conj_tensorIdentityBasis U hUleft energy parent
    shift edge
  calc physicalLeafHamiltonian (U * Matrix.diagonal energy * Uᴴ) parent shift edge
      = (tensorIdentityBasis (ρ := ρ) U * (tensorIdentityBasis (ρ := ρ) U)ᴴ) *
          physicalLeafHamiltonian (U * Matrix.diagonal energy * Uᴴ) parent shift edge *
          (tensorIdentityBasis (ρ := ρ) U * (tensorIdentityBasis (ρ := ρ) U)ᴴ) := by
        rw [hT, Matrix.one_mul, Matrix.mul_one]
    _ = tensorIdentityBasis (ρ := ρ) U *
          ((tensorIdentityBasis (ρ := ρ) U)ᴴ *
            physicalLeafHamiltonian (U * Matrix.diagonal energy * Uᴴ) parent shift edge *
            tensorIdentityBasis (ρ := ρ) U) *
          (tensorIdentityBasis (ρ := ρ) U)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = tensorIdentityBasis (ρ := ρ) U *
          (W * Matrix.diagonal nextEnergy * Wᴴ) * (tensorIdentityBasis (ρ := ρ) U)ᴴ := by
        rw [hcoord, hdiag]
    _ = physicalLeafSpectralBasis U W * Matrix.diagonal nextEnergy *
          (physicalLeafSpectralBasis U W)ᴴ := by
        rw [physicalLeafSpectralBasis, Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]

end GaloisForLFunctions.HTGeometry

end
