import GaloisForLFunctions.HTGeometry.HaynsworthInertia

/-!
# Positive-definite complex Schur complements

Haynsworth's explicit block congruence and invertibility of its unitriangular matrix show that the
block diagonal form consisting of the head and Schur complement is positive definite.  Restriction
to the trailing block gives strict positivity of the Hermitian Schur complement.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The Schur complement of a Hermitian invertible head in a positive-definite complex block
matrix is positive definite. -/
theorem schurComplement_posDef_complex {A : Matrix ι ι ℂ} (hAu : IsUnit A)
    (hA : A.IsHermitian) (B : Matrix ι κ ℂ) (C : Matrix κ κ ℂ)
    (hfull : (fromBlocks A B Bᴴ C).PosDef) :
    (C - Bᴴ * A⁻¹ * B).PosDef := by
  let S := C - Bᴴ * A⁻¹ * B
  let Q := fromBlocks (1 : Matrix ι ι ℂ) (A⁻¹ * B) 0 (1 : Matrix κ κ ℂ)
  have hQ : IsUnit Q := isUnit_fromBlocks_one_upper (A⁻¹ * B)
  have hcongr : (Qᴴ * fromBlocks A 0 0 S * Q).PosDef := by
    rw [show Qᴴ * fromBlocks A 0 0 S * Q = fromBlocks A B Bᴴ C by
      exact fromBlocks_schur_congr hAu hA B C]
    exact hfull
  have hdiag : (fromBlocks A 0 0 S).PosDef := by
    exact (hQ.posDef_star_left_conjugate_iff).mp hcongr
  have hsub := hdiag.submatrix
    (Sum.inr_injective : Function.Injective (Sum.inr : κ → ι ⊕ κ))
  have heq : (fromBlocks A 0 0 S).submatrix Sum.inr Sum.inr = S := by
    ext i j
    rfl
  rw [heq] at hsub
  exact hsub

end GaloisForLFunctions.HTGeometry
