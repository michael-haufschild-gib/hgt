import GaloisForLFunctions.HTGeometry.HaferkampLiftedCliffordAction

/-!
# Prefix transport for the Appendix-B block induction

The block selected for a Pauli transported through prior Clifford blocks has a
terminal root-`Z` coordinate.  Reversing both transport identities expresses
that coordinate in the original independent Pauli direction.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Reverse the prior-prefix and current-block Pauli transports.  This is the
exact stripped form of one Appendix-B block coordinate, including its nonzero
phase. -/
theorem reverse_block_prefix_transport
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (pre block : Matrix.unitaryGroup (Q → Bool) ℂ)
    (P R Z : Q → Option (Fin 3)) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hpre : (pre : Matrix (Q → Bool) (Q → Bool) ℂ) * finitePauliMatrix P *
        Matrix.conjTranspose (pre : Matrix (Q → Bool) (Q → Bool) ℂ) =
      a • finitePauliMatrix R)
    (hblock : (block : Matrix (Q → Bool) (Q → Bool) ℂ) * finitePauliMatrix R *
        Matrix.conjTranspose (block : Matrix (Q → Bool) (Q → Bool) ℂ) =
      b • finitePauliMatrix Z) :
    Matrix.conjTranspose (pre : Matrix (Q → Bool) (Q → Bool) ℂ) *
        Matrix.conjTranspose (block : Matrix (Q → Bool) (Q → Bool) ℂ) *
        finitePauliMatrix Z * (block : Matrix (Q → Bool) (Q → Bool) ℂ) *
        (pre : Matrix (Q → Bool) (Q → Bool) ℂ) =
      (b * a)⁻¹ • finitePauliMatrix P := by
  have hblockrev :=
    reverse_unitary_conjugation_of_smul_finitePauli block R Z b hb hblock
  have hprerev :=
    reverse_unitary_conjugation_of_smul_finitePauli pre P R a ha hpre
  calc
    Matrix.conjTranspose (pre : Matrix (Q → Bool) (Q → Bool) ℂ) *
        Matrix.conjTranspose (block : Matrix (Q → Bool) (Q → Bool) ℂ) *
        finitePauliMatrix Z * (block : Matrix (Q → Bool) (Q → Bool) ℂ) *
        (pre : Matrix (Q → Bool) (Q → Bool) ℂ) =
      Matrix.conjTranspose (pre : Matrix (Q → Bool) (Q → Bool) ℂ) *
        (Matrix.conjTranspose (block : Matrix (Q → Bool) (Q → Bool) ℂ) *
          finitePauliMatrix Z * (block : Matrix (Q → Bool) (Q → Bool) ℂ)) *
        (pre : Matrix (Q → Bool) (Q → Bool) ℂ) := by
          simp only [Matrix.mul_assoc]
    _ = b⁻¹ • (Matrix.conjTranspose (pre : Matrix (Q → Bool) (Q → Bool) ℂ) *
          finitePauliMatrix R * (pre : Matrix (Q → Bool) (Q → Bool) ℂ)) := by
          rw [hblockrev, Matrix.mul_smul, Matrix.smul_mul]
    _ = b⁻¹ • (a⁻¹ • finitePauliMatrix P) := by rw [hprerev]
    _ = (b * a)⁻¹ • finitePauliMatrix P := by
      rw [smul_smul]
      congr 1
      simp [mul_comm]

end

end GaloisForLFunctions.HTGeometry
