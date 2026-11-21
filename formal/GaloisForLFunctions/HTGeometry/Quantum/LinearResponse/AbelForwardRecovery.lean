import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelForwardProbeCertificate

/-!
# Reconstruction from two fixed forward readings

The measured outputs determine the entries of an anchored linear
system for the Hamiltonian. Its right-hand side uses only the original
probes, their outputs, and the known damping width.
-/

open Matrix Set
open scoped Matrix Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ}

/-- Scaling both probes scales every commutator row and preserves the anchor row. -/
theorem anchoredProbeMatrix_smul (o : Fin d) (s : ℂ) (A B : Matrix (Fin d) (Fin d) ℂ) :
    anchoredProbeMatrix o (s • A) (s • B) =
      Matrix.diagonal (fun p => if p = (o, o) then 1 else s) * anchoredProbeMatrix o A B := by
  have hsmul (T : Matrix (Fin d) (Fin d) ℂ) (p q : Fin d × Fin d) :
      commutatorKroneckerMatrix (s • T) p q = s * commutatorKroneckerMatrix T p q := by
    rcases p with ⟨p₁, p₂⟩
    rcases q with ⟨q₁, q₂⟩
    simp only [commutatorKroneckerMatrix, Matrix.sub_apply, Matrix.kronecker_apply,
      Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  ext p q
  rw [Matrix.diagonal_mul]
  by_cases ho : p = (o, o)
  · simp only [anchoredProbeMatrix, Matrix.of_apply, if_pos ho, one_mul]
  · by_cases hp : p.1 = p.2
    · simp only [anchoredProbeMatrix, Matrix.of_apply, if_neg ho, if_pos hp, hsmul]
    · simp only [anchoredProbeMatrix, Matrix.of_apply, if_neg ho, if_neg hp, hsmul]

theorem abelForwardReading_det_ne_zero_of_certificate (o : Fin d) {H : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) (ε : Ioi (0 : ℝ))
    (hcert : abelForwardCertificateValue o (hamiltonianAbelShift ε)⁻¹ H
      (abelDiagonalProbe d) (abelSumProbe d) ≠ 0) :
    (anchoredProbeMatrix o (hamiltonianDampedGapResponse hH 0 ε (abelDiagonalProbe d))
      (hamiltonianDampedGapResponse hH 0 ε (abelSumProbe d))).det ≠ 0 := by
  rw [abelForwardCertificateValue, abelClearedResponse_eq hH, abelClearedResponse_eq hH,
    anchoredProbeMatrix_smul, Matrix.det_mul] at hcert
  exact (mul_ne_zero_iff.mp hcert).2

private def abelForwardRecoveryRhs (o : Fin d) (ε : Ioi (0 : ℝ))
    (A B : Matrix (Fin d) (Fin d) ℂ) (p : Fin d × Fin d) : ℂ :=
  if p = (o, o) then 0
  else if p.1 = p.2 then (abelCommutatorReadout ε (abelSumProbe d) B) p.2 o
  else (abelCommutatorReadout ε (abelDiagonalProbe d) A) p.2 p.1

/-- Recover the Hamiltonian relative to the chosen diagonal entry from the two outputs. -/
def abelForwardRelativeRecovery (o : Fin d) (ε : Ioi (0 : ℝ))
    (A B : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j =>
    ((anchoredProbeMatrix o A B)⁻¹ *ᵥ abelForwardRecoveryRhs o ε A B) (j, i)

private theorem abelForwardRelativeRecovery_linearSystem (o : Fin d)
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) (ε : Ioi (0 : ℝ)) :
    let A := hamiltonianDampedGapResponse hH 0 ε (abelDiagonalProbe d)
    let B := hamiltonianDampedGapResponse hH 0 ε (abelSumProbe d)
    anchoredProbeMatrix o A B *ᵥ (H - H o o • 1).vec = abelForwardRecoveryRhs o ε A B := by
  let T := H - H o o • 1
  have hTo : T o o = 0 := by
    simp only [T, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one, sub_self]
  have hcomm (X : Matrix (Fin d) (Fin d) ℂ) :
      let Y := hamiltonianDampedGapResponse hH 0 ε X
      Y * T - T * Y = abelCommutatorReadout ε X Y := by
    let Y := hamiltonianDampedGapResponse hH 0 ε X
    have hread : abelCommutatorReadout ε Y X = H * Y - Y * H :=
      (congrArg (abelCommutatorReadout ε Y)
        (hamiltonianAbelInverse_leftInverse hH ε X)).symm.trans
        (abelCommutatorReadout_inverse H ε Y)
    calc
      Y * T - T * Y = -(H * Y - Y * H) := by
        simp only [T, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, Matrix.one_mul]
        abel
      _ = -abelCommutatorReadout ε Y X := congrArg Neg.neg hread.symm
      _ = abelCommutatorReadout ε X Y := by
        rw [abelCommutatorReadout, abelCommutatorReadout, ← smul_neg, neg_sub]
  change anchoredProbeMatrix o (hamiltonianDampedGapResponse hH 0 ε (abelDiagonalProbe d))
    (hamiltonianDampedGapResponse hH 0 ε (abelSumProbe d)) *ᵥ T.vec = _
  funext p
  simp only [anchoredProbeMatrix_mulVec_vec, hTo, hcomm, abelForwardRecoveryRhs]

/-- The measured system reconstructs the anchored Hamiltonian whenever its
coefficient determinant is nonzero. -/
theorem abelForwardRelativeRecovery_exact (o : Fin d)
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) (ε : Ioi (0 : ℝ))
    (hdet : (anchoredProbeMatrix o (hamiltonianDampedGapResponse hH 0 ε (abelDiagonalProbe d))
      (hamiltonianDampedGapResponse hH 0 ε (abelSumProbe d))).det ≠ 0) :
    abelForwardRelativeRecovery o ε (hamiltonianDampedGapResponse hH 0 ε (abelDiagonalProbe d))
      (hamiltonianDampedGapResponse hH 0 ε (abelSumProbe d)) = H - H o o • 1 := by
  let A := hamiltonianDampedGapResponse hH 0 ε (abelDiagonalProbe d)
  let B := hamiltonianDampedGapResponse hH 0 ε (abelSumProbe d)
  let M := anchoredProbeMatrix o A B
  apply Matrix.vec_inj.mp
  change M⁻¹ *ᵥ abelForwardRecoveryRhs o ε A B = (H - H o o • 1).vec
  rw [← abelForwardRelativeRecovery_linearSystem o hH ε, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

#print axioms abelForwardReading_det_ne_zero_of_certificate
#print axioms abelForwardRelativeRecovery_exact

end

end GaloisForLFunctions.HTGeometry
