import GaloisForLFunctions.RHTower.PaperPrimeRotationCompression
import GaloisForLFunctions.HTGeometry.FiniteBilateralWeightedShiftGram

/-! # Ordinary determinant blindness and the surviving native Gram determinant -/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry HilbertSchmidt _root_.ContinuousLinearMap

theorem paperPrimeRotationCompression_traceCost_zero (p : Nat.Primes) (q N : ℕ) :
    compactOperatorTraceCost PaperRotationHilbert (paperPrimeRotationCompression p q N) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (paperPrimeRotationCompression_compact p q N)

theorem paperPrimeRotationCompression_opTrace (p : Nat.Primes) (q N : ℕ) :
    opTrace (paperPrimeRotationCompression p q N) = 0 := by
  rw [paperPrimeRotationCompression_eq_weightedShift, opTrace_finiteBilateralWeightedShift]

theorem paperPrimeRotationCompression_fredholmDet (p : Nat.Primes) (q N : ℕ) :
    fredholmDetOp (lpBasis ℤ) (paperPrimeRotationCompression p q N) = 1 := by
  rw [paperPrimeRotationCompression_eq_weightedShift, fredholmDetOp_finiteBilateralWeightedShift]

theorem paperPrimeRotationCompression_smul_fredholmDet (p : Nat.Primes) (q N : ℕ) (z : ℂ) :
    fredholmDetOp (lpBasis ℤ) (z • paperPrimeRotationCompression p q N) = 1 := by
  have hc (i j : ℤ) : coordMatrix (lpBasis ℤ) (z • paperPrimeRotationCompression p q N) (i, j) =
      z * coordMatrix (lpBasis ℤ)
        (finiteBilateralWeightedShift N (paperPrimeRotationEdgeWeight p q)) (i, j) := by
    rw [paperPrimeRotationCompression_eq_weightedShift]
    simp only [coordMatrix_apply, smul_apply, inner_smul_right]
  apply fredholmDetOp_eq_one_of_strict_lower (lpBasis ℤ)
    (memSchattenClass_one_smul (paperPrimeRotationCompression_traceClass p q N) z)
    (bilateralShiftWindow N)
  · rintro ⟨i, j⟩ h
    rw [hc, finiteBilateralWeightedShift_coordinate_support N _ (i, j) h, mul_zero]
  · intro i j h
    rw [hc, finiteBilateralWeightedShift_strict_lower N _ i j h, mul_zero]

theorem paperPrimeRotationCompression_gram_traceClass (p : Nat.Primes) (q N : ℕ) :
    MemSchattenClass 1
      ((paperPrimeRotationCompression p q N).adjoint ∘L paperPrimeRotationCompression p q N) :=
  memSchattenClass_one_comp_left (paperPrimeRotationCompression_traceClass p q N) _

theorem paperPrimeRotationCompression_gram_eq (p : Nat.Primes) (q N : ℕ) :
    (paperPrimeRotationCompression p q N).adjoint ∘L paperPrimeRotationCompression p q N =
      (‖paperPrimeRotationCommutator p q 0 1 1 0‖ ^ 2 : ℂ) •
        coordTruncation (bilateralShiftEdges N) := by
  rw [paperPrimeRotationCompression_eq_weightedShift]
  apply HasLpMatrix.ext (K := fun i j =>
    if i = j ∧ j ∈ bilateralShiftEdges N
    then (‖paperPrimeRotationCommutator p q 0 1 1 0‖ ^ 2 : ℂ) else 0)
  · intro i j
    have h := coordMatrix_finiteBilateralWeightedShift_gram N
      (paperPrimeRotationEdgeWeight p q) i j
    rw [coordMatrix_apply, lpBasis_apply, lpBasis_apply] at h
    change inner ℂ (lpBasisVec i)
      (((finiteBilateralWeightedShift N (paperPrimeRotationEdgeWeight p q)).adjoint ∘L
        finiteBilateralWeightedShift N (paperPrimeRotationEdgeWeight p q)) (lpBasisVec j)) = _ at h
    rw [inner_lpBasisVec] at h
    simpa [paperPrimeRotationEdgeWeight_norm, paperPrimeRotationCommutator_norm] using h
  · intro i j
    rw [smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, coordTruncation_apply_coordinate]
    by_cases h : i = j
    · subst i
      simp [lpBasisVec, lp.single_apply]
    · simp [lpBasisVec, lp.single_apply, h]

theorem paperPrimeRotationCompression_gram_fredholmDet (p : Nat.Primes) (q N : ℕ) :
    fredholmDetOp (lpBasis ℤ)
      ((paperPrimeRotationCompression p q N).adjoint ∘L paperPrimeRotationCompression p q N) =
      (1 + (‖paperPrimeRotationCommutator p q 0 1 1 0‖ ^ 2 : ℝ) : ℂ) ^ N := by
  rw [paperPrimeRotationCompression_eq_weightedShift,
    fredholmDetOp_finiteBilateralWeightedShift_gram]
  simp [paperPrimeRotationEdgeWeight_norm, paperPrimeRotationCommutator_norm,
    bilateralShiftEdges, Int.card_Ico]

end
end RHTower
