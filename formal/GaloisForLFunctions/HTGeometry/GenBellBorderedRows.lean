import GaloisForLFunctions.HTGeometry.AffineTopBellJacobian
import GaloisForLFunctions.HTGeometry.BellCoordinateJacobian
import GaloisForLFunctions.HTGeometry.UniformScaledDeterminant
import GaloisForLFunctions.HTGeometry.DerivationBellChain
import GaloisForLFunctions.HTGeometry.ProductLawFractionModel

/-!
# Replacing the Bell rows by jet rows, for any derivation

The universal coefficients relating gradients of affine Bell values to gradients of the jets of the
multiplier are upper triangular with unit diagonal, and they do not depend on which derivation is
applied.  So in a bordered determinant the Bell rows may be replaced by the jet rows without
changing the determinant.

Everything here is stated for an arbitrary derivation of the rational model, since nothing in the
argument sees the law.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial

variable (δ : Derivation ℂ CascadeField CascadeField)

/-- **The gradient of an affine Bell value is a universal combination of the gradients of the jets
of its multiplier.** -/
theorem fpderiv_genJetA_succ (U : CascadeField) (n : ℕ) (r : Fin (n + 1)) (j : ℕ) :
    fpderiv j (genJetA δ U ((r : ℕ) + 1))
      = ∑ k : Fin (n + 1),
          MvPolynomial.aeval
            (fun l : Fin (n + 1) => ((δ : CascadeField → CascadeField)^[(l : ℕ)]) U)
            (bellCoordinateJacobian n k r)
          * fpderiv j (((δ : CascadeField → CascadeField)^[(k : ℕ)]) U) := by
  rw [genJetA_eq_derivationBellValue δ U n r, derivationBellValue,
    derivation_aeval_eq_sum_pderiv]
  rfl

/-- The evaluated Bell coefficients, truncated to the rows the bordered matrix uses. -/
noncomputable def genBellCoeff (U : CascadeField) (n : ℕ) : Matrix (Fin n) (Fin n) CascadeField :=
  fun k r =>
    MvPolynomial.aeval
      (fun l : Fin (n + 1) => ((δ : CascadeField → CascadeField)^[(l : ℕ)]) U)
      (bellCoordinateJacobian n k.castSucc r.castSucc)

theorem genBellCoeff_triangular (U : CascadeField) (n : ℕ) :
    Matrix.BlockTriangular (genBellCoeff δ U n) id := by
  intro i j hji
  have h : bellCoordinateJacobian n i.castSucc j.castSucc = 0 := by
    refine bellCoordinateJacobian_blockTriangular n ?_
    simpa using hji
  rw [genBellCoeff, h, map_zero]

theorem genBellCoeff_diagonal (U : CascadeField) (n : ℕ) (i : Fin n) :
    genBellCoeff δ U n i i = 1 := by
  rw [genBellCoeff, bellCoordinateJacobian_diagonal, map_one]

theorem genBellCoeff_det (U : CascadeField) (n : ℕ) : (genBellCoeff δ U n).det = 1 := by
  rw [Matrix.det_of_upperTriangular (genBellCoeff_triangular δ U n)]
  simp [genBellCoeff_diagonal]

/-- **The Bell gradients are the truncated combination of the jet gradients.** -/
theorem fpderiv_genJetA_succ_truncated (U : CascadeField) (n : ℕ) (r : Fin n) (j : ℕ) :
    fpderiv j (genJetA δ U ((r : ℕ) + 1))
      = ∑ k : Fin n, genBellCoeff δ U n k r
          * fpderiv j (((δ : CascadeField → CascadeField)^[(k : ℕ)]) U) := by
  have hfull := fpderiv_genJetA_succ δ U n r.castSucc j
  rw [Fin.sum_univ_castSucc] at hfull
  have hlast : MvPolynomial.aeval
      (fun l : Fin (n + 1) => ((δ : CascadeField → CascadeField)^[(l : ℕ)]) U)
      (bellCoordinateJacobian n (Fin.last n) r.castSucc) = 0 := by
    have h : bellCoordinateJacobian n (Fin.last n) r.castSucc = 0 := by
      refine bellCoordinateJacobian_blockTriangular n ?_
      simp only [id_eq]
      exact r.isLt
    rw [h, map_zero]
  rw [hlast, zero_mul, add_zero] at hfull
  rw [Fin.val_castSucc] at hfull
  exact hfull

/-- **The bordered Bell determinant is the bordered jet determinant.** -/
theorem uniformBordered_genBell_det_eq (U : CascadeField) (n : ℕ)
    (a : Fin (n + 1) → CascadeField) :
    (uniformBordered a
        (fun r : Fin n => fun j : Fin (n + 1) =>
          fpderiv ((j : ℕ) + 1) (genJetA δ U ((r : ℕ) + 1)))).det
      = (uniformBordered a
        (fun k : Fin n => fun j : Fin (n + 1) =>
          fpderiv ((j : ℕ) + 1)
            (((δ : CascadeField → CascadeField)^[(k : ℕ)]) U))).det := by
  classical
  set J : Matrix (Fin (n + 1)) (Fin (n + 1)) CascadeField :=
    uniformBordered a (fun k : Fin n => fun j : Fin (n + 1) =>
      fpderiv ((j : ℕ) + 1)
        (((δ : CascadeField → CascadeField)^[(k : ℕ)]) U)) with hJ
  set D : Matrix (Fin (n + 1)) (Fin (n + 1)) CascadeField :=
    Matrix.of fun i i' =>
      Fin.cases (Fin.cases (1 : CascadeField) (fun _ => 0) i')
        (fun r => Fin.cases (0 : CascadeField) (fun k => genBellCoeff δ U n k r) i') i with hD
  have hprod : uniformBordered a
      (fun r : Fin n => fun j : Fin (n + 1) =>
        fpderiv ((j : ℕ) + 1) (genJetA δ U ((r : ℕ) + 1))) = D * J := by
    funext i j
    rw [Matrix.mul_apply]
    refine Fin.cases ?_ (fun r => ?_) i
    · rw [Fin.sum_univ_succ]
      simp [hD, hJ, uniformBordered]
    · rw [Fin.sum_univ_succ]
      simp only [hD, hJ, uniformBordered, Matrix.of_apply, Fin.cases_succ, Fin.cases_zero,
        zero_mul, zero_add]
      exact fpderiv_genJetA_succ_truncated δ U n r ((j : ℕ) + 1)
  rw [hprod, Matrix.det_mul]
  have hdetD : D.det = 1 := by
    rw [Matrix.det_succ_row_zero]
    have hzero : ∀ j : Fin (n + 1), j ≠ 0 → D 0 j = 0 := by
      intro j hj
      obtain ⟨j', rfl⟩ : ∃ j' : Fin n, j = j'.succ := by
        rcases Fin.eq_zero_or_eq_succ j with h | h
        · exact absurd h hj
        · exact h
      simp [hD]
    rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · have h00 : D 0 0 = 1 := by simp [hD]
      rw [h00]
      have hminor : (D.submatrix Fin.succ (Fin.succAbove 0)) = (genBellCoeff δ U n).transpose := by
        funext r k
        simp [hD, Matrix.submatrix]
      rw [hminor, Matrix.det_transpose, genBellCoeff_det]
      simp
    · intro j _ hj
      rw [hzero j hj]
      simp
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin (n + 1))) h
  rw [hdetD, one_mul]

end GaloisForLFunctions.HTGeometry
