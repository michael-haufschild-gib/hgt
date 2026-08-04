import GaloisForLFunctions.HTGeometry.ProductLawBellFactorization

/-!
# Replacing the Bell rows by jet rows in the bordered determinant

The universal coefficients relating gradients of Bell values to gradients of jets are upper triangular
with unit diagonal, so truncating them to the rows actually used and transposing gives a matrix of
determinant one.  The bordered matrix of Bell gradients is therefore that matrix, bordered by an
identity row, times the bordered matrix of jet gradients — and the two determinants agree.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial

variable (Q v : ℕ → Polynomial ℂ)

/-- The evaluated Bell coefficients, truncated to the rows the bordered matrix uses. -/
noncomputable def bellCoeff (U : CascadeField) (n : ℕ) : Matrix (Fin n) (Fin n) CascadeField :=
  fun k r =>
    MvPolynomial.aeval
      (fun l : Fin (n + 1) => ((prodDerivation Q v : CascadeField → CascadeField)^[(l : ℕ)]) U)
      (bellCoordinateJacobian n k.castSucc r.castSucc)

theorem bellCoeff_triangular (U : CascadeField) (n : ℕ) :
    Matrix.BlockTriangular (bellCoeff Q v U n) id := by
  intro i j hji
  have h : bellCoordinateJacobian n i.castSucc j.castSucc = 0 := by
    refine bellCoordinateJacobian_blockTriangular n ?_
    simpa using hji
  rw [bellCoeff, h, map_zero]

theorem bellCoeff_diagonal (U : CascadeField) (n : ℕ) (i : Fin n) :
    bellCoeff Q v U n i i = 1 := by
  rw [bellCoeff, bellCoordinateJacobian_diagonal, map_one]

theorem bellCoeff_det (U : CascadeField) (n : ℕ) : (bellCoeff Q v U n).det = 1 := by
  rw [Matrix.det_of_upperTriangular (bellCoeff_triangular Q v U n)]
  simp [bellCoeff_diagonal]

/-- **The Bell gradients are the truncated combination of the jet gradients.** -/
theorem fpderiv_prodBell_succ_truncated (U : CascadeField) (n : ℕ) (r : Fin n) (j : ℕ) :
    fpderiv j (prodBell Q v U ((r : ℕ) + 1))
      = ∑ k : Fin n, bellCoeff Q v U n k r
          * fpderiv j (((prodDerivation Q v : CascadeField → CascadeField)^[(k : ℕ)]) U) := by
  have hfull := fpderiv_prodBell_succ Q v U n r.castSucc j
  rw [Fin.sum_univ_castSucc] at hfull
  have hlast : MvPolynomial.aeval
      (fun l : Fin (n + 1) => ((prodDerivation Q v : CascadeField → CascadeField)^[(l : ℕ)]) U)
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
theorem uniformBordered_bell_det_eq (U : CascadeField) (n : ℕ)
    (a : Fin (n + 1) → CascadeField) :
    (uniformBordered a
        (fun r : Fin n => fun j : Fin (n + 1) =>
          fpderiv ((j : ℕ) + 1) (prodBell Q v U ((r : ℕ) + 1)))).det
      = (uniformBordered a
        (fun k : Fin n => fun j : Fin (n + 1) =>
          fpderiv ((j : ℕ) + 1)
            (((prodDerivation Q v : CascadeField → CascadeField)^[(k : ℕ)]) U))).det := by
  classical
  set J : Matrix (Fin (n + 1)) (Fin (n + 1)) CascadeField :=
    uniformBordered a (fun k : Fin n => fun j : Fin (n + 1) =>
      fpderiv ((j : ℕ) + 1)
        (((prodDerivation Q v : CascadeField → CascadeField)^[(k : ℕ)]) U)) with hJ
  set D : Matrix (Fin (n + 1)) (Fin (n + 1)) CascadeField :=
    Matrix.of fun i i' =>
      Fin.cases (Fin.cases (1 : CascadeField) (fun _ => 0) i')
        (fun r => Fin.cases (0 : CascadeField) (fun k => bellCoeff Q v U n k r) i') i with hD
  have hprod : uniformBordered a
      (fun r : Fin n => fun j : Fin (n + 1) =>
        fpderiv ((j : ℕ) + 1) (prodBell Q v U ((r : ℕ) + 1))) = D * J := by
    funext i j
    rw [Matrix.mul_apply]
    refine Fin.cases ?_ (fun r => ?_) i
    · rw [Fin.sum_univ_succ]
      simp [hD, hJ, uniformBordered]
    · rw [Fin.sum_univ_succ]
      simp only [hD, hJ, uniformBordered, Matrix.of_apply, Fin.cases_succ, Fin.cases_zero,
        zero_mul, zero_add]
      exact fpderiv_prodBell_succ_truncated Q v U n r ((j : ℕ) + 1)
  rw [hprod, Matrix.det_mul]
  have hdetD : D.det = 1 := by
    rw [Matrix.det_succ_row_zero]
    have hzero : ∀ j : Fin (n + 1), j ≠ 0 → D 0 j = 0 := by
      intro j hj
      refine Fin.cases ?_ (fun j' => ?_) j
      · exact (hj rfl).elim
      · simp [hD]
    rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · have h00 : D 0 0 = 1 := by simp [hD]
      rw [h00]
      have hminor : (D.submatrix Fin.succ (Fin.succAbove 0)) = (bellCoeff Q v U n).transpose := by
        funext r k
        simp [hD, Matrix.submatrix]
      rw [hminor, Matrix.det_transpose, bellCoeff_det]
      simp
    · intro j _ hj
      rw [hzero j hj]
      simp
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin (n + 1))) h
  rw [hdetD, one_mul]

end GaloisForLFunctions.HTGeometry
