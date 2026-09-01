import GaloisForLFunctions.HTGeometry.DerivationTerminalLinearJacobian
import GaloisForLFunctions.HTGeometry.UniformScaledDeterminant

/-!
# The unconditional bordered reduction of a terminal-linear output jet

For an output `H` with `δ H = U · H` the positive jets are `δ^(i+1) H = H · B_i`, so every gradient
splits as `H · ∂_j B_i + B_i · ∂_j H`.  Subtracting the Bell multiple of the border row `∂_j H`
removes the second summand from every later row without touching the determinant, and the surviving
common factor `H` comes out of each of them.  Replacing the Bell gradients by the gradients of the
jets of `U` costs a unitriangular change of rows.

The outcome is an identity with **no hypothesis beyond the law `δ H = U · H`**:

`det (∂_j δ^i H) = H^(n+1) · det (border row `∂_j H`, rows `∂_j δ^s U`)`.

The terminal-scaled reduction of `DerivationTerminalLinearJacobian` is the special case in which one
coordinate kills every jet of `U`, so that the bordered determinant expands along that column.  When
no coordinate does — the situation of a cascade whose top level is only asymptotically linear — the
bordered form is still available and is the correct object to iterate.
-/

noncomputable section

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- The evaluated Bell coefficients of a derivation frame: the entry `(k, r)` is the coefficient of
the `k`-th jet of `U` in the gradient of the `r`-th Bell value. -/
def derivationBellCoeff (δ : Derivation ℂ R R) (U : R) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun k r => aeval (fun l : Fin (n + 1) => ((δ : R → R)^[(l : ℕ)]) U)
    (bellCoordinateJacobian n k r)

theorem derivationBellCoeff_blockTriangular (δ : Derivation ℂ R R) (U : R) (n : ℕ) :
    Matrix.BlockTriangular (derivationBellCoeff δ U n) id := by
  intro i j hji
  rw [derivationBellCoeff, bellCoordinateJacobian_blockTriangular n hji, map_zero]

theorem derivationBellCoeff_diagonal (δ : Derivation ℂ R R) (U : R) (n : ℕ) (i : Fin (n + 1)) :
    derivationBellCoeff δ U n i i = 1 := by
  rw [derivationBellCoeff, bellCoordinateJacobian_diagonal, map_one]

/-- **The Bell coefficient matrix has determinant one.** -/
theorem derivationBellCoeff_det (δ : Derivation ℂ R R) (U : R) (n : ℕ) :
    (derivationBellCoeff δ U n).det = 1 := by
  rw [Matrix.det_of_upperTriangular (derivationBellCoeff_blockTriangular δ U n)]
  simp [derivationBellCoeff_diagonal]

/-- **Every gradient of a Bell value is the Bell combination of the gradients of the jets.** -/
theorem derivation_derivationBellValue (δ : Derivation ℂ R R) (D : Derivation ℂ R R)
    (U : R) (n : ℕ) (r : Fin (n + 1)) :
    D (derivationBellValue δ U n r)
      = ∑ k : Fin (n + 1), derivationBellCoeff δ U n k r * D (((δ : R → R)^[(k : ℕ)]) U) := by
  rw [derivationBellValue, derivation_aeval_eq_sum_pderiv]
  rfl

/-- The output-jet Jacobian is the uniformly scaled matrix built from the border row `∂_j H`, the
Bell values, and the Bell gradients. -/
theorem derivationIterateOutputJacobian_eq_uniformScaled
    (δ : Derivation ℂ R R) (n : ℕ) (partials : Fin (n + 2) → Derivation ℂ R R) (H U : R)
    (hδH : δ H = U * H) :
    derivationIterateOutputJacobian δ n partials H
      = uniformScaledMatrix H (fun j => partials j H)
          (fun r : Fin (n + 1) => derivationBellValue δ U n r)
          (fun r : Fin (n + 1) => fun j : Fin (n + 2) =>
            partials j (derivationBellValue δ U n r)) := by
  funext i j
  refine Fin.cases ?_ (fun r => ?_) i
  · simp [derivationIterateOutputJacobian, uniformScaledMatrix]
  · rw [derivationIterateOutputJacobian,
      show ((r.succ : Fin (n + 2)) : ℕ) = (r : ℕ) + 1 by simp,
      derivation_iterate_terminalLinear_eq_derivationBellValue δ H U hδH n r,
      Derivation.leibniz]
    simp [uniformScaledMatrix, smul_eq_mul]

/-- **The bordered jet determinant, with no hypothesis beyond the law.**  The Bell rows are
replaced by the jet rows at the cost of a unitriangular matrix, whose determinant is one. -/
theorem uniformBordered_derivationBell_det_eq
    (δ : Derivation ℂ R R) (n : ℕ) (partials : Fin (n + 2) → Derivation ℂ R R) (U : R)
    (a : Fin (n + 2) → R) :
    (uniformBordered a (fun r : Fin (n + 1) => fun j : Fin (n + 2) =>
        partials j (derivationBellValue δ U n r))).det
      = (uniformBordered a (fun k : Fin (n + 1) => fun j : Fin (n + 2) =>
        partials j (((δ : R → R)^[(k : ℕ)]) U))).det := by
  classical
  set J : Matrix (Fin (n + 2)) (Fin (n + 2)) R :=
    uniformBordered a (fun k : Fin (n + 1) => fun j : Fin (n + 2) =>
      partials j (((δ : R → R)^[(k : ℕ)]) U)) with hJ
  set D : Matrix (Fin (n + 2)) (Fin (n + 2)) R :=
    Matrix.of fun i i' =>
      Fin.cases (Fin.cases (1 : R) (fun _ => 0) i')
        (fun r => Fin.cases (0 : R) (fun k => derivationBellCoeff δ U n k r) i') i with hD
  have hprod : uniformBordered a (fun r : Fin (n + 1) => fun j : Fin (n + 2) =>
      partials j (derivationBellValue δ U n r)) = D * J := by
    funext i j
    rw [Matrix.mul_apply]
    refine Fin.cases ?_ (fun r => ?_) i
    · rw [Fin.sum_univ_succ]
      simp [hD, hJ, uniformBordered]
    · rw [Fin.sum_univ_succ]
      simp only [hD, hJ, uniformBordered, Matrix.of_apply, Fin.cases_succ, Fin.cases_zero,
        zero_mul, zero_add]
      exact derivation_derivationBellValue δ (partials j) U n r
  rw [hprod, Matrix.det_mul]
  have hdetD : D.det = 1 := by
    rw [Matrix.det_succ_row_zero]
    have hzero : ∀ j : Fin (n + 2), j ≠ 0 → D 0 j = 0 := by
      intro j hj
      obtain ⟨j', rfl⟩ : ∃ j' : Fin (n + 1), j = j'.succ := by
        rcases Fin.eq_zero_or_eq_succ j with h | h
        · exact absurd h hj
        · exact h
      simp [hD]
    rw [Finset.sum_eq_single (0 : Fin (n + 2))]
    · have h00 : D 0 0 = 1 := by simp [hD]
      rw [h00]
      have hminor : (D.submatrix Fin.succ (Fin.succAbove 0))
          = (derivationBellCoeff δ U n).transpose := by
        funext r k
        simp [hD, Matrix.submatrix]
      rw [hminor, Matrix.det_transpose, derivationBellCoeff_det]
      simp
    · intro j _ hj
      rw [hzero j hj]
      simp
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin (n + 2))) h
  rw [hdetD, one_mul]

/-- **The unconditional bordered reduction.**  For any output obeying a terminal-linear law, the
output-jet determinant is a power of the output times the determinant of the matrix whose border row
is the gradient of the output and whose remaining rows are the gradients of the jets of the
multiplier.  No coordinate is required to kill anything. -/
theorem derivationIterateOutputJacobian_det_uniformBordered
    (δ : Derivation ℂ R R) (n : ℕ) (partials : Fin (n + 2) → Derivation ℂ R R) (H U : R)
    (hδH : δ H = U * H) :
    (derivationIterateOutputJacobian δ n partials H).det
      = H ^ (n + 1) *
        (uniformBordered (fun j => partials j H)
          (fun k : Fin (n + 1) => fun j : Fin (n + 2) =>
            partials j (((δ : R → R)^[(k : ℕ)]) U))).det := by
  rw [derivationIterateOutputJacobian_eq_uniformScaled δ n partials H U hδH,
    uniformScaledMatrix_det, uniformBordered_derivationBell_det_eq]

/-- Nonvanishing of the bordered determinant certifies nonvanishing of the output-jet
determinant. -/
theorem derivationIterateOutputJacobian_det_ne_zero_of_uniformBordered
    {R : Type*} [CommRing R] [IsDomain R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ) (partials : Fin (n + 2) → Derivation ℂ R R) (H U : R)
    (hδH : δ H = U * H) (hH : H ≠ 0)
    (hdet : (uniformBordered (fun j => partials j H)
      (fun k : Fin (n + 1) => fun j : Fin (n + 2) =>
        partials j (((δ : R → R)^[(k : ℕ)]) U))).det ≠ 0) :
    (derivationIterateOutputJacobian δ n partials H).det ≠ 0 := by
  rw [derivationIterateOutputJacobian_det_uniformBordered δ n partials H U hδH]
  exact mul_ne_zero (pow_ne_zero _ hH) hdet

end GaloisForLFunctions.HTGeometry

end
