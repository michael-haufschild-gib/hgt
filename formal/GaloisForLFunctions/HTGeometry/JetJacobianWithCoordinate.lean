import GaloisForLFunctions.HTGeometry.PolynomialCascadeModel
import GaloisForLFunctions.HTGeometry.JacobianDomainCriterion

/-!
# The coordinate contributes a unit column

The family the analytic transfer needs is the coordinate together with the jets of a state.  Its
Jacobian against the coordinate derivations has a unit **column** — the coordinate's own column — so
expanding there reduces the determinant to the jets' Jacobian against the higher derivations, with no
condition on how the jets depend on the coordinate.

That is a small improvement on the tower's argument, which expanded along the corresponding row and so
needed the jets to be free of the coordinate; the product law of a general first-order linear cascade
is not.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {δ : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ)}

/-- **Algebraic independence of the coordinate together with the jets.** -/
theorem algebraicIndependent_cons_of_jetDet {N m : ℕ}
    (hdet : (Matrix.of fun i j : Fin (m + 1) =>
        (MvPolynomial.pderiv ((i : ℕ) + 1)) (modelJet δ N (j : ℕ))).det ≠ 0) :
    AlgebraicIndependent ℂ
      (Fin.cons (MvPolynomial.X (0 : ℕ))
        (fun j : Fin (m + 1) => modelJet δ N (j : ℕ)) : Fin (m + 2) → MvPolynomial ℕ ℂ) := by
  classical
  set v : Fin (m + 2) → MvPolynomial ℕ ℂ :=
    Fin.cons (MvPolynomial.X (0 : ℕ)) (fun j : Fin (m + 1) => modelJet δ N (j : ℕ)) with hv
  set M : Matrix (Fin (m + 2)) (Fin (m + 2)) (MvPolynomial ℕ ℂ) :=
    Matrix.of fun i j => (MvPolynomial.pderiv ((i : ℕ))) (v j) with hM
  have hcol0 : ∀ i : Fin (m + 2), M i 0 = if i = 0 then 1 else 0 := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simp [hM, hv]
    · intro l
      have hne : (Fin.succ l : Fin (m + 2)) ≠ 0 := Fin.succ_ne_zero l
      simp only [hM, hv, Matrix.of_apply, Fin.cons_zero, Fin.val_succ]
      rw [MvPolynomial.pderiv_X_of_ne (by omega : (0 : ℕ) ≠ (l : ℕ) + 1)]
      simp [hne]
  have hdetM : M.det ≠ 0 := by
    rw [Matrix.det_succ_column_zero]
    have hsum : ∑ i : Fin (m + 2), (-1) ^ (i : ℕ) * M i 0 *
        (M.submatrix i.succAbove Fin.succ).det
        = (M.submatrix (Fin.succAbove 0) Fin.succ).det := by
      rw [Finset.sum_eq_single (0 : Fin (m + 2))]
      · simp [hcol0]
      · intro i _ hi
        rw [hcol0 i]
        simp [hi]
      · intro h
        exact absurd (Finset.mem_univ (0 : Fin (m + 2))) h
    rw [hsum]
    have hsub : M.submatrix (Fin.succAbove 0) Fin.succ
        = Matrix.of fun i j : Fin (m + 1) =>
            (MvPolynomial.pderiv ((i : ℕ) + 1)) (modelJet δ N (j : ℕ)) := by
      funext i j
      simp [hM, hv, Fin.succAbove_zero]
    rw [hsub]
    exact hdet
  refine algebraicIndependent_of_domain_jacobian (K := ℂ) v
    (fun i => fun P => (MvPolynomial.pderiv ((i : ℕ))) P) ?_ ?_ ?_ M hdetM ?_
  · intro i a b
    exact map_add _ a b
  · intro i a b
    rw [Derivation.leibniz]
    simp [smul_eq_mul]
  · intro i c
    have hc : (algebraMap ℂ (MvPolynomial ℕ ℂ)) c = MvPolynomial.C c := rfl
    rw [hc, MvPolynomial.pderiv_C]
  · intro i j
    rfl

end GaloisForLFunctions.HTGeometry
