import GaloisForLFunctions.HTGeometry.JacobianDomainCriterion
import GaloisForLFunctions.HTGeometry.ProductLawFractionModel

/-!
# The coordinate contributes a unit column, in the rational model

The family the analytic transfer needs is the base coordinate together with the jets of a state.  In
the rational model the same argument works: its Jacobian against the coordinate derivations has a
unit *column* — the base coordinate's own — so expanding there reduces the determinant to the jets'
Jacobian against the higher derivations, with no condition on how the jets depend on the base
coordinate.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {δ : Derivation ℂ CascadeField CascadeField}

/-- **Algebraic independence of the base coordinate together with the jets, in the rational
model.** -/
theorem algebraicIndependent_cons_of_fieldJetDet {N m : ℕ}
    (hdet : (Matrix.of fun i j : Fin (m + 1) =>
        fpderiv ((i : ℕ) + 1)
          (((δ : CascadeField → CascadeField)^[(j : ℕ)]) (fx N))).det ≠ 0) :
    AlgebraicIndependent ℂ
      (Fin.cons (fx 0)
        (fun j : Fin (m + 1) => ((δ : CascadeField → CascadeField)^[(j : ℕ)]) (fx N))
        : Fin (m + 2) → CascadeField) := by
  classical
  set v : Fin (m + 2) → CascadeField :=
    Fin.cons (fx 0)
      (fun j : Fin (m + 1) => ((δ : CascadeField → CascadeField)^[(j : ℕ)]) (fx N)) with hv
  set M : Matrix (Fin (m + 2)) (Fin (m + 2)) CascadeField :=
    Matrix.of fun i j => fpderiv ((i : ℕ)) (v j) with hM
  have hcol0 : ∀ i : Fin (m + 2), M i 0 = if i = 0 then 1 else 0 := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simp [hM, hv]
    · intro l
      have hne : (Fin.succ l : Fin (m + 2)) ≠ 0 := Fin.succ_ne_zero l
      simp only [hM, hv, Matrix.of_apply, Fin.cons_zero, Fin.val_succ]
      rw [fpderiv_fx_of_ne (by omega : (0 : ℕ) ≠ (l : ℕ) + 1)]
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
            fpderiv ((i : ℕ) + 1)
              (((δ : CascadeField → CascadeField)^[(j : ℕ)]) (fx N)) := by
      funext i j
      simp [hM, hv, Fin.succAbove_zero]
    rw [hsub]
    exact hdet
  refine algebraicIndependent_of_domain_jacobian (K := ℂ) v
    (fun i => fun P => fpderiv ((i : ℕ)) P) ?_ ?_ ?_ M hdetM ?_
  · intro i a b
    exact map_add _ a b
  · intro i a b
    rw [Derivation.leibniz]
    simp [smul_eq_mul]
  · intro i c
    exact (fpderiv (i : ℕ)).map_algebraMap c
  · intro i j
    rfl

/-- **The output-jet determinant in its `Fin.lastCases` shape gives independence.** -/
theorem algebraicIndependent_cons_of_output {m : ℕ}
    (hdet : (Matrix.of fun i j : Fin (m + 1) =>
        Fin.lastCases (motive := fun _ => CascadeField)
          (fpderiv (m + 1) (((δ : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
          (fun j' : Fin m => fpderiv ((j' : ℕ) + 1)
            (((δ : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
          j).det ≠ 0) :
    AlgebraicIndependent ℂ
      (Fin.cons (fx 0)
        (fun j : Fin (m + 1) => ((δ : CascadeField → CascadeField)^[(j : ℕ)]) (fx (m + 1)))
        : Fin (m + 2) → CascadeField) := by
  refine algebraicIndependent_cons_of_fieldJetDet (δ := δ) (N := m + 1) ?_
  have hshape : (Matrix.of fun i j : Fin (m + 1) =>
      fpderiv ((j : ℕ) + 1)
        (((δ : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
      = Matrix.of fun i j : Fin (m + 1) =>
        Fin.lastCases (motive := fun _ => CascadeField)
          (fpderiv (m + 1) (((δ : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
          (fun j' : Fin m => fpderiv ((j' : ℕ) + 1)
            (((δ : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
          j := by
    funext i j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · show fpderiv (((Fin.last m : Fin (m + 1)) : ℕ) + 1)
          (((δ : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1)))
        = Fin.lastCases (motive := fun _ => CascadeField)
            (fpderiv (m + 1) (((δ : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
            (fun j'' : Fin m => fpderiv ((j'' : ℕ) + 1)
              (((δ : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
            (Fin.last m)
      rw [Fin.lastCases_last, Fin.val_last]
    · show fpderiv (((j'.castSucc : Fin (m + 1)) : ℕ) + 1)
          (((δ : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1)))
        = Fin.lastCases (motive := fun _ => CascadeField)
            (fpderiv (m + 1) (((δ : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
            (fun j'' : Fin m => fpderiv ((j'' : ℕ) + 1)
              (((δ : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
            j'.castSucc
      rw [Fin.lastCases_castSucc, Fin.val_castSucc]
  have htrans : (Matrix.of fun i j : Fin (m + 1) =>
      fpderiv ((i : ℕ) + 1)
        (((δ : CascadeField → CascadeField)^[(j : ℕ)]) (fx (m + 1))))
      = (Matrix.of fun i j : Fin (m + 1) =>
        fpderiv ((j : ℕ) + 1)
          (((δ : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1)))).transpose := by
    funext i j
    rfl
  rw [htrans, Matrix.det_transpose, hshape]
  exact hdet

end GaloisForLFunctions.HTGeometry
