import GaloisForLFunctions.HTGeometry.SchurVariablePresentation

/-!
# The induction step for the rectangular section

Every hypothesis of the corner criterion is available for the rectangular section in the reversed
presentation: the corner is the first variable, the other entries are free of it, the corner minor is
the smaller section read two variables later, and the unit tail separates that minor from the
determinant.

So the irreducibility of a section follows from that of the section one smaller in each parameter.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K]

/-- **The induction step.**  A rectangular section is irreducible once the section one smaller in
each parameter is. -/
theorem irreducible_det_schur_step [DecidableEq K] {n' m' : ℕ} (hn : 0 < n') (hm : 0 < m')
    (hmn : m' ≤ n')
    (ih : Irreducible ((rectangularSchurToeplitz (schurVar K (n' + m' - 1)) n' m').det)) :
    Irreducible
      ((rectangularSchurToeplitz (schurVar K (n' + m' - 1 + 2)) (n' + 1) (m' + 1)).det) := by
  refine irreducible_det_of_corner_X_zero
    (M := rectangularSchurToeplitz (schurVar K (n' + m' - 1 + 2)) (n' + 1) (m' + 1))
    (r₀ := Fin.last m')
    (φ := (unitTailEval K (n' + m' - 1 + 1) (n' + 1)).toRingHom)
    (ψ := (unitTailEval K (n' + m' - 1 + 2) (n' + 1)).toRingHom)
    (hcorner := ?_) (hfree := ?_)
    (hminor := det_submatrix_eq_rename_succ)
    (hAirr := irreducible_rename_succ ih)
    (hcomp := fun p => unitTailEval_rename_succ (K := K) (L := n' + m' - 1 + 1)
      (n := n' + 1) p) (hA0 := ?_) (hdet0 := ?_)
  · rw [rectangularSchurToeplitz]
    have h0 : ((0 : Fin (m' + 1)) : ℕ) = 0 := rfl
    have hlast : ((Fin.last m' : Fin (m' + 1)) : ℕ) = m' := rfl
    rw [h0, hlast, if_pos (by omega : (0 : ℕ) ≤ n' + 1 + m'),
      show n' + 1 + m' - 0 = n' + m' - 1 + 2 by omega]
    exact schurVar_top (by omega)
  · intro i j hij
    rw [rectangularSchurToeplitz]
    by_cases hg : (j : ℕ) ≤ n' + 1 + (i : ℕ)
    · rw [if_pos hg]
      have hi := i.isLt
      have hj := j.isLt
      refine degreeOf_zero_schurVar (by omega) (by omega) ?_
      intro hcon
      refine hij ⟨Fin.ext ?_, Fin.ext ?_⟩
      · show (i : ℕ) = m'
        omega
      · show (j : ℕ) = 0
        omega
    · rw [if_neg hg, MvPolynomial.degreeOf_zero]
  · show unitTailEval K (n' + m' - 1 + 1) (n' + 1)
        (MvPolynomial.rename Fin.succ
          ((rectangularSchurToeplitz (schurVar K (n' + m' - 1)) n' m').det)) = 0
    rw [unitTailEval_rename_succ]
    exact unitTailEval_succ_det_rectangularSchurToeplitz' rfl hm hmn
  · show unitTailEval K (n' + m' - 1 + 2) (n' + 1)
        ((rectangularSchurToeplitz (schurVar K (n' + m' - 1 + 2)) (n' + 1) (m' + 1)).det) ≠ 0
    rw [unitTailEval_det_rectangularSchurToeplitz' (by omega) (by omega)]
    exact one_ne_zero

/-- **Every rectangular section with shift at least its height is irreducible.**  Induction on the
height with the difference of the parameters fixed: the corner expansion lowers both by one, the
height-one section is a single variable, and the step supplies the rest. -/
theorem irreducible_det_schur [DecidableEq K] :
    ∀ (m d : ℕ), 0 < m →
      Irreducible ((rectangularSchurToeplitz (schurVar K (m + d + m - 1)) (m + d) m).det) := by
  intro m
  induction m with
  | zero => intro d h; exact absurd h (by omega)
  | succ m ih =>
    intro d _
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      have h := irreducible_det_rectangularSchurToeplitz_one (K := K) (n := 1 + d) (by omega)
      have hpar : 0 + 1 + d = 1 + d := by omega
      rw [hpar]
      exact h
    · have hstep := irreducible_det_schur_step (K := K) (n' := m + d) (m' := m)
        (by omega) hm0 (by omega) (ih d hm0)
      have heq : m + d + m - 1 + 2 = m + 1 + d + (m + 1) - 1 := by omega
      have hpar : m + d + 1 = m + 1 + d := by omega
      rw [hpar] at hstep
      rw [← rename_finCongr_det_rectangularSchurToeplitz heq (m + 1 + d) (m + 1)]
      exact (irreducible_rename_finCongr heq _).2 hstep

/-- **The same in the natural parametrisation.** -/
theorem irreducible_det_schur_of_le [DecidableEq K] {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    Irreducible ((rectangularSchurToeplitz (schurVar K (n + m - 1)) n m).det) := by
  have h := irreducible_det_schur (K := K) m (n - m) hm
  have hpar : m + (n - m) = n := by omega
  rw [hpar] at h
  exact h

end GaloisForLFunctions.HTGeometry
