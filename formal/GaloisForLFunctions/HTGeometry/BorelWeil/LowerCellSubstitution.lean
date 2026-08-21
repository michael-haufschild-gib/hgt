import GaloisForLFunctions.HTGeometry.BorelWeil.CellTrivialization

/-!
# Restricting to the big cell

The big cell of the flag variety is the affine space of lower unitriangular matrices, and
restricting a polynomial to it is the substitution `lowerSubst` sending the strictly lower variables
to themselves, the diagonal ones to `1` and the strictly upper ones to `0`.  All leading minors of a
lower unitriangular matrix are `1`, so the cell equation of the identity cell restricts to `1`; and
because the intersection of all the Bruhat cells meets the big cell, the whole cover equation
restricts to a nonzero polynomial.

## Main definitions

* `lowerMat`, `lowerSubst`

## Main results

* `leadingMinorMat_of_isLowerUni` — the leading minors of a lower unitriangular matrix are `1`.
* `exists_isLowerUni_matEval_totalDenom_ne_zero` — the big cell meets every Bruhat cell.
* `lowerSubst_totalDenom_ne_zero` — the cover equation does not vanish on the big cell.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- The lower unitriangular matrix built from the strictly lower entries of a matrix. -/
def lowerMat {R : Type*} [CommRing R] (g : Matrix (Fin N) (Fin N) R) :
    Matrix (Fin N) (Fin N) R :=
  Matrix.of fun i j => if (j : ℕ) < (i : ℕ) then g i j else if i = j then 1 else 0

theorem isLowerUni_lowerMat (g : Matrix (Fin N) (Fin N) k) : IsLowerUni (lowerMat g) := by
  constructor
  · intro i j hij
    have h1 : ¬ ((j : ℕ) < (i : ℕ)) := by
      have : (i : ℕ) < (j : ℕ) := hij
      omega
    have h2 : i ≠ j := ne_of_lt hij
    rw [lowerMat]
    simp only [Matrix.of_apply, if_neg h1, if_neg h2]
  · intro i
    rw [lowerMat]
    simp only [Matrix.of_apply, if_neg (by omega : ¬ ((i : ℕ) < (i : ℕ)))]
    simp

theorem lowerMat_of_isLowerUni {L : Matrix (Fin N) (Fin N) k} (hL : IsLowerUni L) :
    lowerMat L = L := by
  ext i j
  rw [lowerMat]
  simp only [Matrix.of_apply]
  by_cases h1 : (j : ℕ) < (i : ℕ)
  · rw [if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : i = j
    · rw [if_pos h2, h2, hL.2]
    · rw [if_neg h2]
      refine (hL.1 i j ?_).symm
      have : i ≠ j := h2
      rcases lt_or_gt_of_ne this with h | h
      · exact h
      · exact absurd (show (j : ℕ) < (i : ℕ) from h) h1

/-- Restriction of a polynomial function to the big cell. -/
noncomputable def lowerSubst :
    MvPolynomial (Fin N × Fin N) k →ₐ[k] MvPolynomial (Fin N × Fin N) k :=
  MvPolynomial.aeval fun ij : Fin N × Fin N =>
    if (ij.2 : ℕ) < (ij.1 : ℕ) then MvPolynomial.X ij
    else if ij.1 = ij.2 then 1 else 0

theorem matEval_lowerSubst (g : Matrix (Fin N) (Fin N) k) (p : MvPolynomial (Fin N × Fin N) k) :
    matEval g (lowerSubst p) = matEval (lowerMat g) p := by
  have hcomp : (MvPolynomial.eval fun ij : Fin N × Fin N => g ij.1 ij.2).comp
      (lowerSubst (k := k) (N := N)).toRingHom
      = MvPolynomial.eval fun ij : Fin N × Fin N => (lowerMat g) ij.1 ij.2 := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [lowerSubst]
    · intro ij
      simp only [RingHom.comp_apply, MvPolynomial.eval_X]
      show MvPolynomial.eval (fun ij : Fin N × Fin N => g ij.1 ij.2)
        (lowerSubst (MvPolynomial.X ij)) = _
      rw [lowerSubst, MvPolynomial.aeval_X]
      by_cases h1 : (ij.2 : ℕ) < (ij.1 : ℕ)
      · rw [if_pos h1, MvPolynomial.eval_X, lowerMat]
        simp only [Matrix.of_apply, if_pos h1]
      · rw [if_neg h1, lowerMat]
        simp only [Matrix.of_apply, if_neg h1]
        by_cases h2 : ij.1 = ij.2 <;> simp [h2]
  exact congrFun (congrArg (fun φ : MvPolynomial (Fin N × Fin N) k →+* k => (φ : _ → k)) hcomp) p

/-- **The leading minors of a lower unitriangular matrix are `1`.** -/
theorem leadingMinorMat_of_isLowerUni {L : Matrix (Fin N) (Fin N) k} (hL : IsLowerUni L) (j : ℕ) :
    leadingMinorMat j L = 1 := by
  classical
  have htri : (truncate j L).BlockTriangular (OrderDual.toDual : Fin N → (Fin N)ᵒᵈ) := by
    intro r c hrc
    have hlt : r < c := hrc
    by_cases h1 : (r : ℕ) < j
    · by_cases h2 : (c : ℕ) < j
      · rw [truncate_apply_of_both h1 h2]
        exact hL.1 r c hlt
      · rw [truncate_apply_of_not_right h2, if_neg (ne_of_lt hlt)]
    · rw [truncate_apply_of_not_left h1, if_neg (ne_of_lt hlt)]
  have hdiag : ∀ i : Fin N, (truncate j L) i i = 1 := by
    intro i
    by_cases h1 : (i : ℕ) < j
    · rw [truncate_apply_of_both h1 h1, hL.2]
    · rw [truncate_apply_of_not_left h1, if_pos rfl]
  rw [leadingMinorMat, Matrix.det_of_lowerTriangular _ htri]
  rw [Finset.prod_congr rfl fun i _ => hdiag i, Finset.prod_const_one]

theorem matEval_cellDenomPoly_one_of_isLowerUni {L : Matrix (Fin N) (Fin N) k}
    (hL : IsLowerUni L) : matEval L (cellDenomPoly N k (1 : Equiv.Perm (Fin N))) = 1 := by
  classical
  rw [cellDenomPoly, matEval_prod]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [matEval_minorPolyAt]
  have hsub : L.submatrix (⇑(1 : Equiv.Perm (Fin N))) id = L := by
    ext r s
    rfl
  rw [hsub, leadingMinorMat_of_isLowerUni hL]

/-- **The big cell meets every Bruhat cell.** -/
theorem exists_isLowerUni_matEval_totalDenom_ne_zero :
    ∃ L : Matrix (Fin N) (Fin N) k, IsLowerUni L ∧ matEval L (totalDenom N k) ≠ 0 := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : Matrix (Fin N) (Fin N) k, matEval g (totalDenom N k) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact totalDenom_ne_zero (matEval_injective fun g => by rw [hcon g]; simp [matEval])
  obtain ⟨L, B, hL, hB, rfl⟩ := exists_lu_of_matEval_totalDenom_ne_zero hg
  refine ⟨L, hL, ?_⟩
  intro hzero
  exact hg (by rw [matEval_totalDenom_mul hB, hzero, mul_zero])

/-- **The cover equation does not vanish on the big cell.** -/
theorem lowerSubst_totalDenom_ne_zero : lowerSubst (totalDenom N k) ≠ 0 := by
  obtain ⟨L, hL, hne⟩ := exists_isLowerUni_matEval_totalDenom_ne_zero (N := N) (k := k)
  intro hzero
  refine hne ?_
  have := matEval_lowerSubst L (totalDenom N k)
  rw [hzero, lowerMat_of_isLowerUni hL] at this
  rw [← this]
  simp [matEval]

end GaloisForLFunctions.HTGeometry.BorelWeil
