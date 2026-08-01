import GaloisForLFunctions.HTGeometry.DualRectangularSection

/-!
# The cofactor locus is proper inside the section divisor

A rectangular section is linear in the first variable: that variable occupies the corner entry and no
other, so the section is the corner cofactor times the variable plus a remainder free of it.  The
cofactor is the smaller section, which is irreducible and in particular nonzero, so the section has
degree exactly one in the first variable while the cofactor has degree zero.

Divisibility cannot lower the degree in a variable, so the section does not divide its corner
cofactor: the locus where that cofactor vanishes is a proper closed subset of the divisor the section
cuts out.  Since the section is irreducible it is also squarefree, so that divisor is reduced.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K]

/-! ## Divisibility and the degree in the first variable -/

/-- **Divisibility does not lower the degree in the first variable.** -/
theorem degreeOf_le_of_dvd {N : ℕ} {p q : MvPolynomial (Fin (N + 1)) K} (hpq : p ∣ q) (hq : q ≠ 0) :
    MvPolynomial.degreeOf 0 p ≤ MvPolynomial.degreeOf 0 q := by
  rw [← MvPolynomial.natDegree_finSuccEquiv, ← MvPolynomial.natDegree_finSuccEquiv]
  refine Polynomial.natDegree_le_of_dvd (map_dvd _ hpq) ?_
  simpa using hq

/-- **A polynomial in the later variables has degree zero in the first one.** -/
theorem degreeOf_zero_rename_succ {N : ℕ} (p : MvPolynomial (Fin N) K) :
    MvPolynomial.degreeOf 0 (MvPolynomial.rename Fin.succ p) = 0 := by
  rw [← MvPolynomial.natDegree_finSuccEquiv, finSuccEquiv_rename_succ, Polynomial.natDegree_C]

/-- **Adjoining a variable does not create a zero.** -/
theorem rename_succ_ne_zero {N : ℕ} {p : MvPolynomial (Fin N) K} (hp : p ≠ 0) :
    MvPolynomial.rename (R := K) Fin.succ p ≠ 0 := fun hcon =>
  hp ((map_eq_zero_iff _ (MvPolynomial.rename_injective _ (Fin.succ_injective _))).1 hcon)

/-! ## The corner of a rectangular section -/

/-- **The corner entry of a rectangular section is the first variable.** -/
theorem rectangularSchur_corner {n' m' : ℕ} (hn : 0 < n') :
    rectangularSchurToeplitz (schurVar K (n' + m' - 1 + 2)) (n' + 1) (m' + 1)
        (Fin.last m') 0 = MvPolynomial.X 0 := by
  rw [rectangularSchurToeplitz]
  have h0 : ((0 : Fin (m' + 1)) : ℕ) = 0 := rfl
  have hlast : ((Fin.last m' : Fin (m' + 1)) : ℕ) = m' := rfl
  rw [h0, hlast, if_pos (by omega : (0 : ℕ) ≤ n' + 1 + m'),
    show n' + 1 + m' - 0 = n' + m' - 1 + 2 by omega]
  exact schurVar_top (by omega)

/-- **No other entry involves the first variable.** -/
theorem rectangularSchur_free {n' m' : ℕ} (i j : Fin (m' + 1))
    (hij : ¬ (i = Fin.last m' ∧ j = 0)) :
    MvPolynomial.degreeOf 0
      (rectangularSchurToeplitz (schurVar K (n' + m' - 1 + 2)) (n' + 1) (m' + 1) i j) = 0 := by
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

/-- **The corner cofactor is nonzero**, being the image of the smaller section, which is
irreducible. -/
theorem det_submatrix_rectangularSchur_ne_zero [DecidableEq K] {n' m' : ℕ} (hn : 0 < n')
    (hm : 0 < m') :
    ((rectangularSchurToeplitz (schurVar K (n' + m' - 1 + 2)) (n' + 1) (m' + 1)).submatrix
        (Fin.last m').succAbove Fin.succ).det ≠ 0 := by
  rw [det_submatrix_eq_rename_succ]
  exact rename_succ_ne_zero
    (rename_succ_ne_zero (irreducible_det_rectangularSchurToeplitz (K := K) hn hm).ne_zero)

/-- **A rectangular section has degree exactly one in the first variable.**  The corner expansion
writes it as the variable times the corner cofactor plus a remainder free of the variable, and the
cofactor is nonzero. -/
theorem degreeOf_zero_det_rectangularSchur [DecidableEq K] {n' m' : ℕ} (hn : 0 < n') (hm : 0 < m') :
    MvPolynomial.degreeOf 0
      ((rectangularSchurToeplitz (schurVar K (n' + m' - 1 + 2)) (n' + 1) (m' + 1)).det) = 1 := by
  classical
  obtain ⟨B, hBdeg, hdet⟩ := det_eq_corner_mul_minor_add
    (rectangularSchurToeplitz (schurVar K (n' + m' - 1 + 2)) (n' + 1) (m' + 1))
    (0 : Fin (n' + m' - 1 + 2)) (Fin.last m') (rectangularSchur_corner hn) rectangularSchur_free
  obtain ⟨B', hB'⟩ := exists_rename_succ_of_degreeOf_zero hBdeg
  set A : MvPolynomial (Fin (n' + m' - 1 + 1)) K :=
    (-1 : MvPolynomial (Fin (n' + m' - 1 + 1)) K) ^ m' *
      MvPolynomial.rename Fin.succ
        ((rectangularSchurToeplitz (schurVar K (n' + m' - 1)) n' m').det) with hAdef
  have hA0 : A ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ ?_) ?_
    · exact neg_ne_zero.2 one_ne_zero
    · exact rename_succ_ne_zero (irreducible_det_rectangularSchurToeplitz (K := K) hn hm).ne_zero
  have hArename : MvPolynomial.rename Fin.succ A
      = (-1 : MvPolynomial (Fin (n' + m' - 1 + 2)) K) ^ ((Fin.last m' : Fin (m' + 1)) : ℕ) *
        MvPolynomial.rename Fin.succ (MvPolynomial.rename Fin.succ
          ((rectangularSchurToeplitz (schurVar K (n' + m' - 1)) n' m').det)) := by
    rw [hAdef, map_mul, map_pow, map_neg, map_one]
    rfl
  have hshape : (rectangularSchurToeplitz (schurVar K (n' + m' - 1 + 2)) (n' + 1) (m' + 1)).det
      = MvPolynomial.X 0 * MvPolynomial.rename Fin.succ A + MvPolynomial.rename Fin.succ B' := by
    rw [hdet, det_submatrix_eq_rename_succ, hB', hArename]
    ring
  rw [← MvPolynomial.natDegree_finSuccEquiv, hshape, finSuccEquiv_linear,
    Polynomial.natDegree_linear hA0]

/-! ## The cofactor locus -/

/-- **The section does not divide its corner cofactor.**  So the cofactor does not vanish
identically on the divisor the section cuts out: the corank jumps only on a proper closed subset. -/
theorem not_dvd_det_submatrix_rectangularSchur [DecidableEq K] {n' m' : ℕ} (hn : 0 < n')
    (hm : 0 < m') :
    ¬ ((rectangularSchurToeplitz (schurVar K (n' + m' - 1 + 2)) (n' + 1) (m' + 1)).det ∣
      ((rectangularSchurToeplitz (schurVar K (n' + m' - 1 + 2)) (n' + 1) (m' + 1)).submatrix
        (Fin.last m').succAbove Fin.succ).det) := by
  intro hdvd
  have hle := degreeOf_le_of_dvd hdvd (det_submatrix_rectangularSchur_ne_zero hn hm)
  rw [degreeOf_zero_det_rectangularSchur hn hm, det_submatrix_eq_rename_succ,
    degreeOf_zero_rename_succ] at hle
  omega

/-- **The section is squarefree**, so the divisor it cuts out is reduced. -/
theorem squarefree_det_rectangularSchurToeplitz [DecidableEq K] {n m : ℕ} (hn : 0 < n)
    (hm : 0 < m) :
    Squarefree ((rectangularSchurToeplitz (schurVar K (n + m - 1)) n m).det) :=
  (irreducible_det_rectangularSchurToeplitz hn hm).squarefree

end GaloisForLFunctions.HTGeometry
