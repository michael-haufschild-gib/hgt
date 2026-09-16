import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc

/-!
# A determinant is of degree one in a variable occurring in a single entry

Each term of the determinant expansion uses exactly one entry from each column, so a variable
confined to a single entry appears at most once in every term.

Hence the determinant is a polynomial of degree at most one in that variable, and its coefficient
there is the complementary minor.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K σ ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]

theorem degreeOf_zsmul_le (s : σ) (n : ℤ) (p : MvPolynomial σ K) :
    MvPolynomial.degreeOf s (n • p) ≤ MvPolynomial.degreeOf s p := by
  rw [zsmul_eq_mul]
  refine le_trans (MvPolynomial.degreeOf_mul_le s _ _) ?_
  rw [show ((n : ℤ) : MvPolynomial σ K) = MvPolynomial.C (n : K) by
    simp only [map_intCast]]
  rw [MvPolynomial.degreeOf_C]
  omega

/-- **A determinant is of degree at most one in a variable confined to one entry.** -/
theorem degreeOf_det_le_one_of_unique_entry (M : Matrix ι ι (MvPolynomial σ K)) (s : σ)
    (r₀ i₀ : ι) (hone : MvPolynomial.degreeOf s (M r₀ i₀) ≤ 1)
    (hzero : ∀ i j, ¬ (i = r₀ ∧ j = i₀) → MvPolynomial.degreeOf s (M i j) = 0) :
    MvPolynomial.degreeOf s M.det ≤ 1 := by
  classical
  rw [Matrix.det_apply]
  refine le_trans (MvPolynomial.degreeOf_sum_le s _ _) ?_
  refine Finset.sup_le fun e _ => ?_
  refine le_trans (degreeOf_zsmul_le s _ _) ?_
  refine le_trans (MvPolynomial.degreeOf_prod_le s _ _) ?_
  have hterm : ∀ i ∈ (Finset.univ : Finset ι),
      MvPolynomial.degreeOf s (M (e i) i) ≤ if i = i₀ then 1 else 0 := by
    intro i _
    by_cases hi : i = i₀
    · rw [if_pos hi]
      by_cases he : e i = r₀
      · rw [hi] at he ⊢
        rw [he]
        exact hone
      · rw [hzero (e i) i (fun hcon => he hcon.1)]
        omega
    · rw [if_neg hi, hzero (e i) i (fun hcon => hi hcon.2)]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_ite_eq' (Finset.univ : Finset ι) i₀ (fun _ => 1)]
  rw [if_pos (Finset.mem_univ i₀)]

/-- **A determinant of entries free of a variable is free of it.** -/
theorem degreeOf_det_eq_zero (M : Matrix ι ι (MvPolynomial σ K)) (s : σ)
    (h : ∀ i j, MvPolynomial.degreeOf s (M i j) = 0) :
    MvPolynomial.degreeOf s M.det = 0 := by
  classical
  refine Nat.le_zero.1 ?_
  rw [Matrix.det_apply]
  refine le_trans (MvPolynomial.degreeOf_sum_le s _ _) ?_
  refine Finset.sup_le fun e _ => ?_
  refine le_trans (degreeOf_zsmul_le s _ _) ?_
  refine le_trans (MvPolynomial.degreeOf_prod_le s _ _) ?_
  refine le_of_eq ?_
  refine Finset.sum_eq_zero fun i _ => ?_
  exact h (e i) i

/-- **Expansion along the column carrying a variable.**  If a variable occupies the entry `(r₀, 0)`
and no other, the determinant is that variable times the complementary minor, up to sign, plus a
term free of the variable. -/
theorem det_eq_corner_mul_minor_add {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial σ K)) (s : σ) (r₀ : Fin (n + 1))
    (hcorner : M r₀ 0 = MvPolynomial.X s)
    (hzero : ∀ i j, ¬ (i = r₀ ∧ j = 0) → MvPolynomial.degreeOf s (M i j) = 0) :
    ∃ B : MvPolynomial σ K, MvPolynomial.degreeOf s B = 0 ∧
      M.det = (-1 : MvPolynomial σ K) ^ (r₀ : ℕ) * MvPolynomial.X s *
        (M.submatrix r₀.succAbove Fin.succ).det + B := by
  classical
  have hminor : ∀ i : Fin (n + 1),
      MvPolynomial.degreeOf s (M.submatrix i.succAbove Fin.succ).det = 0 := by
    intro i
    refine degreeOf_det_eq_zero _ s fun a b => ?_
    refine hzero _ _ ?_
    rintro ⟨-, hb⟩
    exact (Fin.succ_ne_zero b) hb
  refine ⟨∑ i ∈ Finset.univ.erase r₀,
      (-1 : MvPolynomial σ K) ^ (i : ℕ) * M i 0 *
        (M.submatrix i.succAbove Fin.succ).det, ?_, ?_⟩
  · refine Nat.le_zero.1 ?_
    refine le_trans (MvPolynomial.degreeOf_sum_le s _ _) ?_
    refine Finset.sup_le fun i hi => ?_
    rw [Finset.mem_erase] at hi
    refine le_trans (MvPolynomial.degreeOf_mul_le s _ _) ?_
    have h1 : MvPolynomial.degreeOf s
        ((-1 : MvPolynomial σ K) ^ (i : ℕ) * M i 0) = 0 := by
      refine Nat.le_zero.1 ?_
      refine le_trans (MvPolynomial.degreeOf_mul_le s _ _) ?_
      have hneg : MvPolynomial.degreeOf s ((-1 : MvPolynomial σ K) ^ (i : ℕ)) = 0 := by
        rw [show ((-1 : MvPolynomial σ K)) = MvPolynomial.C (-1 : K) by simp,
          ← map_pow, MvPolynomial.degreeOf_C]
      rw [hneg, hzero i 0 (fun hcon => hi.1 hcon.1)]
    rw [h1, hminor i]
  · rw [Matrix.det_succ_column_zero]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r₀), hcorner]

/-- A polynomial of degree zero in one variable has zero partial derivative in that variable. -/
theorem pderiv_eq_zero_of_degreeOf_eq_zero
    (p : MvPolynomial σ K) (s : σ) (h : MvPolynomial.degreeOf s p = 0) :
    MvPolynomial.pderiv s p = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
  exact not_ne_iff.mpr h

/-- **Fresh-variable noncancellation for a determinant.** If one corner is a new variable, all
other entries are independent of it, and the complementary minor is nonzero, then the full
determinant is nonzero. -/
theorem det_ne_zero_of_fresh_corner {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial σ K)) (s : σ)
    (r₀ : Fin (n + 1))
    (hcorner : M r₀ 0 = MvPolynomial.X s)
    (hzero : ∀ i j, ¬ (i = r₀ ∧ j = 0) → MvPolynomial.degreeOf s (M i j) = 0)
    (hminor : (M.submatrix r₀.succAbove Fin.succ).det ≠ 0) :
    M.det ≠ 0 := by
  have hminorDegree : MvPolynomial.degreeOf s
      (M.submatrix r₀.succAbove Fin.succ).det = 0 := by
    apply degreeOf_det_eq_zero
    intro i j
    apply hzero
    rintro ⟨-, hj⟩
    exact Fin.succ_ne_zero j hj
  obtain ⟨B, hB, hdet⟩ := det_eq_corner_mul_minor_add M s r₀ hcorner hzero
  intro hM
  have hderiv := congrArg (MvPolynomial.pderiv s) hdet
  have hminorDeriv : MvPolynomial.pderiv s
      (M.submatrix r₀.succAbove Fin.succ).det = 0 :=
    pderiv_eq_zero_of_degreeOf_eq_zero _ _ hminorDegree
  have hBDeriv : MvPolynomial.pderiv s B = 0 :=
    pderiv_eq_zero_of_degreeOf_eq_zero _ _ hB
  rw [hM] at hderiv
  simp [hminorDeriv, hBDeriv] at hderiv
  exact hminor (by simpa using hderiv.symm)

/-- A closed two-dimensional certificate for the fresh-coefficient mechanism. -/
theorem fresh_variable_two_by_two_det_ne_zero :
    (!![MvPolynomial.X (), 0; 0, 1] :
      Matrix (Fin 2) (Fin 2) (MvPolynomial Unit ℤ)).det ≠ 0 := by
  rw [Matrix.det_fin_two]
  simp

end GaloisForLFunctions.HTGeometry
