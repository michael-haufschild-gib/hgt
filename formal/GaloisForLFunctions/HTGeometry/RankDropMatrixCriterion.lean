import GaloisForLFunctions.HTGeometry.RankDropFibreCriterion
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The rank-drop criterion as a matrix kernel

The dependency criterion for the existence of a compatible jet is a statement about `m + 1`
elements of `K[t]/t^L`.  Writing those elements in the monomial basis turns it into a statement
about an `L x (m+1)` matrix over the field: the fibre over a reciprocal is nonempty exactly when
that matrix has a nonzero kernel vector.

The entries of the matrix are linear in the reciprocal, so this is the form in which the fibre count
over the whole reciprocal space becomes the degree of a rank locus.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

section Entries

variable {R : Type*} [CommRing R] {m L : ℕ}

/-- **The rank-drop matrix of an observation at a reciprocal.**  Its first `m` columns are the
shifts `t^j Q` of the reciprocal and its last column is the correction `1 - U Q`, each read off in
the monomial basis below the horizon. -/
noncomputable def rankDropMatrix (U Q : R[X]) (m L : ℕ) : Matrix (Fin L) (Fin (m + 1)) R :=
  Matrix.of fun k j => if (j : ℕ) < m then ((X : R[X]) ^ (j : ℕ) * Q).coeff (k : ℕ)
    else (1 - U * Q).coeff (k : ℕ)

theorem rankDropMatrix_castSucc (U Q : R[X]) (k : Fin L) (i : Fin m) :
    rankDropMatrix U Q m L k i.castSucc = ((X : R[X]) ^ (i : ℕ) * Q).coeff (k : ℕ) := by
  simp only [rankDropMatrix, Matrix.of_apply, Fin.val_castSucc, if_pos i.isLt]

theorem rankDropMatrix_last (U Q : R[X]) (k : Fin L) :
    rankDropMatrix U Q m L k (Fin.last m) = (1 - U * Q).coeff (k : ℕ) := by
  simp [rankDropMatrix]

/-- The coefficients of a product with a polynomial written in the monomial basis. -/
theorem coeff_sum_range_mul (b : ℕ → R) (S : R[X]) (N k : ℕ) :
    ((∑ j ∈ Finset.range N, C (b j) * X ^ j) * S).coeff k
      = ∑ j ∈ Finset.range N, b j * ((X : R[X]) ^ j * S).coeff k := by
  rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, Polynomial.coeff_C_mul]

/-- The coefficients of a combination of the shifted reciprocals with the correction. -/
theorem coeff_shift_combination (lam : ℕ → R) (μ : R) (U Q : R[X]) (k : ℕ) :
    ((∑ i ∈ Finset.range m, C (lam i) * X ^ i) * Q + C μ * (1 - U * Q)).coeff k
      = (∑ i ∈ Finset.range m, lam i * ((X : R[X]) ^ i * Q).coeff k)
        + μ * (1 - U * Q).coeff k := by
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, coeff_sum_range_mul]

/-- The matrix acts on a coefficient vector as the combination of the columns. -/
theorem mulVec_rankDropMatrix (U Q : R[X]) (lam : ℕ → R) (μ : R) (k : Fin L) :
    (rankDropMatrix U Q m L).mulVec (fun j => if (j : ℕ) < m then lam (j : ℕ) else μ) k
      = ((∑ i ∈ Finset.range m, C (lam i) * X ^ i) * Q + C μ * (1 - U * Q)).coeff (k : ℕ) := by
  rw [coeff_shift_combination]
  have hexp : (rankDropMatrix U Q m L).mulVec (fun j => if (j : ℕ) < m then lam (j : ℕ) else μ) k
      = ∑ j : Fin (m + 1),
          rankDropMatrix U Q m L k j * (if (j : ℕ) < m then lam (j : ℕ) else μ) := rfl
  rw [hexp, Fin.sum_univ_castSucc, rankDropMatrix_last, Fin.val_last, if_neg (lt_irrefl m),
    ← Fin.sum_univ_eq_sum_range (fun i => lam i * ((X : R[X]) ^ i * Q).coeff (k : ℕ)) m]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [rankDropMatrix_castSucc, Fin.val_castSucc, if_pos i.isLt, mul_comm]
  · rw [mul_comm]

end Entries

section Field

variable {K : Type*} [Field K] {m L : ℕ}

/-- **The fibre over a reciprocal is nonempty exactly when the rank-drop matrix has a kernel.**
This is the dependency criterion written in the monomial basis. -/
theorem exists_fibre_iff_mulVec_eq_zero (hmL : m ≤ L) {U Q : K[X]} (hQ : Q.coeff 0 ≠ 0) :
    (∃ A : K[X], A.degree < (m : ℕ) ∧ (X : K[X]) ^ L ∣ ((A + U) * Q - 1)) ↔
      ∃ v : Fin (m + 1) → K, v ≠ 0 ∧ (rankDropMatrix U Q m L).mulVec v = 0 := by
  rw [exists_fibre_iff_dependent_coeffs hmL hQ]
  constructor
  · rintro ⟨lam, μ, hne, hdvd⟩
    refine ⟨fun j => if (j : ℕ) < m then lam (j : ℕ) else μ, ?_, ?_⟩
    · intro h0
      have hval : ∀ j : Fin (m + 1), (if (j : ℕ) < m then lam (j : ℕ) else μ) = 0 :=
        fun j => congrFun h0 j
      rcases hne with ⟨i, him, hlam⟩ | hμ0
      · refine hlam ?_
        have := hval ⟨i, by omega⟩
        rwa [if_pos him] at this
      · refine hμ0 ?_
        have := hval (Fin.last m)
        rwa [Fin.val_last, if_neg (lt_irrefl m)] at this
    · funext k
      rw [mulVec_rankDropMatrix]
      exact (Polynomial.X_pow_dvd_iff.1 hdvd) (k : ℕ) k.isLt
  · rintro ⟨v, hv, hmul⟩
    refine ⟨fun i => if h : i < m then v ⟨i, by omega⟩ else 0, v (Fin.last m), ?_, ?_⟩
    · by_contra hall
      push Not at hall
      obtain ⟨hlam, hμ⟩ := hall
      refine hv (funext fun j => ?_)
      rcases lt_or_ge (j : ℕ) m with hj | hj
      · have hj0 := hlam (j : ℕ) hj
        rw [dif_pos hj] at hj0
        simpa using hj0
      · have hjlt := j.isLt
        have hjm : j = Fin.last m := Fin.ext (by rw [Fin.val_last]; omega)
        rw [hjm, hμ]
        rfl
    · have hveq : (fun j : Fin (m + 1) => if (j : ℕ) < m
            then (fun i => if h : i < m then v ⟨i, by omega⟩ else 0) (j : ℕ)
            else v (Fin.last m)) = v := by
        funext j
        rcases lt_or_ge (j : ℕ) m with hj | hj
        · simp [hj]
        · have hjlt := j.isLt
          have hjm : j = Fin.last m := Fin.ext (by rw [Fin.val_last]; omega)
          rw [hjm, Fin.val_last, if_neg (lt_irrefl m)]
      refine Polynomial.X_pow_dvd_iff.2 fun k hk => ?_
      have hcol := mulVec_rankDropMatrix (m := m) U Q
        (fun i => if h : i < m then v ⟨i, by omega⟩ else 0) (v (Fin.last m)) ⟨k, hk⟩
      rw [← hcol, hveq, hmul]
      rfl


/-! ## The maximal minors vanish on the fibre locus -/

/-- **A nonempty fibre forces every maximal minor of the rank-drop matrix to vanish.**  A kernel
vector of the whole matrix is a kernel vector of each of its square row selections, and a square
matrix with a kernel has determinant zero.  These are polynomial equations in the reciprocal, and
they cut out the locus over which the observation has a compatible jet. -/
theorem det_submatrix_rankDropMatrix_eq_zero (hmL : m ≤ L) {U Q : K[X]} (hQ : Q.coeff 0 ≠ 0)
    (hfib : ∃ A : K[X], A.degree < (m : ℕ) ∧ (X : K[X]) ^ L ∣ ((A + U) * Q - 1))
    (f : Fin (m + 1) → Fin L) :
    ((rankDropMatrix U Q m L).submatrix f id).det = 0 := by
  obtain ⟨v, hv, hmul⟩ := (exists_fibre_iff_mulVec_eq_zero hmL hQ).1 hfib
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, ?_⟩
  funext i
  have : ((rankDropMatrix U Q m L).submatrix f id).mulVec v i
      = (rankDropMatrix U Q m L).mulVec v (f i) := rfl
  rw [this, hmul]
  rfl

end Field

end GaloisForLFunctions.HTGeometry
