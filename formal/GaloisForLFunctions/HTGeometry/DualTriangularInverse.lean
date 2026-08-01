import GaloisForLFunctions.HTGeometry.DualSchurVariables

/-!
# The two coefficient families give inverse triangular matrices

Arranging the complete homogeneous coefficients in a lower triangular matrix and the signed dual
coefficients in the same shape, the convolution identity says exactly that the two matrices are
inverse to one another.

This is the linear-algebraic form of the relation between the families, and the starting point of the
duality between the two Jacobi--Trudi determinants.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K]

/-- The lower triangular matrix of complete homogeneous coefficients. -/
noncomputable def schurTri (K : Type*) [Field K] (L N : ℕ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (Fin L) K) :=
  Matrix.of fun i j => if (j : ℕ) ≤ (i : ℕ) then schurVar K L ((i : ℕ) - (j : ℕ)) else 0

/-- The lower triangular matrix of signed dual coefficients. -/
noncomputable def dualTri (K : Type*) [Field K] (L N : ℕ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (Fin L) K) :=
  Matrix.of fun i j =>
    if (j : ℕ) ≤ (i : ℕ) then
      (-1 : MvPolynomial (Fin L) K) ^ ((i : ℕ) - (j : ℕ)) * dualVar K L ((i : ℕ) - (j : ℕ))
    else 0

theorem schurTri_apply {L N : ℕ} (i j : Fin N) :
    schurTri K L N i j =
      if (j : ℕ) ≤ (i : ℕ) then schurVar K L ((i : ℕ) - (j : ℕ)) else 0 := rfl

theorem dualTri_apply {L N : ℕ} (i j : Fin N) :
    dualTri K L N i j =
      if (j : ℕ) ≤ (i : ℕ) then
        (-1 : MvPolynomial (Fin L) K) ^ ((i : ℕ) - (j : ℕ)) * dualVar K L ((i : ℕ) - (j : ℕ))
      else 0 := rfl

theorem schurTri_diag {L N : ℕ} (i : Fin N) : schurTri K L N i i = 1 := by
  rw [schurTri_apply, if_pos (le_refl _), show (i : ℕ) - (i : ℕ) = 0 from by omega, schurVar,
    if_pos rfl]

theorem dualTri_diag {L N : ℕ} (i : Fin N) : dualTri K L N i i = 1 := by
  rw [dualTri_apply, if_pos (le_refl _), show (i : ℕ) - (i : ℕ) = 0 from by omega, dualVar_zero,
    pow_zero, mul_one]

/-! ## The product is unitriangular -/

/-- **Above the diagonal the product vanishes.** -/
theorem schurTri_mul_dualTri_above {L N : ℕ} {i k : Fin N} (hik : ¬ ((k : ℕ) ≤ (i : ℕ))) :
    (schurTri K L N * dualTri K L N) i k = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : (j : ℕ) ≤ (i : ℕ)
  · rw [dualTri_apply, if_neg (by omega), mul_zero]
  · rw [schurTri_apply, if_neg hj, zero_mul]

/-- **On the diagonal the product is one.** -/
theorem schurTri_mul_dualTri_diag {L N : ℕ} (i : Fin N) :
    (schurTri K L N * dualTri K L N) i i = 1 := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · rw [schurTri_diag, dualTri_diag, one_mul]
  · intro j _ hj
    by_cases hji : (j : ℕ) ≤ (i : ℕ)
    · have hne : ¬ ((i : ℕ) ≤ (j : ℕ)) := by
        intro hcon
        exact hj (Fin.ext (by omega))
      rw [dualTri_apply, if_neg hne, mul_zero]
    · rw [schurTri_apply, if_neg hji, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **Both matrices have determinant one.** -/
theorem det_schurTri {L N : ℕ} : (schurTri K L N).det = 1 := by
  have htri : ∀ i j : Fin N, i < j → schurTri K L N i j = 0 := by
    intro i j hij
    have hlt : (i : ℕ) < (j : ℕ) := hij
    rw [schurTri_apply, if_neg (by omega)]
  rw [Matrix.det_of_lowerTriangular _ htri]
  exact Finset.prod_eq_one fun i _ => schurTri_diag i

theorem det_dualTri {L N : ℕ} : (dualTri K L N).det = 1 := by
  have htri : ∀ i j : Fin N, i < j → dualTri K L N i j = 0 := by
    intro i j hij
    have hlt : (i : ℕ) < (j : ℕ) := hij
    rw [dualTri_apply, if_neg (by omega)]
  rw [Matrix.det_of_lowerTriangular _ htri]
  exact Finset.prod_eq_one fun i _ => dualTri_diag i

/-- **Below the diagonal the product vanishes.**  The entry is the alternating convolution of the two
families, reindexed over the interval between the two indices. -/
theorem schurTri_mul_dualTri_below {L N : ℕ} {i k : Fin N} (hki : (k : ℕ) < (i : ℕ)) :
    (schurTri K L N * dualTri K L N) i k = 0 := by
  classical
  rw [Matrix.mul_apply]
  set f : ℕ → MvPolynomial (Fin L) K := fun t =>
    (if t ≤ (i : ℕ) then schurVar K L ((i : ℕ) - t) else 0) *
      (if (k : ℕ) ≤ t then
        (-1 : MvPolynomial (Fin L) K) ^ (t - (k : ℕ)) * dualVar K L (t - (k : ℕ))
      else 0) with hf
  have hfun : ∀ j : Fin N, schurTri K L N i j * dualTri K L N j k = f (j : ℕ) := by
    intro j
    rw [schurTri_apply, dualTri_apply, hf]
  rw [Finset.sum_congr rfl fun j _ => hfun j, Fin.sum_univ_eq_sum_range f N, hf]
  have hsub : ∀ t ∈ Finset.range N, t ∉ Finset.Ico (k : ℕ) ((i : ℕ) + 1) →
      (if t ≤ (i : ℕ) then schurVar K L ((i : ℕ) - t) else 0) *
        (if (k : ℕ) ≤ t then
          (-1 : MvPolynomial (Fin L) K) ^ (t - (k : ℕ)) * dualVar K L (t - (k : ℕ))
        else 0) = 0 := by
    intro t _ ht
    rw [Finset.mem_Ico] at ht
    by_cases hk : (k : ℕ) ≤ t
    · rw [if_neg (by omega : ¬ t ≤ (i : ℕ)), zero_mul]
    · rw [if_neg hk, mul_zero]
  have hIco : Finset.Ico (k : ℕ) ((i : ℕ) + 1) ⊆ Finset.range N := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    have hi := i.isLt
    exact Finset.mem_range.2 (by omega)
  rw [← Finset.sum_subset hIco hsub, Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ t ∈ Finset.range ((i : ℕ) + 1 - (k : ℕ)),
      (if (k : ℕ) + t ≤ (i : ℕ) then schurVar K L ((i : ℕ) - ((k : ℕ) + t)) else 0) *
        (if (k : ℕ) ≤ (k : ℕ) + t then
          (-1 : MvPolynomial (Fin L) K) ^ ((k : ℕ) + t - (k : ℕ)) *
            dualVar K L ((k : ℕ) + t - (k : ℕ))
        else 0) =
      (-1 : MvPolynomial (Fin L) K) ^ t * dualVar K L t *
        schurVar K L ((i : ℕ) - (k : ℕ) - t) := by
    intro t ht
    rw [Finset.mem_range] at ht
    rw [if_pos (by omega), if_pos (by omega), show (k : ℕ) + t - (k : ℕ) = t from by omega,
      show (i : ℕ) - ((k : ℕ) + t) = (i : ℕ) - (k : ℕ) - t from by omega]
    ring
  rw [Finset.sum_congr rfl hterm]
  have hlen : (i : ℕ) + 1 - (k : ℕ) = ((i : ℕ) - (k : ℕ) - 1) + 2 := by omega
  rw [hlen]
  have h := sum_dualVar_schurVar (K := K) (L := L) (k := (i : ℕ) - (k : ℕ) - 1)
  rw [show (i : ℕ) - (k : ℕ) - 1 + 1 = (i : ℕ) - (k : ℕ) from by omega] at h
  exact h

/-- **The two triangular matrices are inverse.** -/
theorem schurTri_mul_dualTri {L N : ℕ} :
    schurTri K L N * dualTri K L N = 1 := by
  refine Matrix.ext fun i k => ?_
  rw [Matrix.one_apply]
  by_cases hik : i = k
  · rw [if_pos hik, ← hik, schurTri_mul_dualTri_diag]
  · rw [if_neg hik]
    by_cases hle : (k : ℕ) ≤ (i : ℕ)
    · exact schurTri_mul_dualTri_below
        (by rcases lt_or_eq_of_le hle with h | h
            · exact h
            · exact absurd (Fin.ext h.symm) hik)
    · exact schurTri_mul_dualTri_above hle

/-- **The dual matrix is the inverse.**  Stated in the form the complementary-minor formula
consumes. -/
theorem inv_schurTri {L N : ℕ} : (schurTri K L N)⁻¹ = dualTri K L N :=
  Matrix.inv_eq_right_inv schurTri_mul_dualTri

/-- **And conversely.** -/
theorem dualTri_mul_schurTri {L N : ℕ} :
    dualTri K L N * schurTri K L N = 1 :=
  _root_.mul_eq_one_comm.1 schurTri_mul_dualTri

end GaloisForLFunctions.HTGeometry
