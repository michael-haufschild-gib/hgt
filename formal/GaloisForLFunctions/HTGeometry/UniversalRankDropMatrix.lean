import GaloisForLFunctions.HTGeometry.RankDropMatrixCriterion

/-!
# The rank-drop matrix is affine-linear in the reciprocal

Over the space of reciprocals of an observation — the unknown low coefficients, above the observed
tail — the entries of the rank-drop matrix are polynomials of total degree at most one.  Each of its
maximal minors is therefore a polynomial of total degree at most `m + 1` on that space, and the
locus over which the observation has a compatible jet is cut by those minors.

This is the shape a degree count consumes: a rank locus of a matrix of affine-linear forms, of
expected codimension `L - m` in a space of dimension `n = L - m`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [CommRing K] [Nontrivial K] {m n L : ℕ}

/-! ## The universal reciprocal -/

/-- **The universal reciprocal of an observation**: the observed tail with unknown low
coefficients. -/
noncomputable def univRecip (V : K[X]) (n : ℕ) : (MvPolynomial (Fin n) K)[X] :=
  (∑ j : Fin n, Polynomial.C (MvPolynomial.X j) * Polynomial.X ^ (j : ℕ))
    + V.map MvPolynomial.C

omit [Nontrivial K] in
theorem univRecip_coeff (V : K[X]) (n k : ℕ) :
    (univRecip V n).coeff k
      = (if h : k < n then MvPolynomial.X (⟨k, h⟩ : Fin n) else 0)
        + MvPolynomial.C (V.coeff k) := by
  rw [univRecip, Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.finsetSum_coeff]
  congr 1
  have hterm : ∀ j : Fin n, ((Polynomial.C (MvPolynomial.X j) * Polynomial.X ^ (j : ℕ) :
        (MvPolynomial (Fin n) K)[X])).coeff k
      = if k = (j : ℕ) then MvPolynomial.X j else 0 := by
    intro j
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hkj : k = (j : ℕ) <;> simp [hkj]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hterm j)]
  by_cases h : k < n
  · rw [dif_pos h, Finset.sum_eq_single (⟨k, h⟩ : Fin n)]
    · simp
    · intro b _ hb
      have hkb : k ≠ (b : ℕ) := fun hk => hb (Fin.ext hk.symm)
      simp [hkb]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hkj : k ≠ (j : ℕ) := fun hk => h (hk ▸ j.isLt)
    simp [hkj]

omit [Nontrivial K] in
/-- Specialising the universal reciprocal at a point of the reciprocal space. -/
theorem map_univRecip (V : K[X]) (x : Fin n → K) :
    (univRecip V n).map (MvPolynomial.eval x)
      = (∑ j : Fin n, Polynomial.C (x j) * Polynomial.X ^ (j : ℕ)) + V := by
  rw [univRecip, Polynomial.map_add, Polynomial.map_sum, Polynomial.map_map]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      MvPolynomial.eval_X]
  · have hcomp : ((MvPolynomial.eval x).comp
        (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)) = RingHom.id K := by
      ext a
      simp
    rw [hcomp, Polynomial.map_id]

/-! ## Affine-linear entries -/

/-- Every coefficient of the universal reciprocal is affine-linear. -/
theorem totalDegree_coeff_univRecip (V : K[X]) (k : ℕ) :
    ((univRecip V n).coeff k).totalDegree ≤ 1 := by
  rw [univRecip_coeff]
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
  · by_cases h : k < n
    · rw [dif_pos h, MvPolynomial.totalDegree_X]
    · rw [dif_neg h, MvPolynomial.totalDegree_zero]
      exact Nat.zero_le 1
  · rw [MvPolynomial.totalDegree_C]
    exact Nat.zero_le 1

omit [Nontrivial K] in
/-- Shifting a polynomial with affine-linear coefficients keeps them affine-linear. -/
theorem totalDegree_coeff_X_pow_mul {P : (MvPolynomial (Fin n) K)[X]}
    (h : ∀ k, (P.coeff k).totalDegree ≤ 1) (j k : ℕ) :
    ((((X : (MvPolynomial (Fin n) K)[X])) ^ j * P).coeff k).totalDegree ≤ 1 := by
  rw [mul_comm, Polynomial.coeff_mul_X_pow']
  by_cases hj : j ≤ k
  · rw [if_pos hj]; exact h _
  · rw [if_neg hj, MvPolynomial.totalDegree_zero]; exact Nat.zero_le 1

omit [Nontrivial K] in
/-- Multiplying by an observed tail keeps the coefficients affine-linear. -/
theorem totalDegree_coeff_map_C_mul {P : (MvPolynomial (Fin n) K)[X]}
    (h : ∀ k, (P.coeff k).totalDegree ≤ 1) (U : K[X]) (k : ℕ) :
    (((U.map (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)) * P).coeff k).totalDegree ≤ 1 := by
  rw [Polynomial.coeff_mul]
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  refine Finset.sup_le fun p _ => ?_
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [Polynomial.coeff_map, MvPolynomial.totalDegree_C, zero_add]
  exact h _

/-- **Every entry of the universal rank-drop matrix is affine-linear in the reciprocal.** -/
theorem totalDegree_rankDropMatrix_univRecip (U V : K[X]) (k : Fin L) (j : Fin (m + 1)) :
    (rankDropMatrix (U.map (MvPolynomial.C : K →+* MvPolynomial (Fin n) K))
      (univRecip V n) m L k j).totalDegree ≤ 1 := by
  rw [rankDropMatrix, Matrix.of_apply]
  by_cases hj : (j : ℕ) < m
  · rw [if_pos hj]
    exact totalDegree_coeff_X_pow_mul (totalDegree_coeff_univRecip V) _ _
  · rw [if_neg hj]
    rw [sub_eq_add_neg, Polynomial.coeff_add, Polynomial.coeff_neg]
    refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
    · rcases eq_or_ne (k : ℕ) 0 with h0 | h0
      · rw [h0, Polynomial.coeff_one_zero, MvPolynomial.totalDegree_one]
        exact Nat.zero_le 1
      · rw [Polynomial.coeff_one, if_neg h0, MvPolynomial.totalDegree_zero]
        exact Nat.zero_le 1
    · rw [MvPolynomial.totalDegree_neg]
      exact totalDegree_coeff_map_C_mul (totalDegree_coeff_univRecip V) U _

/-! ## The minors have bounded degree -/

/-- **Every maximal minor of the universal rank-drop matrix has total degree at most `m + 1`.**
The determinant is a signed sum of products of `m + 1` entries, each affine-linear. -/
theorem totalDegree_det_submatrix_rankDropMatrix (U V : K[X]) (f : Fin (m + 1) → Fin L) :
    (((rankDropMatrix (U.map (MvPolynomial.C : K →+* MvPolynomial (Fin n) K))
        (univRecip V n) m L).submatrix f id).det).totalDegree ≤ m + 1 := by
  classical
  rw [Matrix.det_apply']
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le fun σ _ => ?_)
  have hsign : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin n) K) = 1 ∨
      ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin n) K) = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · exact Or.inl (by rw [h]; norm_num)
    · exact Or.inr (by rw [h]; norm_num)
  have hprod : (∏ i : Fin (m + 1),
      ((rankDropMatrix (U.map (MvPolynomial.C : K →+* MvPolynomial (Fin n) K))
        (univRecip V n) m L).submatrix f id) (σ i) i).totalDegree ≤ m + 1 := by
    refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
    calc ∑ i : Fin (m + 1),
          (((rankDropMatrix (U.map (MvPolynomial.C : K →+* MvPolynomial (Fin n) K))
            (univRecip V n) m L).submatrix f id) (σ i) i).totalDegree
        ≤ ∑ _i : Fin (m + 1), 1 :=
          Finset.sum_le_sum fun i _ => totalDegree_rankDropMatrix_univRecip U V _ _
      _ = m + 1 := by simp
  rcases hsign with h | h
  · rw [h, one_mul]; exact hprod
  · rw [h, neg_one_mul, MvPolynomial.totalDegree_neg]; exact hprod


/-! ## Specialising the universal matrix -/

omit [Nontrivial K] in
theorem map_map_C_univ (U : K[X]) (x : Fin n → K) :
    (U.map (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)).map (MvPolynomial.eval x) = U := by
  rw [Polynomial.map_map]
  have hcomp : ((MvPolynomial.eval x).comp
      (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)) = RingHom.id K := by
    ext a
    simp
  rw [hcomp, Polynomial.map_id]

omit [Nontrivial K] in
/-- **The universal rank-drop matrix specialises to the rank-drop matrix of the named
reciprocal.** -/
theorem rankDropMatrix_univRecip_map (U V : K[X]) (x : Fin n → K) :
    (rankDropMatrix (U.map (MvPolynomial.C : K →+* MvPolynomial (Fin n) K))
        (univRecip V n) m L).map (MvPolynomial.eval x)
      = rankDropMatrix U ((∑ j : Fin n, Polynomial.C (x j) * Polynomial.X ^ (j : ℕ)) + V) m L := by
  ext k j
  rw [Matrix.map_apply, rankDropMatrix, rankDropMatrix, Matrix.of_apply, Matrix.of_apply]
  by_cases hj : (j : ℕ) < m
  · rw [if_pos hj, if_pos hj, ← Polynomial.coeff_map, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, map_univRecip]
  · rw [if_neg hj, if_neg hj, ← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_one,
      Polynomial.map_mul, map_map_C_univ, map_univRecip]

omit [Nontrivial K] in
/-- **The minors of the universal matrix are the equations of the fibre locus.**  Evaluating a
maximal minor at a point of the reciprocal space gives the corresponding minor of the rank-drop
matrix there. -/
theorem eval_det_submatrix_rankDropMatrix (U V : K[X]) (x : Fin n → K)
    (f : Fin (m + 1) → Fin L) :
    MvPolynomial.eval x
        (((rankDropMatrix (U.map (MvPolynomial.C : K →+* MvPolynomial (Fin n) K))
          (univRecip V n) m L).submatrix f id).det)
      = ((rankDropMatrix U ((∑ j : Fin n, Polynomial.C (x j) * Polynomial.X ^ (j : ℕ)) + V)
          m L).submatrix f id).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map,
    rankDropMatrix_univRecip_map]

end GaloisForLFunctions.HTGeometry
