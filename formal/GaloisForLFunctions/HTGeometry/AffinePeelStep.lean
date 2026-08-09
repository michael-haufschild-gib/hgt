import GaloisForLFunctions.HTGeometry.AffinePeelLimitVector

/-!
# The peel step for an affine factor family

Scaling the newest column by its coordinate makes every entry of the orbit matrix converge, and the
limit matrix has a single nonzero entry in that column — the residue, in the border row.  Expanding
along it leaves one minor, and the minor is again an orbit one level down.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

namespace AffineFam

variable (E : AffineFam)

/-! ## From the second row on, the limit vectors are an orbit -/

theorem limVec_succ_succ (n : ℕ) (g₁ g₂ : Polynomial ℂ) (L : ℕ → CascadeField) (i : ℕ) :
    E.limVec n L (peelRes g₁ g₂) (i + 2)
      = E.toPairFam.gradShift n (E.limVec n L (peelRes g₁ g₂) (i + 1)) := by
  funext k
  by_cases hk : k ≤ n
  · rw [E.limVec_succ_of_le n L (peelRes g₁ g₂) (i + 1) k hk,
      peelRes_of_ne_zero g₁ g₂ (by omega : i + 1 ≠ 0)]
    ring
  · rw [E.limVec_succ_of_gt n L (peelRes g₁ g₂) (i + 1) k (by omega)]
    exact (E.toPairFam.gradShift_vanish_above (by omega : n < k)
      (E.limVec_succ_of_gt n L (peelRes g₁ g₂) i k (by omega))).symm

theorem limVec_succ_eq_iterate (n : ℕ) (g₁ g₂ : Polynomial ℂ) (L : ℕ → CascadeField) (i : ℕ) :
    E.limVec n L (peelRes g₁ g₂) (i + 1)
      = ((E.toPairFam.gradShift n)^[i]) (E.limVec n L (peelRes g₁ g₂) 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [show i + 1 + 1 = i + 2 from rfl, E.limVec_succ_succ, ih,
        Function.iterate_succ_apply']

/-! ## The limit matrix -/

/-- The limit of the orbit matrix after scaling the newest column. -/
noncomputable def peelLimitMatrix (n : ℕ) (g₁ g₂ : Polynomial ℂ) (L : ℕ → CascadeField) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) CascadeField :=
  Matrix.of fun i j =>
    if j = Fin.last n then peelRes g₁ g₂ (i : ℕ)
    else E.limVec n L (peelRes g₁ g₂) (i : ℕ) ((j : ℕ) + 1)

@[simp] theorem peelLimitMatrix_last (n : ℕ) (g₁ g₂ : Polynomial ℂ) (L : ℕ → CascadeField)
    (i : Fin (n + 1)) :
    E.peelLimitMatrix n g₁ g₂ L i (Fin.last n) = peelRes g₁ g₂ (i : ℕ) := by
  simp [peelLimitMatrix]

theorem peelLimitMatrix_of_ne (n : ℕ) (g₁ g₂ : Polynomial ℂ) (L : ℕ → CascadeField)
    (i j : Fin (n + 1)) (hj : j ≠ Fin.last n) :
    E.peelLimitMatrix n g₁ g₂ L i j
      = E.limVec n L (peelRes g₁ g₂) (i : ℕ) ((j : ℕ) + 1) := by
  simp [peelLimitMatrix, hj]

/-- **Expanding along the scaled column leaves one minor, and it is an orbit.** -/
theorem det_peelLimitMatrix (n : ℕ) (g₁ g₂ : Polynomial ℂ) (L : ℕ → CascadeField) :
    (E.peelLimitMatrix n g₁ g₂ L).det
      = (-1 : CascadeField) ^ (0 + n) * peelRes g₁ g₂ 0
        * (E.toPairFam.orbitMatrix n n (E.limVec n L (peelRes g₁ g₂) 1)).det := by
  classical
  rw [Matrix.det_succ_column (E.peelLimitMatrix n g₁ g₂ L) (Fin.last n)]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · have hentry : E.peelLimitMatrix n g₁ g₂ L 0 (Fin.last n) = peelRes g₁ g₂ 0 := by
      rw [E.peelLimitMatrix_last, Fin.val_zero]
    have hminor : (E.peelLimitMatrix n g₁ g₂ L).submatrix
          (0 : Fin (n + 1)).succAbove (Fin.last n).succAbove
        = E.toPairFam.orbitMatrix n n (E.limVec n L (peelRes g₁ g₂) 1) := by
      funext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_zero, Fin.succAbove_last]
      rw [E.peelLimitMatrix_of_ne n g₁ g₂ L _ _ (Fin.castSucc_lt_last j).ne,
        PairFam.orbitMatrix, Matrix.of_apply, Fin.val_succ, Fin.val_castSucc,
        E.limVec_succ_eq_iterate]
    rw [hentry, hminor, Fin.val_zero, Fin.val_last]
  · intro b _ hb
    have hbne : (b : ℕ) ≠ 0 := fun hc => hb (Fin.ext hc)
    have hz : E.peelLimitMatrix n g₁ g₂ L b (Fin.last n) = 0 := by
      rw [E.peelLimitMatrix_last]
      exact peelRes_of_ne_zero g₁ g₂ hbne
    rw [hz, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin (n + 1))) h

/-! ## The step -/

/-- **The peel step.**  A nonzero orbit determinant one level down forces one at this level. -/
theorem det_orbitMatrix_ne_zero_of_peel {g₁ g₂ : Polynomial ℂ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (hres : ((g₁.natDegree : ℤ) - (g₂.natDegree : ℤ)) ≠ -1)
    {n : ℕ} {u L : ℕ → CascadeField}
    (hmem : ∀ l, u l ∈ coordField (n + 1))
    (hvan : ∀ l, n + 1 < l → u l = 0)
    (hLmem : ∀ l, L l ∈ coordField n)
    (hlim0 : ∀ l, TopLim (n + 1) (u l) (L l))
    (hshape : E.BorderShape g₁ g₂ (n + 1) u)
    (hminor : (E.toPairFam.orbitMatrix n n (E.limVec n L (peelRes g₁ g₂) 1)).det ≠ 0) :
    (E.toPairFam.orbitMatrix (n + 1) (n + 1) u).det ≠ 0 := by
  classical
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) CascadeField :=
    E.toPairFam.orbitMatrix (n + 1) (n + 1) u with hA
  set A' : Matrix (Fin (n + 1)) (Fin (n + 1)) CascadeField :=
    A.updateCol (Fin.last n) (fx (n + 1) • fun i => A i (Fin.last n)) with hA'
  have hdetA' : A'.det = fx (n + 1) * A.det := by
    rw [hA', Matrix.det_updateCol_smul, Matrix.updateCol_eq_self]
  have hentry : ∀ i j : Fin (n + 1),
      TopLim (n + 1) (A' i j) (E.peelLimitMatrix n g₁ g₂ L i j) := by
    intro i j
    by_cases hj : j = Fin.last n
    · subst hj
      have hupd : A' i (Fin.last n) = fx (n + 1) * A i (Fin.last n) := by
        rw [hA', Matrix.updateCol_apply, if_pos rfl]
        rfl
      have hval : A i (Fin.last n)
          = ((E.toPairFam.gradShift (n + 1))^[(i : ℕ)]) u (n + 1) := by
        rw [hA, PairFam.orbitMatrix]
        simp [Fin.val_last]
      rw [hupd, hval, E.peelLimitMatrix_last]
      exact E.topLim_fx_mul_iterate_res hg₁ hg₂ hshape (hmem (n + 1)) (i : ℕ)
    · have hupd : A' i j = A i j := by
        rw [hA', Matrix.updateCol_apply, if_neg hj]
      rw [hupd, hA, PairFam.orbitMatrix, E.peelLimitMatrix_of_ne n g₁ g₂ L _ _ hj]
      exact E.topLim_iterate_gradShift hg₁ hg₂ hmem hvan hLmem hlim0 hshape (i : ℕ) ((j : ℕ) + 1)
  have hfree : ∀ i j : Fin (n + 1),
      TopFree (n + 1) (E.peelLimitMatrix n g₁ g₂ L i j) := by
    intro i j
    by_cases hj : j = Fin.last n
    · subst hj
      rw [E.peelLimitMatrix_last]
      exact topFree_peelRes g₁ g₂ (n + 1) (i : ℕ)
    · rw [E.peelLimitMatrix_of_ne n g₁ g₂ L _ _ hj]
      exact E.topFree_limVec hLmem (peelRes_mem_coordField g₁ g₂ n) (i : ℕ) ((j : ℕ) + 1)
  have hdetlim : TopLim (n + 1) A'.det (E.peelLimitMatrix n g₁ g₂ L).det :=
    topLim_det A' _ hfree hentry
  have hresne : peelRes g₁ g₂ 0 ≠ 0 := by
    show algebraMap ℂ CascadeField (1 + (g₁.natDegree : ℂ) - (g₂.natDegree : ℂ)) ≠ 0
    exact (map_ne_zero_iff _ (algebraMap ℂ CascadeField).injective).mpr (residue_ne_zero hres)
  have hdetLne : (E.peelLimitMatrix n g₁ g₂ L).det ≠ 0 := by
    rw [E.det_peelLimitMatrix]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hresne) hminor
  intro hzero
  have hA'0 : A'.det = 0 := by rw [hdetA', hzero, mul_zero]
  rw [hA'0] at hdetlim
  refine hdetLne ?_
  exact (topLim_unique (topFree_zero (n + 1))
    (topFree_det _ hfree) topLim_const hdetlim).symm

end AffineFam

end GaloisForLFunctions.HTGeometry
