import GaloisForLFunctions.HTGeometry.PairPeelLimitVector

/-!
# The peel step

Scaling the newest column by its coordinate makes every entry of the orbit matrix converge as that
coordinate grows, and the limit matrix has a single nonzero entry in the scaled column — the residue
`1 + deg g`, in the border row.  Expanding along that column leaves one minor, and the minor is
again an orbit, one level down, of the first limit vector.

So a nonzero orbit determinant one level down forces a nonzero orbit determinant at the current
level.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {p : ℕ → MvPolynomial (Fin 2) ℂ} {α β : Polynomial ℂ} {m' : ℕ}

/-! ## From the second row on, the limit vectors are an orbit -/

theorem pairPeelRes_of_ne_zero (g : Polynomial ℂ) {k : ℕ} (hk : k ≠ 0) : pairPeelRes g k = 0 := by
  match k with
  | 0 => exact absurd rfl hk
  | (_ + 1) => rfl

theorem pairLimVec_succ_succ (p : ℕ → MvPolynomial (Fin 2) ℂ) (α g : Polynomial ℂ) (m' : ℕ)
    (L : ℕ → CascadeField) (i : ℕ) :
    pairLimVec p α m' L (pairPeelRes g) (i + 2)
      = pairGradShift p m' (pairLimVec p α m' L (pairPeelRes g) (i + 1)) := by
  funext k
  by_cases hk : k ≤ m'
  · rw [pairLimVec_succ_of_le p α m' L (pairPeelRes g) (i + 1) k hk,
      pairPeelRes_of_ne_zero g (by omega : i + 1 ≠ 0)]
    ring
  · rw [pairLimVec_succ_of_gt p α m' L (pairPeelRes g) (i + 1) k (by omega)]
    exact (pairGradShift_vanish_above (by omega : m' < k)
      (pairLimVec_succ_of_gt p α m' L (pairPeelRes g) i k (by omega))).symm

theorem pairLimVec_succ_eq_iterate (p : ℕ → MvPolynomial (Fin 2) ℂ) (α g : Polynomial ℂ)
    (m' : ℕ) (L : ℕ → CascadeField) (i : ℕ) :
    pairLimVec p α m' L (pairPeelRes g) (i + 1)
      = ((pairGradShift p m')^[i]) (pairLimVec p α m' L (pairPeelRes g) 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [show i + 1 + 1 = i + 2 from rfl, pairLimVec_succ_succ, ih,
        Function.iterate_succ_apply']

/-! ## The limit matrix -/

/-- The limit of the orbit matrix after scaling the newest column. -/
noncomputable def pairPeelLimitMatrix (p : ℕ → MvPolynomial (Fin 2) ℂ) (α g : Polynomial ℂ)
    (m' : ℕ) (L : ℕ → CascadeField) : Matrix (Fin (m' + 1)) (Fin (m' + 1)) CascadeField :=
  Matrix.of fun i j =>
    if j = Fin.last m' then pairPeelRes g (i : ℕ)
    else pairLimVec p α m' L (pairPeelRes g) (i : ℕ) ((j : ℕ) + 1)

@[simp] theorem pairPeelLimitMatrix_last (p : ℕ → MvPolynomial (Fin 2) ℂ) (α g : Polynomial ℂ)
    (m' : ℕ) (L : ℕ → CascadeField) (i : Fin (m' + 1)) :
    pairPeelLimitMatrix p α g m' L i (Fin.last m') = pairPeelRes g (i : ℕ) := by
  simp [pairPeelLimitMatrix]

theorem pairPeelLimitMatrix_of_ne (p : ℕ → MvPolynomial (Fin 2) ℂ) (α g : Polynomial ℂ)
    (m' : ℕ) (L : ℕ → CascadeField) (i j : Fin (m' + 1)) (hj : j ≠ Fin.last m') :
    pairPeelLimitMatrix p α g m' L i j
      = pairLimVec p α m' L (pairPeelRes g) (i : ℕ) ((j : ℕ) + 1) := by
  simp [pairPeelLimitMatrix, hj]

/-- **Expanding along the scaled column leaves one minor, and it is an orbit.** -/
theorem det_pairPeelLimitMatrix (p : ℕ → MvPolynomial (Fin 2) ℂ) (α g : Polynomial ℂ) (m' : ℕ)
    (L : ℕ → CascadeField) :
    (pairPeelLimitMatrix p α g m' L).det
      = (-1 : CascadeField) ^ (0 + m') * pairPeelRes g 0
        * (pairOrbitMatrix p m' m' (pairLimVec p α m' L (pairPeelRes g) 1)).det := by
  classical
  rw [Matrix.det_succ_column (pairPeelLimitMatrix p α g m' L) (Fin.last m')]
  rw [Finset.sum_eq_single (0 : Fin (m' + 1))]
  · have hentry : pairPeelLimitMatrix p α g m' L 0 (Fin.last m') = pairPeelRes g 0 := by
      rw [pairPeelLimitMatrix_last, Fin.val_zero]
    have hminor : (pairPeelLimitMatrix p α g m' L).submatrix
          (0 : Fin (m' + 1)).succAbove (Fin.last m').succAbove
        = pairOrbitMatrix p m' m' (pairLimVec p α m' L (pairPeelRes g) 1) := by
      funext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_zero, Fin.succAbove_last]
      rw [pairPeelLimitMatrix_of_ne p α g m' L _ _ (Fin.castSucc_lt_last j).ne,
        pairOrbitMatrix, Matrix.of_apply, Fin.val_succ, Fin.val_castSucc,
        pairLimVec_succ_eq_iterate]
    rw [hentry, hminor, Fin.val_zero, Fin.val_last]
  · intro b _ hb
    have hbne : (b : ℕ) ≠ 0 := fun hc => hb (Fin.ext hc)
    have hz : pairPeelLimitMatrix p α g m' L b (Fin.last m') = 0 := by
      rw [pairPeelLimitMatrix_last]
      exact pairPeelRes_of_ne_zero g hbne
    rw [hz, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin (m' + 1))) h

/-! ## The step -/

/-- **The peel step.**  A nonzero orbit determinant one level down forces one at this level. -/
theorem det_pairOrbitMatrix_ne_zero_of_peel (hα : α ≠ 0) {g : Polynomial ℂ} (hg : g ≠ 0)
    (hp : p m' = affinePair α β) (hne : ∀ j, pairFactor (p j) j ≠ 0)
    {u L : ℕ → CascadeField}
    (hmem : ∀ l, u l ∈ coordField (m' + 1))
    (hvan : ∀ l, m' + 1 < l → u l = 0)
    (hLmem : ∀ l, L l ∈ coordField m')
    (hlim0 : ∀ l, TopLim (m' + 1) (u l) (L l))
    (hshape : PairBorderShape p g (m' + 1) u)
    (hminor : (pairOrbitMatrix p m' m' (pairLimVec p α m' L (pairPeelRes g) 1)).det ≠ 0) :
    (pairOrbitMatrix p (m' + 1) (m' + 1) u).det ≠ 0 := by
  classical
  set A : Matrix (Fin (m' + 1)) (Fin (m' + 1)) CascadeField :=
    pairOrbitMatrix p (m' + 1) (m' + 1) u with hA
  set A' : Matrix (Fin (m' + 1)) (Fin (m' + 1)) CascadeField :=
    A.updateCol (Fin.last m') (fx (m' + 1) • fun i => A i (Fin.last m')) with hA'
  have hdetA' : A'.det = fx (m' + 1) * A.det := by
    rw [hA', Matrix.det_updateCol_smul, Matrix.updateCol_eq_self]
  have hentry : ∀ i j : Fin (m' + 1),
      TopLim (m' + 1) (A' i j) (pairPeelLimitMatrix p α g m' L i j) := by
    intro i j
    by_cases hj : j = Fin.last m'
    · subst hj
      have hupd : A' i (Fin.last m') = fx (m' + 1) * A i (Fin.last m') := by
        rw [hA', Matrix.updateCol_apply, if_pos rfl]
        rfl
      have hval : A i (Fin.last m')
          = ((pairGradShift p (m' + 1))^[(i : ℕ)]) u (m' + 1) := by
        rw [hA, pairOrbitMatrix]
        simp [Fin.val_last]
      rw [hupd, hval, pairPeelLimitMatrix_last]
      exact topLim_fx_mul_iterate_pairRes hα hg hp hshape (hmem (m' + 1)) (i : ℕ)
    · have hupd : A' i j = A i j := by
        rw [hA', Matrix.updateCol_apply, if_neg hj]
      rw [hupd, hA, pairOrbitMatrix, pairPeelLimitMatrix_of_ne p α g m' L _ _ hj]
      exact topLim_iterate_pairGradShift hα hg hp hne hmem hvan hLmem hlim0 hshape
        (i : ℕ) ((j : ℕ) + 1)
  have hfree : ∀ i j : Fin (m' + 1),
      TopFree (m' + 1) (pairPeelLimitMatrix p α g m' L i j) := by
    intro i j
    by_cases hj : j = Fin.last m'
    · subst hj
      rw [pairPeelLimitMatrix_last]
      exact topFree_pairPeelRes g (m' + 1) (i : ℕ)
    · rw [pairPeelLimitMatrix_of_ne p α g m' L _ _ hj]
      exact topFree_pairLimVec hLmem (pairPeelRes_mem_coordField g m') (i : ℕ) ((j : ℕ) + 1)
  have hdetlim : TopLim (m' + 1) A'.det (pairPeelLimitMatrix p α g m' L).det :=
    topLim_det A' _ hfree hentry
  have hresne : pairPeelRes g 0 ≠ 0 := by
    show algebraMap ℂ CascadeField (1 + (g.natDegree : ℂ)) ≠ 0
    refine (map_ne_zero_iff _ (algebraMap ℂ CascadeField).injective).mpr ?_
    intro hc
    have hre : (1 : ℝ) + (g.natDegree : ℝ) = 0 := by
      have := congrArg Complex.re hc
      simpa using this
    have : (0 : ℝ) ≤ (g.natDegree : ℝ) := Nat.cast_nonneg _
    linarith
  have hdetLne : (pairPeelLimitMatrix p α g m' L).det ≠ 0 := by
    rw [det_pairPeelLimitMatrix]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hresne) hminor
  intro hzero
  have hA'0 : A'.det = 0 := by rw [hdetA', hzero, mul_zero]
  rw [hA'0] at hdetlim
  refine hdetLne ?_
  exact (topLim_unique (topFree_zero (m' + 1))
    (topFree_det _ hfree) topLim_const hdetlim).symm

end GaloisForLFunctions.HTGeometry
