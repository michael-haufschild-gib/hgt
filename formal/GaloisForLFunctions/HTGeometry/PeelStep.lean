import GaloisForLFunctions.HTGeometry.PeelLimitVector

/-!
# The peel step

Scaling the newest column by its coordinate makes every entry of the orbit matrix converge as that
coordinate grows, and the limit matrix has a single nonzero entry in the scaled column — the degree
of the newest denominator, in the border row.  Expanding along that column leaves one minor, and the
minor is again an orbit, one level down, of the first limit vector.

So a nonzero orbit determinant one level down forces a nonzero orbit determinant at the current
level.  That is the induction step; the rescaling law then restores the starting vector's shape.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-! ## From the second row on, the limit vectors are an orbit -/

theorem peelRes_of_ne_zero {m' k : ℕ} (hk : k ≠ 0) : peelRes Q m' k = 0 := by
  match k with
  | 0 => exact absurd rfl hk
  | (_ + 1) => rfl

theorem limVec_succ_succ {m' : ℕ} (α : ℂ) (L : ℕ → CascadeField) (i : ℕ) :
    limVec Q v m' α L (peelRes Q m') (i + 2)
      = gradShift Q v m' (limVec Q v m' α L (peelRes Q m') (i + 1)) := by
  funext k
  by_cases hk : k ≤ m'
  · rw [limVec_succ_of_le Q v α L (peelRes Q m') (i + 1) k hk,
      peelRes_of_ne_zero Q (by omega : i + 1 ≠ 0)]
    ring
  · rw [limVec_succ_of_gt Q v α L (peelRes Q m') (i + 1) k (by omega)]
    exact (gradShift_vanish_above Q v (by omega : m' < k)
      (limVec_succ_of_gt Q v α L (peelRes Q m') i k (by omega))).symm

theorem limVec_succ_eq_iterate {m' : ℕ} (α : ℂ) (L : ℕ → CascadeField) (i : ℕ) :
    limVec Q v m' α L (peelRes Q m') (i + 1)
      = ((gradShift Q v m')^[i]) (limVec Q v m' α L (peelRes Q m') 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [show i + 1 + 1 = i + 2 from rfl, limVec_succ_succ, ih, Function.iterate_succ_apply']

/-! ## Determinants of coordinate-free matrices -/

theorem topFree_det {m n : ℕ} (M : Matrix (Fin n) (Fin n) CascadeField)
    (hM : ∀ i j, TopFree m (M i j)) : TopFree m M.det := by
  classical
  rw [Matrix.det_apply]
  refine topFree_sum _ _ fun σ _ => ?_
  have hprod : TopFree m (∏ i, M (σ i) i) := topFree_prod _ _ fun i _ => hM (σ i) i
  have hsign : ((Equiv.Perm.sign σ : ℤ) : CascadeField) = 1 ∨
      ((Equiv.Perm.sign σ : ℤ) : CascadeField) = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs] <;> simp
  rcases hsign with hs | hs <;>
    simp only [Units.smul_def, zsmul_eq_mul, hs, one_mul, neg_mul] <;>
    [exact hprod; exact hprod.neg]

/-! ## The limit matrix -/

/-- The limit of the orbit matrix after scaling the newest column. -/
noncomputable def peelLimitMatrix (Q v : ℕ → Polynomial ℂ) (m' : ℕ) (α : ℂ)
    (L : ℕ → CascadeField) : Matrix (Fin (m' + 1)) (Fin (m' + 1)) CascadeField :=
  Matrix.of fun i j =>
    if j = Fin.last m' then peelRes Q m' (i : ℕ)
    else limVec Q v m' α L (peelRes Q m') (i : ℕ) ((j : ℕ) + 1)

@[simp] theorem peelLimitMatrix_last (m' : ℕ) (α : ℂ) (L : ℕ → CascadeField)
    (i : Fin (m' + 1)) :
    peelLimitMatrix Q v m' α L i (Fin.last m') = peelRes Q m' (i : ℕ) := by
  simp [peelLimitMatrix]

theorem peelLimitMatrix_of_ne (m' : ℕ) (α : ℂ) (L : ℕ → CascadeField)
    (i j : Fin (m' + 1)) (hj : j ≠ Fin.last m') :
    peelLimitMatrix Q v m' α L i j
      = limVec Q v m' α L (peelRes Q m') (i : ℕ) ((j : ℕ) + 1) := by
  simp [peelLimitMatrix, hj]

/-- **Expanding along the scaled column leaves one minor, and it is an orbit.** -/
theorem det_peelLimitMatrix {m' : ℕ} (α : ℂ) (L : ℕ → CascadeField) :
    (peelLimitMatrix Q v m' α L).det
      = (-1 : CascadeField) ^ (0 + m') * peelRes Q m' 0
        * (jetOrbitMatrix Q v m' m' (limVec Q v m' α L (peelRes Q m') 1)).det := by
  classical
  rw [Matrix.det_succ_column (peelLimitMatrix Q v m' α L) (Fin.last m')]
  rw [Finset.sum_eq_single (0 : Fin (m' + 1))]
  · have hentry : peelLimitMatrix Q v m' α L 0 (Fin.last m') = peelRes Q m' 0 := by
      rw [peelLimitMatrix_last, Fin.val_zero]
    have hminor : (peelLimitMatrix Q v m' α L).submatrix
          (0 : Fin (m' + 1)).succAbove (Fin.last m').succAbove
        = jetOrbitMatrix Q v m' m' (limVec Q v m' α L (peelRes Q m') 1) := by
      funext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_zero, Fin.succAbove_last]
      rw [peelLimitMatrix_of_ne Q v m' α L _ _ (Fin.castSucc_lt_last j).ne,
        jetOrbitMatrix, Matrix.of_apply, Fin.val_succ, Fin.val_castSucc,
        limVec_succ_eq_iterate]
    rw [hentry, hminor, Fin.val_zero, Fin.val_last]
  · intro b _ hb
    have hbne : (b : ℕ) ≠ 0 := fun hc => hb (Fin.ext hc)
    have : peelLimitMatrix Q v m' α L b (Fin.last m') = 0 := by
      rw [peelLimitMatrix_last]
      exact peelRes_of_ne_zero Q hbne
    rw [this, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin (m' + 1))) h

/-! ## The step -/

/-- **The peel step.**  A nonzero orbit determinant one level down forces one at this level. -/
theorem det_jetOrbitMatrix_ne_zero_of_peel {m' : ℕ} (hQ : ∀ j, Q j ≠ 0) {α β : ℂ}
    (hv : v (m' + 1) = Polynomial.C α * Polynomial.X + Polynomial.C β)
    (hq : 1 ≤ (Q (m' + 1)).natDegree) (hvd : (v (m' + 1)).natDegree = 1)
    {u L : ℕ → CascadeField}
    (hmem : ∀ l, u l ∈ lowSub Q v (m' + 1))
    (hvan : ∀ l, m' + 1 < l → u l = 0)
    (hLmem : ∀ l, L l ∈ lowSub Q v m')
    (hlim0 : ∀ l, TopLim (m' + 1) (u l) (L l))
    (hshape : BorderShape Q (m' + 1) u)
    (hsubmem : u (m' + 1) - logFactor (Q (m' + 1)) (m' + 1) ∈ lowSub Q v (m' + 1))
    (hminor : (jetOrbitMatrix Q v m' m' (limVec Q v m' α L (peelRes Q m') 1)).det ≠ 0) :
    (jetOrbitMatrix Q v (m' + 1) (m' + 1) u).det ≠ 0 := by
  classical
  set A : Matrix (Fin (m' + 1)) (Fin (m' + 1)) CascadeField :=
    jetOrbitMatrix Q v (m' + 1) (m' + 1) u with hA
  set A' : Matrix (Fin (m' + 1)) (Fin (m' + 1)) CascadeField :=
    A.updateCol (Fin.last m') (fx (m' + 1) • fun i => A i (Fin.last m')) with hA'
  have hdetA' : A'.det = fx (m' + 1) * A.det := by
    rw [hA', Matrix.det_updateCol_smul, Matrix.updateCol_eq_self]
  -- entrywise limits
  have hentry : ∀ i j : Fin (m' + 1),
      TopLim (m' + 1) (A' i j) (peelLimitMatrix Q v m' α L i j) := by
    intro i j
    by_cases hj : j = Fin.last m'
    · subst hj
      have hupd : A' i (Fin.last m') = fx (m' + 1) * A i (Fin.last m') := by
        rw [hA', Matrix.updateCol_apply, if_pos rfl]
        rfl
      rw [hupd]
      have hval : A i (Fin.last m')
          = ((gradShift Q v (m' + 1))^[(i : ℕ)]) u (m' + 1) := by
        rw [hA, jetOrbitMatrix]
        simp [Fin.val_last]
      rw [hval]
      have hlim := topLim_fx_mul_iterate_res Q v (hQ (m' + 1)) hq hvd hshape hsubmem
        (hmem (m' + 1)) (i : ℕ)
      rw [peelLimitMatrix_last]
      exact hlim
    · have hupd : A' i j = A i j := by
        rw [hA', Matrix.updateCol_apply, if_neg hj]
      rw [hupd, hA, jetOrbitMatrix]
      have hlim := topLim_iterate_gradShift Q v hQ hv hq hvd hmem hvan hLmem hlim0 hshape
        hsubmem (i : ℕ) ((j : ℕ) + 1)
      rw [peelLimitMatrix_of_ne Q v m' α L _ _ hj]
      exact hlim
  have hfree : ∀ i j : Fin (m' + 1), TopFree (m' + 1) (peelLimitMatrix Q v m' α L i j) := by
    intro i j
    by_cases hj : j = Fin.last m'
    · subst hj
      rw [peelLimitMatrix_last]
      exact topFree_peelRes Q m' (i : ℕ)
    · rw [peelLimitMatrix_of_ne Q v m' α L _ _ hj]
      exact topFree_limVec Q v hLmem (peelRes_mem_lowSub Q v m') (i : ℕ) ((j : ℕ) + 1)
  have hdetlim : TopLim (m' + 1) A'.det (peelLimitMatrix Q v m' α L).det :=
    topLim_det A' _ hfree hentry
  -- the limit determinant is nonzero
  have hqne : (algebraMap ℂ CascadeField ((Q (m' + 1)).natDegree : ℂ)) ≠ 0 := by
    refine (map_ne_zero_iff _ (algebraMap ℂ CascadeField).injective).mpr ?_
    exact_mod_cast Nat.cast_ne_zero.mpr (by omega : (Q (m' + 1)).natDegree ≠ 0)
  have hdetLne : (peelLimitMatrix Q v m' α L).det ≠ 0 := by
    rw [det_peelLimitMatrix]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_) hminor
    exact hqne
  -- conclude
  intro hzero
  have hA'0 : A'.det = 0 := by rw [hdetA', hzero, mul_zero]
  rw [hA'0] at hdetlim
  refine hdetLne ?_
  exact (topLim_unique (topFree_zero (m' + 1))
    (topFree_det _ hfree) topLim_const hdetlim).symm

end GaloisForLFunctions.HTGeometry
