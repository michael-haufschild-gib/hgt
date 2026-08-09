import GaloisForLFunctions.HTGeometry.BorderShapeColumn

/-!
# The limit vectors of the peel

Iterating the lower-column recursion produces, level by level, the limit of every row of the
logarithmic Jacobian.  The recursion is the same operator one level down, with a single correction
in the first step — the residue of the newest column vanishes from the second row on, so only the
first application sees it.

The bookkeeping the induction needs is that the low subalgebra is monotone in its level, that the
shifted operator preserves it, and that a vector vanishing above its level keeps doing so.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-! ## Monotonicity and stability of the low subalgebra -/

theorem lowSub_mono {m m' : ℕ} (h : m ≤ m') : lowSub Q v m ≤ lowSub Q v m' := by
  rw [lowSub, lowSub]
  refine Algebra.adjoin_mono ?_
  rintro x ((⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩)
  · exact Or.inl (Or.inl ⟨j, by omega, rfl⟩)
  · exact Or.inl (Or.inr ⟨j, by omega, rfl⟩)
  · exact Or.inr ⟨j, by omega, rfl⟩

theorem jetResponse_mem_lowSub {k l m : ℕ} (h : l ≤ m) :
    jetResponse Q v k l ∈ lowSub Q v m :=
  lowSub_mono Q v h (fpderiv_mem_lowSub Q v (prodJet_mem_lowSub Q v (le_refl l)))

theorem logFactor_mem_lowSub_of_le {k m : ℕ} (h : k ≤ m) :
    logFactor (Q k) k ∈ lowSub Q v m := logFactorQ_mem_lowSub Q v h

/-- **The shifted operator preserves the low subalgebra.** -/
theorem gradShift_mem_lowSub {m k : ℕ} {u : ℕ → CascadeField}
    (hu : ∀ l, u l ∈ lowSub Q v m) : gradShift Q v m u k ∈ lowSub Q v m := by
  rw [gradShift]
  refine Subalgebra.add_mem _ (prodDerivation_mem_lowSub Q v (hu k)) ?_
  refine Subalgebra.sum_mem _ fun l hl => ?_
  have hlm : l ≤ m := by
    have := Finset.mem_range.mp hl
    omega
  exact Subalgebra.mul_mem _ (jetResponse_mem_lowSub Q v hlm) (hu l)

/-! ## Vanishing above the level -/

/-- **A vector vanishing above the level keeps doing so.** -/
theorem gradShift_vanish_above {m l : ℕ} (hl : m < l) {u : ℕ → CascadeField}
    (hu : u l = 0) : gradShift Q v m u l = 0 := by
  rw [gradShift, hu, map_zero, zero_add]
  refine Finset.sum_eq_zero fun l' hl' => ?_
  have hlt : l' < l := by
    have := Finset.mem_range.mp hl'
    omega
  rw [jetResponse_of_lt Q v hlt, zero_mul]

theorem iterate_gradShift_vanish_above {m l : ℕ} (hl : m < l) {u : ℕ → CascadeField}
    (hu : u l = 0) (i : ℕ) : ((gradShift Q v m)^[i]) u l = 0 := by
  induction i with
  | zero => simpa using hu
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact gradShift_vanish_above Q v hl ih

theorem iterate_gradShift_mem_lowSub {m : ℕ} {u : ℕ → CascadeField}
    (hu : ∀ l, u l ∈ lowSub Q v m) (i : ℕ) (k : ℕ) :
    ((gradShift Q v m)^[i]) u k ∈ lowSub Q v m := by
  induction i generalizing k with
  | zero => simpa using hu k
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact gradShift_mem_lowSub Q v fun l => ih l

/-! ## The limit vectors -/

/-- The limit vector of the `i`-th row of the peeled Jacobian: the same operator one level down,
plus the residue correction of the newest column. -/
noncomputable def limVec (Q v : ℕ → Polynomial ℂ) (m' : ℕ) (α : ℂ) (L : ℕ → CascadeField)
    (res : ℕ → CascadeField) : ℕ → ℕ → CascadeField
  | 0 => L
  | (i + 1) => fun k =>
      if k ≤ m' then
        gradShift Q v m' (limVec Q v m' α L res i) k
          + logFactor (Q k) k
            * (prodHead Q (m' + 1) * (algebraMap ℂ CascadeField α * res i))
      else 0

@[simp] theorem limVec_zero {m' : ℕ} (α : ℂ) (L : ℕ → CascadeField) (res : ℕ → CascadeField) :
    limVec Q v m' α L res 0 = L := rfl

theorem limVec_succ_of_le {m' : ℕ} (α : ℂ) (L : ℕ → CascadeField) (res : ℕ → CascadeField)
    (i k : ℕ) (hk : k ≤ m') :
    limVec Q v m' α L res (i + 1) k
      = gradShift Q v m' (limVec Q v m' α L res i) k
        + logFactor (Q k) k * (prodHead Q (m' + 1)
            * (algebraMap ℂ CascadeField α * res i)) := by
  simp only [limVec]
  rw [if_pos hk]

theorem limVec_succ_of_gt {m' : ℕ} (α : ℂ) (L : ℕ → CascadeField) (res : ℕ → CascadeField)
    (i k : ℕ) (hk : m' < k) : limVec Q v m' α L res (i + 1) k = 0 := by
  simp only [limVec]
  rw [if_neg (by omega : ¬ k ≤ m')]

theorem prodHead_succ_mem_lowSub (m' : ℕ) : prodHead Q (m' + 1) ∈ lowSub Q v m' := by
  rw [prodHead]
  refine Subalgebra.prod_mem _ fun j hj => ?_
  have hjm : j < m' + 1 := Finset.mem_range.mp hj
  exact fact_mem_lowSub Q v (by omega) (Q j)

theorem limVec_mem_lowSub {m' : ℕ} {α : ℂ} {L : ℕ → CascadeField} {res : ℕ → CascadeField}
    (hL : ∀ l, L l ∈ lowSub Q v m') (hres : ∀ i, res i ∈ lowSub Q v m') (i k : ℕ) :
    limVec Q v m' α L res i k ∈ lowSub Q v m' := by
  induction i generalizing k with
  | zero => exact hL k
  | succ i ih =>
      by_cases hk : k ≤ m'
      · rw [limVec_succ_of_le Q v α L res i k hk]
        refine Subalgebra.add_mem _ (gradShift_mem_lowSub Q v fun l => ih l) ?_
        exact Subalgebra.mul_mem _ (logFactor_mem_lowSub_of_le Q v hk)
          (Subalgebra.mul_mem _ (prodHead_succ_mem_lowSub Q v m')
            (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ α) (hres i)))
      · rw [limVec_succ_of_gt Q v α L res i k (by omega)]
        exact Subalgebra.zero_mem _

theorem topFree_limVec {m' : ℕ} {α : ℂ} {L : ℕ → CascadeField} {res : ℕ → CascadeField}
    (hL : ∀ l, L l ∈ lowSub Q v m') (hres : ∀ i, res i ∈ lowSub Q v m') (i k : ℕ) :
    TopFree (m' + 1) (limVec Q v m' α L res i k) :=
  topFree_of_mem_lowSub (by omega) (limVec_mem_lowSub Q v hL hres i k)

/-! ## The newest entry, uniformly in the row -/

theorem topDegLE_iterate_top_of_borderShape {m' : ℕ} (hQ : Q (m' + 1) ≠ 0)
    (hq : 1 ≤ (Q (m' + 1)).natDegree) (hvd : (v (m' + 1)).natDegree = 1)
    {u : ℕ → CascadeField} (hshape : BorderShape Q (m' + 1) u)
    (hsubmem : u (m' + 1) - logFactor (Q (m' + 1)) (m' + 1) ∈ lowSub Q v (m' + 1))
    (hmemu : u (m' + 1) ∈ lowSub Q v (m' + 1)) (i : ℕ) :
    TopDegLE (m' + 1) (-1) (((gradShift Q v (m' + 1))^[i]) u (m' + 1)) := by
  match i with
  | 0 =>
      simp only [Function.iterate_zero, id_eq]
      have hsplit : u (m' + 1)
          = logFactor (Q (m' + 1)) (m' + 1)
            + (u (m' + 1) - logFactor (Q (m' + 1)) (m' + 1)) := by ring
      rw [hsplit]
      exact TopDegLE.add (topDegLE_logFactor (m' + 1) hq) (TopDegLE.mono (by norm_num) hshape)
  | (r + 1) =>
      rw [iterate_gradShift_top, Function.iterate_succ_apply]
      exact TopDegLE.mono (by norm_num)
        (topDegLE_iterate_of_borderShape hQ hq hvd hshape hsubmem hmemu r)

/-- The residue of the newest column: the degree at the border, zero below it. -/
noncomputable def peelRes (Q : ℕ → Polynomial ℂ) (m' : ℕ) : ℕ → CascadeField
  | 0 => algebraMap ℂ CascadeField ((Q (m' + 1)).natDegree : ℂ)
  | (_ + 1) => 0

theorem peelRes_mem_lowSub (m' : ℕ) (i : ℕ) : peelRes Q m' i ∈ lowSub Q v m' := by
  match i with
  | 0 => exact Subalgebra.algebraMap_mem _ _
  | (_ + 1) => exact Subalgebra.zero_mem _

theorem topFree_peelRes (m' : ℕ) (i : ℕ) : TopFree (m' + 1) (peelRes Q m' i) := by
  match i with
  | 0 => exact topFree_algebraMap_complex (m' + 1) _
  | (_ + 1) => exact topFree_zero (m' + 1)

theorem topLim_fx_mul_iterate_res {m' : ℕ} (hQ : Q (m' + 1) ≠ 0)
    (hq : 1 ≤ (Q (m' + 1)).natDegree) (hvd : (v (m' + 1)).natDegree = 1)
    {u : ℕ → CascadeField} (hshape : BorderShape Q (m' + 1) u)
    (hsubmem : u (m' + 1) - logFactor (Q (m' + 1)) (m' + 1) ∈ lowSub Q v (m' + 1))
    (hmemu : u (m' + 1) ∈ lowSub Q v (m' + 1)) (i : ℕ) :
    TopLim (m' + 1) (fx (m' + 1) * (((gradShift Q v (m' + 1))^[i]) u (m' + 1)))
      (peelRes Q m' i) := by
  match i with
  | 0 =>
      simp only [Function.iterate_zero, id_eq, peelRes]
      exact topLim_fx_mul_of_borderShape hq hshape
  | (r + 1) =>
      simp only [peelRes]
      exact topLim_fx_mul_iterate_of_borderShape hQ hq hvd hshape hsubmem hmemu r

/-! ## The limit of every row -/

/-- **Every row of the peeled Jacobian has the predicted limit.** -/
theorem topLim_iterate_gradShift {m' : ℕ} (hQ : ∀ j, Q j ≠ 0) {α β : ℂ}
    (hv : v (m' + 1) = Polynomial.C α * Polynomial.X + Polynomial.C β)
    (hq : 1 ≤ (Q (m' + 1)).natDegree) (hvd : (v (m' + 1)).natDegree = 1)
    {u L : ℕ → CascadeField}
    (hmem : ∀ l, u l ∈ lowSub Q v (m' + 1))
    (hvan : ∀ l, m' + 1 < l → u l = 0)
    (hLmem : ∀ l, L l ∈ lowSub Q v m')
    (hlim0 : ∀ l, TopLim (m' + 1) (u l) (L l))
    (hshape : BorderShape Q (m' + 1) u)
    (hsubmem : u (m' + 1) - logFactor (Q (m' + 1)) (m' + 1) ∈ lowSub Q v (m' + 1))
    (i l : ℕ) :
    TopLim (m' + 1) (((gradShift Q v (m' + 1))^[i]) u l)
      (limVec Q v m' α L (peelRes Q m') i l) := by
  classical
  induction i generalizing l with
  | zero =>
      rw [limVec_zero, Function.iterate_zero_apply]
      exact hlim0 l
  | succ i ih =>
      by_cases hl : l ≤ m'
      · rw [limVec_succ_of_le Q v α L (peelRes Q m') i l hl, Function.iterate_succ_apply']
        exact topLim_gradShift_lower (Q := Q) (v := v) (m' := m') (k := l) hl hQ hv
          (u := ((gradShift Q v (m' + 1))^[i]) u) (L := limVec Q v m' α L (peelRes Q m') i)
          (res := peelRes Q m' i)
          (fun l' => Subalgebra.sub_mem _ (iterate_gradShift_mem_lowSub Q v hmem i l')
            (lowSub_mono Q v (by omega)
              (limVec_mem_lowSub Q v hLmem (peelRes_mem_lowSub Q v m') i l')))
          (fun l' => topFree_limVec Q v hLmem (peelRes_mem_lowSub Q v m') i l')
          (fun l' => ih l')
          (topFree_peelRes Q m' i)
          (topDegLE_iterate_top_of_borderShape Q v (hQ (m' + 1)) hq hvd hshape hsubmem
            (hmem (m' + 1)) i)
          (topLim_fx_mul_iterate_res Q v (hQ (m' + 1)) hq hvd hshape hsubmem
            (hmem (m' + 1)) i)
      · by_cases hl2 : l = m' + 1
        · subst hl2
          rw [limVec_succ_of_gt Q v α L (peelRes Q m') i (m' + 1) (by omega), TopLim, sub_zero]
          exact topDegLE_iterate_top_of_borderShape Q v (hQ (m' + 1)) hq hvd hshape hsubmem
            (hmem (m' + 1)) (i + 1)
        · rw [limVec_succ_of_gt Q v α L (peelRes Q m') i l (by omega),
            iterate_gradShift_vanish_above Q v (by omega : m' + 1 < l) (hvan l (by omega)) (i + 1)]
          exact topLim_const

end GaloisForLFunctions.HTGeometry
