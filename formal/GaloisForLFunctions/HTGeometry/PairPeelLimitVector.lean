import GaloisForLFunctions.HTGeometry.PairColumnLimits

/-!
# The limit vectors of the peel

Iterating the lower-column recursion produces, level by level, the limit of every row of the
peeled matrix.  The recursion is the same operator one level down — with the head that the limit
creates — plus a single correction in the first step: the residue of the newest column vanishes from
the second row on, so only the first application sees it.

The bookkeeping the induction needs is that the coordinate subfield is stable under the shifted
operator, and that a vector vanishing above its level keeps doing so.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {p : ℕ → MvPolynomial (Fin 2) ℂ} {α β : Polynomial ℂ} {m' : ℕ}

/-! ## Stability of the subfield -/

theorem pairResponse_mem_coordField {k l m : ℕ} (h : l ≤ m) :
    pairResponse p k l ∈ coordField m := by
  rw [pairResponse]
  exact fpderiv_mem_coordField k (pairJet_mem_coordField h)

/-- **The shifted operator preserves the subfield.** -/
theorem pairGradShift_mem_coordField {m k : ℕ} {u : ℕ → CascadeField}
    (hu : ∀ l, u l ∈ coordField m) : pairGradShift p m u k ∈ coordField m := by
  rw [pairGradShift]
  refine add_mem (pairDerivation_mem_coordField (hu k)) (sum_mem fun l hl => ?_)
  have hlm : l ≤ m := by
    have := Finset.mem_range.mp hl
    omega
  exact mul_mem (pairResponse_mem_coordField hlm) (hu l)

theorem iterate_pairGradShift_mem_coordField {m : ℕ} {u : ℕ → CascadeField}
    (hu : ∀ l, u l ∈ coordField m) (i k : ℕ) :
    ((pairGradShift p m)^[i]) u k ∈ coordField m := by
  induction i generalizing k with
  | zero => simpa using hu k
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact pairGradShift_mem_coordField fun l => ih l

/-! ## Vanishing above the level -/

theorem pairGradShift_vanish_above {m l : ℕ} (hl : m < l) {u : ℕ → CascadeField}
    (hu : u l = 0) : pairGradShift p m u l = 0 := by
  rw [pairGradShift, hu, map_zero, zero_add]
  refine Finset.sum_eq_zero fun l' hl' => ?_
  have hlt : l' < l := by
    have := Finset.mem_range.mp hl'
    omega
  rw [pairResponse_of_lt hlt, zero_mul]

theorem iterate_pairGradShift_vanish_above {m l : ℕ} (hl : m < l) {u : ℕ → CascadeField}
    (hu : u l = 0) (i : ℕ) : ((pairGradShift p m)^[i]) u l = 0 := by
  induction i with
  | zero => simpa using hu
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact pairGradShift_vanish_above hl ih

/-! ## The limit vectors -/

/-- The limit vector of the `i`-th row: the same operator one level down, with the head created by
the limit, plus the residue correction of the newest column. -/
noncomputable def pairLimVec (p : ℕ → MvPolynomial (Fin 2) ℂ) (α : Polynomial ℂ) (m' : ℕ)
    (L : ℕ → CascadeField) (res : ℕ → CascadeField) : ℕ → ℕ → CascadeField
  | 0 => L
  | (i + 1) => fun k =>
      if k ≤ m' then
        pairGradShift p m' (pairLimVec p α m' L res i) k
          + headBorder p α m' k * (pairJet p m' * fact α m' * res i)
      else 0

@[simp] theorem pairLimVec_zero (p : ℕ → MvPolynomial (Fin 2) ℂ) (α : Polynomial ℂ) (m' : ℕ)
    (L res : ℕ → CascadeField) : pairLimVec p α m' L res 0 = L := rfl

theorem pairLimVec_succ_of_le (p : ℕ → MvPolynomial (Fin 2) ℂ) (α : Polynomial ℂ) (m' : ℕ)
    (L res : ℕ → CascadeField) (i k : ℕ) (hk : k ≤ m') :
    pairLimVec p α m' L res (i + 1) k
      = pairGradShift p m' (pairLimVec p α m' L res i) k
        + headBorder p α m' k * (pairJet p m' * fact α m' * res i) := by
  simp only [pairLimVec]
  rw [if_pos hk]

theorem pairLimVec_succ_of_gt (p : ℕ → MvPolynomial (Fin 2) ℂ) (α : Polynomial ℂ) (m' : ℕ)
    (L res : ℕ → CascadeField) (i k : ℕ) (hk : m' < k) :
    pairLimVec p α m' L res (i + 1) k = 0 := by
  simp only [pairLimVec]
  rw [if_neg (by omega : ¬ k ≤ m')]

theorem pairLimVec_mem_coordField {L res : ℕ → CascadeField}
    (hL : ∀ l, L l ∈ coordField m') (hres : ∀ i, res i ∈ coordField m') (i k : ℕ) :
    pairLimVec p α m' L res i k ∈ coordField m' := by
  induction i generalizing k with
  | zero => exact hL k
  | succ i ih =>
      by_cases hk : k ≤ m'
      · rw [pairLimVec_succ_of_le p α m' L res i k hk]
        refine add_mem (pairGradShift_mem_coordField fun l => ih l) (mul_mem ?_ ?_)
        · exact headBorder_mem_coordField α m' k
        · exact mul_mem (mul_mem (pairJet_mem_coordField (le_refl m'))
            (fact_mem_coordField (le_refl m') α)) (hres i)
      · rw [pairLimVec_succ_of_gt p α m' L res i k (by omega)]
        exact zero_mem _

theorem topFree_pairLimVec {L res : ℕ → CascadeField}
    (hL : ∀ l, L l ∈ coordField m') (hres : ∀ i, res i ∈ coordField m') (i k : ℕ) :
    TopFree (m' + 1) (pairLimVec p α m' L res i k) :=
  topFree_of_mem_coordField (by omega) (pairLimVec_mem_coordField hL hres i k)

/-! ## The newest entry, uniformly in the row -/

theorem topDegLE_headBorder_top (hα : α ≠ 0) (g : Polynomial ℂ) (hp : p m' = affinePair α β) :
    TopDegLE (m' + 1) (-1) (headBorder p g (m' + 1) (m' + 1)) := by
  rw [headBorder_self, pairLogBorder_top]
  refine TopDegLE.add ?_ ?_
  · rw [pairLogTerm, fpderiv_top_pairFactor hp, div_eq_mul_inv]
    have hA : TopFree (m' + 1) (fact α m') := topFree_fact (by omega) α
    have hF : TopDegLE (m' + 1) (-1) ((pairFactor (p m') m')⁻¹) := by
      rw [hp]
      exact topDegLE_inv_pairFactor_affine hα β m'
    have h := TopDegLE.mul hA.topDegLE hF
    simpa using h
  · rcases Nat.eq_zero_or_pos g.natDegree with h0 | h0
    · rw [logFactor_eq_zero_of_natDegree_zero h0]
      exact topDegLE_zero _ _
    · exact topDegLE_logFactor (m' + 1) h0

theorem topDegLE_iterate_top_of_shape (hα : α ≠ 0) {g : Polynomial ℂ} (hg : g ≠ 0)
    (hp : p m' = affinePair α β) {u : ℕ → CascadeField}
    (hshape : PairBorderShape p g (m' + 1) u)
    (hmem : u (m' + 1) ∈ coordField (m' + 1)) (i : ℕ) :
    TopDegLE (m' + 1) (-1) (((pairGradShift p (m' + 1))^[i]) u (m' + 1)) := by
  match i with
  | 0 =>
      simp only [Function.iterate_zero, id_eq]
      have hsplit : u (m' + 1)
          = headBorder p g (m' + 1) (m' + 1)
            + (u (m' + 1) - headBorder p g (m' + 1) (m' + 1)) := by ring
      rw [hsplit]
      exact TopDegLE.add (topDegLE_headBorder_top hα g hp)
        (TopDegLE.mono (by norm_num) hshape)
  | (r + 1) =>
      rw [iterate_pairGradShift_top, Function.iterate_succ_apply]
      exact TopDegLE.mono (by norm_num)
        (topDegLE_iterate_of_shape hα hg hp hshape hmem r)

/-- The residue of the newest column: `1 + deg g` at the border, zero below it. -/
noncomputable def pairPeelRes (g : Polynomial ℂ) : ℕ → CascadeField
  | 0 => algebraMap ℂ CascadeField (1 + (g.natDegree : ℂ))
  | (_ + 1) => 0

theorem pairPeelRes_mem_coordField (g : Polynomial ℂ) (m : ℕ) (i : ℕ) :
    pairPeelRes g i ∈ coordField m := by
  match i with
  | 0 => exact (coordField m).algebraMap_mem _
  | (_ + 1) => exact zero_mem _

theorem topFree_pairPeelRes (g : Polynomial ℂ) (m : ℕ) (i : ℕ) :
    TopFree m (pairPeelRes g i) := by
  match i with
  | 0 => exact topFree_algebraMap_complex m _
  | (_ + 1) => exact topFree_zero m

theorem topLim_fx_mul_iterate_pairRes (hα : α ≠ 0) {g : Polynomial ℂ} (hg : g ≠ 0)
    (hp : p m' = affinePair α β) {u : ℕ → CascadeField}
    (hshape : PairBorderShape p g (m' + 1) u)
    (hmem : u (m' + 1) ∈ coordField (m' + 1)) (i : ℕ) :
    TopLim (m' + 1) (fx (m' + 1) * (((pairGradShift p (m' + 1))^[i]) u (m' + 1)))
      (pairPeelRes g i) := by
  match i with
  | 0 =>
      simp only [Function.iterate_zero, id_eq, pairPeelRes]
      exact topLim_fx_mul_of_shape hα g hp hshape
  | (r + 1) =>
      simp only [pairPeelRes]
      exact topLim_fx_mul_iterate_of_shape hα hg hp hshape hmem r

/-! ## The limit of every row -/

/-- **Every row of the peeled matrix has the predicted limit.** -/
theorem topLim_iterate_pairGradShift (hα : α ≠ 0) {g : Polynomial ℂ} (hg : g ≠ 0)
    (hp : p m' = affinePair α β) (hne : ∀ j, pairFactor (p j) j ≠ 0)
    {u L : ℕ → CascadeField}
    (hmem : ∀ l, u l ∈ coordField (m' + 1))
    (hvan : ∀ l, m' + 1 < l → u l = 0)
    (hLmem : ∀ l, L l ∈ coordField m')
    (hlim0 : ∀ l, TopLim (m' + 1) (u l) (L l))
    (hshape : PairBorderShape p g (m' + 1) u)
    (i l : ℕ) :
    TopLim (m' + 1) (((pairGradShift p (m' + 1))^[i]) u l)
      (pairLimVec p α m' L (pairPeelRes g) i l) := by
  classical
  induction i generalizing l with
  | zero =>
      rw [pairLimVec_zero, Function.iterate_zero_apply]
      exact hlim0 l
  | succ i ih =>
      by_cases hl : l ≤ m'
      · rw [pairLimVec_succ_of_le p α m' L (pairPeelRes g) i l hl,
          Function.iterate_succ_apply']
        refine topLim_pairGradShift_lower hα hp hne hl
          (fun l' => sub_mem (iterate_pairGradShift_mem_coordField hmem i l')
            (coordField_mono (by omega)
              (pairLimVec_mem_coordField hLmem (pairPeelRes_mem_coordField g m') i l')))
          (fun l' => topFree_pairLimVec hLmem (pairPeelRes_mem_coordField g m') i l')
          (fun l' => ih l')
          (topFree_pairPeelRes g (m' + 1) i)
          (topDegLE_iterate_top_of_shape hα hg hp hshape (hmem (m' + 1)) i)
          (topLim_fx_mul_iterate_pairRes hα hg hp hshape (hmem (m' + 1)) i)
      · by_cases hl2 : l = m' + 1
        · subst hl2
          rw [pairLimVec_succ_of_gt p α m' L (pairPeelRes g) i (m' + 1) (by omega),
            TopLim, sub_zero]
          exact topDegLE_iterate_top_of_shape hα hg hp hshape (hmem (m' + 1)) (i + 1)
        · rw [pairLimVec_succ_of_gt p α m' L (pairPeelRes g) i l (by omega),
            iterate_pairGradShift_vanish_above (by omega : m' + 1 < l) (hvan l (by omega)) (i + 1)]
          exact topLim_const

end GaloisForLFunctions.HTGeometry
