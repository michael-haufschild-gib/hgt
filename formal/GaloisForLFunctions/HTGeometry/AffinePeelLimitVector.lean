import GaloisForLFunctions.HTGeometry.AffineColumnLimits
import GaloisForLFunctions.HTGeometry.PairFamOrbitScaling

/-!
# The limit vectors of the affine peel

Iterating the lower-column recursion produces, level by level, the limit of every row of the peeled
matrix.  The recursion is the same operator one level down — with the head that the limit creates —
plus a single correction in the first step: the residue of the newest column vanishes from the
second row on.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

namespace PairFam

variable (F : PairFam)

/-- **The shifted operator preserves the subfield.** -/
theorem gradShift_mem_coordField {m k : ℕ} {u : ℕ → CascadeField}
    (hu : ∀ l, u l ∈ coordField m) : F.gradShift m u k ∈ coordField m := by
  rw [gradShift]
  refine add_mem (F.law_mem_coordField (hu k)) (sum_mem fun l hl => ?_)
  have hlm : l ≤ m := by
    have := Finset.mem_range.mp hl
    omega
  exact mul_mem (F.response_mem_coordField hlm) (hu l)

theorem iterate_gradShift_mem_coordField {m : ℕ} {u : ℕ → CascadeField}
    (hu : ∀ l, u l ∈ coordField m) (i k : ℕ) :
    ((F.gradShift m)^[i]) u k ∈ coordField m := by
  induction i generalizing k with
  | zero => simpa using hu k
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact F.gradShift_mem_coordField fun l => ih l

theorem gradShift_vanish_above {m l : ℕ} (hl : m < l) {u : ℕ → CascadeField}
    (hu : u l = 0) : F.gradShift m u l = 0 := by
  rw [gradShift, hu, map_zero, zero_add]
  refine Finset.sum_eq_zero fun l' hl' => ?_
  have hlt : l' < l := by
    have := Finset.mem_range.mp hl'
    omega
  rw [F.response_of_lt hlt, zero_mul]

theorem iterate_gradShift_vanish_above {m l : ℕ} (hl : m < l) {u : ℕ → CascadeField}
    (hu : u l = 0) (i : ℕ) : ((F.gradShift m)^[i]) u l = 0 := by
  induction i with
  | zero => simpa using hu
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact F.gradShift_vanish_above hl ih

end PairFam

namespace AffineFam

variable (E : AffineFam)

/-! ## The limit vectors -/

/-- The limit vector of the `i`-th row: the same operator one level down, with the head created by
the limit, plus the residue correction of the newest column. -/
noncomputable def limVec (E : AffineFam) (n : ℕ) (L res : ℕ → CascadeField) :
    ℕ → ℕ → CascadeField
  | 0 => L
  | (i + 1) => fun k =>
      if k ≤ n then
        E.toPairFam.gradShift n (E.limVec n L res i) k
          + E.toPairFam.headBorder (E.lead n) n k
            * (E.toPairFam.jet n * E.lead n * res i)
      else 0

@[simp] theorem limVec_zero (n : ℕ) (L res : ℕ → CascadeField) : E.limVec n L res 0 = L := rfl

theorem limVec_succ_of_le (n : ℕ) (L res : ℕ → CascadeField) (i k : ℕ) (hk : k ≤ n) :
    E.limVec n L res (i + 1) k
      = E.toPairFam.gradShift n (E.limVec n L res i) k
        + E.toPairFam.headBorder (E.lead n) n k
          * (E.toPairFam.jet n * E.lead n * res i) := by
  simp only [limVec]
  rw [if_pos hk]

theorem limVec_succ_of_gt (n : ℕ) (L res : ℕ → CascadeField) (i k : ℕ) (hk : n < k) :
    E.limVec n L res (i + 1) k = 0 := by
  simp only [limVec]
  rw [if_neg (by omega : ¬ k ≤ n)]

theorem limVec_mem_coordField {n : ℕ} {L res : ℕ → CascadeField}
    (hL : ∀ l, L l ∈ coordField n) (hres : ∀ i, res i ∈ coordField n) (i k : ℕ) :
    E.limVec n L res i k ∈ coordField n := by
  induction i generalizing k with
  | zero => exact hL k
  | succ i ih =>
      by_cases hk : k ≤ n
      · rw [E.limVec_succ_of_le n L res i k hk]
        refine add_mem (E.toPairFam.gradShift_mem_coordField fun l => ih l) (mul_mem ?_ ?_)
        · exact E.toPairFam.headBorder_mem_coordField (E.lead_mem_coordField (le_refl n)) k
        · exact mul_mem (mul_mem (E.toPairFam.jet_mem_coordField (le_refl n))
            (E.lead_mem_coordField (le_refl n))) (hres i)
      · rw [E.limVec_succ_of_gt n L res i k (by omega)]
        exact zero_mem _

theorem topFree_limVec {n : ℕ} {L res : ℕ → CascadeField}
    (hL : ∀ l, L l ∈ coordField n) (hres : ∀ i, res i ∈ coordField n) (i k : ℕ) :
    TopFree (n + 1) (E.limVec n L res i k) :=
  topFree_of_mem_coordField (by omega) (E.limVec_mem_coordField hL hres i k)

/-! ## The residue vector -/

/-- The residue of the newest column: the border value at the top, zero below it. -/
noncomputable def peelRes (g₁ g₂ : Polynomial ℂ) : ℕ → CascadeField
  | 0 => algebraMap ℂ CascadeField (1 + (g₁.natDegree : ℂ) - (g₂.natDegree : ℂ))
  | (_ + 1) => 0

theorem peelRes_mem_coordField (g₁ g₂ : Polynomial ℂ) (m i : ℕ) :
    peelRes g₁ g₂ i ∈ coordField m := by
  match i with
  | 0 => exact (coordField m).algebraMap_mem _
  | (_ + 1) => exact zero_mem _

theorem topFree_peelRes (g₁ g₂ : Polynomial ℂ) (m i : ℕ) : TopFree m (peelRes g₁ g₂ i) := by
  match i with
  | 0 => exact topFree_algebraMap_complex m _
  | (_ + 1) => exact topFree_zero m

theorem peelRes_of_ne_zero (g₁ g₂ : Polynomial ℂ) {k : ℕ} (hk : k ≠ 0) :
    peelRes g₁ g₂ k = 0 := by
  match k with
  | 0 => exact absurd rfl hk
  | (_ + 1) => rfl

/-! ## The newest entry, uniformly in the row -/

theorem topDegLE_iterate_top_of_shape {g₁ g₂ : Polynomial ℂ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    {n : ℕ} {u : ℕ → CascadeField} (hshape : E.BorderShape g₁ g₂ (n + 1) u)
    (hmem : u (n + 1) ∈ coordField (n + 1)) (i : ℕ) :
    TopDegLE (n + 1) (-1) (((E.toPairFam.gradShift (n + 1))^[i]) u (n + 1)) := by
  match i with
  | 0 =>
      simp only [Function.iterate_zero, id_eq]
      have hsplit : u (n + 1)
          = E.toPairFam.headBorder (ratFact g₁ g₂ (n + 1)) (n + 1) (n + 1)
            + (u (n + 1)
              - E.toPairFam.headBorder (ratFact g₁ g₂ (n + 1)) (n + 1) (n + 1)) := by ring
      rw [hsplit]
      exact TopDegLE.add (E.topDegLE_headBorder_top hg₁ hg₂ n)
        (TopDegLE.mono (by norm_num) hshape)
  | (r + 1) =>
      rw [E.toPairFam.iterate_gradShift_top, Function.iterate_succ_apply]
      exact TopDegLE.mono (by norm_num)
        (E.topDegLE_iterate_of_shape hg₁ hg₂ hshape hmem r)

theorem topLim_fx_mul_iterate_res {g₁ g₂ : Polynomial ℂ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    {n : ℕ} {u : ℕ → CascadeField} (hshape : E.BorderShape g₁ g₂ (n + 1) u)
    (hmem : u (n + 1) ∈ coordField (n + 1)) (i : ℕ) :
    TopLim (n + 1) (fx (n + 1) * (((E.toPairFam.gradShift (n + 1))^[i]) u (n + 1)))
      (peelRes g₁ g₂ i) := by
  match i with
  | 0 =>
      simp only [Function.iterate_zero, id_eq, peelRes]
      exact E.topLim_fx_mul_of_shape hg₁ hg₂ hshape
  | (r + 1) =>
      simp only [peelRes]
      exact E.topLim_fx_mul_iterate_of_shape hg₁ hg₂ hshape hmem r

/-! ## The limit of every row -/

/-- **Every row of the peeled matrix has the predicted limit.** -/
theorem topLim_iterate_gradShift {g₁ g₂ : Polynomial ℂ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    {n : ℕ} {u L : ℕ → CascadeField}
    (hmem : ∀ l, u l ∈ coordField (n + 1))
    (hvan : ∀ l, n + 1 < l → u l = 0)
    (hLmem : ∀ l, L l ∈ coordField n)
    (hlim0 : ∀ l, TopLim (n + 1) (u l) (L l))
    (hshape : E.BorderShape g₁ g₂ (n + 1) u)
    (i l : ℕ) :
    TopLim (n + 1) (((E.toPairFam.gradShift (n + 1))^[i]) u l)
      (E.limVec n L (peelRes g₁ g₂) i l) := by
  classical
  induction i generalizing l with
  | zero =>
      rw [E.limVec_zero, Function.iterate_zero_apply]
      exact hlim0 l
  | succ i ih =>
      by_cases hl : l ≤ n
      · rw [E.limVec_succ_of_le n L (peelRes g₁ g₂) i l hl, Function.iterate_succ_apply']
        refine E.topLim_gradShift_lower hl
          (fun l' => sub_mem (E.toPairFam.iterate_gradShift_mem_coordField hmem i l')
            (coordField_mono (by omega)
              (E.limVec_mem_coordField hLmem (peelRes_mem_coordField g₁ g₂ n) i l')))
          (fun l' => E.topFree_limVec hLmem (peelRes_mem_coordField g₁ g₂ n) i l')
          (fun l' => ih l')
          (topFree_peelRes g₁ g₂ (n + 1) i)
          (E.topDegLE_iterate_top_of_shape hg₁ hg₂ hshape (hmem (n + 1)) i)
          (E.topLim_fx_mul_iterate_res hg₁ hg₂ hshape (hmem (n + 1)) i)
      · by_cases hl2 : l = n + 1
        · subst hl2
          rw [E.limVec_succ_of_gt n L (peelRes g₁ g₂) i (n + 1) (by omega), TopLim, sub_zero]
          exact E.topDegLE_iterate_top_of_shape hg₁ hg₂ hshape (hmem (n + 1)) (i + 1)
        · rw [E.limVec_succ_of_gt n L (peelRes g₁ g₂) i l (by omega),
            E.toPairFam.iterate_gradShift_vanish_above (by omega : n + 1 < l)
              (hvan l (by omega)) (i + 1)]
          exact topLim_const

end AffineFam

end GaloisForLFunctions.HTGeometry
