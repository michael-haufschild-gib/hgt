import GaloisForLFunctions.RHTower.DeningerBarFibre

/-!
# The bar differential squares to zero

Two unit insertions commute, so the double fibre of two bar faces depends only on the unordered
pair of inserted positions.  The standard simplicial pairing `(j, j') ↦ (j'-1, j)` on the index
set therefore matches the double fibres while reversing the sign, and the alternating sum
vanishes.

* `deningerBarDouble` : the double fibre of two faces.
* `deningerBarDouble_swap` : **the simplicial identity for double fibres.**
* `deningerBarDiffCoe_comp_self` : **`b² = 0`.**
-/

namespace RHTower

open GaloisForLFunctions

open scoped Classical

noncomputable section

variable {L : ℕ}

/-! ## Insertion in natural coordinates -/

/-- The commutation of two unit insertions, in natural-number positions. -/
theorem deningerInsertUnit_comm_nat {r : ℕ} (f : Fin (r + 1) → DeningerPrimeLattice) (p q : ℕ)
    (hp : p < r + 3) (hq : q < r + 2) (hpq : p ≤ q) :
    deningerInsertUnit ⟨p, hp⟩ (deningerInsertUnit ⟨q, hq⟩ f)
      = deningerInsertUnit ⟨q + 1, by omega⟩
          (deningerInsertUnit ⟨p, by omega⟩ f) := by
  have hcast : (Fin.castSucc (⟨p, by omega⟩ : Fin (r + 2)) : Fin (r + 3)) = ⟨p, hp⟩ :=
    Fin.ext (by simp)
  have hsucc : (Fin.succ (⟨q, hq⟩ : Fin (r + 2)) : Fin (r + 3)) = ⟨q + 1, by omega⟩ :=
    Fin.ext (by simp)
  have h := deningerInsertUnit_comm f ⟨p, by omega⟩ ⟨q, hq⟩ (by simpa using hpq)
  rw [hcast, hsucc] at h
  exact h

/-! ## The double fibre -/

/-- The double fibre of the faces `j` and `j'`. -/
def deningerBarDouble (j : Fin (L + 1)) (j' : Fin (L + 2))
    (f : Fin (L + 1) → DeningerPrimeLattice) : Finset (Fin (L + 3) → DeningerPrimeLattice) :=
  (deningerBarFibre j f).biUnion (deningerBarFibre j')

theorem deningerBarDouble_eq (j : Fin (L + 1)) (j' : Fin (L + 2))
    (f : Fin (L + 1) → DeningerPrimeLattice) :
    deningerBarDouble j j' f =
      ({deningerInsertUnit j'.castSucc (deningerInsertUnit j.castSucc f),
        deningerInsertUnit j'.succ (deningerInsertUnit j.castSucc f),
        deningerInsertUnit j'.castSucc (deningerInsertUnit j.succ f),
        deningerInsertUnit j'.succ (deningerInsertUnit j.succ f)} :
          Finset (Fin (L + 3) → DeningerPrimeLattice)) := by
  rw [deningerBarDouble, deningerBarFibre, Finset.biUnion_insert, Finset.singleton_biUnion,
    deningerBarFibre, deningerBarFibre]
  ext u
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The double fibre in natural coordinates. -/
theorem deningerBarDouble_eq_nat (j : Fin (L + 1)) (j' : Fin (L + 2))
    (f : Fin (L + 1) → DeningerPrimeLattice) :
    deningerBarDouble j j' f =
      ({deningerInsertUnit ⟨(j' : ℕ), by omega⟩ (deningerInsertUnit ⟨(j : ℕ), by omega⟩ f),
        deningerInsertUnit ⟨(j' : ℕ) + 1, by omega⟩
          (deningerInsertUnit ⟨(j : ℕ), by omega⟩ f),
        deningerInsertUnit ⟨(j' : ℕ), by omega⟩
          (deningerInsertUnit ⟨(j : ℕ) + 1, by omega⟩ f),
        deningerInsertUnit ⟨(j' : ℕ) + 1, by omega⟩
          (deningerInsertUnit ⟨(j : ℕ) + 1, by omega⟩ f)} :
          Finset (Fin (L + 3) → DeningerPrimeLattice)) := by
  rw [deningerBarDouble_eq]
  have e1 : (j'.castSucc : Fin (L + 3)) = ⟨(j' : ℕ), by omega⟩ := Fin.ext (by simp)
  have e2 : (j'.succ : Fin (L + 3)) = ⟨(j' : ℕ) + 1, by omega⟩ := Fin.ext (by simp)
  have e3 : (j.castSucc : Fin (L + 2)) = ⟨(j : ℕ), by omega⟩ := Fin.ext (by simp)
  have e4 : (j.succ : Fin (L + 2)) = ⟨(j : ℕ) + 1, by omega⟩ := Fin.ext (by simp)
  rw [e1, e2, e3, e4]

/-- **The simplicial identity for double fibres.** -/
theorem deningerBarDouble_swap (f : Fin (L + 1) → DeningerPrimeLattice)
    (j : Fin (L + 1)) (j' : Fin (L + 2)) (h : (j : ℕ) < (j' : ℕ)) :
    deningerBarDouble j j' f
      = deningerBarDouble ⟨(j' : ℕ) - 1, by omega⟩ ⟨(j : ℕ), by omega⟩ f := by
  have hjL : (j : ℕ) < L + 1 := j.isLt
  have hj'L : (j' : ℕ) < L + 2 := j'.isLt
  rw [deningerBarDouble_eq_nat, deningerBarDouble_eq_nat]
  have hnorm : (⟨(j' : ℕ) - 1 + 1, by omega⟩ : Fin (L + 2)) = ⟨(j' : ℕ), hj'L⟩ :=
    Fin.ext (by simp; omega)
  rw [hnorm]
  have r1 : deningerInsertUnit (⟨(j : ℕ), by omega⟩ : Fin (L + 3))
        (deningerInsertUnit (⟨(j' : ℕ) - 1, by omega⟩ : Fin (L + 2)) f)
      = deningerInsertUnit (⟨(j' : ℕ), by omega⟩ : Fin (L + 3))
        (deningerInsertUnit (⟨(j : ℕ), by omega⟩ : Fin (L + 2)) f) := by
    rw [deningerInsertUnit_comm_nat f (j : ℕ) ((j' : ℕ) - 1) (by omega) (by omega) (by omega)]
    congr 1
    exact Fin.ext (by simp; omega)
  have r3 : deningerInsertUnit (⟨(j : ℕ), by omega⟩ : Fin (L + 3))
        (deningerInsertUnit (⟨(j' : ℕ), hj'L⟩ : Fin (L + 2)) f)
      = deningerInsertUnit (⟨(j' : ℕ) + 1, by omega⟩ : Fin (L + 3))
        (deningerInsertUnit (⟨(j : ℕ), by omega⟩ : Fin (L + 2)) f) :=
    deningerInsertUnit_comm_nat f (j : ℕ) (j' : ℕ) (by omega) hj'L (by omega)
  have r4 : deningerInsertUnit (⟨(j : ℕ) + 1, by omega⟩ : Fin (L + 3))
        (deningerInsertUnit (⟨(j' : ℕ), hj'L⟩ : Fin (L + 2)) f)
      = deningerInsertUnit (⟨(j' : ℕ) + 1, by omega⟩ : Fin (L + 3))
        (deningerInsertUnit (⟨(j : ℕ) + 1, by omega⟩ : Fin (L + 2)) f) :=
    deningerInsertUnit_comm_nat f ((j : ℕ) + 1) (j' : ℕ) (by omega) hj'L (by omega)
  rcases Nat.lt_or_ge ((j : ℕ) + 1) (j' : ℕ) with hlt | hge
  · have r2 : deningerInsertUnit (⟨(j : ℕ) + 1, by omega⟩ : Fin (L + 3))
          (deningerInsertUnit (⟨(j' : ℕ) - 1, by omega⟩ : Fin (L + 2)) f)
        = deningerInsertUnit (⟨(j' : ℕ), by omega⟩ : Fin (L + 3))
          (deningerInsertUnit (⟨(j : ℕ) + 1, by omega⟩ : Fin (L + 2)) f) := by
      rw [deningerInsertUnit_comm_nat f ((j : ℕ) + 1) ((j' : ℕ) - 1)
        (by omega) (by omega) (by omega)]
      congr 1
      exact Fin.ext (by simp; omega)
    ext u
    simp only [Finset.mem_insert, Finset.mem_singleton, r1, r2, r3, r4]
    tauto
  · have hj'eq : (j' : ℕ) = (j : ℕ) + 1 := by omega
    have r2 : deningerInsertUnit (⟨(j : ℕ) + 1, by omega⟩ : Fin (L + 3))
          (deningerInsertUnit (⟨(j' : ℕ) - 1, by omega⟩ : Fin (L + 2)) f)
        = deningerInsertUnit (⟨(j' : ℕ), by omega⟩ : Fin (L + 3))
          (deningerInsertUnit (⟨(j : ℕ), by omega⟩ : Fin (L + 2)) f) := by
      have hstep := deningerInsertUnit_comm_nat f (j : ℕ) (j : ℕ)
        (by omega) (by omega) (le_refl _)
      have e1 : (⟨(j' : ℕ) - 1, by omega⟩ : Fin (L + 2)) = ⟨(j : ℕ), by omega⟩ :=
        Fin.ext (by simp; omega)
      have e2 : (⟨(j : ℕ) + 1, by omega⟩ : Fin (L + 3))
          = ⟨(j' : ℕ), by omega⟩ := Fin.ext (by simp; omega)
      rw [e1, ← e2, ← hstep]
    have l4 : deningerInsertUnit (⟨(j' : ℕ) + 1, by omega⟩ : Fin (L + 3))
          (deningerInsertUnit (⟨(j : ℕ) + 1, by omega⟩ : Fin (L + 2)) f)
        = deningerInsertUnit (⟨(j' : ℕ), by omega⟩ : Fin (L + 3))
          (deningerInsertUnit (⟨(j : ℕ) + 1, by omega⟩ : Fin (L + 2)) f) := by
      have hstep := deningerInsertUnit_comm_nat f ((j : ℕ) + 1) ((j : ℕ) + 1)
        (by omega) (by omega) (le_refl _)
      have e2 : (⟨(j : ℕ) + 1 + 1, by omega⟩ : Fin (L + 3))
          = ⟨(j' : ℕ) + 1, by omega⟩ := Fin.ext (by simp; omega)
      have e3 : (⟨(j : ℕ) + 1, by omega⟩ : Fin (L + 3))
          = ⟨(j' : ℕ), by omega⟩ := Fin.ext (by simp; omega)
      rw [← e3, ← e2, ← hstep]
    ext u
    simp only [Finset.mem_insert, Finset.mem_singleton, r1, r2, r3, r4, l4]
    tauto

/-! ## The involution and the vanishing -/

/-- The simplicial pairing on the index set of the double sum. -/
def deningerBarSwapIdx (q : Fin (L + 1) × Fin (L + 2)) : Fin (L + 1) × Fin (L + 2) :=
  if h : (q.1 : ℕ) < (q.2 : ℕ) then
    (⟨(q.2 : ℕ) - 1, by have := q.1.isLt; have := q.2.isLt; omega⟩,
      ⟨(q.1 : ℕ), by have := q.1.isLt; omega⟩)
  else
    (⟨(q.2 : ℕ), by have := q.1.isLt; have := q.2.isLt; omega⟩,
      ⟨(q.1 : ℕ) + 1, by have := q.1.isLt; omega⟩)

theorem deningerBarSwapIdx_pos {q : Fin (L + 1) × Fin (L + 2)} (h : (q.1 : ℕ) < (q.2 : ℕ)) :
    deningerBarSwapIdx q
      = (⟨(q.2 : ℕ) - 1, by have := q.1.isLt; have := q.2.isLt; omega⟩,
          ⟨(q.1 : ℕ), by have := q.1.isLt; omega⟩) := dif_pos h

theorem deningerBarSwapIdx_neg {q : Fin (L + 1) × Fin (L + 2)}
    (h : ¬ ((q.1 : ℕ) < (q.2 : ℕ))) :
    deningerBarSwapIdx q
      = (⟨(q.2 : ℕ), by have := q.1.isLt; have := q.2.isLt; omega⟩,
          ⟨(q.1 : ℕ) + 1, by have := q.1.isLt; omega⟩) := dif_neg h

theorem deningerBarSwapIdx_involutive (q : Fin (L + 1) × Fin (L + 2)) :
    deningerBarSwapIdx (deningerBarSwapIdx q) = q := by
  have h1 := q.1.isLt
  have h2 := q.2.isLt
  by_cases h : (q.1 : ℕ) < (q.2 : ℕ)
  · rw [deningerBarSwapIdx_pos h,
      deningerBarSwapIdx_neg (q := (⟨(q.2 : ℕ) - 1, by omega⟩, ⟨(q.1 : ℕ), by omega⟩))
        (by simp; omega)]
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    all_goals simp
    all_goals omega
  · rw [deningerBarSwapIdx_neg h,
      deningerBarSwapIdx_pos (q := (⟨(q.2 : ℕ), by omega⟩, ⟨(q.1 : ℕ) + 1, by omega⟩))
        (by simp; omega)]
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    all_goals simp

theorem deningerBarSwapIdx_ne (q : Fin (L + 1) × Fin (L + 2)) :
    deningerBarSwapIdx q ≠ q := by
  have h1 := q.1.isLt
  have h2 := q.2.isLt
  by_cases h : (q.1 : ℕ) < (q.2 : ℕ)
  · rw [deningerBarSwapIdx_pos h]
    intro hq
    have hval : ((q.1 : ℕ)) = ((q.2 : Fin (L + 2)) : ℕ) := by
      have hc := congrArg (fun x : Fin (L + 1) × Fin (L + 2) => ((x.2 : Fin (L + 2)) : ℕ)) hq
      simpa using hc
    omega
  · rw [deningerBarSwapIdx_neg h]
    intro hq
    have hval : ((q.1 : ℕ) + 1) = ((q.2 : Fin (L + 2)) : ℕ) := by
      have hc := congrArg (fun x : Fin (L + 1) × Fin (L + 2) => ((x.2 : Fin (L + 2)) : ℕ)) hq
      simpa using hc
    omega

theorem deningerBarDouble_swapIdx (f : Fin (L + 1) → DeningerPrimeLattice)
    (q : Fin (L + 1) × Fin (L + 2)) :
    deningerBarDouble (deningerBarSwapIdx q).1 (deningerBarSwapIdx q).2 f
      = deningerBarDouble q.1 q.2 f := by
  have h1 := q.1.isLt
  have h2 := q.2.isLt
  by_cases h : (q.1 : ℕ) < (q.2 : ℕ)
  · rw [deningerBarSwapIdx_pos h]
    exact (deningerBarDouble_swap f q.1 q.2 h).symm
  · rw [deningerBarSwapIdx_neg h]
    have hlt : ((⟨(q.2 : ℕ), by omega⟩ : Fin (L + 1)) : ℕ)
        < ((⟨(q.1 : ℕ) + 1, by omega⟩ : Fin (L + 2)) : ℕ) := by simp; omega
    rw [deningerBarDouble_swap f ⟨(q.2 : ℕ), by omega⟩ ⟨(q.1 : ℕ) + 1, by omega⟩ hlt]
    congr 1

theorem deningerBarSign_swapIdx (q : Fin (L + 1) × Fin (L + 2)) :
    ((-1 : ℂ) ^ (((deningerBarSwapIdx q).1 : Fin (L + 1)) : ℕ) *
        (-1 : ℂ) ^ (((deningerBarSwapIdx q).2 : Fin (L + 2)) : ℕ))
      = -((-1 : ℂ) ^ ((q.1 : Fin (L + 1)) : ℕ) * (-1 : ℂ) ^ ((q.2 : Fin (L + 2)) : ℕ)) := by
  have h1 := q.1.isLt
  have h2 := q.2.isLt
  by_cases h : (q.1 : ℕ) < (q.2 : ℕ)
  · rw [deningerBarSwapIdx_pos h]
    have hq2 : ((q.2 : Fin (L + 2)) : ℕ) = ((q.2 : ℕ) - 1) + 1 := by omega
    show (-1 : ℂ) ^ ((q.2 : ℕ) - 1) * (-1 : ℂ) ^ ((q.1 : ℕ))
      = -((-1 : ℂ) ^ ((q.1 : ℕ)) * (-1 : ℂ) ^ ((q.2 : ℕ)))
    calc (-1 : ℂ) ^ ((q.2 : ℕ) - 1) * (-1 : ℂ) ^ ((q.1 : ℕ))
        = -((-1 : ℂ) ^ ((q.1 : ℕ)) * ((-1 : ℂ) ^ ((q.2 : ℕ) - 1) * (-1))) := by ring
      _ = -((-1 : ℂ) ^ ((q.1 : ℕ)) * (-1 : ℂ) ^ (((q.2 : ℕ) - 1) + 1)) := by rw [pow_succ]
      _ = -((-1 : ℂ) ^ ((q.1 : ℕ)) * (-1 : ℂ) ^ ((q.2 : ℕ))) := by rw [← hq2]
  · rw [deningerBarSwapIdx_neg h]
    show (-1 : ℂ) ^ ((q.2 : ℕ)) * (-1 : ℂ) ^ ((q.1 : ℕ) + 1)
      = -((-1 : ℂ) ^ ((q.1 : ℕ)) * (-1 : ℂ) ^ ((q.2 : ℕ)))
    rw [pow_succ]
    ring

/-- **The bar differential squares to zero.** -/
theorem deningerBarDiffCoe_comp_self (c : DeningerBarWord → ℂ) :
    deningerBarDiffCoe (deningerBarDiffCoe c) = 0 := by
  funext w
  obtain ⟨L, f⟩ := w
  show deningerBarDiffCoe (deningerBarDiffCoe c) (⟨L, f⟩ : DeningerBarWord) = 0
  set F : Fin (L + 1) × Fin (L + 2) → ℂ := fun q =>
    ((-1 : ℂ) ^ ((q.1 : Fin (L + 1)) : ℕ) * (-1 : ℂ) ^ ((q.2 : Fin (L + 2)) : ℕ)) *
      ∑ u ∈ deningerBarDouble q.1 q.2 f, c (⟨L + 2, u⟩ : DeningerBarWord) with hF
  have hexpand : deningerBarDiffCoe (deningerBarDiffCoe c) (⟨L, f⟩ : DeningerBarWord)
      = ∑ q : Fin (L + 1) × Fin (L + 2), F q := by
    rw [deningerBarDiffCoe_eq_sum]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hv : ∀ v ∈ deningerBarFibre j f,
        deningerBarDiffCoe c (⟨L + 1, v⟩ : DeningerBarWord)
          = ∑ j' : Fin (L + 2), (-1 : ℂ) ^ (j' : ℕ) *
              ∑ u ∈ deningerBarFibre j' v, c (⟨L + 2, u⟩ : DeningerBarWord) :=
      fun v _ => deningerBarDiffCoe_eq_sum c v
    rw [Finset.sum_congr rfl hv, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [hF]
    show _ = ((-1 : ℂ) ^ (j : ℕ) * (-1 : ℂ) ^ (j' : ℕ)) *
      ∑ u ∈ deningerBarDouble j j' f, c (⟨L + 2, u⟩ : DeningerBarWord)
    rw [deningerBarDouble, Finset.sum_biUnion, Finset.mul_sum, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun v _ => ?_
      ring
    · intro v hv' v' hv'' hne
      exact deningerBarFibre_disjoint hne
  rw [hexpand]
  refine Finset.sum_involution (fun q _ => deningerBarSwapIdx q) ?_ ?_ ?_ ?_
  · intro q _
    rw [hF]
    show (((-1 : ℂ) ^ ((q.1 : Fin (L + 1)) : ℕ) * (-1 : ℂ) ^ ((q.2 : Fin (L + 2)) : ℕ)) *
        ∑ u ∈ deningerBarDouble q.1 q.2 f, c (⟨L + 2, u⟩ : DeningerBarWord))
      + (((-1 : ℂ) ^ (((deningerBarSwapIdx q).1 : Fin (L + 1)) : ℕ) *
          (-1 : ℂ) ^ (((deningerBarSwapIdx q).2 : Fin (L + 2)) : ℕ)) *
        ∑ u ∈ deningerBarDouble (deningerBarSwapIdx q).1 (deningerBarSwapIdx q).2 f,
          c (⟨L + 2, u⟩ : DeningerBarWord)) = 0
    rw [deningerBarDouble_swapIdx f q, deningerBarSign_swapIdx q]
    ring
  · intro q _ _
    exact deningerBarSwapIdx_ne q
  · intro q _
    exact Finset.mem_univ _
  · intro q _
    exact deningerBarSwapIdx_involutive q

end

end RHTower
