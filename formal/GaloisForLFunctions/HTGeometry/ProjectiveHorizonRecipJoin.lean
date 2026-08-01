import GaloisForLFunctions.HTGeometry.ProjectiveHorizonRecipSystemMatrix
import GaloisForLFunctions.HTGeometry.LinearSystemIntermediateField

/-!
# Two deep horizons of a coordinate and its reciprocal reconstruct every jet

The reciprocal relations of orders `2n` to `4n-1` form a nonsingular square system whose unknowns
are exactly the jets below order `n` of the base coordinate and of its reciprocal, and whose
coefficients and constants involve only jets of order at least `n`.

So any intermediate field containing the deep jets of the coordinate and the deep jets of its
reciprocal contains the missing ones as well, hence every jet, hence everything.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- The unknowns of the reconstruction system: the jets below order `n` of the base coordinate and
of its reciprocal. -/
def recipUnknown (C : Type*) [Field C] (n : ℕ) : Fin n ⊕ Fin n → FreeScalarJetField C :=
  Sum.elim (fun k : Fin n => freeCoordinate C ℕ (k : ℕ)) (fun j : Fin n => recipJet C (j : ℕ))

/-- The constant side of the reconstruction system: the part of each relation in which both orders
are at least `n`. -/
def recipRHS (C : Type*) [Field C] (n : ℕ) (r : Fin n ⊕ Fin n) : FreeScalarJetField C :=
  -∑ k ∈ Finset.Ico n (reconNode n r + 1 - n),
      (Nat.choose (reconNode n r) k : FreeScalarJetField C) *
        (freeCoordinate C ℕ k * recipJet C (reconNode n r - k))

omit [CharZero C] in
/-- **The reconstruction system holds.** -/
theorem recipSystem_mulVec (n : ℕ) (hn : 0 < n) :
    (recipSystemMatrix C n).mulVec (recipUnknown C n) = recipRHS C n := by
  funext r
  have hnode := two_mul_le_reconNode n r
  have hm : 0 < reconNode n r := by omega
  have hnm : 2 * n ≤ reconNode n r + 1 := by omega
  have h := recip_relation_split (C := C) (n := n) hm hnm
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  simp only [recipSystemMatrix, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, recipUnknown]
  rw [Fin.sum_univ_eq_sum_range (fun k => (Nat.choose (reconNode n r) k :
      FreeScalarJetField C) * recipJet C (reconNode n r - k) * freeCoordinate C ℕ k) n,
    Fin.sum_univ_eq_sum_range (fun j => (Nat.choose (reconNode n r) j :
      FreeScalarJetField C) * freeCoordinate C ℕ (reconNode n r - j) * recipJet C j) n]
  have e1 : ∑ k ∈ Finset.range n, (Nat.choose (reconNode n r) k : FreeScalarJetField C) *
        recipJet C (reconNode n r - k) * freeCoordinate C ℕ k =
      ∑ k ∈ Finset.range n, (Nat.choose (reconNode n r) k) •
        (freeCoordinate C ℕ k * recipJet C (reconNode n r - k)) :=
    Finset.sum_congr rfl fun k _ => by rw [nsmul_eq_mul]; ring
  have e2 : ∑ j ∈ Finset.range n, (Nat.choose (reconNode n r) j : FreeScalarJetField C) *
        freeCoordinate C ℕ (reconNode n r - j) * recipJet C j =
      ∑ j ∈ Finset.range n, (Nat.choose (reconNode n r) j) •
        (freeCoordinate C ℕ (reconNode n r - j) * recipJet C j) :=
    Finset.sum_congr rfl fun j _ => by rw [nsmul_eq_mul]; ring
  rw [e1, e2, recipRHS, eq_neg_iff_add_eq_zero]
  have e3 : ∑ k ∈ Finset.Ico n (reconNode n r + 1 - n),
        (Nat.choose (reconNode n r) k : FreeScalarJetField C) *
          (freeCoordinate C ℕ k * recipJet C (reconNode n r - k)) =
      ∑ k ∈ Finset.Ico n (reconNode n r + 1 - n), (Nat.choose (reconNode n r) k) •
        (freeCoordinate C ℕ k * recipJet C (reconNode n r - k)) :=
    Finset.sum_congr rfl fun k _ => by rw [nsmul_eq_mul]
  rw [e3]
  linear_combination h

/-- **Every jet is recovered.**  An intermediate field containing the jets of order at least `n` of
the base coordinate and of its reciprocal contains every jet of the base coordinate. -/
theorem freeCoordinate_mem_of_recip_tail {n : ℕ}
    (L : IntermediateField C (FreeScalarJetField C))
    (hx : ∀ j, n ≤ j → freeCoordinate C ℕ j ∈ L)
    (hb : ∀ j, n ≤ j → recipJet C j ∈ L) :
    ∀ i : ℕ, freeCoordinate C ℕ i ∈ L := by
  intro i
  rcases le_or_gt n i with hi | hi
  · exact hx i hi
  have hn : 0 < n := by omega
  have hM : ∀ r s, recipSystemMatrix C n r s ∈ L := by
    intro r s
    have hnode := two_mul_le_reconNode n r
    rw [recipSystemMatrix, Matrix.of_apply]
    cases s with
    | inl k =>
        have hk := k.2
        rw [Sum.elim_inl]
        exact mul_mem (natCast_mem L _) (hb _ (by omega))
    | inr j =>
        have hj := j.2
        rw [Sum.elim_inr]
        exact mul_mem (natCast_mem L _) (hx _ (by omega))
  have hc : ∀ r, recipRHS C n r ∈ L := by
    intro r
    have hnode := two_mul_le_reconNode n r
    rw [recipRHS]
    refine neg_mem (sum_mem fun k hk => ?_)
    rw [Finset.mem_Ico] at hk
    exact mul_mem (natCast_mem L _)
      (mul_mem (hx k hk.1) (hb _ (by omega)))
  have hsol := mulVec_solution_mem L hM hc (det_recipSystemMatrix_ne_zero (C := C) n)
    (recipSystem_mulVec (C := C) n hn) (Sum.inl ⟨i, hi⟩)
  rw [recipUnknown, Sum.elim_inl] at hsol
  exact hsol

/-- **The join of two opposite deep horizons is everything.**  An intermediate field containing the
jets of order at least `n` of the base coordinate and of its reciprocal is the whole free scalar
jet field. -/
theorem recipTail_join_eq_top {n : ℕ}
    (L : IntermediateField C (FreeScalarJetField C))
    (hx : ∀ j, n ≤ j → freeCoordinate C ℕ j ∈ L)
    (hb : ∀ j, n ≤ j → recipJet C j ∈ L) : L = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← freeCoordinateField_univ (C := C) (σ := ℕ), freeCoordinateField,
    IntermediateField.adjoin_le_iff]
  rintro _ ⟨m, -, rfl⟩
  exact freeCoordinate_mem_of_recip_tail L hx hb m

/-- **The all-depth join.**  At every depth the field generated by the deep jets of the base
coordinate together with the field generated by the deep jets of its reciprocal is the whole free
scalar jet field. -/
theorem jetTail_sup_recipTail_eq_top (n : ℕ) :
    IntermediateField.adjoin C {z | ∃ j, n ≤ j ∧ z = freeCoordinate C ℕ j} ⊔
      IntermediateField.adjoin C {z | ∃ j, n ≤ j ∧ z = recipJet C j} = ⊤ := by
  refine recipTail_join_eq_top (n := n) _ (fun j hj => ?_) (fun j hj => ?_)
  · have h : IntermediateField.adjoin C {z | ∃ j, n ≤ j ∧ z = freeCoordinate C ℕ j} ≤
        IntermediateField.adjoin C {z | ∃ j, n ≤ j ∧ z = freeCoordinate C ℕ j} ⊔
          IntermediateField.adjoin C {z | ∃ j, n ≤ j ∧ z = recipJet C j} := le_sup_left
    exact h (IntermediateField.subset_adjoin _ _ ⟨j, hj, rfl⟩)
  · have h : IntermediateField.adjoin C {z | ∃ j, n ≤ j ∧ z = recipJet C j} ≤
        IntermediateField.adjoin C {z | ∃ j, n ≤ j ∧ z = freeCoordinate C ℕ j} ⊔
          IntermediateField.adjoin C {z | ∃ j, n ≤ j ∧ z = recipJet C j} := le_sup_right
    exact h (IntermediateField.subset_adjoin _ _ ⟨j, hj, rfl⟩)

end

end GaloisForLFunctions.HTGeometry
